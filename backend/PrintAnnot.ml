(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Printing annotations in asm syntax *)

open Printf
open Datatypes
open Integers
open Floats
open Camlcoq
open AST
open Memdata
open Asm

(** Line number annotations *)

let filename_info : (string, int * Printlines.filebuf option) Hashtbl.t
                  = Hashtbl.create 7

let last_file = ref ""

let reset_filenames () =
  Hashtbl.clear filename_info; last_file := ""

let close_filenames () =
  Hashtbl.iter
    (fun file (num, fb) ->
       match fb with Some b -> Printlines.close b | None -> ())
    filename_info;
  reset_filenames()

let enter_filename f =
  let num = Hashtbl.length filename_info + 1 in
  let filebuf =
    if !Clflags.option_S || !Clflags.option_dasm then begin
      try Some (Printlines.openfile f)
      with Sys_error _ -> None
    end else None in
  Hashtbl.add filename_info f (num, filebuf);
  (num, filebuf)

(* Add file and line debug location, using GNU assembler-style DWARF2
   directives *)

let print_file_line oc pref file line =
  if !Clflags.option_g && file <> "" then begin
    let (filenum, filebuf) =
      try
        Hashtbl.find filename_info file
      with Not_found ->
        let (filenum, filebuf as res) = enter_filename file in
        fprintf oc "	.file	%d %S\n" filenum file;
        res in
    fprintf oc "	.loc	%d %d\n" filenum line;
    match filebuf with
    | None -> ()
    | Some fb -> Printlines.copy oc pref fb line line
  end

(* Add file and line debug location, using DWARF1 directives in the style
   of Diab C 5 *)

let print_file_line_d1 oc pref file line =
  if !Clflags.option_g && file <> "" then begin
    let (_, filebuf) =
      try
        Hashtbl.find filename_info file
      with Not_found ->
        enter_filename file in
    if file <> !last_file then begin
      fprintf oc "	.d1file	%S\n" file;
      last_file := file
    end;
    fprintf oc "	.d1line	%d\n" line;
    match filebuf with
    | None -> ()
    | Some fb -> Printlines.copy oc pref fb line line
  end

(** "True" annotations *)

let re_annot_param = Str.regexp "%%\\|%[1-9][0-9]*"

type arg_value =
  | Reg of preg
  | Stack of memory_chunk * Int.int
  | Intconst of Int.int
  | Floatconst of float

let print_annot_text print_preg sp_reg_name oc txt args =
  let print_fragment = function
  | Str.Text s ->
      output_string oc s
  | Str.Delim "%%" ->
      output_char oc '%'
  | Str.Delim s ->
      let n = int_of_string (String.sub s 1 (String.length s - 1)) in
      try
        match List.nth args (n-1) with
        | Reg r ->
            print_preg oc r
        | Stack(chunk, ofs) ->
            fprintf oc "mem(%s + %ld, %ld)"
               sp_reg_name
               (camlint_of_coqint ofs)
               (camlint_of_coqint (size_chunk chunk))
        | Intconst n ->
            fprintf oc "%ld" (camlint_of_coqint n)
        | Floatconst n ->
            fprintf oc "%.18g" (camlfloat_of_coqfloat n)
      with Failure _ ->
        fprintf oc "<bad parameter %s>" s in
  List.iter print_fragment (Str.full_split re_annot_param txt);
  fprintf oc "\n"

let rec annot_args tmpl args =
  match tmpl, args with
  | [], _ -> []
  | AA_arg _ :: tmpl', APreg r :: args' ->
      Reg r :: annot_args tmpl' args'
  | AA_arg _ :: tmpl', APstack(chunk, ofs) :: args' ->
      Stack(chunk, ofs) :: annot_args tmpl' args'
  | AA_arg _ :: tmpl', [] -> []         (* should never happen *)
  | AA_int n :: tmpl', _ ->
      Intconst n :: annot_args tmpl' args
  | AA_float n :: tmpl', _ ->
      Floatconst n :: annot_args tmpl' args

let print_annot_stmt print_preg sp_reg_name oc txt tmpl args =
  print_annot_text print_preg sp_reg_name oc txt (annot_args tmpl args)

let print_annot_val print_preg oc txt args =
  print_annot_text print_preg "<internal error>" oc txt
    (List.map (fun r -> Reg r) args)

(* Print CompCert version and command-line as asm comment *)

let print_version_and_options oc comment =
  fprintf oc "%s File generated by CompCert %s\n" comment Configuration.version;
  fprintf oc "%s Command line:" comment;
  for i = 1 to Array.length Sys.argv - 1 do
    fprintf oc " %s" Sys.argv.(i)
  done;
  fprintf oc "\n"

