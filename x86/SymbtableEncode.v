(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Sep 21, 2019 *)
(* *******************  *)

(** * Encoding of the symbol table into a section *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import RelocProgram Encode.
Require Import SeqTable Memdata.
Require Import Hex encode.Bits.
Import Hex Bits.
Import ListNotations.


Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.


(** Symbol entry definition:

   typedef struct {
   Elf32_Word     st_name;
   Elf32_Addr     st_value;
   Elf32_Word     st_size;
   unsigned char  st_info;
   unsigned char  st_other;
   Elf32_Half     st_shndx;
   } Elf32_Sym

*)

Definition encode_symbtype (t:symbtype) :=
  match t with
  | symb_func => 2
  | symb_data => 1
  | symb_notype => 0
  end.

Definition encode_symbbind (b:bindtype) :=
  match b with
  | bind_local => 0
  | bind_global => 1
  end.

Definition encode_glob_symb_info (b:bindtype) (t:symbtype) := 
  (encode_symbbind b) * (Z.pow 2 4) + encode_symbtype t.

Definition encode_secindex (i:secindex) :=
  let shn_comm := HZ["FFF2"] in
  let shn_undef := 0 in 
  let v := 
      match i with
      | secindex_comm => shn_comm
      | secindex_undef => shn_undef
      | secindex_normal i => Z.of_N i
      end in
  encode_int 2 v.

Section WITH_STRTAB.

Variable (strtab: strtable).

Definition encode_symbentry (e:symbentry)  : res (list byte) :=
  do name_index <-
     let id := (symbentry_id e) in
     match strtab ! id with
     | None => Error [MSG "No string associated with this symbol"; POS id]
     | Some si => OK si
     end;
  let st_name_bytes := encode_int32 name_index in 
  let st_value_bytes := encode_int32 (symbentry_value e) in
  let st_size_bytes := encode_int32 (symbentry_size e) in
  let st_info_bytes := 
      bytes_of_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  let st_shndx_bytes := encode_secindex (symbentry_secindex e) in
  OK (st_name_bytes ++ st_value_bytes ++ st_size_bytes ++
                    st_info_bytes ++ st_other_bytes ++ st_shndx_bytes).

Definition encode_dummy_symbentry : (list byte) :=
  let e := {| symbentry_id := 1%positive;
              symbentry_bind := bind_local;
              symbentry_type := symb_notype;
              symbentry_value := 0;
              symbentry_secindex := secindex_undef;
              symbentry_size := 0;
           |} in
  let st_name_bytes := encode_int32 0 in 
  let st_value_bytes := encode_int32 (symbentry_value e) in
  let st_size_bytes := encode_int32 (symbentry_size e) in
  let st_info_bytes := 
      bytes_of_int 1 (encode_glob_symb_info (symbentry_bind e) (symbentry_type e)) in
  let st_other_bytes := [Byte.repr 0] in
  let st_shndx_bytes := encode_secindex (symbentry_secindex e) in
  (st_name_bytes ++ st_value_bytes ++ st_size_bytes ++
                 st_info_bytes ++ st_other_bytes ++ st_shndx_bytes).
  
  
Definition acc_bytes e r :=
  do bytes <- r;
  do ebytes <- (encode_symbentry e);
  OK (ebytes ++ bytes).

Definition encode_symbtable (t:symbtable) : res (list byte) :=
  fold_right acc_bytes (OK []) t.

Definition create_symbtable_section (t:symbtable) : res section :=
  do bytes <- encode_symbtable t;
  OK (sec_bytes (encode_dummy_symbentry ++ bytes)).

End WITH_STRTAB.

(** Transform the program *)
Definition transf_program p : res program :=
  let t := prog_symbtable p in
  let strtab := (prog_strtable p) in
  do s <- create_symbtable_section strtab t;
  let p' :=
      {| prog_defs := prog_defs p;
        prog_public := prog_public p;
        prog_main := prog_main p;
        prog_sectable := (prog_sectable p) ++ [s];
        prog_strtable := strtab;
        prog_symbtable := prog_symbtable p;
        prog_reloctables := prog_reloctables p;
        prog_senv := prog_senv p;
     |} in
  let len := (length (prog_sectable p')) in
  if beq_nat len 5 then
    OK p'
  else
    Error [MSG "In SymtableEncode: Number of sections is incorrect (not 5): "; POS (Pos.of_nat len)].
