open Clflags
open Driveraux
open Assembler
open Diagnostics

let tool_name = "Rust verified compiler"

let sdump_suffix = ref ".json"

let nolink () =
  !option_c || !option_S || !option_E || !option_interp

let object_filename sourcename =
  if nolink () then
    output_filename ~final: !option_c sourcename ~suffix:".o"
  else
    tmp_file ".o"

(* From Clight to asm. It is used in Rust Compiler *)

let compile_clight prog name =
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename name ~suffix:ext)
      else None in
  set_dest Cprint.destination option_dparse ".parsed.c";
  set_dest PrintCsyntax.destination option_dcmedium ".compcert.c";
  set_dest PrintClight.destination option_dclight ".light.c";
  set_dest PrintCminor.destination option_dcminor ".cm";
  set_dest PrintRTL.destination option_drtl ".rtl";
  set_dest Regalloc.destination_alloctrace option_dalloctrace ".alloctrace";
  set_dest PrintLTL.destination option_dltl ".ltl";
  set_dest PrintMach.destination option_dmach ".mach";
  set_dest AsmToJSON.destination option_sdump !sdump_suffix;
  (* Compile the Clight program *)
let asm =
    match Compiler.apply_partial
               (Compiler.transf_clight_program prog)
               Asmexpand.expand_program with
    | Errors.OK asm ->
        asm
    | Errors.Error msg ->
      let loc = file_loc name in
        fatal_error loc "%a"  print_error msg in
  (* Dump Asm in binary and JSON format *)
  AsmToJSON.print_if asm name;
  (* Print Asm in text form no matter whether we set '-dasm' or not. *)
  let ofile = output_filename name ~suffix:".s" in
  let oc = open_out ofile in
  PrintAsm.print_program oc asm;
  close_out oc;
  if !option_S then
    (* Do not call the assembler *)
    ofile
  else
    (* invoke assembler *)
    let objname = object_filename name in
    assemble ofile objname;
    objname

let set_dest dst opt name ext =
  dst := if !opt then Some (output_filename name ~suffix:ext)
     else None

let compile_rustsyntax prog name =
  set_dest PrintRustlight.destination option_drustlight name ".rustlight";
  set_dest PrintRustIR.destination option_drminor name ".rminor";
  set_dest PrintRustIR.destination_cfg option_rcfg name ".rcfg";
  set_dest PrintRustIR.destination_cfg_initanalysis option_dinit name ".init";
  set_dest PrintRustIR.destination_before_borrowck option_dbefore_borrowck name ".before_borrowck";
  set_dest PrintRustIR.destination_moveck option_dmoveck name ".moveck";
  set_dest PrintBorrowCheck.destination option_dborrowck name ".borrowck";
  (* Compile the Rustsyntax program *)
  let clight_prog =
    match Compiler.transf_rust_to_clight prog with
    | Errors.OK clight ->
        clight
    | Errors.Error msg ->
      let loc = file_loc name in
        fatal_error loc "%a"  print_error msg in
  clight_prog

(* Processing the source rust file (suffix with .rs), it takes the name of the rust file as input and outputs the object file name *)
let process_rust_file test_case =
  (* Format.fprintf logout "Compile file %s@." test_case; *)
    let clight_prog =
      let items = RustsurfaceDriver.parse test_case in
      let module R = Rustsurface in
      (* Format.fprintf logout "Rustsurface to Rustsyntax@."; *)
      set_dest R.To_syntax.destination option_drustsyntax test_case ".rustsyntax";
      let m_syntax = items |> R.prog_of_items |> R.To_syntax.transl_prog in
      let (syntax_result, symmap) = R.To_syntax.(run_monad m_syntax skeleton_st) in
      (match syntax_result with
      | Result.Ok syntax ->
        let clight_prog = compile_rustsyntax syntax test_case in
        (* legacy code *)
        (* (* Print Rustlight. clight_prog is just used to debug. To
        support only invoking the verified transf_rustlight_program,
        we should remove the insertion of helper function for the
        selection pass which force us to separate the compilation
        chain *)
        let clight_prog = syntax
                          |> debug_Rustlightgen test_case
                          |> debug_RustIRgen test_case
                          |> debug_RustCFG test_case
                          |> debug_ReplaceOrigins test_case
                          |> debug_InitAnalysis test_case
                          |> debug_ElaborateDrop test_case
                          |> debug_MoveChecking test_case
                          |> debug_BorrowCheck test_case
                          |> debug_ClightComposite
                          |> debug_Clightgen in *)
        clight_prog
      | Result.Error e ->
        Rustsurface.To_syntax.pp_print_error Format.err_formatter e symmap;
        raise Abort)
    in
    (* Set config *)
    Machine.config := Machine.x86_64;
    (* Add helper functions which are required by Selection pass. The
    important problem here is that this operation makes the
    compilation implemented in Ocaml side mismatched with the
    implementation in Rocq side (i.e., the top-level function in
    Compiler.v). One possible solution is to insert this operation in
    the Clightgen pass and prove its correctness. *)
    let gl = C2C.add_helper_functions clight_prog.Ctypes.prog_defs in
    let clight_prog' =
      { Ctypes.prog_defs = gl;
        Ctypes.prog_public = C2C.public_globals gl;
        Ctypes.prog_main = clight_prog.Ctypes.prog_main;
        Ctypes.prog_types = clight_prog.Ctypes.prog_types;
        Ctypes.prog_comp_env = clight_prog.Ctypes.prog_comp_env;
      } in
    (* The following code compiles the generated Clight program  *)
    let objfile = compile_clight clight_prog' test_case in
    objfile
