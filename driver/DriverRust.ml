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
  (* Print Asm in text form. It is necessary because we need to use the GAS to assemble the test asm file *)
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

(* Debug the Rust compiler *)

let compile_log_file = "rust_compile.log"

let logout = Format.formatter_of_out_channel (open_out compile_log_file)

let debug_Rustlightgen (syntax: Rustsyntax.program) =
  match Rustlightgen.transl_program syntax with
  | Errors.OK rustlight_prog ->
    Format.fprintf logout "Rustlight: @.";
    PrintRustlight.print_program logout rustlight_prog;
    rustlight_prog
  | Errors.Error msg ->
    fatal_error no_loc "%a"  print_error msg

let debug_RustIRgen (rustlight_prog: Rustlight.program) =
  Format.fprintf logout "@.RustIR: @.";
  let rustir_prog = RustIRgen.transl_program rustlight_prog in
  PrintRustIR.print_program logout rustir_prog;
  rustir_prog

let debug_RustCFG rustir_prog =
  Format.fprintf logout "@.Rust CFG: @.";
  PrintRustIR.print_cfg_program logout rustir_prog;
  rustir_prog

let debug_InitAnalysis rustir_prog =
  Format.fprintf logout "@.Initialized Analysis: @.";
  PrintRustIR.print_cfg_program_debug logout rustir_prog;
  rustir_prog

let debug_ElaborateDrop rustir_prog =
  match ElaborateDrop.transl_program rustir_prog with
  | Errors.OK rustir_prog_drop ->
   Format.fprintf logout "@.Elaborate Drop: @.";
   PrintRustIR.print_program logout rustir_prog_drop;
   rustir_prog_drop
  | Errors.Error msg ->
    fatal_error no_loc "%a"  print_error msg

let debug_borrow_check = true

let debug_ReplaceOrigins (prog: RustIR.program) =
  match ReplaceOrigins.transl_program prog with
  | Errors.OK rustir_after_replace_origins ->
    Format.fprintf logout "@.After Replacing Origins: @.";
    PrintRustIR.print_cfg_program logout rustir_after_replace_origins;
    rustir_after_replace_origins
  | Errors.Error msg ->
    fatal_error no_loc "%a"  print_error msg

let debug_BorrowCheck (prog: RustIR.program) =  
  Format.fprintf logout "@.Borrow Check: @.";
  PrintBorrowCheck.print_cfg_program_borrow_check logout prog;
  (* The top-level borrow check which includes the move checking *)
  match BorrowCheck.borrow_check_program prog with
  | Errors.OK _ ->
    Format.fprintf logout "@.Borrow Check Success@.";
    prog
  | Errors.Error msg ->
     fatal_error no_loc "@.Borrow checking error: %a"  print_error msg

let debug_MoveChecking (prog: RustIR.program) =
  match MoveChecking.move_check_program prog with
  | Errors.OK _ ->
    Format.fprintf logout "@.Move Checking Success@.";
    prog
  | Errors.Error msg ->
    fatal_error no_loc "%a"  print_error msg

let debug_ClightComposite prog =
  match Clightgen.transl_composites prog.Rusttypes.prog_types with
  | Some clight_composites -> 
    Format.fprintf logout "@.Clightgen Composites: @.";
    Format.fprintf logout "@[<v 0>"; 
    List.iter (PrintCsyntax.define_composite logout) clight_composites;
    Format.fprintf logout "@]@.";
    prog
  |  None -> fatal_error no_loc "@.Translate composites error @."

let debug_Clightgen prog =
  match Clightgen.transl_program prog with
  | Errors.OK clight_prog ->
    Format.fprintf logout "@.Clightgen: @.";
    PrintClight.print_program PrintClight.Clight1 logout clight_prog;
    clight_prog
  | Errors.Error msg -> fatal_error no_loc "%a" print_error msg

(* Processing the source rust file (suffix with .rs), it takes the name of the rust file as input and outputs the object file name *)
let process_rust_file test_case =
  Format.fprintf logout "Compile file %s@." test_case;
    let clight_prog =
      let items = RustsurfaceDriver.parse test_case in
      let module R = Rustsurface in
      Format.fprintf logout "Rustsurface to Rustsyntax@.";
      let m_syntax = items |> R.prog_of_items |> R.To_syntax.transl_prog logout in
      let (syntax_result, symmap) = R.To_syntax.(run_monad m_syntax skeleton_st) in
      (match syntax_result with
      | Result.Ok syntax ->
        (* Print Rustlight. clight_prog is just used to debug. To
        support only invoking the verified transf_rustlight_program,
        we should remove the insertion of helper function for the
        selection pass which force us to separate the compilation
        chain *)
        let clight_prog = syntax
                          |> debug_Rustlightgen
                          |> debug_RustIRgen
                          |> debug_RustCFG
                          |> debug_ElaborateDrop
                          |> debug_ReplaceOrigins
                          |> debug_InitAnalysis
                          |> debug_MoveChecking
                          |> debug_BorrowCheck
                          |> debug_ClightComposite
                          |> debug_Clightgen in
        clight_prog
      | Result.Error e ->
        Rustsurface.To_syntax.pp_print_error Format.err_formatter e symmap;
        raise Abort)
    in
    (* Set config *)
    Machine.config := Machine.x86_64;
    (* add helper functions which is required by Selection pass *)
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
