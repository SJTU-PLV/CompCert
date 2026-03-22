open Format
open Camlcoq
(* open PrintAST *)
open Rusttypes
(* open Ctypes *)
open RustIR
open RustIRcfg
(* open PrintCsyntax *)
open PrintRustsyntax
open PrintRustlight
open Maps
open InitDomain

let rec collapse_skip s =
  match s with
  | Ssequence(Sskip, s2) -> collapse_skip s2
  | Ssequence(s1, Sskip) -> collapse_skip s1
  | Ssequence(s1, s2) -> Ssequence(collapse_skip s1, collapse_skip s2)
  | Sifthenelse(e, s1, s2) -> Sifthenelse(e, collapse_skip s1, collapse_skip s2)
  | Sloop(s1) -> Sloop(collapse_skip s1)
  | _ -> s

let rec print_stmt p (s: RustIR.statement) =
  let s = collapse_skip s in
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
    fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id) (extern_atom id) print_expr e
  | Scall(v, e1, el) ->
    fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
              print_place v
              expr (15, e1)
              print_expr_list (true, el)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
    fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
    fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s1) ->
    fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sbreak ->
    fprintf p "break;"
  | Scontinue ->
    fprintf p "continue;"
  (* | Sreturn None ->
    fprintf p "return;" *)
  | Sreturn v ->
    fprintf p "return %a;" print_place v 
    (* (name_rust_type (Rustlight.typeof_place v)) *)
  | Sbox(v, e) ->
    fprintf p "@[<hv 2>%a =@ Box::new(%a);@]" print_place v   print_expr e
  | Sstoragelive id ->
    fprintf p "storagelive %s;" (extern_atom id)
  | Sstoragedead id ->
    fprintf p "storagedead %s;" (extern_atom id)
  | Sdrop v ->
    fprintf p "drop(%a of %s);" print_place v (name_rust_type (Rustlight.typeof_place v))
    

(* Print cfg of RustIR *)

let print_instruction pp prog (pc, i) =
  fprintf pp "%5d:\t" pc;
  match i with
  | Inop s ->
    let s = P.to_int s in
    if s = pc - 1
    then fprintf pp "nop@."
    else fprintf pp "goto %d@." s
  | Isel(sel, s) ->
    (match select_stmt prog sel with
    | Some stmt ->
      let s = P.to_int s in
      fprintf pp "%a%s@." print_stmt stmt ((sprintf " goto %d" s))
    | None ->
      fprintf pp "Error: cannot find statement@.")
  | Icond(e, s1, s2) ->
    fprintf pp "if (%a) goto %d else goto %d@."
        PrintRustlight.print_expr e
        (P.to_int s1) (P.to_int s2)
  | Iend ->
    fprintf pp "return@."

let print_param pp param =
  let (id,ty) = param in
  fprintf pp "%s: %s" (extern_atom id) (name_rust_type ty)

  let rec print_params pp = function
  | [] -> ()
  | [r] -> print_param pp r
  | r1::rl -> fprintf pp "%a, %a" print_param r1 print_params rl

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let print_function pp id f =
  fprintf pp "%s@ "
            (PrintRustsyntax.name_rust_function_decl
               (extern_atom id)
               f.fn_params
               f.fn_callconv
               f.fn_generic_origins
               f.fn_origins_relation
               f.fn_return);
  fprintf pp "@[<v 2>{@ ";
  (* Print variables and their types *)
  List.iter
    (fun (id, ty) ->
      fprintf pp "let %s;@ " (name_rust_binding (extern_atom id) ty))
    f.fn_vars;
  print_stmt pp f.fn_body;
  fprintf pp "@;<0 -2>}@]@ @ "

let print_cfg_body pp (body, entry, cfg) = 
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg)) in
  print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction pp body) instrs;
  fprintf pp "}\n\n"

let print_cfg pp id f =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    fprintf pp "%s {\n"
      (PrintRustsyntax.name_rust_function_decl
         (extern_atom id)
         f.fn_params
         f.fn_callconv
         f.fn_generic_origins
         f.fn_origins_relation
         f.fn_return);
    (* Print variables and their types *)
    List.iter
    (fun (id, ty) ->
      fprintf pp "let %s;@ " (name_rust_binding (extern_atom id) ty)) f.fn_vars;
    print_cfg_body pp (f.fn_body, entry, cfg)
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG: %a" Driveraux.print_error msg
 
(* Print CFG with MaybeInit and MaybeUninit *)

let print_paths_map pp (name, (pathmap: InitDomain.PathsMap.t)) =
  let (_, l') = List.split (PTree.elements pathmap) in
  let l = List.concat l' in
  fprintf pp "%s: {@[<hov>%a@]}@ "
    name
    (pp_print_list ~pp_sep: (fun out () -> fprintf out ";@ ") print_place) l

let print_instruction_debug pp prog (pc, (i, (mayinit, mayuninit))) =
  fprintf pp "%5d:\t" pc;
  match mayinit, mayuninit with
  | IM.State(mayinit), IM.State(mayuninit) ->
    (* meaningful analysis result *)
    begin match i with
    | Inop s ->
      let s = P.to_int s in
      if s = pc - 1
      then fprintf pp "nop@ "
      else fprintf pp "goto %d@ " s
    | Isel(sel, s) ->
      (match select_stmt prog sel with
      | Some stmt ->
        fprintf pp "%a@ " print_stmt stmt
      | None ->
        fprintf pp "Error: cannot find statement@ ")
    | Icond(e, s1, s2) ->
      fprintf pp "if (%a) goto %d else goto %d@ "
          PrintRustlight.print_expr e
          (P.to_int s1) (P.to_int s2)
    | Iend ->
      fprintf pp "return@ "
    end;
    fprintf pp "%a@ %a@."
      print_paths_map ("MayInit", mayinit)
      print_paths_map ("MayUninit", mayuninit)
  | _, _ ->
    fprintf pp "unreachable@."

let combine x y =
  match x,y with
  | Some x, Some y -> Some (x,y)
  | _, _ -> None

let print_cfg_body_debug pp (body, entry, cfg) mayinit mayuninit = 
  let (_, mayinit) = mayinit in
  let (_, mayuninit) = mayuninit in
  let cfg' = PTree.combine combine cfg (PTree.combine combine mayinit mayuninit) in
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg')) in
  print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
  List.iter (print_instruction_debug pp body) instrs;
  fprintf pp "}\n\n"

let print_cfg_initanalysis_debug ce pp id f  =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    (match InitAnalysis.analyze ce f cfg entry with
    | Errors.OK ((mayinit, mayuninit), _) ->
      fprintf pp "%s {\n"
        (PrintRustsyntax.name_rust_function_decl
           (extern_atom id)
           f.fn_params
           f.fn_callconv
           f.fn_generic_origins
           f.fn_origins_relation
           f.fn_return);
      (* Print variables and their types *)
      List.iter
      (fun (id, ty) ->
        fprintf pp "let %s;@ " (name_rust_binding (extern_atom id) ty)) f.fn_vars;
      print_cfg_body_debug pp (f.fn_body, entry, cfg) mayinit mayuninit
    | Errors.Error msg ->
      Diagnostics.fatal_error Diagnostics.no_loc "Error in InitAnalysis: %a" Driveraux.print_error msg)
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG: %a" Driveraux.print_error msg

(* Print program *)


let print_fundef p id fd print =
  match fd with
  | Rusttypes.External(_,_,_, _, _, _) ->
      ()
  | Internal f ->
      print p id f

let print_fundecl p id fd =
  match fd with
  | External(_, _, (AST.EF_external _ | AST.EF_runtime _ | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ "
                (PrintRustsyntax.name_rust_function_decl_from_type
                   (extern_atom id)
                   []
                   []
                   args
                   res
                   cconv)
  | External(_, _, _, _, _, _) ->
      ()
  | Internal f ->
      fprintf p "%s;@ "
                (PrintRustsyntax.name_rust_function_decl
                   (extern_atom id)
                   f.fn_params
                   f.fn_callconv
                   f.fn_generic_origins
                   f.fn_origins_relation
                   f.fn_return)

let print_globdef p print (id, gd)  =
  match gd with
  | AST.Gfun f -> print_fundef p id f print
  | AST.Gvar v -> PrintRustsyntax.print_globvar p id v  (* from PrintRustsyntax.ml *)

let print_globdecl p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundecl p id f
  | AST.Gvar v -> ()

let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (PrintRustsyntax.declare_composite p) prog.prog_types;
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.prog_defs;
  List.iter (print_globdef p print_function) prog.prog_defs;
  fprintf p "@]@."

let print_cfg_program p prog =
  fprintf p "@[<v 0>";
  List.iter (PrintRustsyntax.declare_composite p) prog.prog_types;
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.prog_defs;
  List.iter (print_globdef p print_cfg) prog.prog_defs;
  fprintf p "@]@."

let print_cfg_program_initanalysis_debug p prog =
  fprintf p "@[<v 0>";
  List.iter (PrintRustsyntax.declare_composite p) prog.prog_types;
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.prog_defs;
  List.iter (print_globdef p (print_cfg_initanalysis_debug prog.prog_comp_env)) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc

let destination_cfg : string option ref = ref None

let print_if_cfg prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_cfg_program (formatter_of_out_channel oc) prog;
      close_out oc

let destination_cfg_initanalysis : string option ref = ref None

let print_if_cfg_initanalysis prog =
  match !destination_cfg_initanalysis with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_cfg_program_initanalysis_debug (formatter_of_out_channel oc) prog;
      close_out oc

let destination_moveck : string option ref = ref None

(** Just print the result of init analysis *)
let print_if_moveck prog =
  match !destination_moveck with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_cfg_program_initanalysis_debug (formatter_of_out_channel oc) prog;
      close_out oc

let destination_after_elabdrop : string option ref = ref None

let print_if_after_elabdrop prog =
  match !destination_after_elabdrop with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
