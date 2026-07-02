open Format
open! Camlcoq
(* open PrintAST *)
open Rusttypes
(* open Ctypes *)
open RustIR
open RustIRcfg
(* open PrintCsyntax *)
open PrintRustlight
open Maps
open BorrowCheckDomain
open UnionFindDelete
open RegionLiveness

module Old = BorrowCheckPolonius
module Fwd = BorrowCheckPoloniusForward

let print_mutkind pp (mut: mutkind) =
  match mut with
  | Mutable -> fprintf pp "mut"
  | Immutable -> fprintf pp "shr"

let print_loan pp (l: loan) =
  match l with
  | Lextern(org) ->
    fprintf pp "Lextern(%s)" (extern_atom org)
  | Lintern(mut, p) ->
    fprintf pp "(%a, %a)" print_mutkind mut print_place p

let origin_list_to_string (orgs: origin list) : string =
  let rec aux orgs =
    match orgs with
    | [] -> ""
    | [org] -> extern_atom org
    | org :: orgs' -> (extern_atom org) ^ ", " ^ (aux orgs') in
  "[" ^ (aux orgs) ^ "]"

let print_loanset pp (ls: LoanSet.t) =
  let l = LoanSet.elements ls in
  pp_print_list ~pp_sep: (fun out () -> fprintf out ";@ ") print_loan pp l

let print_origin pp org =
  fprintf pp "%s" (extern_atom org)

(* let print_originset pp (ls: OriginSet.t) =
  let l = OriginSet.elements ls in
  pp_print_list ~pp_sep: (fun out () -> fprintf out ";@ ") print_origin pp l *)

let print_dead_origin pp (orgs: origin list) =
  fprintf pp "%s: Dead@ " (origin_list_to_string orgs)

let print_origin_state pp (org_st: origin list * LOrgLnSt.t) =
  let (orgs, st) = org_st in
  match st with
  (* | Obot -> fprintf pp "%s: Bot@ " (extern_atom org) *)
  | LOrgLnSt.Live(ls) ->
    fprintf pp "%s: {@[<hov>%a@]}@ " (origin_list_to_string orgs) print_loanset ls
  | LOrgLnSt.Dead ->
    print_dead_origin pp orgs

let find_same_set (org: origin) (uf: UFD.unionfind) : origin list =
  let all_orgs = List.map fst (PTree.elements uf) in
  (* all_orgs may be empty *)
  (* Be careful of the structural equality and physical equality in Ocaml! *)
  org :: (List.filter (fun o -> (o <> org) && (UFD.repr uf o = UFD.repr uf org)) all_orgs)

let print_origin_env pp (e: LOrgEnv.t) =
  fprintf pp "OrgEnv: ";
  let l = (PTree.elements (LOrgEnv.m e)) in
  (* collect the repr nodes *)
  let repr_l = List.filter (fun (org, _) -> UFD.repr (LOrgEnv.uf e) org = org) l in
  (* only print the representative elements of each set *)
  (* collect the equivalent set where each element uses the element
  (same position) in l as the repr node *)
  let (orgs, ls) = List.split repr_l in
  let orgs_ds = List.map (fun o -> find_same_set o (LOrgEnv.uf e)) orgs in
  List.iter (print_origin_state pp) (List.combine orgs_ds ls)

let print_origin_opt_state pp (org_st: origin list * LOrgLnOptSt.t) =
  let (orgs, st) = org_st in
  match st with
  | Some (LOrgLnSt.Live ls) ->
    fprintf pp "%s: {@[<hov>%a@]}@ " (origin_list_to_string orgs) print_loanset ls
  | Some LOrgLnSt.Dead ->
    print_dead_origin pp orgs
  | None ->
    fprintf pp "%s: Invalidated@ " (origin_list_to_string orgs)

let print_origin_opt_env pp (e: LOrgOptEnv.t) =
  fprintf pp "OrgOptEnv: ";
  let l = (PTree.elements (LOrgOptEnv.m e)) in
  let repr_l = List.filter (fun (org, _) -> UFD.repr (LOrgOptEnv.uf e) org = org) l in
  let (orgs, ls) = List.split repr_l in
  let orgs_ds = List.map (fun o -> find_same_set o (LOrgOptEnv.uf e)) orgs in
  List.iter (print_origin_opt_state pp) (List.combine orgs_ds ls)

let print_live_loans pp (ls: LoanSet.t) =
  fprintf pp "May-Live Loans: {@[<hov>%a@]}@ " print_loanset ls

(* let print_alias_graph pp (ag: LAliasGraph.t) =
  let l = PTree.elements ag in
  match l with
  | [] -> fprintf pp "Alias Graph is empty "
  | _ ->
    fprintf pp "Alias Graph: ";
    List.iter
        (fun (org, ls) -> fprintf pp "%s: {@[<hov>%a@]}@ " (extern_atom org) print_originset ls) l *)

let print_ae pp ae =
  match ae with
  | LoansEnv.Bot ->
    fprintf pp "Unreachable point@.@."
  | LoansEnv.State(org_env) ->
    (* TODO: print alias graph *)
    fprintf pp "%a@.@." print_origin_env org_env

let print_forward_ae pp ae =
  match ae with
  | LoansOptEnv.Bot ->
    fprintf pp "Unreachable point@.@."
  | LoansOptEnv.State (org_env, log) ->
    fprintf pp "%a" print_origin_opt_env org_env;
    (match log with
    | [] -> ()
    | _ -> fprintf pp "@ Diagnostics: %a" Driveraux.print_error log);
    fprintf pp "@.@."

let print_live_regions pp live =
  let orgs = RegionSet.elements live in
  fprintf pp "Live regions (after this node): %s@." (origin_list_to_string orgs) 

let print_instruction_debug pp prog (pc, (i, (live, ae))) =
  PrintRustIR.print_instruction pp prog (pc,i);
  print_live_regions pp live;
  print_ae pp ae

let print_instruction_forward_debug pp prog (pc, (i, ae)) =
  PrintRustIR.print_instruction pp prog (pc,i);
  print_forward_ae pp ae

let print_cfg_body_borrow_check pp (body, entry, cfg) live ae =
  (* Debug code: fprintf pp "Length of cfg, live and ae are %d, %d, %d@." 
     (Nat.to_int (PTree_Properties.cardinal cfg)) (Nat.to_int (PTree_Properties.cardinal live)) (Nat.to_int (PTree_Properties.cardinal ae)); *)
  (* We show the result of liveness analysis as the checking would
  first apply liveness to the loans environment first *)
  let cfg' = PTree.combine PrintRustIR.combine cfg (PTree.combine PrintRustIR.combine live ae) in
  (* let cfg' = PTree.combine PrintRustIR.combine cfg ae in *)
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg')) in
  PrintRustIR.print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
    List.iter (print_instruction_debug pp body) instrs;
    fprintf pp "}\n\n"

let print_cfg_body_borrow_check_forward pp (body, entry, cfg) ae =
  let cfg' = PTree.combine PrintRustIR.combine cfg ae in
  let instrs =
    List.sort
    (fun (pc1, _) (pc2, _) -> compare pc2 pc1)
    (List.rev_map
      (fun (pc, i) -> (P.to_int pc, i))
      (PTree.elements cfg')) in
  PrintRustIR.print_succ pp entry
    (match instrs with (pc1, _) :: _ -> pc1 | [] -> -1);
    List.iter (print_instruction_forward_debug pp body) instrs;
    fprintf pp "}\n\n"

let print_cfg_header pp id f =
      fprintf pp "%s@ "
          (PrintRustsyntax.name_rust_function_decl
             (extern_atom id)
             f.fn_params
             f.fn_callconv
             f.fn_generic_origins
             f.fn_origins_relation
             f.fn_return);
      fprintf pp "@[<v 2>{@ ";
      (* fprintf pp "%s(%a) {\n" (extern_atom id) PrintRustIR.print_params f.fn_params; *)
      (* Print variables and their types *)
      List.iter
      (fun (id, ty) ->
        fprintf pp "let %s;@ " (PrintRustsyntax.name_rust_binding (extern_atom id) ty)) f.fn_vars

let print_cfg_borrow_check_old ce pp id f entry cfg =
  match Old.loans_flow_analyze ce f cfg entry with
  | Errors.OK (live, ae) ->
      print_cfg_header pp id f;
      print_cfg_body_borrow_check pp (f.fn_body, entry, cfg) (snd live) (snd ae)
  | Errors.Error msg ->
      Diagnostics.fatal_error Diagnostics.no_loc "Error in borrow check: %a@ " Driveraux.print_error msg

let print_cfg_borrow_check_forward ce pp id f entry cfg =
  match Fwd.borrow_check_interpret ce f cfg entry with
  | Errors.OK ae ->
      print_cfg_header pp id f;
      print_cfg_body_borrow_check_forward pp (f.fn_body, entry, cfg) (snd ae)
  | Errors.Error msg ->
      Diagnostics.fatal_error Diagnostics.no_loc "Error in forward borrow check: %a@ " Driveraux.print_error msg

let print_cfg_borrow_check ce pp id f  =
  match generate_cfg f.fn_body with
  | Errors.OK(entry, cfg) ->
    if !Clflags.option_fborrowck_forward then
      print_cfg_borrow_check_forward ce pp id f entry cfg
    else
      print_cfg_borrow_check_old ce pp id f entry cfg
  | Errors.Error msg ->
    Diagnostics.fatal_error Diagnostics.no_loc "Error in generating CFG (borrow check): %a@ " Driveraux.print_error msg

let print_cfg_program_borrow_check p (prog: RustIR.coq_function Rusttypes.program) =
  fprintf p "@[<v 0>";
  (* List.iter (PrintRustsyntax.declare_composite p) prog.prog_types; *)
  List.iter (PrintRustsyntax.define_composite p) prog.prog_types;
  List.iter (PrintRustIR.print_globdecl p) prog.prog_defs;
  List.iter (PrintRustIR.print_globdef p (print_cfg_borrow_check prog.prog_comp_env)) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_cfg_program_borrow_check (formatter_of_out_channel oc) prog;
      close_out oc
