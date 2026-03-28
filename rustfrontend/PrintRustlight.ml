open Format
open Camlcoq
(* open PrintAST *)
(* open Rusttypes *)
open Ctypes
open Cop
open Rustlight
open PrintCsyntax
open PrintRustsyntax

let temp_name (id: AST.ident) =
  try
    "$" ^ Hashtbl.find string_of_atom id
  with Not_found ->
    Printf.sprintf "$%d" (P.to_int id)

let rec print_place out (p: place) =
  (* Also print the type of this place *)
  (* match p with
  | Plocal(id, ty) ->
    fprintf out "%s with %s " (extern_atom id) (name_rust_type ty)
  | Pderef(p', ty) ->
    fprintf out "*%a with %s " print_place p' (name_rust_type ty)
  | Pfield(p', fid, ty) ->
    fprintf out "%a.%s with %s " print_place p' (extern_atom fid)  (name_rust_type ty)
  | Pdowncast(p',fid, ty) ->
      fprintf out "(%a as %s) with %s " print_place p' (extern_atom fid) (name_rust_type ty) *)
  match p with
  | Plocal(id, ty) ->
    fprintf out "%s" (extern_atom id)
  | Pderef(p', ty) ->
    fprintf out "*%a" print_place p'
  | Pfield(p', fid, ty) ->
    fprintf out "%a.%s" print_place p' (extern_atom fid)
  | Pdowncast(p',fid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom fid)

(* Precedences and associativity (copy from PrintClight.ml) *)

let precedence' = function
  | Eunit -> (16, NA)
  | Econst_int _ -> (16, NA)
  | Econst_float _ -> (16, NA)
  | Econst_single _ -> (16, NA)
  | Econst_long _ -> (16, NA)
  | Eglobal(_,_) -> (16, NA)
  | Eunop _ -> (15, RtoL)
  | Ebinop((Omul|Odiv|Omod), _, _, _) -> (13, LtoR)
  | Ebinop((Oadd|Osub), _, _, _) -> (12, LtoR)
  | Ebinop((Oshl|Oshr), _, _, _) -> (11, LtoR)
  | Ebinop((Olt|Ogt|Ole|Oge), _, _, _) -> (10, LtoR)
  | Ebinop((Oeq|Cop.One), _, _, _) -> (9, LtoR)
  | Ebinop(Oand, _, _, _) -> (8, LtoR)
  | Ebinop(Oxor, _, _, _) -> (7, LtoR)
  | Ebinop(Oor, _, _, _) -> (6, LtoR)
  | Eplace(_, _) -> (16,NA)
  | Ecktag(_, _) -> (15, RtoL)
  | Eref(_, _, _, _) -> (15, RtoL)

let precedence = function
  | Emoveplace(_,_) -> (16,NA)
  | Epure pe -> precedence' pe

(* Expressions *)

let rec pexpr p (prec, e) =
  let (prec', assoc) = precedence' e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Eunit ->  fprintf p "tt"
  | Eplace(v, _) ->
    fprintf p "%a" print_place v
  | Econst_int(n, Rusttypes.Tint(I32, Unsigned)) ->
    fprintf p "%luU" (camlint_of_coqint n)
  | Econst_int(n, _) ->
    fprintf p "%ld" (camlint_of_coqint n)
  | Econst_float(f, _) ->
    fprintf p "%.18g" (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
    fprintf p "%.18gf" (camlfloat_of_coqfloat32 f)
  | Econst_long(n, Rusttypes.Tlong(Unsigned)) ->
    fprintf p "%LuLLU" (camlint64_of_coqint n)
  | Econst_long(n, _) ->
    fprintf p "%LdLL" (camlint64_of_coqint n)
  | Eglobal(id, ty) ->
    (* fprintf p "glob %s with %s" (extern_atom id) (name_rust_type ty) *)
    fprintf p "%s" (extern_atom id)
  | Eunop(Oabsfloat, a1, _) ->
    fprintf p "__builtin_fabs(%a)" pexpr (2, a1)
  | Eunop(op, a1, _) ->
    fprintf p "%s%a" (name_unop op) pexpr (prec', a1)
  | Ebinop(op, a1, a2, _) ->
    fprintf p "%a@ %s %a"
      pexpr (prec1, a1) (name_binop op) pexpr (prec2, a2)
  | Ecktag(v, fid) ->
    fprintf p "%s(%a, %s)" "discriminant_eq" print_place v (extern_atom fid)
  | Eref(org, mut, v, _) ->
    fprintf p "&%s %s%a" (extern_atom org) (string_of_mut mut) print_place v
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let expr p (prec, e) =
  let (prec', assoc) = precedence e in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Epure pe -> pexpr p (prec, pe)
  | Emoveplace(v, _) -> fprintf p "move %a" print_place v
   end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_expr p e = expr p (0, e)

let rec print_expr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      print_expr_list p (false, rl)

let rec collapse_skip s =
  match s with
  | Ssequence(Sskip, s2) -> collapse_skip s2
  | Ssequence(s1, Sskip) -> collapse_skip s1
  | Ssequence(s1, s2) -> Ssequence(collapse_skip s1, collapse_skip s2)
  | Sifthenelse(e, s1, s2) -> Sifthenelse(e, collapse_skip s1, collapse_skip s2)
  | Sloop(s1) -> Sloop(collapse_skip s1)
  | _ -> s

let rec print_stmt p (s: Rustlight.statement) =
  let s = collapse_skip s in
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
    fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id)(extern_atom id) print_expr e
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
  | Sbox(v, e) ->
    fprintf p "@[<hv 2>%a =@ Box::new(%a);@]" print_place v print_expr e
  | Slet(id, ty, s) ->
    fprintf p "@[<v 2>let %s : %s in {@ %a@;<0 -2>}@]"
            (extern_atom id)
            (name_rust_type ty)
            print_stmt s

let print_stmt_direct stmt = print_stmt (formatter_of_out_channel stdout) stmt

let print_function p id f =
  fprintf p "%s@ "
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
      fprintf p "let %s;@ " (name_rust_binding (extern_atom id) ty))
    f.fn_vars;
  fprintf p "@[<v 2>{@ ";
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p id fd =
  match fd with
  | Rusttypes.External(_, _, _, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      print_function p id f

let print_fundecl p id fd =
  match fd with
  | Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _ | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ "
                (PrintRustsyntax.name_rust_function_decl_from_type
                   (extern_atom id)
                   []
                   []
                   args
                   res
                   cconv)
  | Rusttypes.External(_, _ ,_, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      fprintf p "%s;@ "
                (PrintRustsyntax.name_rust_function_decl
                   (extern_atom id)
                   f.fn_params
                   f.fn_callconv
                   f.fn_generic_origins
                   f.fn_origins_relation
                   f.fn_return)

let print_globdef p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundef p id f
  | AST.Gvar v -> PrintRustsyntax.print_globvar p id v  (* from PrintRustsyntax.ml *)

let print_globdecl p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundecl p id f
  | AST.Gvar v -> ()

let print_program p (prog: Rustlight.program) =
  fprintf p "@[<v 0>";
  (* List.iter (PrintRustsyntax.declare_composite p) prog.Rusttypes.prog_types; *)
  List.iter (PrintRustsyntax.define_composite p) prog.Rusttypes.prog_types;
  List.iter (print_globdecl p) prog.Rusttypes.prog_defs;
  List.iter (print_globdef p) prog.Rusttypes.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
