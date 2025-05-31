open Format
open Camlcoq
(* open PrintAST *)
(* open Rusttypes *)
open Ctypes
open Cop
open Rustlight
open PrintCsyntax
open PrintRustsyntax

let coq_z_to_ocaml_int = Z.to_int
let temp_name (id: AST.ident) =
  try
    "$" ^ Hashtbl.find string_of_atom id
  with Not_found ->
    Printf.sprintf "$%d" (P.to_int id)

let extern_coqZ a =
    Printf.sprintf "%d" (coq_z_to_ocaml_int a)

let string_of_op op= 
  match op with
  | Oadd-> "+"
  | Osub -> "-"
  | Oshl -> "<<"
  | Oshr -> ">>"
  | Oand -> "&"
  | Oor -> "|"
  | _ -> "no support this operation"


(* 示例用法 *)
(* let example = [
  (((1, "int"), (0, ""), ("add", ""), First);
  (((2, "int"), (0, ""), ("", ""), First);
  (((3, "int"), (0, ""), ("", ""), Second);
  (((0, ""), (0, ""), ("mul", ""), Third)
] *)

(* let print_paren_list out ll =
  match ll with
  | [] -> ()
  | _ -> List.iter (fun (eid, _) -> fprintf out ".offset(%s)" (extern_atom eid)) ll *)
let rec find_first_part ll =
  match ll with
  | [] -> ([],[])
  | (((((num1, t1), (num2, t2)), (op, t3)), mark) :: rest) ->
    match mark with
    | Coq_first 
    | Coq_second -> ([((((num1, t1), (num2, t2)), (op, t3)), mark)],rest)
    | Coq_third -> let (p1,r1) = find_first_part rest in
                   let (p2,r2) = find_first_part r1 in
                   ([((((num1, t1), (num2, t2)), (op, t3)), mark)]@p1@p2,r2)

let rec print_place out (p: place) =
  match p with
  | Plocal(id, _) ->
    fprintf out "%s" (extern_atom id)
  | Pderef(p', _) ->
    fprintf out "*%a " print_place p'
  | Pfield(p', fid, _) ->
    fprintf out "%a.%s" print_place p' (extern_atom fid)
  | Pdowncast(p',fid, _) ->
    fprintf out "(%a as %s)" print_place p' (extern_atom fid)
  | Pparenthesize(pid, _, ll) ->
    let b = Buffer.create 50 in
      let rec aux = function
      | [] -> ()
      | (((((num, _), (id, _)), (op, _)), mark) :: rest) ->
        match mark with
        | Coq_first ->
          Buffer.add_string b (extern_coqZ num)
        | Coq_second ->
          Buffer.add_string b (extern_atom id);
        | Coq_third ->
          let op_str = string_of_op op in
          Buffer.add_string b "(";
          let (p1,r1) = find_first_part rest in
          aux p1;
          Buffer.add_string b op_str;
          let (p2,r2) = find_first_part r1 in
          aux p2;
          Buffer.add_string b ")";
      in
      begin
      match ll with
      | (((((_, _), (_, _)), (Oadd, _)), Coq_third) :: rest) ->
        begin
        match rest with
        | (((((num, _), (id, _)), (op, _)), mark) :: rest_ll) ->
          aux rest_ll;
          fprintf out "%s.as_mut_ptr().offset(%s)" (extern_atom id) (Buffer.contents b)
        |_ -> fprintf err_formatter "@[<2>Error place list in print_place@]@."
        end
      | _ -> fprintf err_formatter "@[<2>Error place list in print_place@]@."
      end
    (* print_paren_list out ll; *)
  | ParrayIndex(p', aid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom aid)

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
  | Eas(_, _) -> (16, NA)
  | Esizeof(_, _) -> (16, NA)

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
  | Eglobal(id, _) ->
    fprintf p "glob %s" (extern_atom id)
  | Eunop(Oabsfloat, a1, _) ->
    fprintf p "__builtin_fabs(%a)" pexpr (2, a1)
  | Eunop(op, a1, _) ->
    fprintf p "%s%a" (name_unop op) pexpr (prec', a1)
  | Ebinop(op, a1, a2, _) ->
    fprintf p "%a@ %s %a"
      pexpr (prec1, a1) (name_binop op) pexpr (prec2, a2)
  | Ecktag(v, fid) ->
    fprintf p "%s(%a, %s)" "cktag" print_place v (extern_atom fid)
  | Eref(org, mut, v, _) ->
    fprintf p "&%s %s%a" (extern_atom org) (string_of_mut mut) print_place v
  | Eas(pe, ty) ->
      fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty)
  | Esizeof(ty1, ty2) ->
      fprintf p "::core::mem::size_of::<%s>()" (name_rust_type ty1)
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


let rec print_stmt p (s: Rustlight.statement) =
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
    fprintf p "@[<hv 2>let %a =@ %a;@]" print_place v print_expr e
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
      fprintf p "fn%s@ "
                (name_rust_decl_fn (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv f.fn_generic_origins f.fn_origins_relation) f.fn_return);
      fprintf p "@[<v 2>{@ ";
        (* Print variables and their types *)
        (* List.iter
        (fun (id, ty) ->
          fprintf p "%s;@ " (name_rust_decl (extern_atom id) ty))
        f.fn_vars; *)
        print_stmt p f.fn_body;
      fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p id fd =
  match fd with
  | Rusttypes.External(_, _, _, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      print_function p id f

(* Check whether function id is main_id *)
let is_main_id id =
  let fun_name = extern_atom id in
  fun_name = "main"

let print_fundecl p id fd =
  match fd with
  | Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _ | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "unsafe extern \"C\" { %s; }@ "
                (name_rust_decl_fn (extern_atom id) (Rusttypes.Tfunction([], [], args, res, cconv)))
  | Rusttypes.External(_, _ ,_, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      (* We should not print fundecl of main function *)
      if is_main_id id then () else
      fprintf p "%s;@ "
                (name_rust_decl_fn (extern_atom id) (Rustlight.type_of_function f))

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
  List.iter (PrintRustsyntax.declare_composite p) prog.Rusttypes.prog_types;
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