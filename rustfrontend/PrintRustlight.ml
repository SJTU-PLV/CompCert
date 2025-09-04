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
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oand -> "&&"
  | Oor -> "||"
  | Oxor -> "^"
  | Oshl -> "<<"
  | Oshr -> ">>"
  | Oeq -> "=="
  | One -> "!="
  | Olt -> "<"
  | Ogt -> ">"
  | Ole -> "<="
  | Oge -> ">="
  (* | _ -> "no support this operation" *)


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
  | Ederef(_, _) -> (15, RtoL)

let precedence = function
  | Emoveplace(_,_) -> (16,NA)
  | Epure pe -> precedence' pe

  let rec print_place out (p: place) =
    match p with
    | Plocal(id, _) ->
      fprintf out "%s" (extern_atom id)
    | Pderef(p', _) ->
      (* fprintf out "*%a" print_place p' *)
      fprintf out "%a" print_place p'
      (* fprintf out "*%a" print_place p' *)
      fprintf out "%a" print_place p'
    | Pfield(p', fid, _) ->
      fprintf out "%a.%s" print_place p' (extern_atom fid)
    | Pdowncast(p',fid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom fid)
    | Pparenthesize(pid, _, ll) ->
      begin
      match ll with
      | Ebinop(op, lb, lr, _) ->
          fprintf out "%a[%a]" pexpr (0, lb) pexpr (0, lr);
          ()
      | _ -> 
        fprintf out "error in Pparenthesize";()
      end
    | ParrayIndex(p', aid, _) ->
        fprintf out "(%a as %s)" print_place p' (extern_atom aid)

(* Expressions *)

and pexpr p (prec, e) =
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
    fprintf p "%lu_u32" (camlint_of_coqint n)
  | Econst_int(n, _) ->
    fprintf p "%ld" (camlint_of_coqint n)
  | Econst_float(f, _) ->
    fprintf p "%.18g" (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
    fprintf p "%.18g_f32" (camlfloat_of_coqfloat32 f)
  | Econst_long(n, Rusttypes.Tlong(Unsigned)) ->
    fprintf p "%Lu_u64" (camlint64_of_coqint n)
  | Econst_long(n, _) ->
    fprintf p "%Ldi64" (camlint64_of_coqint n)
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
  | Ederef(pe, ty) ->
      fprintf p "*(%a)" pexpr (prec', pe)
      (* fprintf p "(%a)" pexpr (prec', pe) *)
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

let type_of_pexpr (p : Rustlight.pexpr) : Rusttypes.coq_type =
  match p with
  | Eunit -> Rusttypes.Tunit
  | Econst_int (_, ty) -> ty
  | Econst_float (_, ty) -> ty
  | Econst_single (_, ty) -> ty
  | Econst_long (_, ty) -> ty
  | Eplace (_, ty) -> ty
  | Ecktag (_, _) -> Rusttypes.Tint (Ctypes.I32, Ctypes.Signed)  (* 或者你需要的类型 *)
  | Eref (_, _, _, ty) -> ty
  | Eunop (_, _, ty) -> ty
  | Ebinop (_, _, _, ty) -> ty
  | Eglobal (_, ty) -> ty
  | Eas (_, ty) -> ty
  | Esizeof (_, ty) -> ty
  | Ederef (_, ty) -> ty
  
let type_of_expr (e : expr) : Rusttypes.coq_type =
  match e with
  | Emoveplace (_, ty) -> ty
  | Epure p -> type_of_pexpr p

let rec print_expr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      (* 判断类型，如果是数组或指针，加 .as_ptr() *)
      (match type_of_expr r with
       | Rusttypes.Tarray _ | Rusttypes.Traw_pointer _ -> fprintf p ".as_ptr()"
       | _ -> ());
      print_expr_list p (false, rl)

let rec print_expr_list_with_type p (first, exprs, param_tys) =
  match exprs, param_tys with
  | [], [] -> ()
  | r :: rl, ty :: tyl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      (* 判断类型，如果是数组或指针，加 .as_ptr() *)
      (match type_of_expr r with
       | Rusttypes.Tarray _ | Rusttypes.Traw_pointer _ -> fprintf p ".as_ptr()"
       | _ -> ());
      (* 打印参数类型 *)
      fprintf p " as %s" (name_rust_decl "" ty);
      print_expr_list_with_type p (false, rl, tyl)
  | r :: rl, [] ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      (* 判断类型，如果是数组或指针，加 .as_ptr() *)
      (match type_of_expr r with
      | Rusttypes.Tarray _ | Rusttypes.Traw_pointer _ -> fprintf p ".as_ptr()"
      | _ -> ());
      print_expr_list_with_type p (false, rl, [])
  | _ ->
      (* error *)
      ()

let rec typelist_to_list = function
  | Rusttypes.Tnil -> []
  | Rusttypes.Tcons(ty, rest) -> ty :: typelist_to_list rest

(* 辅助函数:解析malloc的参数并生成对应的Rust Box代码 *)
let parse_malloc_param p v param = 
  match param with
  | Epure (Ebinop(Omul, pe1, pe2, _)) ->
      (
        match pe1, pe2 with
        | (Esizeof(ty, _), Econst_int(n, _)) ->
            let rust_type = name_rust_type ty in
            let count = camlint_of_coqint n in
            fprintf p "@[<hv 2>%a =@ vec![0; %ld].into_boxed_slice() as Box<[%s]>;@]" 
              print_place v count rust_type
        | (Econst_int(n, _), Esizeof(ty, _)) ->
            let rust_type = name_rust_type ty in
            let count = camlint_of_coqint n in
            fprintf p "@[<hv 2>%a =@ vec![0; %ld].into_boxed_slice() as Box<[%s]>;@]" 
              print_place v count rust_type
        | _ ->
            fprintf p "@[<hv 2>/* Error:类型信息不足,建议改为sizeof(type)*n的形式 */@]"
      )
  | Epure (Esizeof(ty, _)) ->
      let rust_type = name_rust_type ty in
      fprintf p "@[<hv 2>%a =@ Box::new(0) as Box<%s>;@]" 
        print_place v rust_type
  | Epure (Eas(pe, _)) ->
      (* 处理各种类型转换的情况 *)
      let rec extract_sizeof_expr expr = 
        match expr with
        | Esizeof(ty, _) -> Some ty
        | Eas(pe', _) -> extract_sizeof_expr pe'
        | _ -> None
      in
      (
        match extract_sizeof_expr pe with
        | Some ty ->
            let rust_type = name_rust_type ty in
            fprintf p "@[<hv 2>%a =@ Box::new(0) as Box<%s>;@]" 
              print_place v rust_type
        | None ->
            fprintf p "@[<hv 2>/* 错误:无法从参数中提取类型信息 */@]"
      )
  | _ ->
      fprintf p "@[<hv 2>/* 错误:类型信息不足,建议改为sizeof(type)*n的形式 */@]"

let get_callee_name (e: expr) : string option =
  match e with
  | Epure (Eplace(Plocal(id, _), _)) -> Some (String.lowercase_ascii (extern_atom id))
  | Epure (Eglobal(id, _))           -> Some (String.lowercase_ascii (extern_atom id))
  | _                                -> None

let rec print_stmt p (s: Rustlight.statement) = 
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
    fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id)(extern_atom id) print_expr e
  | Scall(v, e1, el) ->
    (* 检测是否为malloc或free调用 *)
    let is_malloc_call = match e1 with
      | Epure (Eglobal(id, _)) -> 
          let name = extern_atom id in
          let lower_name = String.lowercase_ascii name in
          (* 处理各种可能的malloc变体 *)
          lower_name = "malloc" || lower_name = "__malloc" 
      | _ -> false
    in
    let is_free_call = match e1 with
      | Epure (Eglobal(id, _)) -> 
          let name = extern_atom id in
          let lower_name = String.lowercase_ascii name in
          (* 处理各种可能的free变体 *)
          lower_name = "free" || lower_name = "__free" 
      | _ -> false
    in
    if is_malloc_call then (
      (* 解析malloc参数并生成对应的Box代码 *)
      match el with
      | [param] -> parse_malloc_param p v param
      | _ ->
          fprintf p "@[<hv 2>/* 错误：malloc参数数量错误 */@]"
    ) else if is_free_call then (
      (* free调用不需要输出，Rust的Box会自动处理释放 *)
      fprintf p "/* free call replaced by Rust's ownership system */"
    ) else (
      (* 正常函数调用 *)
      (match get_callee_name e1 with
     | Some ("malloc" | "__malloc") ->
         (match el with
          | [param] -> parse_malloc_param p v param
          | _ -> fprintf p "@[<hv 2>/* Error: wrong number of arguments for malloc */@]")
     | Some ("free" | "__free") ->
         fprintf p "/* free call removed, handled by Box drop */;"
     | _ ->
         (* 正常的函数调用逻辑 (这是你原来的 else 分支) *)
         let fun_ty = type_of_expr e1 in
           let param_tys = 
             match fun_ty with 
             | Rusttypes.Tfunction(_, _, args, _, _) ->  typelist_to_list args
             | _ -> List.map (fun _ -> Rusttypes.Tunit) el  (* fallback: 全部Tunit *)
           in
           fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
             print_place v
             expr (15, e1)
             print_expr_list_with_type (true, el, param_tys)
    )
    )
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if %a {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
    fprintf p "@[<v 2>if ! %a {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
    fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s1) ->
    fprintf p "@[<v 2>while true {@ %a@;<0 -2>}@]"
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

(* Check whether function id is main_id *)
let is_main_id id =
  let fun_name = extern_atom id in
  fun_name = "main"
let print_function p id f =
  if is_main_id id then 
    begin
    fprintf p "fn%s"
        (name_rust_decl_fn (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv f.fn_generic_origins f.fn_origins_relation) f.fn_return);
        fprintf p "{@;@[<v 2>  @[<v 1>@;";
        List.iter 
        (fun (id, ty) ->
          fprintf p "let mut %s;@ " (name_rust_decl_fn_arg (extern_atom id ^ " : ") ty))
        f.fn_vars;
        print_stmt p f.fn_body;
    fprintf p "@]@;<0 -2>}@]@ @ "
    end
  else
    begin
      fprintf p "fn%s@ "
                (name_rust_decl_fn (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv f.fn_generic_origins f.fn_origins_relation) f.fn_return);
      fprintf p "@[<v 2>{@ ";
        (* Print variables and their types *)
        List.iter 
        (fun (id, ty) ->
          fprintf p "let mut %s;@ " (name_rust_decl_var (extern_atom id ^ " : ") ty))
        f.fn_vars;
        (*
        List.iter
        (fun (id, ty) ->
          fprintf p "fn_param: %s;@ " (name_rust_decl (extern_atom id) ty))
        f.fn_params; *)
        print_stmt p f.fn_body;
      fprintf p "@;<0 -2>}@]@ @ "
    end

let print_fundef p id fd =
  match fd with
  | Rusttypes.External(_, _, _, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      print_function p id f

let print_fundecl p id fd = 
  match fd with 
  | Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _), args, res, cconv) ->
      fprintf p "unsafe extern \"C\" { %s; }@ "
                (name_rust_decl_fn (extern_atom id) 
                  (Rusttypes.Tfunction([], [], args, res, cconv)))
  | Rusttypes.External(_, _ ,_, _, _, _) ->
      ()
  | Rusttypes.Internal f ->
      (* We should not print fundecl in rust*)
      ()
      (* We should not print fundecl of main function *)
      (* if is_main_id id then () else
      fprintf p "%s;@ "
                (name_rust_decl_fn (extern_atom id) 
                  (Rustlight.type_of_function f))) *)

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