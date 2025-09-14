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

(* 在 rustfrontend/PrintRustlight.ml 中 *)

let rec print_place out (p: place) =
  match p with
  | Plocal(id, _) ->
      fprintf out "%s" (extern_atom id)
  | Pderef(Pparenthesize(_, _, Ebinop(Oadd, base, index, _)), _) ->
      (* 关键修复 #2: 在索引表达式后添加 'as usize' *)
      fprintf out "%a[%a as usize]" pexpr (0, base) pexpr (0, index)
  | Pderef(p', _) ->
      fprintf out "(*%a)" print_place p'
  | Pfield(p', fid, _) ->
      fprintf out "%a.%s" print_place p' (extern_atom fid)
  | Pdowncast(p',fid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom fid)
  | Pparenthesize(_, _, ll) ->
      fprintf out "(%a)" pexpr (0, ll)
  | ParrayIndex(p_base, p_index, _) ->
      fprintf out "%a[%s as usize]" print_place p_base (extern_atom p_index)
  | Ppair (p1, p2) -> (* 添加这个 case *)
    fprintf out "(%a, %a)" print_place p1 print_place p2

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
  | Ederef(Ebinop(Oadd, base, index, _), _) ->
      (* 关键修复 #2: 在索引表达式后添加 'as usize' *)
      fprintf p "%a[%a as usize]" pexpr (0, base) pexpr (0, index)
  | Ederef(pe, ty) ->
      fprintf p "*(%a)" pexpr (prec', pe)
  | Eunit ->  fprintf p "tt"
  | Eplace(v, _) ->
    fprintf p "%a" print_place v
  (* ... pexpr 函数的其余部分保持不变 ... *)
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

let parse_malloc_param p v param =
  match param with
  (* 匹配 sizeof(T) * N 的模式 *)
  | Epure (Ebinop(Omul, pe1, pe2, _)) ->
      let sizeof_expr, count_expr =
        match pe1, pe2 with
        | (Esizeof _, _) -> (pe1, pe2)
        | (_, Esizeof _) -> (pe2, pe1)
        | _ -> (Eunit, Eunit) (* 错误情况 *)
      in
      (match sizeof_expr, count_expr with
       | (Esizeof(ty, _), count_pe) ->
           let rust_type = name_rust_type ty in
           (*
             关键修复 #1: 使用 `let mut` 直接绑定。
             这会遮蔽掉函数顶部错误的声明，并创建一个类型正确的 Box。
           *)
           fprintf p "@[<hv 2>let mut %a = vec![%s::default(); %a].into_boxed_slice();@]"
             print_place v rust_type pexpr (0, count_pe)
       | _ ->
           fprintf p "@[<hv 2>/* Error: could not parse malloc for array */@]")
  (* 匹配 sizeof(T) 的模式 *)
  | Epure (Esizeof(ty, _)) ->
      let rust_type = name_rust_type ty in
      fprintf p "@[<hv 2>let mut %a = Box::new(%s::default());@]"
        print_place v rust_type
  | _ ->
      fprintf p "@[<hv 2>/* Error: could not parse malloc parameter */@]"

let get_callee_name (e: expr) : string option =
  match e with
  | Epure (Eplace(Plocal(id, _), _)) -> Some (String.lowercase_ascii (extern_atom id))
  | Epure (Eglobal(id, _))           -> Some (String.lowercase_ascii (extern_atom id))
  | _                                -> None

(* Convert C format string to Rust format *)
let convert_c_format_to_rust s =
  let b = Buffer.create (String.length s) in
  let i = ref 0 in
  while !i < String.length s do
    if s.[!i] = '%' then (
      i := !i + 1;
      if !i < String.length s then (
        match s.[!i] with
        | '%' -> Buffer.add_char b '%'
        | 'd' | 'i' | 'u' | 'x' | 'X' | 'o' | 'f' | 'F' | 'e' | 'E' | 'g' | 'G' | 'a' | 'A' | 's' | 'c' ->
            Buffer.add_string b "{}"
        | 'p' -> Buffer.add_string b "{:p}"
        | _ -> () (* Ignore unsupported format specifiers for now *)
      )
    ) else (
      Buffer.add_char b s.[!i]
    );
    i := !i + 1
  done;
  Buffer.contents b

let escape_rust_string s =
  let b = Buffer.create (String.length s + 10) in
  String.iter (function
    | '\n' -> Buffer.add_string b "\\n"
    | '\t' -> Buffer.add_string b "\\t"
    | '\r' -> Buffer.add_string b "\\r"
    | '\\' -> Buffer.add_string b "\\\\"
    | '"' -> Buffer.add_string b "\\\""
    | c -> Buffer.add_char b c) s;
  Buffer.contents b

let rec print_stmt p (s: Rustlight.statement) = 
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
      (* FIX: 检查 v 是否是我们定义的 Ppair 类型 *)
      (match v with
      | Ppair(id_l, id_r) ->
          fprintf p "@[<hv 2>let %a =@ %a;@]"
            print_place v
            print_expr e
      | _ ->
          fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
      )
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id)(extern_atom id) print_expr e
  | Scall(v, e1, el) ->
    (* 检查被调用的函数是否是 "printf" *)
    let callee_name =
      match get_callee_name e1 with
      | Some name -> name
      | None -> ""
    in
    if callee_name = "printf" || callee_name = "__printf" then
      (* 是printf调用，进行特殊处理 *)
      let format_arg, other_args =
        match el with
        | hd :: tl -> (hd, tl)
        | [] -> (Epure Eunit, []) (* printf 不应该没有参数 *)
      in

      (* 修正后的逻辑：正确识别字符串字面量的ID，无论它是Eglobal还是Plocal *)
      let string_id_option =
        match format_arg with
        | Epure (Eglobal (id, _)) -> Some (extern_atom id)
        | Epure (Eplace (Plocal (id, _), _)) -> Some (extern_atom id)
        | _ -> None
      in
      let format_string_literal =
        match string_id_option with
        | Some string_id ->
            (try Hashtbl.find PrintRustsyntax.string_literals string_id
             with Not_found -> Printf.sprintf "<error: string '%s' not found>" string_id)
        | None -> "<error: format argument is not a string literal>"
      in

      (* 将C格式字符串转换为Rust格式 *)
      let rust_format_string = convert_c_format_to_rust format_string_literal in

      (* 在打印前对Rust格式化字符串进行转义，处理\n等特殊字符 *)
      let escaped_format_string = escape_rust_string rust_format_string in

      (* 生成println!宏 *)
      fprintf p "println!(\"%s\"" escaped_format_string;
      if other_args <> [] then (
        fprintf p ", ";
        print_expr_list p (true, other_args)
      );
      fprintf p ");"
    else (
      (* 这是处理所有其他函数调用的原始逻辑 *)
      (match get_callee_name e1 with
     | Some ("malloc" | "__malloc") ->
         (match el with
          | [param] -> parse_malloc_param p v param
          | _ -> fprintf p "@[<hv 2>/* Error: wrong number of arguments for malloc */@]")
     | Some ("free" | "__free") ->
         fprintf p "/* free call removed, handled by Box drop */;"
     | _ ->
         let fun_ty = type_of_expr e1 in
           let param_tys =
             match fun_ty with
             | Rusttypes.Tfunction(_, _, args, _, _) ->  typelist_to_list args
             | _ -> List.map (fun _ -> Rusttypes.Tunit) el
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
  let fun_name = extern_atom id in
  (* 检查函数名是否在屏蔽列表中 *)
  if List.mem fun_name PrintRustsyntax.suppressed_functions then
    () (* if in unsafe function list, do noting *)
  else
    (* if not in unsafe function list, print it *)
    match fd with
    | Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _), args, res, cconv) ->
        fprintf p "unsafe extern \"C\" { %s; }@ "
                  (name_rust_decl_fn (extern_atom id)
                    (Rusttypes.Tfunction([], [], args, res, cconv)))
    | Rusttypes.External(_, _ ,_, _, _, _) ->
        ()
    | Rusttypes.Internal f ->
        ()


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