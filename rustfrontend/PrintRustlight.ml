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

let print_rust_float p f =
  let s = Printf.sprintf "%.18g" f in
  if String.contains s '.' || String.contains s 'e' then
    fprintf p "%s" s
  else
    fprintf p "%s.0" s

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

let is_float_type ty =
  match ty with
  | Rusttypes.Tfloat _ -> true
  | _ -> false

(* Helper function to check if a pexpr is an integer constant *)
let is_int_const pe =
  match pe with
  | Econst_int _ -> true
  | _ -> false

(* Get the type of a pexpr - moved here to be available in pexpr function *)
let type_of_pexpr (p : Rustlight.pexpr) : Rusttypes.coq_type =
  match p with
  | Eunit -> Rusttypes.Tunit
  | Econst_int (_, ty) -> ty
  | Econst_float (_, ty) -> ty
  | Econst_single (_, ty) -> ty
  | Econst_long (_, ty) -> ty
  | Eplace (_, ty) -> ty
  | Ecktag (_, _) -> Rusttypes.Tint (Ctypes.I32, Ctypes.Signed)
  | Eref (_, _, _, ty) -> ty
  | Eunop (_, _, ty) -> ty
  | Ebinop (_, _, _, ty) -> ty
  | Eglobal (_, ty) -> ty
  | Eas (_, ty) -> ty
  | Esizeof (_, ty) -> ty
  | Ederef (_, ty) -> ty

let rec print_place out (p: place) =
  match p with
  | Plocal(id, _) ->
      fprintf out "%s" (extern_atom id)
  | Pderef(Pparenthesize(_, _, Ebinop(Oadd, base, index, _)), _) ->
      (* 关键修复 #2: 在索引表达式后添加 'as usize' *)
      fprintf out "%a[(%a) as usize]" pexpr (0, base) pexpr (0, index)
  | Pderef(p', _) ->
      fprintf out "(*%a)" print_place p'
  | Pfield(p', fid, _) ->
      fprintf out "%a.%s" print_place p' (extern_atom fid)
  | Pdowncast(p',fid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom fid)
  | Pparenthesize(_, _, ll) ->
      fprintf out "(%a)" pexpr (0, ll)
  | ParrayIndex(p_base, p_index, _) ->
      fprintf out "%a[(%s) as usize]" print_place p_base (extern_atom p_index)
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
      fprintf p "%a[(%a) as usize]" pexpr (0, base) pexpr (0, index)
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
    print_rust_float p (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
    fprintf p "%.18g_f32" (camlfloat_of_coqfloat32 f)
  | Econst_long(n, Rusttypes.Tlong(Unsigned)) ->
    fprintf p "(%Lu as usize)" (camlint64_of_coqint n)
  | Econst_long(n, _) ->
    fprintf p "%Ldi64" (camlint64_of_coqint n)
  | Eglobal(id, _) ->
    fprintf p "%s" (extern_atom id)
  | Eunop(Oabsfloat, a1, _) ->
    fprintf p "__builtin_fabs(%a)" pexpr (2, a1)
  | Eunop(op, a1, _) ->
    fprintf p "%s%a" (name_unop op) pexpr (prec', a1)
  | Ebinop(op, a1, a2, ty) ->
    (* Check if this is a float operation - if so, convert int literals to float *)
    let is_float_op = is_float_type ty || is_float_type (type_of_pexpr a1) || is_float_type (type_of_pexpr a2) in
    (* Check if this is a comparison with mixed signed/unsigned types *)
    let is_comparison_op = match op with
      | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge | Cop.Oeq | Cop.One -> true
      | _ -> false
    in
    let ty1 = type_of_pexpr a1 in
    let ty2 = type_of_pexpr a2 in
    let needs_type_conversion = is_comparison_op && (
      match ty1, ty2 with
      (* u32 compared with i32 - convert i32 to u32 *)
      | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned), Rusttypes.Tint(Ctypes.I32, Ctypes.Signed)
      | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed), Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) -> true
      | _ -> false
    ) in
    (* Helper to check if a type is an integer type *)
    let is_int_type t = match t with
      | Rusttypes.Tint(_, _) -> true
      | Rusttypes.Tlong(_) -> true
      | _ -> false
    in
    (* Determine target float type name *)
    let float_type_name = match ty with
      | Rusttypes.Tfloat(Ctypes.F32) -> "f32"
      | Rusttypes.Tfloat(Ctypes.F64) -> "f64"
      | _ -> "f64"  (* default to f64 *)
    in
    (* Print first operand *)
    (match a1 with
     | Econst_int(n, _) when is_float_op ->
         fprintf p "%ld.0" (camlint_of_coqint n)
     | _ ->
         if needs_type_conversion then
           match ty1, ty2 with
           | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed), Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) ->
               (* a1 is i32, a2 is u32 - convert a1 to u32 *)
               fprintf p "(%a as u32)" pexpr (0, a1)
           | _ -> pexpr p (prec1, a1)
         else if is_float_op && is_int_type ty1 then
           (* Float operation with int expression - need conversion *)
           fprintf p "(%a as %s)" pexpr (prec1, a1) float_type_name
         else
           pexpr p (prec1, a1));
    fprintf p "@ %s " (name_binop op);
    (* Print second operand *)
    (match a2 with
     | Econst_int(n, _) when is_float_op ->
         fprintf p "%ld.0" (camlint_of_coqint n)
     | _ ->
         if needs_type_conversion then
           match ty1, ty2 with
           | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned), Rusttypes.Tint(Ctypes.I32, Ctypes.Signed) ->
               (* a1 is u32, a2 is i32 - convert a2 to u32 *)
               fprintf p "(%a as u32)" pexpr (0, a2)
           | _ -> pexpr p (prec2, a2)
         else if is_float_op && is_int_type ty2 then
           (* Float operation with int expression - need conversion *)
           fprintf p "(%a as %s)" pexpr (prec2, a2) float_type_name
         else
           pexpr p (prec2, a2))
  | Ecktag(v, fid) ->
    fprintf p "%s(%a, %s)" "cktag" print_place v (extern_atom fid)
  | Eref(org, mut, v, _) ->
    (* Rust reference syntax: &mut place or &place *)
    fprintf p "&%s%a" (string_of_mut mut) print_place v
  | Eas(pe, ty) ->
      (* Check if this is casting a comparison or bool-valued expression to bool - skip it *)
      let rec is_bool_valued_expr pe = 
        match pe with
        | Ebinop((Oeq | One | Olt | Ogt | Ole | Oge), _, _, _) -> true
        | Ebinop((Oand | Oor), _, _, _) -> true  (* logical and/or also return bool *)
        | Eplace(Pparenthesize(_, _, inner_pe), _) -> is_bool_valued_expr inner_pe
        | Eas(inner_pe, inner_ty) ->
            (* Check if inner cast is to bool *)
            (match inner_ty with
             | Rusttypes.Tint(Ctypes.IBool, _) -> true
             | _ -> is_bool_valued_expr inner_pe)
        | _ -> false
      in
      let is_casting_to_bool = 
        match ty with
        | Rusttypes.Tint(Ctypes.IBool, _) -> true
        | _ -> false
      in
      (* Check if casting to slice type *)
      let is_casting_to_slice = 
        match ty with
        | Rusttypes.Tslice(_, _) -> true
        | _ -> false
      in
      if is_casting_to_bool && is_bool_valued_expr pe then
        (* Skip redundant cast to bool since expression already returns bool *)
        pexpr p (prec', pe)
      else if is_casting_to_slice then
        (* When casting to slice, check if we need to add &mut *)
        (* Don't add &mut if the expression is already a reference (Eref) *)
        let is_already_ref = match pe with
          | Eref(_, _, _, _) -> true
          | _ -> false
        in
        if not is_already_ref then
          (* Need to add &mut or & for the cast *)
          (match ty with
           | Rusttypes.Tslice(Rusttypes.Mutable, _) ->
               fprintf p "(&mut %a as %s)" pexpr (prec', pe) (name_rust_type ty)
           | Rusttypes.Tslice(Rusttypes.Immutable, _) ->
               fprintf p "(&%a as %s)" pexpr (prec', pe) (name_rust_type ty)
           | _ ->
               fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty))
        else
          (* Already has &mut, just cast *)
          fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty)
      else
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

(* type_of_pexpr already defined above *)

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
      (* (match type_of_expr r with
       | Rusttypes.Tarray _ | Rusttypes.Traw_pointer _ -> fprintf p ".as_ptr()"
       | _ -> ()); *)
      print_expr_list p (false, rl)

let rec print_expr_list_with_type p (first, exprs, param_tys, is_c_function) =
  match exprs, param_tys with
  | [], [] -> ()
  | r :: rl, ty :: tyl ->
      if not first then fprintf p ",@ ";
      (* Check if we MUST add .as_mut_ptr() for C FFI compatibility *)
      let expr_ty = type_of_expr r in
      let needs_ptr_conversion = is_c_function && (
        match ty, expr_ty with
        (* C function expects raw pointer, but we have array or slice - MUST convert *)
        | Rusttypes.Traw_pointer(_, _), Rusttypes.Tarray(_, _, _) -> true
        | Rusttypes.Traw_pointer(_, _), Rusttypes.Tslice(_, _) -> true
        (* C function parameter is slice (this represents a pointer in FFI) - MUST convert to raw pointer *)
        (* This handles both: 1) slice→slice (atoi case), 2) array→slice, 3) void*→any slice *)
        | Rusttypes.Tslice(_, _), Rusttypes.Tarray(_, _, _) -> true
        | Rusttypes.Tslice(_, _), Rusttypes.Tslice(_, _) -> true
        | _ -> false
      ) in
      
      if needs_ptr_conversion then begin
        (* MUST use .as_mut_ptr() for FFI safety *)
        (* Check if expression is an Eas (cast) - if so, wrap the whole expression *)
        let expr_contains_cast = match r with
          | Epure (Eas(_, _)) -> true
          | _ -> false
        in
        (* Check if target is c_void pointer and we need extra cast *)
        let needs_cvoid_cast = match ty with
          | Rusttypes.Traw_pointer(_, Rusttypes.Tvoid) -> true
          | Rusttypes.Tslice(_, Rusttypes.Tvoid) -> true
          | _ -> false
        in
        if expr_contains_cast then begin
          if needs_cvoid_cast then
            fprintf p "(%a).as_mut_ptr() as %s" expr (2, r) (PrintRustsyntax.name_rust_type_ffi ty)
          else
            fprintf p "(%a).as_mut_ptr()" expr (2, r)
        end else begin
          expr p (2, r);
          if needs_cvoid_cast then
            fprintf p ".as_mut_ptr() as %s" (PrintRustsyntax.name_rust_type_ffi ty)
          else
            fprintf p ".as_mut_ptr()"
        end
      end else begin
        (* For Rust functions with slice parameters, check if we need to add &mut *)
        let needs_ref = not is_c_function && (
          match ty, expr_ty with
          | Rusttypes.Tslice(Rusttypes.Mutable, _), Rusttypes.Tarray(_, _, _) -> true
          | Rusttypes.Tslice(Rusttypes.Immutable, _), Rusttypes.Tarray(_, _, _) -> true
          | _ -> false
        ) in
        if needs_ref then begin
          (* Need to add &mut or & for array to slice conversion *)
          match ty with
          | Rusttypes.Tslice(Rusttypes.Mutable, _) ->
              fprintf p "&mut ";
              expr p (2, r)
          | Rusttypes.Tslice(Rusttypes.Immutable, _) ->
              fprintf p "&";
              expr p (2, r)
          | _ -> expr p (2, r)
        end else begin
          expr p (2, r);
          (* Only cast if type is not Tunit and not a slice for Rust functions *)
          match ty with
          | Rusttypes.Tunit -> () 
          | Rusttypes.Tslice(_, _) when not is_c_function -> () (* Rust functions accept slices directly (when already a slice) *)
          | _ -> fprintf p " as %s" (name_rust_decl "" ty)
        end
      end;
      print_expr_list_with_type p (false, rl, tyl, is_c_function)

  | r :: rl, [] ->
      (* No more parameter types - this happens with variadic functions like printf *)
      if not first then fprintf p ",@ ";
      (* For C variadic functions, check if we MUST convert arrays/slices to pointers *)
      if is_c_function then
        let expr_ty = type_of_expr r in
        (match expr_ty with
         | Rusttypes.Tarray(_, _, _) | Rusttypes.Tslice(_, _) ->
             (* Arrays and slices MUST be converted to raw pointers for C variadic functions *)
             expr p (2, r);
             fprintf p ".as_mut_ptr()"
         | _ ->
             expr p (2, r))
      else
        expr p (2, r);
      print_expr_list_with_type p (false, rl, [], is_c_function)
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
             Count expression needs to be usize for vec![]
           *)
           fprintf p "@[<hv 2>let mut %a = vec![%s::default(); (%a) as usize].into_boxed_slice();@]"
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

(* Helper to check if pexpr is a comparison that returns bool *)
let rec is_comparison_pexpr pe =
  match pe with
  | Ebinop((Oeq | One | Olt | Ogt | Ole | Oge), _, _, _) -> true
  | Ebinop((Oand | Oor), _, _, _) -> true  (* Logical ops also return bool *)
  | Eplace(p, _) -> 
      (* Check if the place contains a comparison expression *)
      (match p with
       | Pparenthesize(_, _, inner_pe) -> is_comparison_pexpr inner_pe
       | _ -> false)
  | Eas(inner_pe, ty) ->
      (* Check through cast expressions *)
      (match ty with
       | Rusttypes.Tint(Ctypes.IBool, _) -> is_comparison_pexpr inner_pe
       | _ -> false)
  | _ -> false

(* Helper to check if expression is a comparison that returns bool *)
let is_comparison_expr e =
  match e with
  | Epure pe -> is_comparison_pexpr pe
  | _ -> false

(* Helper to get the type of a place *)
let type_of_place (p : place) : Rusttypes.coq_type =
  match p with
  | Plocal(_, ty) -> ty
  | Pderef(_, ty) -> ty
  | Pfield(_, _, ty) -> ty
  | Pdowncast(_, _, ty) -> ty
  | Pparenthesize(_, ty, _) -> ty
  | ParrayIndex(_, _, ty) -> ty
  | Ppair(p1, p2) -> 
      (* For pairs, return a tuple type instead of Tunit *)
      (* This ensures the assignment is printed for method calls returning tuples *)
      Rusttypes.Tint(Ctypes.I32, Ctypes.Signed) (* Placeholder: pairs should have their own type *)

(* Helper to create a printer for expression with auto bool->int conversion if needed *)
let make_expr_printer_with_conversion place_ty e =
  fun p ->
    (* In Rust, comparison operators return bool, but we may be assigning to int *)
    let place_is_int = match place_ty with
      | Rusttypes.Tint(Ctypes.IBool, _) -> false
      | Rusttypes.Tint(_, _) -> true
      | _ -> false
    in
    let expr_ty = type_of_expr e in
    let expr_is_bool_like = match expr_ty with
      | Rusttypes.Tint(Ctypes.IBool, _) -> true
      | _ -> false
    in
    (* Need cast if: (1) expr is comparison that returns bool, OR (2) expr type is bool and place is int *)
    let needs_bool_to_int_cast = 
      (is_comparison_expr e && place_is_int) || 
      (expr_is_bool_like && place_is_int)
    in
    if needs_bool_to_int_cast then
      fprintf p "(%a as i32)" print_expr e
    else
      fprintf p "%a" print_expr e

(* Helper to print if condition - adds '!= 0' for int types but not for comparisons *)
let print_if_condition p e =
  (* Comparison operators in Rust return bool, so they don't need conversion *)
  if is_comparison_expr e then
    fprintf p "%a" print_expr e
  else
    (* Non-comparison expressions that are int types need '!= 0' *)
    let expr_ty = type_of_expr e in
    let is_int_type = match expr_ty with
      | Rusttypes.Tint(Ctypes.IBool, _) -> false (* bool doesn't need conversion *)
      | Rusttypes.Tint(_, _) -> true
      | Rusttypes.Tlong(_) -> true
      | _ -> false
    in
    if is_int_type then
      fprintf p "(%a) != 0" print_expr e
    else
      fprintf p "%a" print_expr e

(* Convert C format string to Rust format *)
(* let convert_c_format_to_rust s =
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
  Buffer.contents b *)

(* List of unsafe C functions that need safe wrappers *)
let unsafe_c_functions = [
  (* Math functions *)
  "floor"; "floorf"; "ceil"; "ceilf"; "sqrt"; "sqrtf"; "pow"; "powf";
  "sin"; "sinf"; "cos"; "cosf"; "tan"; "tanf"; "asin"; "asinf"; "acos"; "acosf"; "atan"; "atanf"; "atan2"; "atan2f";
  "sinh"; "sinhf"; "cosh"; "coshf"; "tanh"; "tanhf";
  "exp"; "expf"; "log"; "logf"; "log10"; "log10f"; "log2"; "log2f";
  "fabs"; "fabsf"; "fmod"; "fmodf"; "remainder"; "remainderf";
  "round"; "roundf"; "trunc"; "truncf"; "rint"; "rintf";
  "fma"; "fmaf"; "fmin"; "fminf"; "fmax"; "fmaxf";
  "hypot"; "hypotf"; "ldexp"; "ldexpf"; "frexp"; "frexpf"; "modf"; "modff";
  
  (* String functions *)
  "strlen"; "strcmp"; "strncmp"; "strcpy"; "strncpy"; "strcat"; "strncat";
  "strchr"; "strrchr"; "strstr"; "strtok"; "memcpy"; "memmove"; "memset"; "memcmp";
  
  (* I/O functions *)
  "printf";
  "fprintf"; "sprintf"; "snprintf"; "vprintf"; "vfprintf"; "vsprintf"; "vsnprintf";
  "scanf"; "fscanf"; "sscanf"; "vscanf"; "vfscanf"; "vsscanf";
  "puts"; "fputs"; "gets"; "fgets"; "putchar"; "fputc"; "getchar"; "fgetc"; "ungetc";
  "fopen"; "fclose"; "fread"; "fwrite"; "fseek"; "ftell"; "rewind"; "feof"; "ferror";
  
  (* Memory functions *)
  "calloc"; "realloc";
  
  (* Other standard functions *)
  "abort"; "exit"; "atexit"; "system"; "getenv";
  "abs"; "labs"; "llabs"; "div"; "ldiv"; "lldiv";
  "atoi"; "atol"; "atoll"; "atof"; "strtol"; "strtoll"; "strtoul"; "strtoull"; "strtod"; "strtof";
  "rand"; "srand"; "qsort"; "bsearch";
  "time"; "clock"; "difftime"; "mktime"; "localtime"; "gmtime"; "strftime";
]

(* Helper function to print function name - just prints the name *)
let print_function_call_name p e =
  match e with
  | Epure (Eglobal(id, _)) ->
      fprintf p "%s" (extern_atom id)
  | Epure (Eplace(Plocal(id, _), _)) ->
      fprintf p "%s" (extern_atom id)
  | _ -> expr p (15, e)

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
          let place_ty = type_of_place v in
          (* Check if expression already returns bool (comparison expr) *)
          let expr_returns_bool = is_comparison_expr e in
          (* Get the cast type name from name_rust_decl_var which matches variable declarations *)
          let full_decl = name_rust_decl_var " : " place_ty in
          let cast_type_name = 
            try
              let colon_idx = String.index full_decl ':' in
              String.trim (String.sub full_decl (colon_idx + 1) (String.length full_decl - colon_idx - 1))
            with Not_found -> "i32"  (* fallback *)
          in
          (* Determine if target is bool by checking the actual declared type name *)
          let is_bool_target = (cast_type_name = "bool") in
          (* Check if we're casting to a slice type and need to add &mut *)
          let is_slice_target = match place_ty with
            | Rusttypes.Tslice(_, _) -> true
            | _ -> false
          in
          let needs_borrow_for_slice = is_slice_target && (
            match e with
            | Epure (Eref(_, _, _, _)) -> false  (* Already a reference *)
            | Epure (Eplace(place, ty)) -> 
                (* Check if this is likely a malloc-generated Box variable *)
                let is_likely_box = match place with
                  | Plocal(id, _) ->
                      let var_name = extern_atom id in
                      (* Temporary variables like _128 (large numbers) that are declared as slice type 
                         but might be redeclared as Box by malloc.
                         Exclude small numbers like _1, _2 which are split_at_mut results *)
                      (String.length var_name > 1 && var_name.[0] = '_' && 
                       try 
                         let num = int_of_string (String.sub var_name 1 (String.length var_name - 1)) in
                         num >= 100  (* Only large temp variable IDs are from Clight, small ones from split_at_mut *)
                       with _ -> false) &&
                      (match ty with
                       | Rusttypes.Tslice(_, _) -> true  (* Type mismatch: declared as slice but redeclared as Box *)
                       | _ -> false)
                  | _ -> false
                in
                (* Only borrow if NOT already a slice AND (is Box OR is Array OR likely Box from malloc) *)
                (match ty with
                 | Rusttypes.Tslice(_, _) when not is_likely_box -> false  (* Already a slice, no borrow *)
                 | Rusttypes.Treference(_, _, _) -> false  (* Already a reference *)
                 | Rusttypes.Tbox _ -> true  (* Box needs &mut *)
                 | Rusttypes.Tarray(_, _, _) -> true  (* Array needs &mut *)
                 | _ when is_likely_box -> true  (* Likely a Box from malloc *)
                 | _ -> false)
            | _ -> false  (* Complex expression - don't add &mut to avoid precedence issues *)
          ) in
          (* Handle different cases of bool/int conversions and slice conversions *)
          if is_bool_target && expr_returns_bool then
            (* bool expr → bool var: direct assignment *)
            fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
          else if is_bool_target && not expr_returns_bool then
            (* int expr → bool var: Rust doesn't allow "i32 as bool", use "!= 0" *)
            fprintf p "@[<hv 2>%a =@ (%a) != 0;@]" print_place v print_expr e
          else if (not is_bool_target) && expr_returns_bool then
            (* bool expr → int var: need to cast bool to int *)
            fprintf p "@[<hv 2>%a =@ ((%a) as %s);@]" print_place v print_expr e cast_type_name
          else if needs_borrow_for_slice then
            (* Casting to slice: add &mut prefix *)
            (match place_ty with
             | Rusttypes.Tslice(Rusttypes.Mutable, _) ->
                 fprintf p "@[<hv 2>%a =@ (&mut %a as %s);@]" print_place v print_expr e cast_type_name
             | Rusttypes.Tslice(Rusttypes.Immutable, _) ->
                 fprintf p "@[<hv 2>%a =@ (&%a as %s);@]" print_place v print_expr e cast_type_name
             | _ ->
                 fprintf p "@[<hv 2>%a =@ (%a) as %s;@]" print_place v print_expr e cast_type_name)
          else
            (* int expr → int var: standard cast *)
            fprintf p "@[<hv 2>%a =@ (%a) as %s;@]" print_place v print_expr e cast_type_name
      )
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id)(extern_atom id) print_expr e
  | Scall(v, e1, el) ->
        (* detect malloc or free *)
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
          (* handle all type of free *)
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
             | _ -> List.map (fun _ -> Rusttypes.Tunit) el  (* fallback: 全部Tunit *)
             in
           (* Check if this is a C function call *)
           let is_c_function = match e1 with
             | Epure (Eglobal(id, _)) ->
                 let name = extern_atom id in
                 List.mem name unsafe_c_functions
             | Epure (Eplace(Plocal(id, _), _)) ->
                 let name = extern_atom id in
                 List.mem name unsafe_c_functions
             | _ -> false
           in
           (* Check if the destination variable type is Tunit - if so, don't print assignment *)
           (* This happens when the return value is ignored in the original C code *)
           let place_ty = type_of_place v in
           let is_ignored_return = match place_ty with
             | Rusttypes.Tunit -> true
             | _ -> false
           in
           (* Since function bodies are already wrapped in unsafe blocks,
              we don't need extra unsafe blocks for calling unsafe C functions *)
           if is_ignored_return then
             (* Only print the function call, no assignment *)
             fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
               print_function_call_name e1
               print_expr_list_with_type (true, el, param_tys, is_c_function)
           else
             (* Print full assignment statement *)
             fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
               print_place v
               print_function_call_name e1
               print_expr_list_with_type (true, el, param_tys, is_c_function)
         )
      )
  | Smethod_call(v, receiver, method_name, el) ->
      (* Method call: place = receiver.method(args) *)
      (* Check if the destination variable type is Tunit - if so, don't print assignment *)
      let place_ty = type_of_place v in
      let is_ignored_return = match place_ty with
        | Rusttypes.Tunit -> true
        | _ -> false
      in
      (* For method calls, we need to determine if the method is mutable (takes &mut self) or not *)
      (* For now, we'll use a simple heuristic: methods that modify the receiver are typically mutable *)
      (* Common patterns: push, pop, insert, remove, clear, etc. *)
      let method_str = extern_atom method_name in
      let is_mut_method = 
        let lower = String.lowercase_ascii method_str in
        (* Common mutable methods *)
        lower = "push" || lower = "pop" || lower = "insert" || lower = "remove" ||
        lower = "clear" || lower = "append" || lower = "extend" || lower = "drain" ||
        lower = "truncate" || lower = "resize" || lower = "swap" || lower = "sort" ||
        lower = "reverse" || lower = "dedup" || lower = "retain" || lower = "fill"
      in
      (* Print the method call *)
      if is_ignored_return then
        (* No assignment, just the method call *)
        if is_mut_method then
          fprintf p "@[<hv 2>(%a).%s@,(@[<hov 0>%a@]);@]"
            print_expr receiver
            method_str
            print_expr_list (true, el)
        else
          fprintf p "@[<hv 2>(%a).%s@,(@[<hov 0>%a@]);@]"
            print_expr receiver
            method_str
            print_expr_list (true, el)
      else
        (* With assignment *)
        if is_mut_method then
          fprintf p "@[<hv 2>%a =@ (%a).%s@,(@[<hov 0>%a@]);@]"
            print_place v
            print_expr receiver
            method_str
            print_expr_list (true, el)
        else
          fprintf p "@[<hv 2>%a =@ (%a).%s@,(@[<hov 0>%a@]);@]"
            print_place v
            print_expr receiver
            method_str
            print_expr_list (true, el)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if %a {@ %a@;<0 -2>}@]"
              print_if_condition e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
      fprintf p "@[<v 2>if !(%a) {@ %a@;<0 -2>}@]"
              print_if_condition e
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if %a {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_if_condition e
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
    fprintf p "fn main()";
    fprintf p "{@;@[<v 2>  @[<v 1>@;";
        fprintf p "unsafe {@ ";  (* Wrap in unsafe for static mut access *)
        (* If C main had parameters (argc, argv), declare them as local variables with default values *)
        List.iter 
        (fun (param_id, param_ty) ->
          let var_name = extern_atom param_id in
          (* Provide default initialization based on parameter name *)
          match var_name with
          | "argc" -> fprintf p "let mut argc : i32 = 0;@ "
          | "argv" -> 
              (* For argv, use a dangling non-null pointer for empty slice to avoid UB *)
              fprintf p "let mut argv : &mut [&mut [i8]] = unsafe { std::slice::from_raw_parts_mut(std::ptr::NonNull::<&mut [i8]>::dangling().as_ptr(), 0) };@ "
          | _ -> fprintf p "let mut %s;@ " (name_rust_decl_var (var_name ^ " : ") param_ty))
        f.fn_params;
        (* Print local variables *)
        List.iter 
        (fun (id, ty) ->
          match ty with
          | Rusttypes.Tarray(_, elem_ty, sz) ->
              (* Initialize arrays with default values *)
              let sz_val = camlint_of_coqint sz in
              let default_val = match elem_ty with
                | Rusttypes.Tint(_, _) -> "0"
                | Rusttypes.Tlong(_) -> "0"
                | Rusttypes.Tfloat(_) -> "0.0"
                | _ -> "Default::default()"
              in
              fprintf p "let mut %s = [%s; %ld];@ " 
                (extern_atom id)
                default_val
                sz_val
          | _ ->
              (* Initialize all variables with default values to avoid E0381 errors *)
              let default_init = match ty with
                | Rusttypes.Tint(_, _) -> " = 0"
                | Rusttypes.Tlong(_) -> " = 0"
                | Rusttypes.Tfloat(_) -> " = 0.0"
                | Rusttypes.Tunit -> ""
                | _ -> " = Default::default()"
              in
              fprintf p "let mut %s%s;@ " (name_rust_decl_var (extern_atom id ^ " : ") ty) default_init)
        f.fn_vars;
        print_stmt p f.fn_body;
        fprintf p "@;<0 -2>}@ ";
    fprintf p "@]@;<0 -2>}@]@ @ "
    end
  else
    begin
      fprintf p "fn%s@ "
                (name_rust_decl_fn (PrintRustsyntax.name_function_parameters extern_atom (extern_atom id) f.fn_params f.fn_callconv f.fn_generic_origins f.fn_origins_relation) f.fn_return);
      fprintf p "@[<v 2>{@ ";
        fprintf p "unsafe {@ ";  (* Wrap in unsafe for static mut access *)
        (* Print variables and their types *)
        List.iter 
        (fun (id, ty) ->
          match ty with
          | Rusttypes.Tarray(_, elem_ty, sz) ->
              (* Initialize arrays with default values *)
              let sz_val = camlint_of_coqint sz in
              let default_val = match elem_ty with
                | Rusttypes.Tint(_, _) -> "0"
                | Rusttypes.Tlong(_) -> "0"
                | Rusttypes.Tfloat(_) -> "0.0"
                | _ -> "Default::default()"
              in
              fprintf p "let mut %s = [%s; %ld];@ " 
                (extern_atom id)
                default_val
                sz_val
          | _ ->
              (* Initialize all variables with default values to avoid E0381 errors *)
              let default_init = match ty with
                | Rusttypes.Tint(_, _) -> " = 0"
                | Rusttypes.Tlong(_) -> " = 0"
                | Rusttypes.Tfloat(_) -> " = 0.0"
                | Rusttypes.Tunit -> ""
                | _ -> " = Default::default()"
              in
              fprintf p "let mut %s%s;@ " (name_rust_decl_var (extern_atom id ^ " : ") ty) default_init)
        f.fn_vars;
        (*
        List.iter
        (fun (id, ty) ->
          fprintf p "fn_param: %s;@ " (name_rust_decl (extern_atom id) ty))
        f.fn_params; *)
        print_stmt p f.fn_body;
        fprintf p "@;<0 -2>}@ ";
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
        (* All external C functions are declared with FFI-safe types *)
        fprintf p "unsafe extern \"C\" { %s; }@ "
                  (PrintRustsyntax.name_rust_decl_fn_ffi (extern_atom id)
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
  | AST.Gvar v -> PrintRustsyntax.print_globvardecl p id v

(* Generate safe wrapper functions for unsafe C functions *)
(* Note: We no longer generate safe wrappers since we automatically wrap 
   unsafe calls in unsafe blocks at the call site *)
let print_safe_wrappers p (prog: Rustlight.program) =
  (* Do nothing - safe wrappers are not needed anymore *)
  ()

let print_program p (prog: Rustlight.program) =
  (* Check if there are any mutable static variables *)
  let has_static_mut = 
    List.exists (fun (_, gd) ->
      match gd with
      | AST.Gvar v -> 
          (match v.AST.gvar_init with
           | [AST.Init_space _] -> 
               (match v.AST.gvar_info with
                | Rusttypes.Tarray(_, _, _) -> true
                | _ -> false)
           | _ -> false)
      | _ -> false
    ) prog.Rusttypes.prog_defs
  in
  fprintf p "@[<v 0>";
  (* Add allow attribute if there are static mut variables *)
  if has_static_mut then
    fprintf p "#![allow(static_mut_refs)]@ ";
  (* Don't print forward declarations - Rust doesn't support them *)
  (* List.iter (PrintRustsyntax.declare_composite p) prog.Rusttypes.prog_types; *)
  (* Add placeholder for commonly undefined system types *)
  fprintf p "pub struct __sFILEX;@ ";
  List.iter (PrintRustsyntax.define_composite p) prog.Rusttypes.prog_types;
  List.iter (print_globdecl p) prog.Rusttypes.prog_defs;
  print_safe_wrappers p prog;
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