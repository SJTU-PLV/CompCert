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
let is_slice_type ty =
  match ty with
  | Rusttypes.Tslice(_, _, _) -> true
  | _ -> false

let is_array_type ty =
  match ty with
  | Rusttypes.Tarray(_, _, _) -> true
  | _ -> false

let rec array_element_type ty =
  match ty with
  | Rusttypes.Tarray(_, elem, _) -> array_element_type elem
  | _ -> ty

let is_ptr_like_type ty =
  match ty with
  | Rusttypes.Tslice(_, _, _) -> true
  | Rusttypes.Traw_pointer(_, _) -> true
  | _ -> false

let is_function_type ty =
  match ty with
  | Rusttypes.Tfunction(_, _, _, _, _) -> true
  | _ -> false

let pointed_type ty =
  match ty with
  | Rusttypes.Tslice(_, elem_ty, _) -> Some elem_ty
  | Rusttypes.Traw_pointer(_, elem_ty) -> Some elem_ty
  | _ -> None

let ptr_origin_of_type ty =
  match ty with
  | Rusttypes.Tslice(_, _, origin) -> Some origin
  | _ -> None

let is_slice_target ty = is_slice_type ty

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

let name_unop = function
  | Onotbool -> "!"
  | Onotint -> "!"
  | Oneg -> "-"
  | Oabsfloat -> "__builtin_fabs"

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
  (* Rust 的运算符优先级与 C 不同：位运算 (& ^ |) 高于比较运算 (== != < <= > >=)。
     这里必须按 Rust 规则设置，否则会出现 `a != 18 & true` 这类被解析成
     `a != (18 & true)` 的类型错误/语义错误。 *)
  | Ebinop(Oand, _, _, _) -> (10, LtoR)
  | Ebinop(Oxor, _, _, _) -> (9, LtoR)
  | Ebinop(Oor, _, _, _) -> (8, LtoR)
  | Ebinop((Olt|Ogt|Ole|Oge|Oeq|Cop.One), _, _, _) -> (7, LtoR)
  | Eplace(_, _) -> (16,NA)
  | Ecktag(_, _) -> (15, RtoL)
  | Eref(_, _, _, _) -> (15, RtoL)
  | Eas(_, _) -> (16, NA)
  | Esizeof(_, _) -> (16, NA)
  | Ederef(_, _) -> (15, RtoL)

let precedence = function
  | Emoveplace(_,_) -> (16,NA)
  | Epure pe -> precedence' pe

module StringSet = Set.Make(String)

let global_var_names : StringSet.t ref = ref StringSet.empty
(* Extern globals whose declared type is a C pointer.
   These must be printed with FFI-safe raw pointer types in `PrintRustsyntax`,
   and uses must wrap them into our `Ptr<T>` runtime representation. *)
let extern_pointer_globals : StringSet.t ref = ref StringSet.empty
let current_name_map = Hashtbl.create 97
let used_local_names : StringSet.t ref = ref StringSet.empty

let rust_reserved_keywords =
  let keywords = [
    "as"; "break"; "const"; "continue"; "crate"; "else"; "enum"; "extern";
    "false"; "fn"; "for"; "if"; "impl"; "in"; "let"; "loop"; "match"; "mod";
    "move"; "mut"; "pub"; "ref"; "return"; "self"; "Self"; "static"; "struct";
    "super"; "trait"; "true"; "type"; "unsafe"; "use"; "where"; "while";
    "async"; "await"; "dyn"; "abstract"; "become"; "box"; "do"; "final";
    "macro"; "override"; "priv"; "try"; "typeof"; "unsized"; "virtual";
    "yield"; "union"
  ] in
  List.fold_left (fun acc kw -> StringSet.add kw acc) StringSet.empty keywords

let sanitize_rust_identifier name =
  let base = if name = "" then "__tmp" else name in
  if StringSet.mem base rust_reserved_keywords then base ^ "_" else base

let lookup_ident_name id =
  try Hashtbl.find current_name_map id
  with Not_found -> sanitize_rust_identifier (extern_atom id)

let binding_with_type name ty =
  Printf.sprintf "%s: %s" name (name_rust_type ty)

let reset_local_name_map () =
  Hashtbl.clear current_name_map;
  used_local_names := !global_var_names

let rec reserve_name base idx =
  let candidate =
    if idx = 0 then base else Printf.sprintf "%s_%d" base idx
  in
  if StringSet.mem candidate !used_local_names then
    reserve_name base (idx + 1)
  else begin
    used_local_names := StringSet.add candidate !used_local_names;
    candidate
  end

let register_local_name id =
  let base = sanitize_rust_identifier (extern_atom id) in
  let name = reserve_name base 0 in
  Hashtbl.add current_name_map id name

let setup_local_names (f: Rustlight.coq_function) =
  reset_local_name_map ();
  List.iter (fun (id, _) -> register_local_name id) f.fn_params;
  List.iter (fun (id, _) -> register_local_name id) f.fn_vars

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

let rec is_ptr_place (p: place) =
  match p with
  | Plocal(_, ty) -> is_ptr_like_type ty
  | Pderef(_, ty) -> is_ptr_like_type ty
  | Pfield(_, _, ty) -> is_ptr_like_type ty
  | Pdowncast(_, _, ty) -> is_ptr_like_type ty
  | Pparenthesize(_, ty, _) -> is_ptr_like_type ty
  | ParrayIndex(base, _, _) -> is_ptr_place base
  | Ppair(_, _) -> false

and extract_pointer_field_place (p: place) =
  match p with
  | Pfield (Pderef(base, _), fid, ty) when is_ptr_place base -> Some (base, fid, ty)
  | _ -> None

and extract_ptr_store_target (p: place) =
  match p with
  | Pderef (Pparenthesize(_, _, Ebinop(Oadd, base, index, _)), _) ->
      Some (base, index)
  | _ -> None

and is_pointer_type ty =
  match ty with
  | Rusttypes.Tslice(_, _, _)
  | Rusttypes.Traw_pointer(_, _) -> true
  | _ -> false

and is_declared_ptr_type ty =
  if is_pointer_type ty then true
  else
    let ty_name = name_rust_type ty in
    String.length ty_name >= 4 && String.sub ty_name 0 4 = "Ptr<"

and is_bool_type ty =
  match ty with
  | Rusttypes.Tint(Ctypes.IBool, _) -> true
  | _ -> false

and is_integer_type ty =
  match ty with
  | Rusttypes.Tint(_, _) | Rusttypes.Tlong(_) -> true
  | _ -> false

and is_unit_type ty =
  match ty with
  | Rusttypes.Tunit | Rusttypes.Tvoid -> true
  | _ -> false

and is_u64_type ty =
  match ty with
  | Rusttypes.Tlong(Ctypes.Unsigned) -> true
  | _ -> false

and is_i64_type ty =
  match ty with
  | Rusttypes.Tlong(Ctypes.Signed) -> true
  | _ -> false

and is_u32_type ty =
  match ty with
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) -> true
  | _ -> false

and is_i32_type ty =
  match ty with
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed) -> true
  | _ -> false

and type_of_place (p : place) : Rusttypes.coq_type =
  match p with
  | Plocal(_, ty) -> ty
  | Pderef(_, ty) -> ty
  | Pfield(_, _, ty) -> ty
  | Pdowncast(_, _, ty) -> ty
  | Pparenthesize(_, ty, _) -> ty
  | ParrayIndex(_, _, ty) -> ty
  | Ppair(_, _) ->
      Rusttypes.Tint(Ctypes.I32, Ctypes.Signed)

let rec resolved_place_type place =
  match place with
  | Pfield(base, fid, default_ty) ->
      let base_ty = type_of_place base in
      (match base_ty with
       | Rusttypes.Tstruct(_, struct_id) ->
           let struct_name = extern_atom struct_id in
           (try
             let fields = Hashtbl.find struct_field_table struct_name in
             snd (List.find (fun (name, _) -> name = extern_atom fid) fields)
           with Not_found -> default_ty)
       | _ -> default_ty)
  | _ -> type_of_place place

and is_null_pexpr pe =
  match pe with
  | Econst_int (n, _) ->
      Int32.compare (camlint_of_coqint n) 0l = 0
  | Econst_long (n, _) ->
      Int64.compare (camlint64_of_coqint n) 0L = 0
  | Eas (inner, _) ->
      is_null_pexpr inner
  | _ -> false

and is_null_ptr_expr e =
  match e with
  | Epure pe -> is_null_pexpr pe
  | _ -> false

let is_string_literal_place place =
  match place with
  | Plocal(id, _) ->
      let name = extern_atom id in
      String.length name >= 12 && String.sub name 0 12 = "__stringlit_"
  | _ -> false

let rec array_place_from_pexpr pe =
  match pe with
  | Eas(inner, _) -> array_place_from_pexpr inner
  | Eplace(place, ty) when is_array_type ty || is_string_literal_place place -> Some place
  | Eref(_, _, place, _) when is_array_type (type_of_place place) || is_string_literal_place place -> Some place
  | _ -> None

and array_place_from_expr = function
  | Epure pe -> array_place_from_pexpr pe
  | _ -> None

and integer_pexpr_from_pexpr pe =
  match pe with
  | Eas(inner, _) -> integer_pexpr_from_pexpr inner
  | Eplace(place, ty) when is_integer_type ty -> Some pe
  | Eref(_, _, place, _) ->
      let place_ty = type_of_place place in
      if is_integer_type place_ty then
        Some (Eplace(place, place_ty))
      else
        None
  | _ ->
      let pe_ty = type_of_pexpr pe in
      if is_integer_type pe_ty then Some pe else None

and integer_pexpr_from_expr = function
  | Emoveplace(place, ty) when is_integer_type ty -> Some (Eplace(place, ty))
  | Epure pe -> integer_pexpr_from_pexpr pe
  | _ -> None

and is_zero_integer_expr expr =
  match integer_pexpr_from_expr expr with
  | Some pe -> is_null_pexpr pe
  | None -> false

and place_from_ptr_arg expr =
  match expr with
  | Epure (Eref(_, _, place, _)) -> Some place
  | Epure (Eplace(place, _)) -> Some place
  | Emoveplace(place, _) -> Some place
  | _ -> None

and print_place out (p: place) =
  match p with
  | Plocal(id, _) ->
      fprintf out "%s" (lookup_ident_name id)
  | Pderef(Pparenthesize(_, _, Ebinop(Oadd, base, index, _)), _) ->
      let base_ty = type_of_pexpr base in
      if is_declared_ptr_type base_ty then
        fprintf out "%a.load((%a) as usize)" pexpr (0, base) pexpr (0, index)
      else
        (* 关键修复 #2: 在索引表达式后添加 'as usize' *)
        fprintf out "%a[(%a) as usize]" pexpr (0, base) pexpr (0, index)
  | Pderef(p', _) ->
      if is_ptr_place p' then
        fprintf out "(*((%a).as_mut_ptr()))" print_place p'
      else
        fprintf out "(*%a)" print_place p'
  | Pfield(p', fid, _) ->
      fprintf out "%a.%s" print_place p' (extern_atom fid)
  | Pdowncast(p',fid, _) ->
      fprintf out "(%a as %s)" print_place p' (extern_atom fid)
  | Pparenthesize(_, _, ll) ->
      fprintf out "(%a)" pexpr (0, ll)
  | ParrayIndex(p_base, p_index, _) ->
      let base_ty = resolved_place_type p_base in
      if is_declared_ptr_type base_ty then
        (match pointed_type base_ty with
         | Some elem_ty when is_array_type elem_ty ->
             fprintf out "%a.row((%s) as usize)" print_place p_base (lookup_ident_name p_index)
         | _ ->
             fprintf out "%a.load((%s) as usize)" print_place p_base (lookup_ident_name p_index))
      else
        fprintf out "%a[(%s) as usize]" print_place p_base (lookup_ident_name p_index)
  | Ppair (p1, p2) -> (* 添加这个 case *)
    fprintf out "(%a, %a)" print_place p1 print_place p2

and print_pointer_operand out pe =
  match pe with
  | Ederef (Ebinop (Oadd, base, index, _), _) ->
      (* When dereferencing a pointer-to-array, the result is an array lvalue in C,
         which decays to a pointer to its first element in pointer arithmetic.
         Printing it as `base.load(index)` copies the whole row and then taking
         `.offset(...)` would operate on the copy (writes won't reach the caller).
         Use `Ptr<[T;N]>::row` to get a pointer into the real row. *)
      let base_ty = type_of_pexpr base in
      if is_declared_ptr_type base_ty then
        (match pointed_type base_ty with
         | Some arr_ty when is_array_type arr_ty ->
             fprintf out "%a.row((%a) as usize)" pexpr (0, base) pexpr (0, index)
         | _ ->
             pexpr out (0, pe))
      else
        pexpr out (0, pe)
  | Eplace (ParrayIndex (base_place, index_id, _), _) ->
      let base_ty = resolved_place_type base_place in
      if is_declared_ptr_type base_ty then
        (match pointed_type base_ty with
         | Some arr_ty when is_array_type arr_ty ->
             fprintf out "%a.row((%s) as usize)" print_place base_place (lookup_ident_name index_id)
         | _ ->
             pexpr out (0, pe))
      else
        pexpr out (0, pe)
  | Eplace (place, ty) when is_array_type ty ->
      fprintf out "Ptr::from_ref(&mut %a[..])" print_place place
  | _ ->
      pexpr out (0, pe)

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
  | Eplace (ParrayIndex(base, idx, _), _) ->
      let base_ty = resolved_place_type base in
      if is_declared_ptr_type base_ty then
        (match pointed_type base_ty with
         | Some elem_ty when is_array_type elem_ty ->
             fprintf p "%a.row((%s) as usize)" print_place base (lookup_ident_name idx)
         | _ ->
             fprintf p "%a.load((%s) as usize)" print_place base (lookup_ident_name idx))
      else
        fprintf p "%a[(%s) as usize]" print_place base (lookup_ident_name idx)
  | Eplace (place, _) ->
      (match extract_pointer_field_place place with
       | Some (ptr_base, fid, _) ->
           fprintf p "(%a.load(0)).%s" print_place ptr_base (extern_atom fid)
       | None ->
           let ty = type_of_place place in
           let is_extern_ptr_global =
             match place with
             | Plocal(id, pty) ->
                 let nm = lookup_ident_name id in
                 StringSet.mem nm !extern_pointer_globals && is_pointer_type pty
             | _ -> false
           in
           if is_extern_ptr_global then
             (match pointed_type ty with
              | Some elem_ty ->
                  fprintf p "unsafe { Ptr::from_raw_parts((%a) as *mut %s, usize::MAX) }"
                    print_place place
                    (name_rust_type elem_ty)
              | None ->
                  (* Shouldn't happen for pointer-typed globals, but keep a fallback. *)
                  fprintf p "%a" print_place place)
           else if is_slice_type ty then
             fprintf p "(%a.clone())" print_place place
           else
             fprintf p "%a" print_place place)
  | Ederef(Ebinop(Oadd, base, index, _), _) ->
      fprintf p "%a.load((%a) as usize)" pexpr (0, base) pexpr (0, index)
  | Ederef(pe, ty) ->
      let pe_ty = type_of_pexpr pe in
      (match pointed_type pe_ty with
       | Some _ ->
           fprintf p "%a.load(0)" pexpr (0, pe)
       | _ ->
           fprintf p "*(%a)" pexpr (prec', pe))
  | Eunit ->  fprintf p "tt"
  (* ... pexpr 函数的其余部分保持不变 ... *)
  | Econst_int(n, ty) ->
      (match ty with
       | Rusttypes.Tslice(_, _, _) ->
           if Int32.compare (camlint_of_coqint n) 0l = 0 then
             fprintf p "Ptr::null()"
           else
             fprintf p "%ld" (camlint_of_coqint n)
       | Rusttypes.Tint(Ctypes.IBool, _) ->
           if Int32.compare (camlint_of_coqint n) 0l = 0 then
             fprintf p "false"
           else
             fprintf p "true"
       | Rusttypes.Tint(I32, Unsigned) ->
           fprintf p "%lu_u32" (camlint_of_coqint n)
       | _ ->
           fprintf p "%ld" (camlint_of_coqint n))
  | Econst_float(f, _) ->
    print_rust_float p (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
    fprintf p "%.18g_f32" (camlfloat_of_coqfloat32 f)
  | Econst_long(n, ty) ->
      (match ty with
       | Rusttypes.Tslice(_, _, _) ->
           if Int64.compare (camlint64_of_coqint n) 0L = 0 then
             fprintf p "Ptr::null()"
           else
             fprintf p "%Ldi64" (camlint64_of_coqint n)
       | Rusttypes.Tlong(Unsigned) ->
           fprintf p "(%Lu as usize)" (camlint64_of_coqint n)
       | _ ->
           fprintf p "%Ldi64" (camlint64_of_coqint n))
  | Eglobal(id, _) ->
    fprintf p "%s" (extern_atom id)
  | Eunop(Oabsfloat, a1, _) ->
    fprintf p "__builtin_fabs(%a)" pexpr (2, a1)
  | Eunop(Onotbool, a1, ty) ->
    (* C 的逻辑非 `!x`：把 x 当作布尔值（0/NULL 为 false），结果是 0/1（通常是 int）。
       Rust 的 `!` 在整数上是按位取反，会导致 `!0 == -1`，从而把 `(!x) != 0` 这类模式变成恒真，
       进而引发死循环/越界（例如 chomp 的 get_value/next_data）。这里统一改为零值比较。 *)
    let a1_ty = type_of_pexpr a1 in
    let want_bool = is_bool_type ty in
    let ty_name = name_rust_type ty in
    let print_cond fmt =
      if is_declared_ptr_type a1_ty || is_pointer_type a1_ty then
        fprintf fmt "(%a).is_null()" pexpr (0, a1)
      else if is_bool_type a1_ty then
        fprintf fmt "!(%a)" pexpr (prec', a1)
      else if is_float_type a1_ty then
        fprintf fmt "((%a) == 0.0)" pexpr (0, a1)
      else
        fprintf fmt "((%a) == 0)" pexpr (0, a1)
    in
    if want_bool then
      fprintf p "%t" print_cond
    else
      fprintf p "((%t) as %s)" print_cond ty_name
  | Eunop(op, a1, _) ->
    fprintf p "%s%a" (name_unop op) pexpr (prec', a1)
  | Ebinop(Oadd, a1, a2, ty) when is_pointer_type ty ->
      fprintf p "%a.offset((%a) as isize)" print_pointer_operand a1 pexpr (0, a2)
  | Ebinop(Oadd, a1, a2, _) when is_pointer_type (type_of_pexpr a1) && is_integer_type (type_of_pexpr a2) ->
      fprintf p "%a.offset((%a) as isize)" print_pointer_operand a1 pexpr (0, a2)
  | Ebinop(Oadd, a1, a2, _) when is_pointer_type (type_of_pexpr a2) && is_integer_type (type_of_pexpr a1) ->
      fprintf p "%a.offset((%a) as isize)" print_pointer_operand a2 pexpr (0, a1)
  | Ebinop(Osub, a1, a2, ty) when is_pointer_type ty ->
      fprintf p "%a.offset(-((%a) as isize))" print_pointer_operand a1 pexpr (0, a2)
  | Ebinop(Osub, a1, a2, _) when is_pointer_type (type_of_pexpr a1) && is_integer_type (type_of_pexpr a2) ->
      fprintf p "%a.offset(-((%a) as isize))" print_pointer_operand a1 pexpr (0, a2)
  | Ebinop(op, a1, a2, ty) ->
    (* Special-case: slice compared with NULL-like slice cast (0 as &mut [..]) *)
    let is_slice_type t = match t with Rusttypes.Tslice(_, _, _) -> true | _ -> false in
    let is_zero_slice_cast_expr pe =
      match pe with
      | Eas (Econst_int(n, _), Rusttypes.Tslice(_, _, _)) -> Int32.compare (camlint_of_coqint n) 0l = 0
      | _ -> false
    in
    (match op with
     | Cop.Oeq | Cop.One ->
         let ty1 = type_of_pexpr a1 in
         let ty2 = type_of_pexpr a2 in
         if is_zero_slice_cast_expr a1 && is_slice_type ty2 then begin
           (match op with
            | Cop.Oeq -> fprintf p "%a.is_null()" pexpr (0, a2)
            | Cop.One -> fprintf p "!(%a).is_null()" pexpr (0, a2)
            | _ -> ());
           ()
         end else if is_zero_slice_cast_expr a2 && is_slice_type ty1 then begin
           (match op with
            | Cop.Oeq -> fprintf p "%a.is_null()" pexpr (0, a1)
            | Cop.One -> fprintf p "!(%a).is_null()" pexpr (0, a1)
            | _ -> ());
           ()
         end else begin
           ()
         end
     | _ -> ());
    (* If the special-case above printed, the rest must be skipped.
       We detect this by re-checking and returning early. *)
    let handled_null_slice_cmp =
      (match op with
       | Cop.Oeq | Cop.One -> is_zero_slice_cast_expr a1 && is_slice_type (type_of_pexpr a2)
                             || is_zero_slice_cast_expr a2 && is_slice_type (type_of_pexpr a1)
       | _ -> false)
    in
    if handled_null_slice_cmp then () else
    (* Check if this is a float operation - if so, convert int literals to float *)
    let is_float_op = is_float_type ty || is_float_type (type_of_pexpr a1) || is_float_type (type_of_pexpr a2) in
    (* Check if this is a comparison with mixed signed/unsigned types *)
    let is_comparison_op = match op with
      | Cop.Olt | Cop.Ogt | Cop.Ole | Cop.Oge | Cop.Oeq | Cop.One -> true
      | _ -> false
    in
    let ty1 = type_of_pexpr a1 in
    let ty2 = type_of_pexpr a2 in
    let convert_left_to_u64 =
      if is_u64_type ty2 && is_integer_type ty1 && not (is_u64_type ty1)
      then Some "u64" else None
    in
    let convert_right_to_u64 =
      if is_u64_type ty1 && is_integer_type ty2 && not (is_u64_type ty2)
      then Some "u64" else None
    in
    let convert_left_to_i64 =
      if is_i64_type ty2 && is_integer_type ty1 && not (is_i64_type ty1)
      then Some "i64" else None
    in
    let convert_right_to_i64 =
      if is_i64_type ty1 && is_integer_type ty2 && not (is_i64_type ty2)
      then Some "i64" else None
    in
    let needs_type_conversion = is_comparison_op && (
      match ty1, ty2 with
      (* u32 compared with i32 - convert i32 to u32 *)
      | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned), Rusttypes.Tint(Ctypes.I32, Ctypes.Signed)
      | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed), Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) -> true
      | _ -> false
    ) in
    let result_is_int = is_integer_type ty && not (is_bool_type ty) in
    (* 对按位与/或/异或、移位等整型运算，统一把参与表达式提升到目标整型，
       避免 u8 与 i32 混用产生的 E0277/E0308（如 get64le 中的按位拼接）。 *)
    let needs_int_cast =
      result_is_int &&
      (match op with
       | Cop.Oadd | Cop.Osub | Cop.Omul | Cop.Odiv | Cop.Omod
       | Cop.Oshl | Cop.Oshr | Cop.Oand | Cop.Oor | Cop.Oxor -> true
       | _ -> false)
    in
    (* 选择一个统一的整型目标：优先保持目标类型；若目标是 bool 或非整型，
       则根据参与者选择 u64>i64>u32>i32 之一，避免 u8 与 i32 等组合。 *)
    let int_target_name =
      if is_integer_type ty && not (is_bool_type ty) then name_rust_type ty else
      if is_u64_type ty1 || is_u64_type ty2 then "u64" else
      if is_i64_type ty1 || is_i64_type ty2 then "i64" else
      if is_u32_type ty1 || is_u32_type ty2 then "u32" else
      if is_i32_type ty1 || is_i32_type ty2 then "i32" else
      (* 默认提升到 u64 保守处理按位操作 *)
      "u64"
    in
    (* Determine target float type name *)
    let float_type_name = match ty with
      | Rusttypes.Tfloat(Ctypes.F32) -> "f32"
      | Rusttypes.Tfloat(Ctypes.F64) -> "f64"
      | _ -> "f64"  (* default to f64 *)
    in
    let print_a1_base fmt () =
      match a1 with
      | Econst_int(n, _) when is_float_op ->
          fprintf fmt "%ld.0" (camlint_of_coqint n)
      | _ ->
          if needs_type_conversion then
            match ty1, ty2 with
            | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed), Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) ->
                fprintf fmt "(%a as u32)" pexpr (0, a1)
            | _ -> pexpr fmt (prec1, a1)
          else if is_float_op && is_integer_type ty1 then
            fprintf fmt "((%a) as %s)" pexpr (0, a1) float_type_name
          else if needs_int_cast then
            fprintf fmt "((%a) as %s)" pexpr (0, a1) int_target_name
          else
            pexpr fmt (prec1, a1)
    in
    let print_a1 fmt =
      match convert_left_to_u64 with
      | Some target ->
          fprintf fmt "((%a) as %s)" print_a1_base () target
      | None ->
          (match convert_left_to_i64 with
           | Some target ->
               fprintf fmt "((%a) as %s)" print_a1_base () target
           | None ->
               print_a1_base fmt ())
    in
    print_a1 p;
    fprintf p "@ %s " (name_binop op);
    let print_a2_base fmt () =
      match a2 with
      | Econst_int(n, _) when is_float_op ->
          fprintf fmt "%ld.0" (camlint_of_coqint n)
      | _ ->
          if needs_type_conversion then
            match ty1, ty2 with
            | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned), Rusttypes.Tint(Ctypes.I32, Ctypes.Signed) ->
                fprintf fmt "(%a as u32)" pexpr (0, a2)
            | _ -> pexpr fmt (prec2, a2)
          else if is_float_op && is_integer_type ty2 then
            fprintf fmt "((%a) as %s)" pexpr (0, a2) float_type_name
          else if needs_int_cast then
            fprintf fmt "((%a) as %s)" pexpr (0, a2) int_target_name
          else
            pexpr fmt (prec2, a2)
    in
    let print_a2 fmt =
      match convert_right_to_u64 with
      | Some target ->
          fprintf fmt "((%a) as %s)" print_a2_base () target
      | None ->
          (match convert_right_to_i64 with
           | Some target ->
               fprintf fmt "((%a) as %s)" print_a2_base () target
           | None ->
               print_a2_base fmt ())
    in
    print_a2 p
  | Ecktag(v, fid) ->
    fprintf p "%s(%a, %s)" "cktag" print_place v (extern_atom fid)
  | Eref(_, mut, v, ty) ->
    let place_ty = type_of_place v in
    (match ty with
     | Rusttypes.Tslice(_, _, origin) ->
         (match origin with
          | Rusttypes.PtrBorrowed ->
              let prefix = string_of_mut mut in
              (match place_ty with
               | Rusttypes.Tarray(_, _, _) ->
                   fprintf p "Ptr::from_ref(&%s%a)" prefix print_place v
               | _ ->
                   fprintf p "Ptr::from_mut(&%s%a)" prefix print_place v)
          | _ ->
              fprintf p "&%s%a" (string_of_mut mut) print_place v)
     | _ ->
         fprintf p "&%s%a" (string_of_mut mut) print_place v)
  | Eas(pe, ty) ->
      let rec is_zero_pointer_literal pe =
        match pe with
        | Econst_int (n, _) -> Int32.compare (camlint_of_coqint n) 0l = 0
        | Econst_long (n, _) -> Int64.compare (camlint64_of_coqint n) 0L = 0
        | Eas(inner, _) -> is_zero_pointer_literal inner
        | _ -> false
      in
      let ty_is_slice =
        match ty with
        | Rusttypes.Tslice(_, _, _) -> true
        | _ -> false
      in
      let ty_is_pointer = is_pointer_type ty in
      let ty_is_int = is_integer_type ty in
      let ty_is_fn = is_function_type ty in
      let ty_name = name_rust_type ty in
      if ty_is_slice && is_zero_pointer_literal pe then
        let elem_ty =
          match pointed_type ty with
          | Some e -> name_rust_type e
          | None -> "std::ffi::c_void"
        in
        fprintf p "Ptr::<%s>::null()" elem_ty
      else if ty_is_pointer && is_zero_pointer_literal pe then
        let elem_ty =
          match pointed_type ty with
          | Some e -> name_rust_type e
          | None -> "std::ffi::c_void"
        in
        fprintf p "Ptr::<%s>::null()" elem_ty
      else
      (* 函数类型之间的转换，统一使用 Rust 的 `as`，避免调用 Ptr::cast *)
      if (String.length ty_name >= 6 && String.sub ty_name 0 6 = "extern") then
        fprintf p "(%a as %s)" pexpr (prec', pe) ty_name
      else
      let pe_ty = type_of_pexpr pe in
      let pe_is_fn = is_function_type pe_ty in
      if ty_is_fn || pe_is_fn then
        (* 函数类型之间的转换用 as，不要使用 Ptr::cast *)
        fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty)
      else
      (match ty, pe_ty with
       | Rusttypes.Tslice(_, elem_ty, _), Rusttypes.Tslice(_, _, _) ->
           fprintf p "unsafe { (%a).cast::<%s>() }" pexpr (0, pe) (name_rust_type elem_ty)
       | _, _ when is_bool_type ty && is_pointer_type pe_ty ->
           fprintf p "!((%a).is_null())" pexpr (0, pe)
       | _, _ when ty_is_int && is_pointer_type pe_ty ->
           fprintf p "((%a).as_ptr() as isize as %s)" pexpr (0, pe) (name_rust_type ty)
       | _ ->
      (* Check if this is casting a comparison or bool-valued expression to bool - skip it *)
      let rec is_bool_valued_expr pe = 
        match pe with
        | Ebinop((Oeq | One | Olt | Ogt | Ole | Oge), _, _, _) -> true
        | Ebinop((Oand | Oor), _, _, ty) ->
            (* In CompCert, Oand/Oor are bitwise ops. Treat them as bool-valued
               only if the IR result type is already bool. *)
            (match ty with
             | Rusttypes.Tint(Ctypes.IBool, _) -> true
             | _ -> false)
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
        | Rusttypes.Tslice(_, _, _) -> true
        | _ -> false
      in
      let array_ref = array_place_from_pexpr pe in
      if is_casting_to_bool && is_bool_valued_expr pe then
        (* Skip redundant cast to bool since expression already returns bool *)
        pexpr p (prec', pe)
      else if is_casting_to_bool && is_integer_type pe_ty then
        fprintf p "((%a) != 0)" pexpr (prec', pe)
      else if is_casting_to_slice then
        (* When casting to slice, check if we need to add &mut *)
        (* Don't add &mut if the expression is already a reference (Eref) *)
        let is_already_ref = match pe with
          | Eref(_, _, _, _) -> true
          | _ -> false
        in
        (match array_ref with
         | Some place ->
             fprintf p "Ptr::from_ref(&mut %a[..])" print_place place
         | None ->
             if not is_already_ref then
               (* Need to add &mut or & for the cast *)
               (match ty with
                | Rusttypes.Tslice(Rusttypes.Mutable, _, _) ->
                    fprintf p "(&mut %a as %s)" pexpr (prec', pe) (name_rust_type ty)
                | Rusttypes.Tslice(Rusttypes.Immutable, _, _) ->
                    fprintf p "(&%a as %s)" pexpr (prec', pe) (name_rust_type ty)
               | _ ->
                   fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty))
             else
               (* Already has &mut, just cast *)
               fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty))
      else if ty_is_pointer then
        (match array_ref with
         | Some place ->
             fprintf p "Ptr::from_ref(&mut %a[..])" print_place place
         | None ->
            (match pe with
              | Eref(_, mut, place, _) ->
                  let place_ty = type_of_place place in
                  if is_integer_type place_ty then begin
                    let elem_ty =
                      match pointed_type ty with
                      | Some e -> name_rust_type e
                      | None -> "std::ffi::c_void"
                    in
                    fprintf p
                      "unsafe { Ptr::from_raw_parts(((%a) as isize) as *mut %s, usize::MAX) }"
                      pexpr (0, Eplace(place, place_ty))
                      elem_ty
                  end else begin
                    let prefix = string_of_mut mut in
                    (match place_ty with
                     | Rusttypes.Tarray(_, _, _) ->
                         fprintf p "Ptr::from_ref(&%s%a)" prefix print_place place
                     | _ ->
                         fprintf p "Ptr::from_mut(&%s%a)" prefix print_place place)
                  end
              | _ when is_integer_type pe_ty ->
                  let elem_ty =
                    match pointed_type ty with
                    | Some e -> name_rust_type e
                    | None -> "std::ffi::c_void"
                  in
                  fprintf p "unsafe { Ptr::from_raw_parts(((%a) as isize) as *mut %s, usize::MAX) }"
                    pexpr (0, pe)
                    elem_ty
              | _ ->
                  fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty)))
      else
        fprintf p "(%a as %s)" pexpr (prec', pe) (name_rust_type ty)
      )
  | Esizeof(ty1, ty2) ->
      let target_name = name_rust_type ty2 in
      fprintf p "(::std::mem::size_of::<%s>() as %s)"
        (name_rust_type ty1)
        target_name
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

type malloc_info = {
  malloc_elem_ty : Rusttypes.coq_type;
  malloc_count : Rustlight.pexpr option;
}

let pending_malloc_temps : (string, malloc_info) Hashtbl.t = Hashtbl.create 17

let is_digit c = c >= '0' && c <= '9'

let is_gensym_temp name =
  let len = String.length name in
  len > 1 && name.[0] = '_' &&
  let rec loop i =
    if i = len then true else
    if is_digit name.[i] then loop (i + 1) else false
  in loop 1

let place_ident = function
  | Plocal(id, _) -> Some (lookup_ident_name id)
  | _ -> None

let rec temp_name_from_pexpr pe =
  match pe with
  | Eplace(Plocal(id, _), _) -> Some (lookup_ident_name id)
  | Eas(inner, _) -> temp_name_from_pexpr inner
  | _ -> None

let temp_name_from_expr e =
  match e with
  | Epure pe -> temp_name_from_pexpr pe
  | _ -> None

let print_ptr_argument p _ arg =
  match arg with
  | Epure (Eref(_, mut, place, _)) ->
      let place_ty = type_of_place place in
      let prefix = string_of_mut mut in
      (match place_ty with
       | Rusttypes.Tarray(_, _, _) ->
           fprintf p "Ptr::from_ref(&%s%a)" prefix print_place place
       | _ ->
           fprintf p "Ptr::from_mut(&%s%a)" prefix print_place place)
  | Epure (Eplace(place, ty)) ->
      (match ty with
       | Rusttypes.Tarray(_, _, _) ->
           fprintf p "Ptr::from_ref(&mut %a)" print_place place
       | _ ->
           expr p (2, arg))
  | _ ->
      expr p (2, arg)

(* type_of_pexpr already defined above *)

let type_of_expr (e : expr) : Rusttypes.coq_type =
  match e with
  | Emoveplace (_, ty) -> ty
  | Epure p -> type_of_pexpr p

let print_store_expr (target_ty: Rusttypes.coq_type) p (expr: expr) =
  match target_ty, expr with
  | Rusttypes.Tfloat _, Epure (Econst_int (n, _)) ->
      fprintf p "(%ld as %s)" (camlint_of_coqint n) (name_rust_type target_ty)
  | Rusttypes.Tfloat _, Epure (Econst_long (n, _)) ->
      fprintf p "(%Ld as %s)" (camlint64_of_coqint n) (name_rust_type target_ty)
  | Rusttypes.Tfloat _, _ when is_integer_type (type_of_expr expr) ->
      fprintf p "((%a) as %s)" print_expr expr (name_rust_type target_ty)
  | ty, _ when is_integer_type ty ->
      let ty_name = name_rust_type ty in
      let expr_ty = type_of_expr expr in
      if is_pointer_type expr_ty then
        fprintf p "((%a).as_ptr() as isize as %s)" print_expr expr ty_name
      else
        fprintf p "((%a) as %s)" print_expr expr ty_name
  | _ ->
      print_expr p expr

let print_pointer_assignment_value place_ty p (expr: expr) =
  match integer_pexpr_from_expr expr, pointed_type place_ty with
  | Some int_pe, Some elem_ty when is_pointer_type place_ty ->
      fprintf p "unsafe { Ptr::from_raw_parts(((%a) as isize) as *mut %s, usize::MAX) }"
        pexpr (0, int_pe)
        (name_rust_type elem_ty)
  | _ ->
      (match array_place_from_expr expr with
       | Some place ->
           fprintf p "Ptr::from_ref(&mut %a[..])" print_place place
        | None ->
            let expr_ty = type_of_expr expr in
           let dest_ty_name = name_rust_type place_ty in
           let dest_is_fn_name =
             String.length dest_ty_name >= 6 && String.sub dest_ty_name 0 6 = "extern"
           in
           let dest_points_to_fn =
             match pointed_type place_ty with
             | Some elem_ty -> is_function_type elem_ty
             | None -> false
           in
           if is_pointer_type place_ty && is_pointer_type expr_ty then
             if dest_is_fn_name || dest_points_to_fn then
               fprintf p "(%a as %s)" print_expr expr dest_ty_name
             else
               (match pointed_type place_ty with
                | Some elem_ty ->
                    let needs_cast =
                      match pointed_type expr_ty with
                      | Some src_elem ->
                          name_rust_type src_elem <> name_rust_type elem_ty
                      | None -> true
                    in
                    if needs_cast then
                      fprintf p "unsafe { (%a).cast::<%s>() }"
                        print_expr expr
                        (name_rust_type elem_ty)
                    else
                      print_expr p expr
                | None ->
                    print_expr p expr)
           else
             print_expr p expr)

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
      let expr_ty = type_of_expr r in
      (match ty with
       | Rusttypes.Tslice(_, target_elem, origin) ->
           let print_base fmt = print_ptr_argument fmt origin r in
           if is_function_type target_elem then
             (* 函数指针不是 Ptr<T>，不要打印 Ptr::cast；直接依赖 Rust 的函数项到函数指针强制转换 *)
             fprintf p "%t" print_base
           else
             fprintf p "unsafe { (%t).cast::<%s>() }"
               print_base
               (name_rust_type target_elem)
       | _ ->
           (* Check if we MUST add .as_mut_ptr() for C FFI compatibility *)
           let needs_ptr_conversion = is_c_function && (
             match ty, expr_ty with
             | Rusttypes.Traw_pointer(_, _), Rusttypes.Tarray(_, _, _) -> true
             | Rusttypes.Traw_pointer(_, _), Rusttypes.Tslice(_, _, _) -> true
             | _ -> false
           ) in
           if needs_ptr_conversion then begin
             let ptr_accessor =
               match ty with
               | Rusttypes.Traw_pointer(Rusttypes.Coq_const, _) -> ".as_ptr()"
               | _ -> ".as_mut_ptr()"
             in
             let expr_contains_cast = match r with
               | Epure (Eas(_, _)) -> true
               | _ -> false
             in
             let needs_cvoid_cast = match ty with
               | Rusttypes.Traw_pointer(_, Rusttypes.Tvoid) -> true
               | Rusttypes.Tslice(_, Rusttypes.Tvoid, _) -> true
               | _ -> false
             in
             if expr_contains_cast then begin
               if needs_cvoid_cast then
                 fprintf p "(%a)%s as %s" expr (2, r) ptr_accessor (PrintRustsyntax.name_rust_type_ffi ty)
               else
                 fprintf p "(%a)%s" expr (2, r) ptr_accessor
             end else begin
               expr p (2, r);
               if needs_cvoid_cast then
                 fprintf p "%s as %s" ptr_accessor (PrintRustsyntax.name_rust_type_ffi ty)
               else
                 fprintf p "%s" ptr_accessor
             end
           end else begin
             let needs_ref = not is_c_function && (
               match ty, expr_ty with
               | Rusttypes.Tslice(Rusttypes.Mutable, _, _), Rusttypes.Tarray(_, _, _) -> true
               | Rusttypes.Tslice(Rusttypes.Immutable, _, _), Rusttypes.Tarray(_, _, _) -> true
               | _ -> false
             ) in
             if needs_ref then begin
               match ty with
               | Rusttypes.Tslice(Rusttypes.Mutable, _, _) ->
                   fprintf p "&mut ";
                   expr p (2, r)
               | Rusttypes.Tslice(Rusttypes.Immutable, _, _) ->
                   fprintf p "&";
                   expr p (2, r)
               | _ -> expr p (2, r)
             end else begin
               match ty with
               | Rusttypes.Tunit ->
                   expr p (2, r)
               | Rusttypes.Tslice(_, _, _) when not is_c_function ->
                   expr p (2, r)
               | _ ->
                   fprintf p "(%a) as %s" expr (2, r) (name_rust_decl "" ty)
             end
           end);
      print_expr_list_with_type p (false, rl, tyl, is_c_function)

  | r :: rl, [] ->
      (* No more parameter types - this happens with variadic functions like printf *)
      if not first then fprintf p ",@ ";
      (* For C variadic functions, check if we MUST convert arrays/slices to pointers *)
      if is_c_function then
        let expr_ty = type_of_expr r in
        (match r with
         | Epure (Eref (_, _, _, _)) ->
             (* 对引用类型参数：不要追加 .as_mut_ptr() 或指针 cast，保持原样 *)
             expr p (2, r)
         | _ ->
             (match expr_ty with
              | Rusttypes.Tslice(mutk, _, _) ->
                  expr p (2, r);
                  (match mutk with
                   | Rusttypes.Immutable -> fprintf p ".as_ptr()"
                   | Rusttypes.Mutable -> fprintf p ".as_mut_ptr()")
              | Rusttypes.Tarray(_, _, _) ->
                  (* Arrays and slices MUST be converted to raw pointers for C variadic functions *)
                  expr p (2, r);
                  fprintf p ".as_mut_ptr()"
              | Rusttypes.Tfloat(Ctypes.F32) ->
                  fprintf p "((%a) as f64)" expr (2, r)
              | _ ->
                  expr p (2, r)))
      else
        expr p (2, r);
      print_expr_list_with_type p (false, rl, [], is_c_function)
  | _ ->
      (* error *)
      ()

let rec typelist_to_list = function
  | Rusttypes.Tnil -> []
  | Rusttypes.Tcons(ty, rest) -> ty :: typelist_to_list rest

let parse_malloc_param param =
  let make_info ty count =
    Some { malloc_elem_ty = ty; malloc_count = count }
  in
  match param with
  | Epure (Ebinop(Omul, pe1, pe2, _)) ->
      let try_pair left right =
        match left with
        | Esizeof(ty, _) -> make_info ty (Some right)
        | _ -> None
      in
      (match try_pair pe1 pe2 with
       | Some info -> Some info
       | None -> try_pair pe2 pe1)
  | Epure (Esizeof(ty, _)) ->
      make_info ty None
  | _ ->
      None

let rec sizeof_type_from_pexpr pe =
  match pe with
  | Esizeof (ty, _) -> Some ty
  | Eas (inner, _) -> sizeof_type_from_pexpr inner
  | _ -> None

let parse_calloc_params nmemb size =
  match nmemb, size with
  | Epure nmemb_pe, Epure size_pe ->
      (match sizeof_type_from_pexpr size_pe with
       | Some ty -> Some { malloc_elem_ty = ty; malloc_count = Some nmemb_pe }
       | None -> None)
  | _ -> None

let rec type_contains_declared_ptr ty =
  match ty with
  | Rusttypes.Tslice _ -> true
  | Rusttypes.Tarray(_, elem, _) -> type_contains_declared_ptr elem
  | Rusttypes.Treference(_, _, elem) -> type_contains_declared_ptr elem
  | Rusttypes.Tstruct(_, struct_id) ->
      let struct_name = extern_atom struct_id in
      (try
         let fields = Hashtbl.find struct_field_table struct_name in
         List.exists (fun (_, fty) -> type_contains_declared_ptr fty) fields
       with Not_found -> false)
  | _ -> false

let get_callee_name (e: expr) : string option =
  match e with
  | Epure (Eplace(Plocal(id, _), _)) -> Some (String.lowercase_ascii (lookup_ident_name id))
  | Epure (Eglobal(id, _))           -> Some (String.lowercase_ascii (extern_atom id))
  | _                                -> None

(* Helper to check if pexpr is a comparison that returns bool *)
let rec is_comparison_pexpr pe =
  match pe with
  | Ebinop((Oeq | One | Olt | Ogt | Ole | Oge), _, _, _) -> true
  | Ebinop((Oand | Oor), _, _, ty) ->
      (* Oand/Oor are bitwise ops. They are only bool-producing if the IR
         explicitly assigns them a bool type. *)
      (match ty with
       | Rusttypes.Tint(Ctypes.IBool, _) -> true
       | _ -> false)
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
let is_void_pointer_place p =
  match type_of_place p with
  | Rusttypes.Tslice(_, Rusttypes.Tvoid, _) -> true
  | _ -> false

let register_malloc_temp place info =
  match place_ident place with
  | Some name when is_gensym_temp name ->
      Hashtbl.replace pending_malloc_temps name info; true
  | _ -> false

let take_malloc_temp name =
  match Hashtbl.find_opt pending_malloc_temps name with
  | None -> None
  | Some info ->
      Hashtbl.remove pending_malloc_temps name;
      Some info

let print_malloc_assignment p dest info =
  let type_name = name_rust_type info.malloc_elem_ty in
  let dest_ty = type_of_place dest in
  let dest_cast_target =
    match pointed_type dest_ty with
    | Some elem_ty ->
        let dest_name = name_rust_type elem_ty in
        if dest_name <> type_name then Some dest_name else None
    | None -> None
  in
  let print_alloc fmt count_printer =
    match dest_cast_target with
    | Some target ->
        fprintf fmt "unsafe { Ptr::<%s>::alloc(%t).cast::<%s>() }"
          type_name count_printer target
    | None ->
        fprintf fmt "Ptr::<%s>::alloc(%t)" type_name count_printer
  in
  match info.malloc_count with
  | Some count_expr ->
      fprintf p "@[<hv 2>%a = %t;@]"
        print_place dest
        (fun fmt -> print_alloc fmt (fun fmt -> fprintf fmt "(%a) as usize" pexpr (0, count_expr)))
  | None ->
      fprintf p "@[<hv 2>%a = %t;@]"
        print_place dest
        (fun fmt -> print_alloc fmt (fun fmt -> fprintf fmt "1"))

let print_malloc_value_for_ty dest_ty p info =
  let type_name = name_rust_type info.malloc_elem_ty in
  let dest_cast_target =
    match pointed_type dest_ty with
    | Some elem_ty ->
        let dest_name = name_rust_type elem_ty in
        if dest_name <> type_name then Some dest_name else None
    | None -> None
  in
  let print_alloc fmt count_printer =
    match dest_cast_target with
    | Some target ->
        fprintf fmt "unsafe { Ptr::<%s>::alloc(%t).cast::<%s>() }"
          type_name count_printer target
    | None ->
        fprintf fmt "Ptr::<%s>::alloc(%t)" type_name count_printer
  in
  match info.malloc_count with
  | Some count_expr ->
      print_alloc p (fun fmt -> fprintf fmt "(%a) as usize" pexpr (0, count_expr))
  | None ->
      print_alloc p (fun fmt -> fprintf fmt "1")

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

let pointer_condition_formatter e =
  match e with
  | Epure pe ->
      (match pe with
       | Eunop(Onotbool, inner, _) when is_declared_ptr_type (type_of_pexpr inner) ->
           Some (fun fmt -> fprintf fmt "(%a).is_null()" pexpr (0, inner))
       | _ ->
           if is_declared_ptr_type (type_of_pexpr pe) then
             Some (fun fmt -> fprintf fmt "!((%a).is_null())" pexpr (0, pe))
           else
             None)
  | Emoveplace(_, ty) ->
      if is_declared_ptr_type ty then
        Some (fun fmt -> fprintf fmt "!((%a).is_null())" print_expr e)
      else
        None

(* Helper to print if condition - adds '!= 0' for int types but not for comparisons *)
let print_if_condition p e =
  match pointer_condition_formatter e with
  | Some printer ->
      printer p
  | None ->
      (* Comparison operators in Rust return bool, so they don't need conversion *)
      if is_comparison_expr e then
        fprintf p "%a" print_expr e
      else
        (* Non-comparison expressions that are int types need '!= 0' *)
        let expr_ty = type_of_expr e in
        let needs_cmp =
          match expr_ty with
          | Rusttypes.Tint(Ctypes.IBool, _) -> false
          | _ -> is_integer_type expr_ty
        in
        if needs_cmp then
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
  "puts"; "fputs"; "gets"; "fgets"; "putchar"; "putc"; "fputc"; "getchar"; "fgetc"; "ungetc";
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

type general_wrapper_kind =
  | Gw_simple
  | Gw_qsort of int  (* index of comparator function pointer *)
  | Gw_bsearch of int  (* index of comparator function pointer *)

type general_wrapper_spec = {
  gw_name: string;
  gw_args: Rusttypes.coq_type list;
  gw_res: Rusttypes.coq_type;
  gw_kind: general_wrapper_kind;
}

let wrapped_function_names : string list ref = ref []

let general_wrapper_blocklist = [
  "printf"; "scanf"; "malloc"; "free";
]

let rec type_contains_function_pointer ty =
  match ty with
  | Rusttypes.Tfunction _ -> true
  | Rusttypes.Tslice(_, elem, _) -> type_contains_function_pointer elem
  | Rusttypes.Tarray(_, elem, _) -> type_contains_function_pointer elem
  | Rusttypes.Treference(_, _, elem) -> type_contains_function_pointer elem
  | _ -> false

let rec is_pointer_return_type ty =
  match ty with
  | Rusttypes.Tslice(_, _, _) -> true
  | Rusttypes.Traw_pointer(_, _) -> true
  | Rusttypes.Tarray(_, elem, _) -> is_pointer_return_type elem
  | _ -> false

let rec find_function_pointer_index args idx =
  match args with
  | [] -> None
  | ty :: rest ->
      (match ty with
       | Rusttypes.Tfunction _ -> Some idx
       | _ -> find_function_pointer_index rest (idx + 1))

let should_generate_general_wrapper name args res cconv =
  List.mem name unsafe_c_functions
  && not (List.mem name general_wrapper_blocklist)
  && cconv.AST.cc_vararg = None
  && not (type_contains_function_pointer res)
  && not (List.exists type_contains_function_pointer (typelist_to_list args))

let collect_general_wrappers prog =
  let rec aux defs acc =
    match defs with
    | [] -> List.rev acc
    | (id, gd) :: rest ->
        (match gd with
         | AST.Gfun (Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _), args, res, cconv)) ->
             let name = extern_atom id in
             let args_list = typelist_to_list args in
             let next =
               if name = "qsort" then begin
                 let cmp_idx =
                   match find_function_pointer_index args_list 0 with
                   | Some idx -> idx
                   | None -> List.length args_list - 1
                 in
                 { gw_name = name; gw_args = args_list; gw_res = res; gw_kind = Gw_qsort cmp_idx } :: acc
               end else if name = "bsearch" then begin
                 let cmp_idx =
                   match find_function_pointer_index args_list 0 with
                   | Some idx -> idx
                   | None -> List.length args_list - 1
                 in
                 { gw_name = name; gw_args = args_list; gw_res = res; gw_kind = Gw_bsearch cmp_idx } :: acc
               end else if should_generate_general_wrapper name args res cconv then
                 { gw_name = name; gw_args = args_list; gw_res = res; gw_kind = Gw_simple } :: acc
               else acc
             in
             aux rest next
         | _ -> aux rest acc)
  in
  aux prog.Rusttypes.prog_defs []

type wrapper_plan = {
  plan_scanf: bool;
  plan_printf: bool;
  plan_general: general_wrapper_spec list;
}

let wrapper_names_of_plan plan =
  let names =
    List.fold_left (fun acc spec -> spec.gw_name :: acc) [] plan.plan_general
  in
  let names =
    (if plan.plan_scanf then "scanf" :: names else names)
  in
  let names =
    (if plan.plan_printf then "printf" :: names else names)
  in
  names

let compute_wrapper_plan prog =
  let has_fn name =
    List.exists (fun (id, _) -> extern_atom id = name) prog.Rusttypes.prog_defs
  in
  {
    plan_scanf = has_fn "scanf";
    plan_printf = has_fn "printf";
    plan_general = collect_general_wrappers prog;
  }

(* Helper function to print function name - just prints the name *)
let print_function_call_name p e =
  match e with
  | Epure (Eglobal(id, _)) ->
      fprintf p "%s" (extern_atom id)
  | Epure (Eplace(Plocal(id, _), _)) ->
      fprintf p "%s" (lookup_ident_name id)
  | _ -> expr p (15, e)

let current_function_is_main = ref false
let current_function_return_type = ref Rusttypes.Tunit

let rec print_stmt p (s: Rustlight.statement) = 
  match s with
  | Sskip ->
    (* comment *)
    fprintf p "/*skip*/"
  | Sassign(v, e) ->
      let handled_ptr_field =
        match extract_pointer_field_place v with
        | Some (ptr_base, fid, field_ty) ->
            fprintf p "@[<v 2>{@ ";
            fprintf p "let mut __tmp = (%a.load(0));@ " print_place ptr_base;
            if is_declared_ptr_type field_ty then begin
              let handled_alloc =
                match temp_name_from_expr e with
                | Some temp_name ->
                    (match take_malloc_temp temp_name with
                     | Some info ->
                         fprintf p "__tmp.%s = %a;@ "
                           (extern_atom fid)
                           (print_malloc_value_for_ty field_ty) info;
                         true
                     | None -> false)
                | None -> false
              in
              if not handled_alloc then begin
                if is_null_ptr_expr e || is_zero_integer_expr e then
                  fprintf p "__tmp.%s = Ptr::null();@ " (extern_atom fid)
                else
                  fprintf p "__tmp.%s = %a;@ "
                    (extern_atom fid)
                    (print_pointer_assignment_value field_ty) e
              end
            end else
              fprintf p "__tmp.%s = %a;@ "
                (extern_atom fid)
                (print_store_expr field_ty) e;
            fprintf p "(%a).store(0, __tmp);@ "
              print_place ptr_base;
            fprintf p "@;<0 -2>}@]";
            true
        | None -> false
      in
      if handled_ptr_field then ()
      else
      let handled =
        match temp_name_from_expr e with
        | Some temp_name ->
            (match take_malloc_temp temp_name with
             | Some info ->
                 print_malloc_assignment p v info;
                 true
             | None -> false)
        | None -> false
      in
      if handled then ()
      else
      (* FIX: 检查 v 是否是我们定义的 Ppair 类型 *)
      let default_assign () =
        match extract_ptr_store_target v with
        | Some (base_expr, index_expr) ->
            let base_ty = type_of_pexpr base_expr in
            if is_array_type base_ty then
              let elem_ty = array_element_type base_ty in
              fprintf p "@[<hv 2>%a[(%a) as usize] = %a;@]"
                pexpr (0, base_expr)
                pexpr (0, index_expr)
                (print_store_expr elem_ty) e
            else
              let target_ty =
                match pointed_type base_ty with
                | Some elem_ty -> elem_ty
                | None -> type_of_place v
              in
              fprintf p "@[<hv 2>%a.store((%a) as usize, %a);@]"
                pexpr (0, base_expr)
                pexpr (0, index_expr)
                (print_store_expr target_ty) e
        | None ->
            let place_ty = resolved_place_type v in
            let full_decl = name_rust_decl_var " : " place_ty in
            let cast_type_name =
              try
                let colon_idx = String.index full_decl ':' in
                String.trim (String.sub full_decl (colon_idx + 1) (String.length full_decl - colon_idx - 1))
              with Not_found -> "i32"
            in
            let looks_like_ptr_decl =
              (String.length cast_type_name >= 4 && String.sub cast_type_name 0 4 = "Ptr<")
              || (String.length cast_type_name >= 13 && String.sub cast_type_name 0 13 = "extern \"C\" fn")
            in
            let expr_is_null_ptr = is_null_ptr_expr e || is_zero_integer_expr e in
            if is_declared_ptr_type place_ty then
              (if expr_is_null_ptr then
                 fprintf p "@[<hv 2>%a =@ Ptr::null();@]" print_place v
               else
                 fprintf p "@[<hv 2>%a =@ %a;@]"
                   print_place v
                   (print_pointer_assignment_value place_ty) e)
            else if looks_like_ptr_decl && expr_is_null_ptr then
              fprintf p "@[<hv 2>%a =@ Ptr::null();@]" print_place v
            else begin
                let expr_returns_bool = is_comparison_expr e in
                let is_bool_target = (cast_type_name = "bool") in
                if is_bool_target && expr_returns_bool then
                  fprintf p "@[<hv 2>%a =@ %a;@]" print_place v print_expr e
                else if is_bool_target && not expr_returns_bool then
                  fprintf p "@[<hv 2>%a =@ (%a) != 0;@]" print_place v print_expr e
                else if (not is_bool_target) && expr_returns_bool then
                  fprintf p "@[<hv 2>%a =@ ((%a) as %s);@]" print_place v print_expr e cast_type_name
                else
                  fprintf p "@[<hv 2>%a =@ (%a) as %s;@]" print_place v print_expr e cast_type_name
            end
      in
      (match v with
      | Ppair(_, _) ->
          fprintf p "@[<hv 2>let %a =@ %a;@]"
            print_place v
            print_expr e
      | Pderef(base, _) ->
          (match pointed_type (type_of_place base) with
           | Some elem_ty ->
               fprintf p "@[<hv 2>%a.store(0, %a);@]"
                 print_place base
                 (print_store_expr elem_ty) e
           | None ->
               default_assign ())
      | ParrayIndex(base, idx, _) ->
          let base_ty = resolved_place_type base in
          if is_declared_ptr_type base_ty then
            (match base_ty with
             | Rusttypes.Tslice(_, elem_ty, _) ->
                 fprintf p "@[<hv 2>%a.store((%s) as usize, %a);@]"
                   print_place base
                   (lookup_ident_name idx)
                   (print_store_expr elem_ty) e
             | _ ->
                 let target_ty =
                   match pointed_type base_ty with
                   | Some elem_ty -> elem_ty
                   | None -> type_of_place v
                 in
                 fprintf p "@[<hv 2>%a.store((%s) as usize, %a);@]"
                   print_place base
                   (lookup_ident_name idx)
                   (print_store_expr target_ty) e)
          else if is_array_type base_ty then
            let elem_ty = array_element_type base_ty in
            fprintf p "@[<hv 2>%a[(%s) as usize] = %a;@]"
              print_place base
              (lookup_ident_name idx)
              (print_store_expr elem_ty) e
          else
            default_assign ()
      | _ ->
          default_assign ()
      )
  | Sassign_variant (v, enum_id, id, e) ->
    fprintf p "@[<hv 2>%a =@ %s::%s(%a);@]" print_place v (extern_atom enum_id)(extern_atom id) print_expr e
  | Scall(v, e1, el) ->
    let place_ty = type_of_place v in
    let callee_name =
      match get_callee_name e1 with
      | Some name -> Some (String.lowercase_ascii name)
      | None -> None
    in
    begin match callee_name, el with
    | Some "scanf", _ :: second :: _ ->
        (match place_from_ptr_arg second with
         | Some target_place ->
             fprintf p "@[<hv 2>%a = read_i32_with_default(%a);@]"
               print_place target_place
               print_place target_place
         | None ->
             fprintf p "@[<hv 2>%a = %a@,(@[<hov 0>%a@]);@]"
               print_place v
               print_function_call_name e1
               print_expr_list_with_type (true, el, [], true))
    | Some "malloc", [param] ->
        (match parse_malloc_param param with
         | Some info ->
             if is_void_pointer_place v && register_malloc_temp v info then
               ()
             else
               print_malloc_assignment p v info
         | None ->
             (* Fallback: treat argument as raw byte length, allocate u8 buffer and cast *)
             let dest_ty = resolved_place_type v in
             let dest_elem_ty_opt = pointed_type dest_ty in
             let alloc_elem_name, cast_target_name =
               match dest_elem_ty_opt with
               | Some Rusttypes.Tvoid -> ("u8", "std::ffi::c_void")
               | Some ty -> let nm = name_rust_type ty in (nm, nm)
               | None -> ("u8", "u8")
             in
             fprintf p "@[<hv 2>%a =@ Ptr::<%s>::alloc((%a) as usize)" print_place v alloc_elem_name print_expr param;
             (match dest_elem_ty_opt with
              | Some ty when name_rust_type ty <> alloc_elem_name ->
                  fprintf p ".cast::<%s>()" (name_rust_type ty)
              | Some Rusttypes.Tvoid -> fprintf p ".cast::<%s>()" cast_target_name
              | _ -> ());
             fprintf p ";@]")
    | Some "malloc", _ ->
        fprintf p "@[<hv 2>/* 错误：malloc参数数量错误 */@]"
    | Some "calloc", [nmemb; size] ->
        (match parse_calloc_params nmemb size with
         | Some info ->
             if is_void_pointer_place v && register_malloc_temp v info then
               ()
             else
               print_malloc_assignment p v info
         | None ->
             fprintf p "@[<hv 2>%a = %a@,(@[<hov 0>%a@]);@]"
               print_place v
               print_function_call_name e1
               print_expr_list_with_type (true, el, [], true))
    | Some "calloc", _ ->
        fprintf p "@[<hv 2>/* 错误：calloc参数数量错误 */@]"
    | Some "realloc", [old_ptr; new_size] ->
        (* `Ptr<T>::alloc` uses Rust allocation; calling libc `realloc` on such
           memory is UB and has caused crashes (allocator mismatch).  Instead,
           model `realloc` by allocating a fresh `Ptr` and copying elements. *)
        let dest_ty = resolved_place_type v in
        let elem_ty, print_new_count =
          match parse_malloc_param new_size with
          | Some info ->
              let ty = info.malloc_elem_ty in
              let printer fmt =
                match info.malloc_count with
                | Some pe -> fprintf fmt "(%a) as usize" pexpr (0, pe)
                | None -> fprintf fmt "1"
              in
              (ty, printer)
          | None ->
              (match pointed_type dest_ty with
               | Some elem when elem <> Rusttypes.Tvoid ->
                   let elem_name = name_rust_type elem in
                   let printer fmt =
                     fprintf fmt
                       "(((%a) as usize) + (std::mem::size_of::<%s>() - 1)) / std::mem::size_of::<%s>()"
                       print_expr new_size
                       elem_name
                       elem_name
                   in
                   (elem, printer)
               | _ ->
                   let ty = Rusttypes.Tint(Ctypes.I8, Ctypes.Unsigned) in
                   let printer fmt =
                     fprintf fmt "(%a) as usize" print_expr new_size
                   in
                   (ty, printer))
        in
        let elem_name = name_rust_type elem_ty in
        let old_ptr_ty = type_of_expr old_ptr in
        let needs_old_cast =
          match pointed_type old_ptr_ty with
          | Some e -> e <> elem_ty
          | None -> true
        in
        let print_old_as_elem fmt =
          if needs_old_cast then
            fprintf fmt "unsafe { (%a).cast::<%s>() }" print_expr old_ptr elem_name
          else
            fprintf fmt "%a" print_expr old_ptr
        in
        let dest_cast_target =
          match pointed_type dest_ty with
          | Some de when de <> elem_ty -> Some (name_rust_type de)
          | _ -> None
        in
        fprintf p "@[<v 2>{@ ";
        fprintf p "let __old : Ptr<%s> = %t;@ " elem_name print_old_as_elem;
        fprintf p "let __new_len : usize = %t;@ " print_new_count;
        fprintf p "let __new : Ptr<%s> = Ptr::<%s>::alloc(__new_len);@ "
          elem_name elem_name;
        fprintf p
          "let __copy_len : usize = std::cmp::min(__old.len().unwrap_or(0), __new_len);@ ";
        fprintf p "let mut __i : usize = 0;@ ";
        fprintf p "while __i < __copy_len {@ ";
        fprintf p "  __new.store(__i, __old.load(__i));@ ";
        fprintf p "  __i += 1;@ ";
        fprintf p "}@ ";
        (match dest_cast_target with
         | Some target ->
             fprintf p "%a = unsafe { __new.cast::<%s>() };@ " print_place v target
         | None ->
             fprintf p "%a = __new;@ " print_place v);
        fprintf p "@;<0 -2>}@]"
    | Some "realloc", _ ->
        fprintf p "@[<hv 2>/* 错误：realloc参数数量错误 */@]"
    | Some "memcpy", [dst; src; nbytes] ->
        (match nbytes with
         | Epure n_pe ->
             (match sizeof_type_from_pexpr n_pe with
              | Some ty when type_contains_declared_ptr ty ->
                  let ty_name = name_rust_type ty in
                  fprintf p "@[<v 2>{@ ";
                  fprintf p "let __tmp = unsafe { (%a).cast::<%s>() }.load(0);@ "
                    print_expr src ty_name;
                  fprintf p "unsafe { (%a).cast::<%s>() }.store(0, __tmp);@ "
                    print_expr dst ty_name;
                  (match place_ty with
                   | Rusttypes.Tunit -> ()
                   | _ ->
                       fprintf p "%a = %a;@ " print_place v print_expr dst);
                  fprintf p "@;<0 -2>}@]"
              | _ ->
                  (* Fallback to the normal wrapper call. *)
                  let fun_ty = type_of_expr e1 in
                  let param_tys =
                    match fun_ty with
                    | Rusttypes.Tfunction(_, _, args, _, _) -> typelist_to_list args
                    | _ -> List.map (fun _ -> Rusttypes.Tunit) el
                  in
                  let is_c_function = true in
                  let is_ignored_return =
                    match place_ty with Rusttypes.Tunit -> true | _ -> false
                  in
                  if is_ignored_return then
                    fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                      print_function_call_name e1
                      print_expr_list_with_type (true, el, param_tys, is_c_function)
                  else
                    fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
                      print_place v
                      print_function_call_name e1
                      print_expr_list_with_type (true, el, param_tys, is_c_function))
         | _ ->
             fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
               print_function_call_name e1
               print_expr_list_with_type (true, el, [], true))
    | Some "memcpy", _ ->
        fprintf p "@[<hv 2>/* 错误：memcpy参数数量错误 */@]"
    | Some "free", arg :: _ ->
        (match place_from_ptr_arg arg with
         | Some place ->
             fprintf p "@[<hv 2>%a.free();@]" print_place place
         | None ->
             fprintf p "@[<hv 2>/* free call could not be translated */@]")
    | Some "free", [] ->
        fprintf p "@[<hv 2>/* free call missing argument */@]"
    | Some "printf", fmt_expr :: rest ->
        let print_printf_arg fmt () =
          let arg_ty = type_of_expr fmt_expr in
          match arg_ty with
          | Rusttypes.Tarray(_, _, _) ->
              fprintf fmt "Ptr::from_ref(&mut ";
              expr fmt (2, fmt_expr);
              fprintf fmt "[..])"
          | _ ->
              expr fmt (2, fmt_expr)
       in
        let print_fmt_ptr fmt () =
          fprintf fmt "%a.as_ptr()" print_printf_arg ()
        in
        if rest = [] then
          (match place_ty with
           | Rusttypes.Tunit ->
               fprintf p "@[<hv 2>print_c_string(@[%a@]);@]" print_printf_arg ()
           | _ ->
               fprintf p "@[<hv 2>%a =@ print_c_string(@[%a@]);@]"
                 print_place v
                 print_printf_arg ())
        else
          let print_libc_printf_call fmt () =
            fprintf fmt "unsafe {@ ";
            fprintf fmt "__libc_printf(@[%a" print_fmt_ptr ();
            fprintf fmt "@]";
            fprintf fmt ",@ %a" print_expr_list_with_type (true, rest, [], true);
            fprintf fmt ");@ ";
            fprintf fmt "}"
          in
          (match place_ty with
           | Rusttypes.Tunit ->
               fprintf p "@[<hv 2>%a;@]" print_libc_printf_call ()
           | _ ->
               fprintf p "@[<hv 2>%a =@ " print_place v;
               print_libc_printf_call p ();
               fprintf p ";@]")
    | _ ->
      let fun_ty = type_of_expr e1 in
      let param_tys = 
        match fun_ty with 
        | Rusttypes.Tfunction(_, _, args, _, _) ->  typelist_to_list args
        | _ -> List.map (fun _ -> Rusttypes.Tunit) el  (* fallback: 全部Tunit *)
      in
      let is_c_function = match e1 with
        | Epure (Eglobal(id, _)) ->
            let name = extern_atom id in
            List.mem name unsafe_c_functions
        | Epure (Eplace(Plocal(id, _), _)) ->
            let name = extern_atom id in
            List.mem name unsafe_c_functions
        | _ -> false
      in
      let is_ignored_return = match place_ty with
        | Rusttypes.Tunit -> true
        | _ -> false
      in
      if is_ignored_return then
        fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
          print_function_call_name e1
          print_expr_list_with_type (true, el, param_tys, is_c_function)
      else
        fprintf p "@[<hv 2>%a =@ %a@,(@[<hov 0>%a@]);@]"
          print_place v
          print_function_call_name e1
          print_expr_list_with_type (true, el, param_tys, is_c_function)
    end
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
    fprintf p "@[<v 2>loop {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sbreak ->
    fprintf p "break;"
  | Scontinue ->
    fprintf p "continue;"
  (* | Sreturn None ->
    fprintf p "return;" *)
  | Sreturn v ->
    if !current_function_is_main then
      fprintf p "::std::process::exit((%a) as i32);" print_place v
    else if is_unit_type !current_function_return_type then
      fprintf p "return;"
    else
      fprintf p "return %a;" print_place v
  | Sbox(v, e) ->
    fprintf p "@[<hv 2>%a =@ Box::new(%a);@]" print_place v print_expr e
  | Slet(id, ty, s) ->
    fprintf p "@[<v 2>let %s : %s in {@ %a@;<0 -2>}@]"
            (lookup_ident_name id)
            (name_rust_type ty)
            print_stmt s

let print_stmt_direct stmt = print_stmt (formatter_of_out_channel stdout) stmt

(* Check whether function id is main_id *)
let is_main_id id =
  let fun_name = extern_atom id in
  fun_name = "main"

let sanitized_fun_name id = sanitize_rust_identifier (extern_atom id)

let print_function p id f =
  setup_local_names f;
  current_function_return_type := f.fn_return;
  if is_main_id id then 
    begin
    let ret_ty = f.fn_return in
    let ret_annotation =
      match ret_ty with
      | Rusttypes.Tunit -> ""
      | _ -> " -> " ^ (name_rust_type ret_ty)
    in
    fprintf p "fn main()%s" ret_annotation;
    fprintf p "{@;@[<v 2>  @[<v 1>@;";
        fprintf p "unsafe {@ ";  (* Wrap in unsafe for static mut access *)
        (* If C main had parameters (argc, argv), declare them as local variables with default values *)
        let print_param_init (param_id, param_ty) =
          let var_name = lookup_ident_name param_id in
          let decl = binding_with_type var_name param_ty in
          match param_ty with
          | Rusttypes.Tslice(_, _, _) ->
              fprintf p "let mut %s = Ptr::null();@ " decl
          | Rusttypes.Tint(_, _) ->
              fprintf p "let mut %s = 0;@ " decl
          | Rusttypes.Tlong(_) ->
              fprintf p "let mut %s = 0;@ " decl
          | Rusttypes.Tfloat(_) ->
              fprintf p "let mut %s = 0.0;@ " decl
          | Rusttypes.Tunit ->
              fprintf p "let mut %s;@ " decl
          | _ ->
              fprintf p "let mut %s = Default::default();@ " decl
        in
        List.iter print_param_init f.fn_params;
        (* Print local variables *)
        List.iter 
        (fun (id, ty) ->
          if ty = Rusttypes.Tunit then () else
          match ty with
          | Rusttypes.Tarray(_, _, _) ->
              let var_name = lookup_ident_name id in
              fprintf p "let mut %s = %s;@ "
                (binding_with_type var_name ty)
                (default_expr_for_type ty)
          | _ ->
              (* 初始化指针/非指针：指针用 Ptr::null()，其他保持默认 *)
              (match ty with
          | Rusttypes.Tslice(_, _, _) ->
              let var_name = lookup_ident_name id in
              let decl = binding_with_type var_name ty in
              fprintf p "let mut %s = Ptr::null();@ " decl
           | _ ->
               let default_init = match ty with
                 | Rusttypes.Tint(_, _) -> " = 0"
                 | Rusttypes.Tlong(_) -> " = 0"
                 | Rusttypes.Tfloat(_) -> " = 0.0"
                 | Rusttypes.Tunit -> ""
                 | _ -> " = Default::default()"
               in
               let var_name = lookup_ident_name id in
               fprintf p "let mut %s%s;@ " (binding_with_type var_name ty) default_init))
        f.fn_vars;
        (* 全局指针/包含指针的静态变量在静态初始化阶段只能放零值，
           真实初始化在 __init_globals 中完成，这里在 main 开头调用一次。 *)
        if PrintRustsyntax.has_pointer_globals () then
          fprintf p "__init_globals();@ ";
        current_function_is_main := true;
        print_stmt p f.fn_body;
        current_function_is_main := false;
        fprintf p "@;<0 -2>}@ ";
    fprintf p "@]@;<0 -2>}@]@ @ "
    end
  else
    begin
      current_function_is_main := false;
      let fun_name = sanitized_fun_name id in
      fprintf p "extern \"C\" fn%s@ "
                (name_rust_decl_fn
                   (PrintRustsyntax.name_function_parameters
                      (fun ident -> sanitize_rust_identifier (lookup_ident_name ident))
                      fun_name
                      f.fn_params
                      f.fn_callconv
                      f.fn_generic_origins
                      f.fn_origins_relation)
                   f.fn_return);
      fprintf p "@[<v 2>{@ ";
        fprintf p "unsafe {@ ";  (* Wrap in unsafe for static mut access *)
        (* Print variables and their types *)
        List.iter 
        (fun (id, ty) ->
          if ty = Rusttypes.Tunit then () else
          match ty with
          | Rusttypes.Tarray(_, _, _) ->
              let var_name = lookup_ident_name id in
              fprintf p "let mut %s = %s;@ "
                (binding_with_type var_name ty)
                (default_expr_for_type ty)
          | Rusttypes.Tslice(_, _, _) ->
              let var_name = lookup_ident_name id in
              let decl = binding_with_type var_name ty in
              fprintf p "let mut %s = Ptr::null();@ " decl
          | _ ->
              let default_init = match ty with
                | Rusttypes.Tint(_, _) -> " = 0"
                | Rusttypes.Tlong(_) -> " = 0"
                | Rusttypes.Tfloat(_) -> " = 0.0"
                | Rusttypes.Tunit -> ""
                | _ -> " = Default::default()"
              in
              let var_name = lookup_ident_name id in
              fprintf p "let mut %s%s;@ " (binding_with_type var_name ty) default_init)
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
  let fun_name = sanitized_fun_name id in
  (* 检查函数名是否在屏蔽列表中 *)
  if List.mem fun_name PrintRustsyntax.suppressed_functions then
    () (* if in unsafe function list, do noting *)
  else
    (* if not in unsafe function list, print it *)
    match fd with
    | Rusttypes.External(_, _, (AST.EF_external _ | AST.EF_runtime _), args, res, cconv) ->
        (* All external C functions are declared with FFI-safe types *)
        fprintf p "unsafe extern \"C\" { %s; }@ "
                  (PrintRustsyntax.name_rust_decl_fn_ffi fun_name
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
  let fun_name = extern_atom id in
  if List.mem fun_name PrintRustsyntax.suppressed_functions
     || List.mem fun_name !wrapped_function_names then
    ()
  else
    match gd with
    | AST.Gfun f -> print_fundecl p id f
    | AST.Gvar v -> PrintRustsyntax.print_globvardecl p id v

(* Generate safe wrapper functions for unsafe C functions *)
let rust_type_to_string ty = PrintRustsyntax.name_rust_decl "" ty

let ptr_accessor_for_mut mutk =
  match mutk with
  | Rusttypes.Mutable -> ".as_mut_ptr()"
  | Rusttypes.Immutable -> ".as_ptr()"

let ptr_from_raw_expression ty raw =
  match ty with
  | Rusttypes.Tslice(_, elem_ty, _) ->
      Printf.sprintf "Ptr::from_raw_parts(%s as *mut %s, 1)" raw (rust_type_to_string elem_ty)
  | Rusttypes.Traw_pointer(_, elem_ty) ->
      Printf.sprintf "Ptr::from_raw_parts(%s as *mut %s, 1)" raw (rust_type_to_string elem_ty)
  | _ ->
      Printf.sprintf "Ptr::from_raw_parts(%s as *mut std::ffi::c_void, 1)" raw

let ffi_info_for_type ty =
  match ty with
  | Rusttypes.Tslice(mutk, elem_ty, _) ->
      let elem_str = rust_type_to_string elem_ty in
      let ffi_ty =
        (match mutk with
         | Rusttypes.Mutable -> "*mut "
         | Rusttypes.Immutable -> "*const ") ^ elem_str
      in
      (rust_type_to_string ty, ffi_ty, fun arg -> arg ^ ptr_accessor_for_mut mutk)
  | Rusttypes.Traw_pointer(_, elem_ty) ->
      let elem_str = rust_type_to_string elem_ty in
      let ffi_ty = "*mut " ^ elem_str in
      (rust_type_to_string ty, ffi_ty, fun arg -> arg ^ ".as_mut_ptr()")
  | _ ->
      let ty_str = rust_type_to_string ty in
      (ty_str, ty_str, fun arg -> arg)

let print_general_wrapper p spec =
  let param_name idx = Printf.sprintf "arg%d" idx in
  let safe_params =
    List.mapi (fun idx ty ->
        Printf.sprintf "%s: %s" (param_name idx) (rust_type_to_string ty))
      spec.gw_args
  in
  let safe_params_str = String.concat ", " safe_params in
  let safe_ret_decl =
    match spec.gw_res with
    | Rusttypes.Tunit -> ""
    | _ -> Printf.sprintf " -> %s" (rust_type_to_string spec.gw_res)
  in
  let ffi_ret_decl =
    match spec.gw_res with
    | Rusttypes.Tunit -> ""
    | _ ->
        let _, ffi_ty, _ = ffi_info_for_type spec.gw_res in
        Printf.sprintf " -> %s" ffi_ty
  in
  match spec.gw_kind with
  | Gw_simple ->
      let ffi_params, call_args =
        List.mapi
          (fun idx ty ->
             let _, ffi_ty, conv = ffi_info_for_type ty in
             (Printf.sprintf "%s: %s" (param_name idx) ffi_ty,
              conv (param_name idx)))
          spec.gw_args
        |> List.split
      in
      let ffi_params_str = String.concat ", " ffi_params in
      let call_args_str = String.concat ", " call_args in
      fprintf p "extern \"C\" {@ ";
      fprintf p "  #[link_name = \"%s\"]@ " spec.gw_name;
      fprintf p "  fn __libc_%s(%s)%s;@ " spec.gw_name ffi_params_str ffi_ret_decl;
      fprintf p "}@ ";
      fprintf p "fn %s(%s)%s {@ " spec.gw_name safe_params_str safe_ret_decl;
      fprintf p "  unsafe {@ ";
      (match spec.gw_res with
       | Rusttypes.Tunit ->
           fprintf p "    __libc_%s(%s);@ " spec.gw_name call_args_str
       | res_ty when is_pointer_return_type res_ty ->
           fprintf p "    let raw = __libc_%s(%s);@ " spec.gw_name call_args_str;
           fprintf p "    %s@ " (ptr_from_raw_expression res_ty "raw")
       | _ ->
           fprintf p "    __libc_%s(%s)@ " spec.gw_name call_args_str);
      fprintf p "  }@ ";
      fprintf p "}@ "
  | Gw_qsort cmp_idx ->
      let base_ty = List.nth spec.gw_args 0 in
      let nmemb_ty = List.nth spec.gw_args 1 in
      let size_ty = List.nth spec.gw_args 2 in
      let _, base_ffi_ty, base_conv = ffi_info_for_type base_ty in
      let _, nmemb_ffi_ty, nmemb_conv = ffi_info_for_type nmemb_ty in
      let _, size_ffi_ty, size_conv = ffi_info_for_type size_ty in
      let base_name = param_name 0 in
      let nmemb_name = param_name 1 in
      let size_name = param_name 2 in
      let cmp_name = param_name cmp_idx in
      fprintf p "extern \"C\" {@ ";
      fprintf p "  #[link_name = \"%s\"]@ " spec.gw_name;
      fprintf p "  fn __libc_%s(%s: %s, %s: %s, %s: %s, %s: extern \"C\" fn(*const std::ffi::c_void, *const std::ffi::c_void) -> i32)%s;@ "
        spec.gw_name
        base_name base_ffi_ty
        nmemb_name nmemb_ffi_ty
        size_name size_ffi_ty
        cmp_name
        ffi_ret_decl;
      fprintf p "}@ ";
      fprintf p "fn %s(%s)%s {@ " spec.gw_name safe_params_str safe_ret_decl;
      fprintf p "  unsafe {@ ";
      fprintf p "    callback::with_void_comparator(%s, || {@ " cmp_name;
      fprintf p "      __libc_%s(%s, %s, %s, callback::void_comparator_trampoline);@ "
        spec.gw_name
        (base_conv base_name)
        (nmemb_conv nmemb_name)
        (size_conv size_name);
      fprintf p "    });@ ";
      fprintf p "  }@ ";
      (match spec.gw_res with
       | Rusttypes.Tunit -> ()
       | _ -> fprintf p "  unsafe { ::std::mem::zeroed() }@ ");
      fprintf p "}@ "
  | Gw_bsearch cmp_idx ->
      let key_ty = List.nth spec.gw_args 0 in
      let base_ty = List.nth spec.gw_args 1 in
      let nmemb_ty = List.nth spec.gw_args 2 in
      let size_ty = List.nth spec.gw_args 3 in
      let _, key_ffi_ty, key_conv = ffi_info_for_type key_ty in
      let _, base_ffi_ty, base_conv = ffi_info_for_type base_ty in
      let _, nmemb_ffi_ty, nmemb_conv = ffi_info_for_type nmemb_ty in
      let _, size_ffi_ty, size_conv = ffi_info_for_type size_ty in
      let key_name = param_name 0 in
      let base_name = param_name 1 in
      let nmemb_name = param_name 2 in
      let size_name = param_name 3 in
      let cmp_name = param_name cmp_idx in
      fprintf p "extern \"C\" {@ ";
      fprintf p "  #[link_name = \"%s\"]@ " spec.gw_name;
      fprintf p "  fn __libc_%s(%s: %s, %s: %s, %s: %s, %s: %s, %s: extern \"C\" fn(*const std::ffi::c_void, *const std::ffi::c_void) -> i32)%s;@ "
        spec.gw_name
        key_name key_ffi_ty
        base_name base_ffi_ty
        nmemb_name nmemb_ffi_ty
        size_name size_ffi_ty
        cmp_name
        ffi_ret_decl;
      fprintf p "}@ ";
      fprintf p "fn %s(%s)%s {@ " spec.gw_name safe_params_str safe_ret_decl;
      fprintf p "  unsafe {@ ";
      fprintf p "    callback::with_void_comparator(%s, || {@ " cmp_name;
      fprintf p "      let raw = __libc_%s(%s, %s, %s, %s, callback::void_comparator_trampoline);@ "
        spec.gw_name
        (key_conv key_name)
        (base_conv base_name)
        (nmemb_conv nmemb_name)
        (size_conv size_name);
      fprintf p "      %s@ " (ptr_from_raw_expression spec.gw_res "raw");
      fprintf p "    })@ ";
      fprintf p "  }@ ";
      fprintf p "}@ "

let print_safe_wrappers p (plan: wrapper_plan) =
  if plan.plan_scanf then begin
    fprintf p "extern \"C\" {@ ";
    fprintf p "  #[link_name = \"scanf\"]@ ";
    fprintf p "  fn __libc_scanf(fmt: *const i8, ...) -> i32;@ ";
    fprintf p "}@ ";
    fprintf p "fn read_i32_with_default(default: i32) -> i32 {@ ";
    fprintf p "  let mut value = default;@ ";
    fprintf p "  unsafe {@ ";
    fprintf p "    let fmt = Ptr::from_ref(&mut __stringlit_1[..]);@ ";
    fprintf p "    __libc_scanf(fmt.as_ptr(), &mut value as *mut i32);@ ";
    fprintf p "  }@ ";
    fprintf p "  value@ ";
    fprintf p "}@ "
  end;
  if plan.plan_printf then begin
    fprintf p "extern \"C\" {@ ";
    fprintf p "  #[link_name = \"printf\"]@ ";
    fprintf p "  fn __libc_printf(fmt: *const i8, ...) -> i32;@ ";
    fprintf p "}@ ";
    fprintf p "fn print_c_string(fmt: Ptr<i8>) -> i32 {@ ";
    fprintf p "  unsafe {@ ";
    fprintf p "    __libc_printf(fmt.as_ptr())@ ";
    fprintf p "  }@ ";
    fprintf p "}@ "
  end;
  List.iter (print_general_wrapper p) plan.plan_general

let collect_global_var_names defs =
  List.fold_left
    (fun acc (id, gd) ->
       match gd with
       | AST.Gvar _ -> StringSet.add (sanitize_rust_identifier (extern_atom id)) acc
       | _ -> acc)
    StringSet.empty defs

let collect_extern_pointer_globals defs =
  List.fold_left
    (fun acc (id, gd) ->
       match gd with
       | AST.Gvar v ->
           if (not (C2C.atom_is_static id))
              && v.AST.gvar_init = []
              && is_pointer_type v.AST.gvar_info
           then
             StringSet.add (sanitize_rust_identifier (extern_atom id)) acc
           else
             acc
       | _ -> acc)
    StringSet.empty defs

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
  global_var_names := collect_global_var_names prog.Rusttypes.prog_defs;
  extern_pointer_globals := collect_extern_pointer_globals prog.Rusttypes.prog_defs;
  (* Pre-collect globals whose initializers contain pointers so that we
     can both (1) avoid non-const pointer operations in their static
     initializers and (2) generate a runtime __init_globals() that
     reconstructs the original values. *)
  PrintRustsyntax.collect_pointer_globals prog.Rusttypes.prog_defs;
  let plan = compute_wrapper_plan prog in
  wrapped_function_names := wrapper_names_of_plan plan;
  fprintf p "@[<v 0>";
  (* Add allow attribute if there are static mut variables *)
  if has_static_mut then
    fprintf p "#![allow(static_mut_refs)]@ ";
  (* Don't print forward declarations - Rust doesn't support them *)
  (* List.iter (PrintRustsyntax.declare_composite p) prog.Rusttypes.prog_types; *)
  (* Add placeholder for commonly undefined system types *)
  fprintf p "#[path = \"/Users/yaodongdong/WorkPlace/project/Compcert/runtime/ptr.rs\"]@ mod ptr;@ use ptr::*;@ ";
  fprintf p "#[path = \"/Users/yaodongdong/WorkPlace/project/Compcert/runtime/callback.rs\"]@ mod callback;@ ";
  fprintf p "pub struct __sFILEX;@ ";
  List.iter (PrintRustsyntax.define_composite p) prog.Rusttypes.prog_types;
  List.iter (print_globdecl p) prog.Rusttypes.prog_defs;
  List.iter (print_globdef p) prog.Rusttypes.prog_defs;
  (* Emit runtime global-initialization function if needed. *)
  PrintRustsyntax.print_global_initializers p;
  print_safe_wrappers p plan;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
