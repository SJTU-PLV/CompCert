open Format
open Camlcoq
(* open Values *)
open AST
open! Rusttypes
(* open Cop *)
(* open Rustsyntax *)
open PrintCsyntax

(* Do not print these unsafe function in rust file *)
let suppressed_functions = [
  "__compcert_va_int32";
  "__compcert_va_int64";
  "__compcert_va_float64";
  "__compcert_va_composite";
  "__compcert_i64_dtos";
  "__compcert_i64_dtou";
  "__compcert_i64_stod";
  "__compcert_i64_utod";
  "__compcert_i64_stof";
  "__compcert_i64_utof";
  "__compcert_i64_sdiv";
  "__compcert_i64_udiv";
  "__compcert_i64_smod";
  "__compcert_i64_umod";
  "__compcert_i64_shl";
  "__compcert_i64_shr";
  "__compcert_i64_sar";
  "__compcert_i64_smulh";
  "__compcert_i64_umulh";
  "__builtin_debug";
  "printf";
  "scanf";
  "qsort";
]
(* Create a hashtable to store string literals *)
let string_literals : (string, string) Hashtbl.t = Hashtbl.create 101
let struct_field_table : (string, (string * Rusttypes.coq_type) list) Hashtbl.t = Hashtbl.create 97

(* Globals whose initializers contain pointer values that cannot be
   expressed as Rust compile-time constants (e.g. Ptr::from_ref on
   string literals).  For these, we emit a zero / null static
   initializer and generate a runtime __init_globals() function that
   performs the original initialization. *)
let pointer_global_inits :
  (string * Rusttypes.coq_type * init_data list) list ref = ref []

let reset_pointer_globals () =
  pointer_global_inits := []

let register_pointer_global (name : string) (ty : Rusttypes.coq_type) (il : init_data list) =
  pointer_global_inits := (name, ty, il) :: !pointer_global_inits

let has_pointer_globals () =
  !pointer_global_inits <> []

let is_pointer_global_name (name : string) =
  List.exists (fun (n, _, _) -> n = name) !pointer_global_inits

let dummy_origin_ref = ref BinNums.Coq_xH

let dummy_origin () = !dummy_origin_ref

let string_of_mut mut =
  match mut with
  | Mutable -> "mut "
  | Immutable -> ""

let string_of_pmut pmut =
  match pmut with
  | Coq_mutable -> "mut "
  | Coq_const -> "const"

let print_origin_as_lifetime a = ""

let print_origins_aux (orgs : origin list) = ""

let print_origins (orgs : origin list) =
  ""
  
let origin_relations_string_aux (rels: origin_rel list) = ""

let origin_relations_string (rels: origin_rel list) =
  ""

let lifetime_of_origin (orig: ptr_origin) =
  match orig with
  | PtrBorrowed -> "'a"
  | PtrHeap
  | PtrNull
  | PtrUnknown -> "'static"

let rec name_rust_decl id ty =
  match ty with
  | Rusttypes.Tunit ->
      "()" ^ name_optid id
  | Rusttypes.Tvoid ->
      "std::ffi::c_void" ^ name_optid id
  | Rusttypes.Tint(sz, sg) ->
      name_inttype sz sg ^ name_optid id
  | Rusttypes.Tfloat(sz) ->
      name_floattype sz ^ name_optid id
  | Rusttypes.Tlong(sg) ->
      name_longtype sg ^ name_optid id
  | Rusttypes.Treference(org, mut, t) ->
      "&" ^ " " ^  string_of_mut mut ^ (name_rust_decl ""  t) ^ name_optid id
  | Tbox(t) ->
      "Box<" ^ (name_rust_decl ""  t) ^ ">" ^ name_optid id
  | Tfunction( _, _, args, res, cconv) ->
      (* Rust function pointer syntax: name : fn(args) -> ret *)
      let b = Buffer.create 20 in
      (* For function pointers, use Rust syntax: fn(...) -> ... *)
      Buffer.add_string b (name_optid id);
      Buffer.add_string b "extern \"C\" fn(";
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl "" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_string b ")";
      (* Add return type *)
      (match res with
       | Rusttypes.Tunit -> Buffer.add_string b ""
       | _ -> 
           Buffer.add_string b " -> ";
           Buffer.add_string b (name_rust_decl "" res));
      Buffer.contents b
  | Tstruct(orgs, name) ->
      extern_atom name ^ print_origins orgs ^ name_optid id
  | Tvariant(orgs, name) ->
      extern_atom name ^ print_origins orgs ^ name_optid id
  | Traw_pointer(mut, ty) ->
    "Ptr<" ^ (name_rust_decl "" ty) ^ ">" ^ name_optid id
  | Tarray(mut, ty, sz) ->
    (* Multi-dimensional arrays: [[T; M]; N] *)
    name_optid id ^ "[" ^ name_rust_decl "" ty ^ "; " ^ sprintf "%ld" (camlint_of_coqint sz) ^ "]"
  | Tslice(_, ty, origin) ->
    ptr_type_string origin ty ^ name_optid id

and ptr_type_string (_orig: ptr_origin) ty =
  match ty with
  | Tfunction(_, _, _, _, _) ->
      name_rust_decl "" ty
  | _ ->
      "Ptr<" ^ (name_rust_decl "" ty) ^ ">"

(*  IBool used in variable context should be i32, not bool *)
let name_inttype_for_var sz sg =
  match sz, sg with
  | Ctypes.IBool, _ -> "i32"  (* In C, _Bool can be used as integer *)
  | _ -> name_inttype sz sg

let rec name_rust_decl_var id ty =
  match ty with
  | Rusttypes.Tunit ->
    name_optid_no_space id ^ "()"
  | Rusttypes.Tvoid ->
    name_optid_no_space id ^ "std::ffi::c_void"    
  | Rusttypes.Tint(sz, sg) ->
    name_optid_no_space id ^ name_inttype_for_var sz sg
  | Rusttypes.Tfloat(sz) ->
    name_optid_no_space id  ^ name_floattype sz
  | Rusttypes.Tlong(sg) ->
    name_optid_no_space id ^ name_longtype sg
  | Rusttypes.Treference(_, mut, t) ->
    name_optid_no_space id ^ "&" ^ string_of_mut mut ^ (name_rust_decl ""  t)
  | Tbox(t) ->
    name_optid_no_space id ^ "Box<" ^ (name_rust_decl ""  t) ^ ">"
  | Tfunction( _, _, args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl "_" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      "extern \"C\" fn" ^ name_rust_decl_var (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      let ty_name = extern_atom name ^ print_origins orgs in
      name_optid_no_space id ^ ty_name
  | Tvariant(orgs, name) ->
      let ty_name = extern_atom name ^ print_origins orgs in
      name_optid_no_space id ^ ty_name
  | Traw_pointer(mut, ty) ->
    name_optid_no_space id ^ "Ptr<" ^ (name_rust_decl ""  ty) ^ ">"
  | Tarray(mut, ty, sz) ->
    (* begin
    (* string_of_mut mut ^ " "^ *)
    match mut with
    | Immutable->
        (* 处理 const 数组 *)
        name_optid id ^ "[" ^ name_rust_decl "" ty ^ ";" ^ sprintf "%ld" (camlint_of_coqint sz) ^ "]"
    | Mutable -> *)
        (* 处理 mutable 数组 *)
        name_optid_no_space id ^ "[" ^ name_rust_decl "" ty ^ ";" ^ sprintf "%ld" (camlint_of_coqint sz) ^ "]"
    (* end *)
  | Tslice(_, ty, origin) ->
    name_optid_no_space id ^ ptr_type_string origin ty

let rec name_rust_decl_fn_arg id ty =
  match ty with
  | Rusttypes.Tunit ->
    name_optid_no_space id ^ "()"
  | Rusttypes.Tvoid ->
    name_optid_no_space id ^ "std::ffi::c_void"    
  | Rusttypes.Tint(sz, sg) ->
    name_optid_no_space id ^ name_inttype sz sg
  | Rusttypes.Tfloat(sz) ->
    name_optid_no_space id  ^ name_floattype sz
  | Rusttypes.Tlong(sg) ->
    name_optid_no_space id ^ name_longtype sg
  | Rusttypes.Treference(org, mut, t) ->
    name_optid_no_space id ^ "&" ^ (print_origin_as_lifetime org) ^" "^  string_of_mut mut ^ (name_rust_decl ""  t)
  | Tbox(t) ->
    name_optid_no_space id ^ "Box<" ^ (name_rust_decl ""  t) ^ ">"
  | Tfunction( _, _, args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl "_" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      "extern \"C\" fn" ^ name_rust_decl_fn_arg (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      let ty_name = extern_atom name ^ print_origins orgs in
      name_optid_no_space id ^ ty_name
  | Tvariant(orgs, name) ->
      extern_atom name ^ print_origins orgs ^ name_optid id
  | Traw_pointer(mut, ty) ->
    name_optid_no_space id ^ "*" ^ string_of_pmut mut ^ (name_rust_decl ""  ty)
  | Tarray(mut, ty, sz) ->
    (* begin
    (* string_of_mut mut ^ " "^ *)
    match mut with
    | Immutable->
        (* 处理 const 数组 *)
        name_optid id ^ "[" ^ name_rust_decl "" ty ^ ";" ^ sprintf "%ld" (camlint_of_coqint sz) ^ "]"
    | Mutable -> *)
        (* 处理 mutable 数组 *)
        name_optid_no_space id ^ "[" ^ name_rust_decl "" ty ^ ";" ^ sprintf "%ld" (camlint_of_coqint sz) ^ "]"
    (* end *)
  | Tslice(_, ty, origin) ->
    name_optid_no_space id ^ ptr_type_string origin ty

let rec name_rust_decl_fn id ty =
  match ty with
  | Rusttypes.Tunit ->
      name_optid id 
  | Rusttypes.Tvoid ->
      name_optid id
  | Rusttypes.Tint(sz, sg) ->
      name_optid id ^ " -> " ^ name_inttype sz sg
  | Rusttypes.Tfloat(sz) ->
      name_optid id  ^ " -> " ^ name_floattype sz
  | Rusttypes.Tlong(sg) ->
      name_optid id ^ " -> " ^ name_longtype sg
  | Rusttypes.Treference(_, mut, t) ->
      name_optid id ^ " -> " ^ "&" ^ string_of_mut mut ^ (name_rust_decl ""  t)
  | Tbox(t) ->
      name_optid id ^ " -> " ^ "Box<" ^ (name_rust_decl ""  t) ^ ">"
  | Tfunction( _, _, args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl_fn_arg "_ : " t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      "fn" ^ name_rust_decl_fn (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      extern_atom name ^ print_origins orgs ^ name_optid id
  | Tvariant(orgs, name) ->
      extern_atom name ^ print_origins orgs ^ name_optid id
  | Traw_pointer(pmut, ty) ->
    name_optid id ^ " -> " ^ "Ptr<" ^ (name_rust_decl ""  ty) ^ ">"
  | Tarray(mut, ty, sz) ->
    (* string_of_mut mut ^ " "^ *)
    name_rust_decl (sprintf "%s[%ld]" id (camlint_of_coqint sz)) ty
  | Tslice(_, ty, origin) ->
    name_optid id ^ " -> " ^ ptr_type_string origin ty
(* Type *)

let name_rust_type ty = name_rust_decl "" ty

let rec type_includes_function ty =
  match ty with
  | Rusttypes.Tfunction(_, _, _, _, _) -> true
  | Rusttypes.Tslice(_, elem_ty, _)
  | Rusttypes.Traw_pointer(_, elem_ty)
  | Rusttypes.Tarray(_, elem_ty, _)
  | Rusttypes.Treference(_, _, elem_ty)
  | Rusttypes.Tbox elem_ty -> type_includes_function elem_ty
  | _ -> false

let default_expr_for_type ty =
  match ty with
  | Rusttypes.Tint(_, _) -> "0"
  | Rusttypes.Tlong(_) -> "0"
  | Rusttypes.Tfloat(_) -> "0.0"
  | Rusttypes.Traw_pointer(_, elem_ty) ->
      Printf.sprintf "Ptr::<%s>::null()" (name_rust_type elem_ty)
  | Rusttypes.Tslice(_, elem_ty, _) ->
      Printf.sprintf "Ptr::<%s>::null()" (name_rust_type elem_ty)
  | _ when type_includes_function ty ->
      let ty_name = name_rust_type ty in
      Printf.sprintf "unsafe { std::mem::MaybeUninit::<%s>::zeroed().assume_init() }" ty_name
  | Rusttypes.Tarray(_, elem_ty, sz) ->
      let elem_ty_name = name_rust_type elem_ty in
      let len = camlint_of_coqint sz in
      Printf.sprintf "array_default::<%s, %ld>()" elem_ty_name len
  | _ ->
      let ty_name = name_rust_type ty in
      if String.length ty_name >= 13 && String.sub ty_name 0 13 = "extern \"C\" fn" then
        Printf.sprintf "unsafe { std::mem::MaybeUninit::<%s>::zeroed().assume_init() }" ty_name
      else
        "Default::default()"

(* Special type printing for FFI - convert slices to raw pointers *)
let name_rust_type_ffi ty = 
  match ty with
  | Tslice(_, elem_ty, origin) ->
      ptr_type_string origin elem_ty
  | _ -> name_rust_type ty

(* FFI-safe version of name_rust_decl_fn for extern "C" functions *)
let name_rust_decl_fn_ffi id ty =
  match ty with
  | Tfunction( _, _, args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b ("_ : " ^ name_rust_type_ffi t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      let result_str = match res with
        | Tunit -> ""
        | _ -> " -> " ^ name_rust_type_ffi res
      in
      "fn " ^ (Buffer.contents b) ^ result_str
  | _ -> name_rust_decl_fn id ty

(* TODO: print expressions and statements *)

let name_function_parameters name_param fun_name params cconv name_origins rels = 
    let b = Buffer.create 20 in 
    Buffer.add_string b fun_name;
    
    (* add a helper function to check if params contain reference type *)
    let rec has_reference_param = function
    | [] -> false
    | (_, ty) :: rem ->
        let rec check_type t = match t with
        | Rusttypes.Treference _ -> true
        | Rusttypes.Tfunction(_, _, args, _, _) -> check_args args
        | _ -> false
        and check_args = function
        | Rusttypes.Tnil -> false
        | Rusttypes.Tcons(t, rest) -> check_type t || check_args rest
        in
        check_type ty || has_reference_param rem
    in
    
    (* only when params contain reference type, add lifetime parameter *)
    if has_reference_param params then
        Buffer.add_string b "<'a>";
    
    Buffer.add_char b '(';
    begin match params with 
    | [] -> 
        Buffer.add_string b (if cconv.cc_vararg <> None then "..." else "") 
    | _ -> 
        let rec add_params first = function 
        | [] -> 
            if cconv.cc_vararg <> None then Buffer.add_string b ",..." 
        | (id, ty) :: rem -> 
            if not first then Buffer.add_string b ", "; 
            Buffer.add_string b ("mut "^(name_param id)^": "^(name_rust_decl_fn_arg "" ty)); 
            add_params false rem in 
        add_params true params 
    end;
    Buffer.add_char b ')'; 
    Buffer.add_string b "\n";
    Buffer.add_string b (origin_relations_string rels); 
    Buffer.contents b

let print_fundecl p id fd =
  match fd with
  | Ctypes.Internal f ->
      let linkage = if C2C.atom_is_static id then "static" else "extern" in
      fprintf p "%s %s;@ @ " linkage
                (name_rust_decl_fn (extern_atom id) (Rustsyntax.type_of_function f))
  | _ -> ()


let print_string_array p id ty il =
  (* Convert the list of Init_int8 to an OCaml string *)
  let s_buffer = Buffer.create (List.length il) in
  List.iter
    (fun init ->
      match init with
      | Init_int8 n ->
        let n_int32 = camlint_of_coqint n in
        (* Ignore the null terminator at the end of the string *)
        if n_int32 <> Int32.zero then
          Buffer.add_char s_buffer (Char.chr (Int32.to_int n_int32))
      | _ -> ()
    ) il;
  let str_content = Buffer.contents s_buffer in
  (* Store the string content in our hashtable with its identifier *)
  Hashtbl.add string_literals (extern_atom id) str_content;

  (* The original printing logic remains unchanged below *)
  let len = List.length il in
  fprintf p "[";
  List.iteri
    (fun i init ->
      match init with
      | Init_int8 n ->
        let n_int32 = camlint_of_coqint n in
        let c =
          if n_int32 = Int32.of_int 10 then "\\n"
          else if n_int32 = Int32.of_int 13 then "\\r"
          else if n_int32 = Int32.of_int 9 then "\\t"
          else if n_int32 = Int32.of_int 0 then "\\0"
          else if n_int32 = Int32.of_int 39 then "\\'"
          else if n_int32 >= Int32.of_int 32 && n_int32 <= Int32.of_int 126 then
            String.make 1 (Char.chr (Int32.to_int n_int32))
          else Printf.sprintf "\\x%02x" (Int32.to_int n_int32)
          in
        fprintf p "    b'%s' as i8" c;
          if i < len - 1 then fprintf p ",\n" else fprintf p "\n"
      | _ -> ()
    ) il;
  fprintf p "]"

let int32_unsigned_to_int64 n = 
  Int64.logand (Int64.of_int32 n) 0xFFFFFFFFL

let int8_unsigned_to_int64 n = 
  Int64.logand (Int64.of_int32 n) 0xFFL

let int16_unsigned_to_int64 n = 
  Int64.logand (Int64.of_int32 n) 0xFFFFL

let bool_to_u8 n = 
  if Int32.compare n 0l = 0 then 0l else 1l

let print_c_init = PrintCsyntax.print_init

let print_init p = function
  | Init_int64 n ->
      fprintf p "%Ld" (camlint64_of_coqint n)
  | other ->
      print_c_init p other

let print_rust_init p typ init = 
  match typ with 
  | Rusttypes.Traw_pointer(_, elem_ty) ->
      (match init with
       | Init_addrof(id, _ofs) ->
           let nm = extern_atom id in
           fprintf p "(Ptr::from_ref(&mut %s[..])).cast::<%s>()"
             nm (name_rust_type elem_ty)
       | _ ->
           print_init p init)
  | Rusttypes.Tint(Ctypes.I8, Ctypes.Unsigned) -> 
      (match init with
       | Init_int8 n ->
           let num = camlint_of_coqint n in
           fprintf p "0x%02Lx_u8" (int8_unsigned_to_int64 num)
       | _ ->
           print_init p init)
  | Rusttypes.Tint(Ctypes.I16, Ctypes.Unsigned) -> 
      (match init with
       | Init_int16 n ->
           let num = camlint_of_coqint n in
           fprintf p "0x%04Lx_u16" (int16_unsigned_to_int64 num)
       | _ ->
           print_init p init)
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) -> 
      (match init with
       | Init_int32 n ->
           let num = camlint_of_coqint n in
           fprintf p "0x%08Lx_u32" (int32_unsigned_to_int64 num)
       | _ ->
           print_init p init)
  | Rusttypes.Tint(Ctypes.IBool, Ctypes.Unsigned) -> 
      (match init with
       | Init_int8 n ->
           let num = camlint_of_coqint n in
           fprintf p "0x%02Lx_u8" (int8_unsigned_to_int64 (bool_to_u8 num))
       | _ ->
           print_init p init)
  | Rusttypes.Tlong(Ctypes.Signed) ->
      (match init with
       | Init_int64 n ->
           let num = Int64.to_string (camlint64_of_coqint n) in
           fprintf p "%si64" num
       | _ ->
           print_init p init)
  | Rusttypes.Tlong(Ctypes.Unsigned) ->
      (match init with
       | Init_int64 n ->
           let num = Z.to_string n in
           fprintf p "%su64" num
       | _ ->
           print_init p init)
  | _ -> 
      print_init p init

let rec print_zero_value p = function
  | Rusttypes.Tint(Ctypes.I8, Ctypes.Unsigned) ->
      fprintf p "0x00_u8"
  | Rusttypes.Tint(Ctypes.I8, Ctypes.Signed) ->
      fprintf p "0x00_i8"
  | Rusttypes.Tint(Ctypes.I16, Ctypes.Unsigned) ->
      fprintf p "0x0000_u16"
  | Rusttypes.Tint(Ctypes.I16, Ctypes.Signed) ->
      fprintf p "0x0000_i16"
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) ->
      fprintf p "0u32"
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Signed) ->
      fprintf p "0"
  | Rusttypes.Tint(Ctypes.IBool, _) ->
      fprintf p "0"
  | Rusttypes.Tlong(Ctypes.Signed) ->
      fprintf p "0i64"
  | Rusttypes.Tlong(Ctypes.Unsigned) ->
      fprintf p "0u64"
  | Rusttypes.Tfloat(Ctypes.F32) ->
      fprintf p "0.0f32"
  | Rusttypes.Tfloat(Ctypes.F64) ->
      fprintf p "0.0f64"
  | Rusttypes.Traw_pointer _ ->
      fprintf p "Ptr::null()"
  | Rusttypes.Tslice(_, elem_ty, _) ->
      fprintf p "Ptr::<%s>::null()" (name_rust_type elem_ty)
  | Rusttypes.Tarray(_, elem_ty, sz) ->
      let count = Int32.to_int (camlint_of_coqint sz) in
      fprintf p "[";
      for i = 0 to count - 1 do
        if i > 0 then fprintf p ", ";
        print_zero_value p elem_ty
      done;
      fprintf p "]"
  | Rusttypes.Tstruct(orgs, name) ->
      let struct_name = extern_atom name in
      (* If we know the fields of this struct, synthesize a literal
         using field-wise zero values to avoid calling Default::default()
         in a static initializer (which is not const). *)
      let ty_name = struct_name ^ print_origins orgs in
      begin match Hashtbl.find_opt struct_field_table struct_name with
      | Some fields ->
          fprintf p "%s {@ " ty_name;
          let rec loop first = function
            | [] -> ()
            | (fname, fty) :: tl ->
                if not first then fprintf p ",@ ";
                fprintf p "%s: " fname;
                print_zero_value p fty;
                loop false tl
          in
          loop true fields;
          fprintf p "@;<0 -2>}"
      | None ->
          fprintf p "%s::default()" ty_name
      end
  | ty ->
      fprintf p "%s::default()" (name_rust_type ty)

(* Skip leading Init_space items when consuming initializers. *)
let rec drop_spaces = function
  | Init_space _ :: tl -> drop_spaces tl
  | lst -> lst

let rec print_value_with_inits ty p il =
  match ty with
  | Rusttypes.Tarray(_, elem_ty, sz) ->
      let count = Int32.to_int (camlint_of_coqint sz) in
      fprintf p "[@ ";
      let rec loop idx remaining =
        if idx = count then remaining
        else begin
          let remaining' = drop_spaces remaining in
          match remaining' with
          | [] ->
              if idx > 0 then fprintf p ",@ ";
              print_zero_value p elem_ty;
              loop (idx + 1) []
          | (Init_addrof _ :: _)
            when (match elem_ty with
                  | Rusttypes.Tint _ | Rusttypes.Tlong _ | Rusttypes.Tfloat _ -> true
                  | _ -> false) ->
              (* 数组元素是标量，但遇到 &__stringlit_* 之类的地址 ——
                 说明后续初始值属于下一个字段，立即停止消费并用 0 填充余下元素。 *)
              if idx > 0 then fprintf p ",@ ";
              for _j = idx to count - 1 do
                if _j > idx then fprintf p ",@ ";
                print_zero_value p elem_ty
              done;
              remaining (* 不消耗，留给后续字段 *)
          | (Init_int32 _ :: _)
            when (match elem_ty with Rusttypes.Tint(Ctypes.I8, _) -> true | _ -> false) ->
              (* 典型于 sha3：u8 数组后面紧跟下一个结构体的 i32 字段（mdlen）。
                 一旦看见 i32，停止消费，余下位置补 0。 *)
              if idx > 0 then fprintf p ",@ ";
              for _j = idx to count - 1 do
                if _j > idx then fprintf p ",@ ";
                print_zero_value p elem_ty
              done;
              remaining
          | _ ->
              if idx > 0 then fprintf p ",@ ";
              let next = print_value_with_inits elem_ty p remaining' in
              loop (idx + 1) next
        end
      in
      let rest = loop 0 il in
      fprintf p "@;<0 -2>]";
      rest
  | Rusttypes.Tstruct(_, name) ->
      (* 支持形如 Init_struct 子列表的按字段消费；若没有包装，则退化为顺序消费 *)
      let struct_name = extern_atom name in
      let fields =
        try Hashtbl.find struct_field_table struct_name
        with Not_found -> []
      in
      let field_inits = il in
      fprintf p "%s {@ " struct_name;
      let rec take_first_addrof acc = function
        | [] -> None
        | Init_addrof(id, _ofs) :: tl -> Some (id, List.rev acc @ tl)
        | x :: tl -> take_first_addrof (x :: acc) tl
      in
      let rec loop first remaining fields =
        match fields with
        | [] -> remaining
        | (fname, fty) :: tl ->
            if not first then fprintf p ",@ ";
            fprintf p "%s: " fname;
            let next =
              match fty with
              | Rusttypes.Traw_pointer(_, elem_ty)
              | Rusttypes.Tslice(_, elem_ty, _) ->
                  begin match drop_spaces remaining with
                  | Init_addrof(id, _ofs) :: rem ->
                      let nm = extern_atom id in
                      fprintf p "(Ptr::from_ref(&mut %s[..])).cast::<%s>()"
                        nm (name_rust_type elem_ty);
                      (* 把前缀空洞与 addrof 一起消费掉（只保留其余部分） *)
                      let _ = remaining in
                      rem
                  | _ ->
                      (* 容错：若当前不是 addrof，但后续有，把第一个 addrof 拿来作为该字段 *)
                      begin match take_first_addrof [] remaining with
                      | Some (id, rem) ->
                          let nm = extern_atom id in
                          fprintf p "(Ptr::from_ref(&mut %s[..])).cast::<%s>()"
                            nm (name_rust_type elem_ty);
                          rem
                      | None ->
                          (* 退化为默认值，避免把 addrof 错塞进后续数组 *)
                          fprintf p "%s::default()" (name_rust_type fty);
                          remaining
                      end
                  end
              | _ -> print_value_with_inits fty p remaining
            in
            loop false next tl
      in
      let remaining = loop true field_inits fields in
      fprintf p "@;<0 -2>}";
      remaining
  | Rusttypes.Traw_pointer(_, elem_ty) ->
      (* 处理指针字段的地址常量初始化（如 char* 指向字符串常量） *)
      (match il with
       | Init_addrof(id, _ofs) :: rest ->
           let nm = extern_atom id in
           fprintf p "(Ptr::from_ref(&mut %s[..])).cast::<%s>()"
             nm (name_rust_type elem_ty);
           rest
       | init :: rest ->
           (* 回退到通用初始化打印 *)
           print_rust_init p ty init; rest
       | [] -> il)
  | _ ->
      (match il with
       | Init_space _ :: rest ->
           print_value_with_inits ty p rest
       | init :: rest ->
           print_rust_init p ty init;
           rest
       | [] -> il)

let print_composite_init_rust var_info p il =
  ignore (print_value_with_inits var_info p il)

let print_globvar p id v =
  let name1 = extern_atom id in
  (* Use 'static mut' for string literals so they can be referenced *)
  let is_string_literal = Str.string_match re_string_literal name1 0 in
  let name2 =
    if is_string_literal then
      "static mut " ^ name1
    else if v.gvar_readonly then
      "const " ^ name1
    else
      "static mut " ^ name1
  in
  let name3 = name2 ^ " : " in
  match v.gvar_init with
  | [] ->
      (* Extern variables with no initialization are already printed in print_globvardecl *)
      (* Don't print them again here to avoid duplication *)
      ()
  | [Init_space _] ->
      (* Uninitialized arrays need default initialization in Rust *)
      (match v.gvar_info with
       | Rusttypes.Tarray(mut, elem_ty, sz) ->
           let sz_val = camlint_of_coqint sz in
           (* Use literal zero for numeric types instead of ::default() *)
           let default_val = match elem_ty with
             | Rusttypes.Tint(_, _) -> "0"
             | Rusttypes.Tlong(_) -> "0"
             | Rusttypes.Tfloat(_) -> "0.0"
             | _ -> (name_rust_type elem_ty) ^ "::default()"
           in
           fprintf p "static mut %s : [%s; %ld] = [%s; %ld];@ @ "
             name1
             (name_rust_type elem_ty)
             sz_val
             default_val
             sz_val
       | _ ->
           fprintf p "%s = %s;@ @ "
                   (name_rust_decl_fn_arg name3 v.gvar_info)
                   (default_expr_for_type v.gvar_info))
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_rust_decl_fn_arg name3 v.gvar_info);
      begin
        (* For globals whose type contains pointers, we cannot faithfully
           translate their C initializers into Rust constant expressions
           (because they require calls like Ptr::from_ref / cast, which
           are not const).  For these, emit a zero / null initializer
           here and reconstruct the real value at runtime in
           __init_globals(). *)
        let is_pointer_global =
          is_pointer_global_name name1 && v.gvar_init <> []
        in
        if is_pointer_global then
          print_zero_value p v.gvar_info
        else
          match v.gvar_info, v.gvar_init with
          | (Rusttypes.Tint _ | Rusttypes.Tlong _ | Rusttypes.Tfloat _ | Tfunction _),
            [i1] ->
              print_rust_init p v.gvar_info i1
          | var_info, il ->
              if is_string_literal
              && List.for_all (function Init_int8 _ -> true | _ -> false) il
              then print_string_array p id v.gvar_info il
              else match var_info with
                   | Rusttypes.Traw_pointer _ ->
                       fprintf p "Box::new(%a)" (print_composite_init_rust var_info) il
                   | _ ->
                       print_composite_init_rust var_info p il
      end;
      fprintf p ";@]@ @ "

let print_globvardecl p id v =
  let name = extern_atom id in
  let linkage = if C2C.atom_is_static id then "static" else "extern" in
  (* Only print declaration for extern variables with no initialization *)
  if linkage = "extern" && v.gvar_init = [] then
    (* Rust extern variables must be in extern "C" block and use 'static' keyword *)
    let mutability = if v.gvar_readonly then "" else "mut " in
    (* FFI-safe extern variable types.
       Extern pointer globals (e.g., stdout/stderr pointers) are raw pointers in C.
       Declaring them as our `Ptr<T>` wrapper would be ABI-incompatible and can
       cause runtime crashes when passed to libc. *)
    let type_str =
      match v.gvar_info with
      | Rusttypes.Tslice(mutk, elem_ty, _) ->
          let elem_str = name_rust_type elem_ty in
          (match mutk with
           | Rusttypes.Mutable -> "*mut " ^ elem_str
           | Rusttypes.Immutable -> "*const " ^ elem_str)
      | Rusttypes.Traw_pointer(mutk, elem_ty) ->
          let elem_str = name_rust_type elem_ty in
          (match mutk with
           | Rusttypes.Coq_mutable -> "*mut " ^ elem_str
           | Rusttypes.Coq_const -> "*const " ^ elem_str)
      | _ ->
          name_rust_type v.gvar_info
    in
    fprintf p "extern \"C\" { static %s%s : %s; }@ @ " 
      mutability
      name
      type_str
  else
    (* For static variables or extern with init, don't print declaration here - will be printed in print_globvar *)
    ()

let print_globdecl p (id,gd) =
  match gd with
  | Gfun f -> print_fundecl p id f
  | Gvar v -> print_globvardecl p id v

let struct_or_variant = function Struct -> "struct" | TaggedUnion -> "variant"

let declare_composite p (Composite(id, su, m, orgs, rels)) =
  fprintf p "%s %s%s %s;@ " (struct_or_variant su) (extern_atom id) (print_origins orgs) (origin_relations_string rels)

(* let print_member p = function
  | Member_plain(id, ty) ->
      fprintf p "@ %s;" (name_rust_decl (extern_atom id) ty) *)

(* let define_composite p (Composite(id, su, m, orgs, rels)) =
  fprintf p "@[<v 2>%s %s%s %s{"
          (struct_or_variant su) (extern_atom id) (print_origins orgs) (origin_relations_string rels);
  List.iter (print_member p) m;
  fprintf p "@;<0 -2>};@]@ @ " *)
let rec type_has_pointer ty =
  match ty with
  | Rusttypes.Tslice(_, _, _)
  | Rusttypes.Traw_pointer(_, _)
  | Rusttypes.Tstruct(_, _)
  | Rusttypes.Tvariant(_, _) -> true
  | Rusttypes.Tarray(_, elem_ty, _) -> type_has_pointer elem_ty
  | _ -> false

let rec type_has_function ty =
  match ty with
  | Rusttypes.Tfunction(_, _, _, _, _) -> true
  | Rusttypes.Tslice(_, elem_ty, _)
  | Rusttypes.Traw_pointer(_, elem_ty)
  | Rusttypes.Tarray(_, elem_ty, _)
  | Rusttypes.Treference(_, _, elem_ty)
  | Rusttypes.Tbox elem_ty -> type_has_function elem_ty
  | _ -> false

let rec type_contains_array ty =
  match ty with
  | Rusttypes.Tarray(_, _, _) -> true
  | Rusttypes.Tslice(_, elem_ty, _)
  | Rusttypes.Traw_pointer(_, elem_ty)
  | Rusttypes.Treference(_, _, elem_ty)
  | Rusttypes.Tbox elem_ty -> type_contains_array elem_ty
  | _ -> false

(* Collect all globals whose types contain pointers and that have a
   non-trivial initializer.  These will be re-initialized at runtime in
   __init_globals to avoid using non-const pointer operations in
   static initializers. *)
let collect_pointer_globals defs =
  reset_pointer_globals ();
  List.iter
    (fun (id, gd) ->
       match gd with
       | Gvar v ->
           let name1 = extern_atom id in
           let is_string_literal = Str.string_match re_string_literal name1 0 in
           let has_real_init =
             match v.gvar_init with
             | [] -> false
             | [Init_space _] -> false
             | _ -> true
           in
           if (not is_string_literal)
              && has_real_init
              && type_has_pointer v.gvar_info
           then
             register_pointer_global name1 v.gvar_info v.gvar_init
       | _ -> ())
    defs

let print_global_initializers p =
  let inits = List.rev !pointer_global_inits in
  match inits with
  | [] -> ()
  | _ ->
      fprintf p "@[<v 2>unsafe fn __init_globals() {@ ";
      List.iter
        (fun (name, ty, il) ->
           fprintf p "@[<v 2>%s = " name;
           print_composite_init_rust ty p il;
           fprintf p ";@]@ ")
        inits;
      fprintf p "@;<0 -2>}@]@ @ "

let print_member p = function
  | Member_plain(id, ty) ->
      (* For struct members with references, use raw pointers to avoid lifetime requirements *)
      fprintf p "pub %s: %s," (extern_atom id) (name_rust_type ty)

let define_composite p (Composite(id, su, m, orgs, rels)) =
  let fields =
    match su with
    | Rusttypes.Struct ->
        let collected =
          List.fold_left (fun acc member ->
              match member with
              | Member_plain(fid, ty) -> (extern_atom fid, ty) :: acc)
            [] m
          |> List.rev
        in
        Hashtbl.replace struct_field_table (extern_atom id) collected;
        collected
    | Rusttypes.TaggedUnion -> []
  in
  let has_pointer_member =
    List.exists (function Member_plain(_, ty) -> type_has_pointer ty) m
  in
  let has_function_member =
    List.exists (function Member_plain(_, ty) -> type_has_function ty) m
  in
  let has_array_member =
    List.exists (function Member_plain(_, ty) -> type_contains_array ty) m
  in
  let need_manual_default =
    match su with
    | Rusttypes.Struct -> has_array_member
    | Rusttypes.TaggedUnion -> false
  in
  let base_derive =
    match su with
    | Rusttypes.Struct ->
        if has_function_member then
          ["Clone"]
        else if has_pointer_member then
          ["Default"; "Clone"]
        else
          ["Default"; "Copy"; "Clone"]
    | Rusttypes.TaggedUnion -> ["Copy"; "Clone"]
  in
  let derive_traits =
    if need_manual_default then
      List.filter (fun trait -> trait <> "Default") base_derive
    else
      base_derive
  in
  let derive_macro =
    match derive_traits with
    | [] -> None
    | _ -> Some ("#[derive(" ^ String.concat ", " derive_traits ^ ")]")
  in
  let keyword =
    match su with
    | Rusttypes.Struct -> "struct"
    | Rusttypes.TaggedUnion -> "union"
  in
  match keyword, derive_macro with
  | "", None -> ()
  | keyword, Some derive ->
      fprintf p "@[<v 2>%s@,pub %s %s%s %s {"
        derive
        keyword
        (extern_atom id) (print_origins orgs) (origin_relations_string rels);
      List.iter (fun member -> fprintf p "@,%a" print_member member) m;
      fprintf p "@;<0 -2>}@]@ @ ";
      (match su with
       | Rusttypes.Struct ->
           if need_manual_default then begin
             fprintf p "@[<v 2>impl Default for %s%s %s {@ "
               (extern_atom id) (print_origins orgs) (origin_relations_string rels);
             fprintf p "fn default() -> Self {@ ";
             fprintf p "@[<v 2>Self {@ ";
             List.iter
               (fun (fname, fty) ->
                  let ty_name = name_rust_type fty in
                  let expr =
                    if String.length ty_name >= 13 && String.sub ty_name 0 13 = "extern \"C\" fn"
                    then Printf.sprintf "unsafe { std::mem::MaybeUninit::<%s>::zeroed().assume_init() }" ty_name
                    else default_expr_for_type fty
                  in
                  fprintf p "@,%s: %s," fname expr)
               fields;
             fprintf p "@;<0 -2>}@]@ ";
             fprintf p "}@;<0 -2>}@]@ @ "
           end
       | Rusttypes.TaggedUnion ->
           (* Rust union 不支持 derive(Default)，但 C 代码里经常需要“有个初值”来满足
              Rust 的 definite-init（随后立刻写入某个 union 字段）。这里统一为 union
              生成一个 Default：选择第一个字段作为 active field，并用其零值初始化。 *)
           (match m with
            | Member_plain(fid, fty) :: _ ->
                let field_name = extern_atom fid in
                let expr =
                  let ty_name = name_rust_type fty in
                  if String.length ty_name >= 13 && String.sub ty_name 0 13 = "extern \"C\" fn"
                  then Printf.sprintf "unsafe { std::mem::MaybeUninit::<%s>::zeroed().assume_init() }" ty_name
                  else default_expr_for_type fty
                in
	                fprintf p "@[<v 2>impl Default for %s%s %s {@ "
	                  (extern_atom id) (print_origins orgs) (origin_relations_string rels);
	                fprintf p "fn default() -> Self {@ ";
	                fprintf p "Self { %s: %s }" field_name expr;
	                fprintf p "}@;<0 -2>}@]@ @ "
	            | [] ->
	                () ))
  | _ -> ()
