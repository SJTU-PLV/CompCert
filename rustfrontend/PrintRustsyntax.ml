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
]
(* Create a hashtable to store string literals *)
let string_literals : (string, string) Hashtbl.t = Hashtbl.create 101

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

let print_origin_as_lifetime a =
  try
    Hashtbl.find string_of_atom a
  with Not_found ->
    Printf.sprintf "'a" 

let rec print_origins_aux (orgs : origin list) =
  match orgs with
  | [] -> ""
  | org :: orgs' -> print_origin_as_lifetime org ^ ", " ^ print_origins_aux orgs'

let print_origins (orgs : origin list) =
  match orgs with
  | [] -> ""
  | _ -> "<" ^ print_origins_aux orgs^ ">"
  
let rec origin_relations_string_aux (rels: origin_rel list) =
  match rels with
  | [] -> ""
  | (org1, org2) :: rels' -> 
    print_origin_as_lifetime org1 ^ ": " ^ print_origin_as_lifetime org2 ^ ", " ^ origin_relations_string_aux rels'

let origin_relations_string (rels: origin_rel list) =
  match rels with
  | [] -> ""
  | _ ->
    "where " ^ origin_relations_string_aux rels

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
      let has_lifetime = ref false in
      let rec check_args = function
      | Tnil -> ()
      | Tcons(t1, tl) ->
          (match t1 with
          | Rusttypes.Treference(_, _, _) -> has_lifetime := true
          | _ -> check_nested t1);
          check_args tl
      and check_nested t = match t with
      | Tfunction(_, _, a, r, c) -> check_args a
      | _ -> ()
      in
      check_args args;
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      if !has_lifetime then Buffer.add_string b "<'a>";
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg <> None then "..." else "void")
          else if cconv.cc_vararg <> None then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_rust_decl "" t1);
          add_args false tl in
      if not cconv.cc_unproto then add_args true args;
      Buffer.add_char b ')';
      name_rust_decl (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      "struct" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Tvariant(orgs, name) ->
      "variant" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Traw_pointer(mut, ty) ->
    "*" ^ string_of_pmut mut ^ (name_rust_decl ""  ty) ^ name_optid id
  | Tarray(mut, ty, sz) ->
    (* string_of_mut mut ^ " "^ *)
    name_rust_decl (sprintf "%s[%ld]" id (camlint_of_coqint sz)) ty
  | Tslice(mut, ty) ->
    "&" ^ string_of_mut mut ^ " [" ^ (name_rust_decl ""  ty) ^ "]" ^ name_optid id

let rec name_rust_decl_var id ty =
  match ty with
  | Rusttypes.Tunit ->
    name_optid_no_space id ^ "i32 /*this is unit */"
  | Rusttypes.Tvoid ->
    name_optid_no_space id ^ "std::ffi::c_void"    
  | Rusttypes.Tint(sz, sg) ->
    name_optid_no_space id ^ name_inttype sz sg
  | Rusttypes.Tfloat(sz) ->
    name_optid_no_space id  ^ name_floattype sz
  | Rusttypes.Tlong(sg) ->
    name_optid_no_space id ^ name_longtype sg
  | Rusttypes.Treference(org, mut, t) ->
    name_optid_no_space id ^ "&" ^  string_of_mut mut ^ (name_rust_decl ""  t)
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
      "fn" ^ name_rust_decl_var (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      "struct" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Tvariant(orgs, name) ->
      "variant" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
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
  | Tslice(mut, ty) ->
    "&" ^ string_of_mut mut ^ " [" ^ (name_rust_decl ""  ty) ^ "]" ^ name_optid id

let rec name_rust_decl_fn_arg id ty =
  match ty with
  | Rusttypes.Tunit ->
    name_optid_no_space id ^ "i32 /*this is unit */"
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
      "fn" ^ name_rust_decl_fn_arg (Buffer.contents b) res
  | Tstruct(orgs, name) ->
      "struct" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Tvariant(orgs, name) ->
      "variant" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
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
  | Tslice(mut, ty) ->
     name_optid_no_space id ^ "&" ^ string_of_mut mut ^ " [" ^ (name_rust_decl ""  ty) ^ "]"

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
  | Rusttypes.Treference(org, mut, t) ->
      name_optid id ^ " -> " ^ "&" ^ (print_origin_as_lifetime org) ^" "^  string_of_mut mut ^ (name_rust_decl ""  t)
  | Tbox(t) ->
      name_optid id ^ " -> " ^ "Box<" ^ (name_rust_decl ""  t) ^ ">"
  | Tfunction( _, _, args, res, cconv) ->
      let has_lifetime = ref false in
      let rec check_args = function
      | Tnil -> ()
      | Tcons(t1, tl) ->
          (match t1 with
          | Rusttypes.Treference(_, _, _) -> has_lifetime := true
          | _ -> check_nested t1);
          check_args tl
      and check_nested t = match t with
      | Tfunction(_, _, a, r, c) -> check_args a
      | _ -> ()
      in
      check_args args;
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      if !has_lifetime then Buffer.add_string b "<'a>";
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
      "struct" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Tvariant(orgs, name) ->
      "variant" ^ print_origins orgs ^ " " ^ extern_atom name ^ name_optid id
  | Traw_pointer(pmut, ty) ->
      name_optid id ^ " -> " ^ "*" ^ string_of_pmut pmut ^ (name_rust_decl ""  ty)
  | Tarray(mut, ty, sz) ->
    (* string_of_mut mut ^ " "^ *)
    name_rust_decl (sprintf "%s[%ld]" id (camlint_of_coqint sz)) ty
  | Tslice(mut, ty) ->
    name_optid id ^ " -> " ^ "&" ^ string_of_mut mut ^ " [" ^ (name_rust_decl ""  ty) ^ "]"
(* Type *)

let name_rust_type ty = name_rust_decl "" ty

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
            Buffer.add_string b ((name_param id)^": "^(name_rust_decl_fn_arg "" ty)); 
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

let print_rust_init p typ init = 
  match typ with 
  | Rusttypes.Tint(Ctypes.I8, Ctypes.Unsigned) -> 
      let num = camlint_of_coqint (match init with Init_int8 n -> n | _ -> assert false) in 
      fprintf p "0x%02Lx_u8" (int8_unsigned_to_int64 num)
  | Rusttypes.Tint(Ctypes.I16, Ctypes.Unsigned) -> 
      let num = camlint_of_coqint (match init with Init_int16 n -> n | _ -> assert false) in 
      fprintf p "0x%04Lx_u16" (int16_unsigned_to_int64 num)
  | Rusttypes.Tint(Ctypes.I32, Ctypes.Unsigned) -> 
      let num = camlint_of_coqint (match init with Init_int32 n -> n | _ -> assert false) in 
      fprintf p "0x%08Lx_u32" (int32_unsigned_to_int64 num)
  | Rusttypes.Tint(Ctypes.IBool, Ctypes.Unsigned) -> 
      let num = camlint_of_coqint (match init with Init_int8 n -> n | _ -> assert false) in 
      fprintf p "0x%02Lx_u8" (int8_unsigned_to_int64 (bool_to_u8 num))
  | _ -> 
      print_init p init

let print_composite_init_rust var_info p il = 
  match var_info with 
  | Rusttypes.Tarray(mut, elem_ty, sz) -> 
    fprintf p "[@ "; 
    let last_index = List.length il - 1 in 
    List.iteri (fun idx i -> 
      print_rust_init p elem_ty i;
      match i with 
      | Init_space _ -> () 
      | _ -> 
          if idx < last_index then 
            fprintf p ",@ " 
    ) il; 
    fprintf p "]"
  | _ -> 
    fprintf p "{@ "; 
    List.iter 
      (fun i -> 
        print_init p i; 
        match i with Init_space _ -> () | _ -> fprintf p ",@ ") 
      il; 
    fprintf p "}"

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  let name3 = name2 ^ " : " in
  match v.gvar_init with
  | [] ->
      fprintf p "extern %s;@ @ "
              (name_rust_decl_fn_arg name3 v.gvar_info)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_rust_decl_fn_arg name3 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_rust_decl_fn_arg name3 v.gvar_info);
      begin match v.gvar_info, v.gvar_init with
      | (Rusttypes.Tint _ | Rusttypes.Tlong _ | Rusttypes.Tfloat _ | Tfunction _),
        [i1] ->
          print_rust_init p v.gvar_info i1
      | var_info, il ->
          if Str.string_match re_string_literal (extern_atom id) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) il
          (* FIX IS HERE: Pass 'id' directly, not 'extern_atom id' *)
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
  let name = if v.gvar_readonly then "const "^name else name in
  let linkage = if C2C.atom_is_static id then "static" else "extern" in
  fprintf p "%s %s;@ @ " linkage (name_rust_decl name v.gvar_info)

let print_globdecl p (id,gd) =
  match gd with
  | Gfun f -> print_fundecl p id f
  | Gvar v -> print_globvardecl p id v

(* TODO *)
(* let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v *)

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
let print_member p = function
  | Member_plain(id, ty) ->
      fprintf p "pub %s: %s," (extern_atom id) (name_rust_type ty)

let define_composite p (Composite(id, su, m, orgs, rels)) =
  let (keyword, derive_macro) =
    match su with
    | Rusttypes.Struct      -> ("struct", Some "#[derive(Default, Copy, Clone)]")
    | Rusttypes.TaggedUnion -> ("union",  Some "#[derive(Copy, Clone)]")
  in
  match keyword, derive_macro with
  | "", None -> ()
  | keyword, Some derive ->
      fprintf p "@[<v 2>%s@,pub %s %s%s %s {"
        derive
        keyword
        (extern_atom id) (print_origins orgs) (origin_relations_string rels);
      List.iter (fun member -> fprintf p "@,%a" print_member member) m;
      (* 修正结尾：只在有成员时才添加换行符，然后打印右括号 *)
      if m <> [] then fprintf p "@,";
      fprintf p "}@];@ @ "
  | _ -> ()
