
type id = string

exception Parse_error of Lexing.position * Lexing.position * string

let dummy_origin_str = "'0"

let wildcard_id = "_"

type ty = | Tunit
          | Tint of Ctypes.intsize * Ctypes.signedness
          | Tlong of Ctypes.signedness
          | Tfloat of Ctypes.floatsize
          | Tfunction of (ty list) * ty * id list * (id * id) list
          | Tbox of ty
          | Tadt of id * Ctypes.attr * id list
          | Treference of ty * id * Rusttypes.mutkind

type struct_or_enum =
  | Struct
  | Enum
let bool_ty = Tint (Ctypes.IBool, Ctypes.Unsigned)

type expr = Eunit
          | Eval of Values.coq_val * ty
          | Evar of id
          | Ebox of expr                                 (** Box(expr) *)
          | Efield of expr * id                          (** expr.id *)
          | Eaccess of id * id                           (** expr::id *)
          | Ederef of expr                               (** *expr *)
          | Eref of expr * Rusttypes.mutkind
          | Eunop of Cop.unary_operation * expr
          | Estruct of id * id list * expr list          (** A {a: 1, b: 2} *)
          | Ebinop of Cop.binary_operation * expr * expr
          | Eassign of expr * expr
          | Ecall of expr * expr list
          | Estr of string

type ref_mut = RefMut | RefImmut

type pat = Pconstructor of id * id * (pat list)
         | Pbind of (ref_mut option * id)

type ident = AST.ident

type pat' = Pconstructor' of ident * ident * (pat' list)
          | Pbind' of (ref_mut option * ident)


and stmt = Sskip
          | Sdo of expr
          | Slet of id * ty * expr option
          | Slet2 of id * expr
          | Ssequence of stmt * stmt
          | Sifthenelse of expr * stmt * stmt
          | Swhile of expr * stmt
          | Sloop of stmt
          | Sbreak
          | Scontinue
          | Sreturn of expr option
          | Smatch of expr * case list
          | Sscope of stmt

and case = { pattern: pat
            ; body: stmt }

type case' = { pattern': pat'; body': Rustsyntax.statement }

type fn = { generic_origins: id list
          ; origin_relations: (id * id) list
          ; return: ty
          ; params: (id * ty) list
          ; body: stmt }

(* function declarations *)
type fn_decl = { generic_origins: id list
              ; origin_relations: (id * id) list
              ; return: ty
              ; params: (id * ty) list }

type comp_struc = (id * ty) list

type comp_enum = (id * (ty list)) list

type comp_enum' = (ident * (Rusttypes.coq_type list)) list

let get_enum_variant_ids (enum: comp_enum) : id list =
  List.map fst enum

module IdMap = Map.Make (struct
    type t = id
    let compare = String.compare
end)

let mk_fn (generic_origins: id list) (origin_relations: (id * id) list)
    (return: ty) (params: (id * ty) list) (body: stmt) : fn =
  { generic_origins
  ; origin_relations = origin_relations
  ; return
  ; params
  ; body
  }

let mk_fn_decl (generic_origins: id list) (origin_relations: (id * id) list)
    (return: ty) (params: (id * ty) list) : fn_decl =
  { generic_origins
  ; origin_relations = origin_relations
  ; return
  ; params
  }

let mk_fn_ty (params: ty list) (return: ty) (generic_origins: id list)
    (origin_relations: (id * id) list) : ty =
  Tfunction (params, return, generic_origins, origin_relations)
module IdentMap = Map.Make (struct
    type t = ident
    let compare = Camlcoq.P.compare
end)

type prog_item = Pfn of id * fn
               | Pfn_decl of id * fn_decl
               | Pstruc of id * comp_struc * id list * (id * id) list
               | Penum of id * comp_enum * id list * (id * id) list
               | Pcomp_decl of id * struct_or_enum * id list * (id * id) list

type prog = { funcs: (id * fn) list
            ; strucs: (id * comp_struc * id list * (id * id) list) list
            ; enums: (id * comp_enum * id list * (id * id) list) list 
            ; composite_decls: (id * struct_or_enum * id list * (id * id) list) list
            ; fun_decls: (id * fn_decl) list
            }

let rec prog_of_items (pis: prog_item list): prog = match pis with
  | (Pfn (x, f))::pis ->
    let p = prog_of_items pis in
    { p with funcs = (x, f)::p.funcs }
  | (Pstruc (x, c, orgs, rels))::pis ->
    let p = prog_of_items pis in
    { p with strucs = (x, c, orgs, rels)::p.strucs }
  | (Penum (x, c, orgs, rels)) :: pis ->
    let p = prog_of_items pis in
    { p with enums = (x, c, orgs, rels) :: p.enums }
  | (Pcomp_decl(x, s_or_e, orgs, rels)) :: pis ->
    let p = prog_of_items pis in    
    { p with composite_decls = (x, s_or_e, orgs, rels) :: p.composite_decls}
  | Pfn_decl (x, f) :: pis ->
    let p = prog_of_items pis in
    { p with fun_decls = (x, f) :: p.fun_decls}
  | nil -> { funcs = []; strucs = []; enums = []; composite_decls = []; fun_decls = [] }

module To_syntax = struct

  let infer_composite_decls (p: prog) =
    (* Struct/enum definitions implicitly serve as forward declarations so
       mutually recursive composites do not require extra surface syntax. *)
    let from_struc (x, _, orgs, rels) = (x, Struct, orgs, rels) in
    let from_enum (x, _, orgs, rels) = (x, Enum, orgs, rels) in
    (List.map from_struc p.strucs) @ (List.map from_enum p.enums) @ p.composite_decls

  let noattr = Ctypes.noattr

  type state = { symmap: ident IdMap.t
               ; rev_symmap: id IdentMap.t
               ; local_types: Rusttypes.coq_type IdentMap.t
               ; next_ident: ident
               ; funcs: fn IdentMap.t
               (* Adhoc: used to record the information (type here) of the identities *)
               ; fun_decls: Rusttypes.coq_type IdentMap.t
               ; enums: comp_enum' IdentMap.t
               ; composites: Rusttypes.composite_definition IdentMap.t
               ; gvars: (ident * (Rusttypes.coq_type AST.globvar)) list 
               ; external_funs: (ident * (Rustsyntax.fundef, Rusttypes.coq_type) AST.globdef) list}

  type error = Efield_of_non_struct of Rusttypes.coq_type
             | Efield_not_found of id
             | Ederef_non_deref of Rusttypes.coq_type
             | Enot_callable of Rusttypes.coq_type
             | Eunop_type_error of Cop.unary_operation * Rusttypes.coq_type
             | Ebinop_type_error of Cop.binary_operation
                                      * Rusttypes.coq_type
                                      * Rusttypes.coq_type
             | Econstructor_alone of id * id
             | Econstructor_wrong_arity of ident * ident * int * int
             | Emulti_args_to_constructor of expr list * id * id
             | Enot_a_composite of id
             | Ename_not_found of id
             | Eno_variant of ident * ident
             | Enot_a_enum of Rusttypes.coq_type
             | Eduplicated_patterns

  let rec typelist_to_list (tl: Rusttypes.typelist)
    : (Rusttypes.coq_type list) =
    let module T = Rusttypes in
    match tl with
    | T.Tcons (t, tl) -> t::(typelist_to_list tl)
    | T.Tnil -> []


  let pp_print_origin (symmap: id IdentMap.t) pp (org: Rusttypes.origin) =
    Format.fprintf pp "%s" (IdentMap.find org symmap)

  let pp_print_origin_rel (symmap: id IdentMap.t) pp (rel: Rusttypes.origin_rel) =
    let (org1, org2) = rel in
    Format.fprintf pp "%s: %s" (IdentMap.find org1 symmap) (IdentMap.find org2 symmap)

  let pp_print_origins (symmap: id IdentMap.t) pp (orgs: Rusttypes.origin list) =
    match orgs with
    | [] -> ()
    | _ ->
      Format.fprintf pp "<@[<hov>%a@]>" (Format.pp_print_list ~pp_sep: (fun out () -> Format.fprintf out ",@ ") (pp_print_origin symmap)) orgs

  let pp_print_origin_relations (symmap: id IdentMap.t) pp (rels: Rusttypes.origin_rel list) =
    match rels with
    | [] -> ()
    | _ ->
      Format.fprintf pp "where @[<hov>%a@]" (Format.pp_print_list ~pp_sep: (fun out () -> Format.fprintf out ",@ ") (pp_print_origin_rel symmap)) rels


  let rec pp_print_rust_type (symmap: id IdentMap.t) pp (t: Rusttypes.coq_type)  =
    let open Format in
    let module T = Rusttypes in
    match t with
    | T.Tunit -> pp_print_string pp "()"
    | T.Tint (s, si) -> (
      match si with
      | Ctypes.Signed -> pp_print_string pp "int"
      | Ctypes.Unsigned -> pp_print_string pp "uint"
      );(
      match s with
      | Ctypes.I32 -> pp_print_string pp "32"
      | Ctypes.I16 -> pp_print_string pp "16"
      | Ctypes.I8 -> pp_print_string pp "8"
      | Ctypes.IBool -> pp_print_string pp "_bool"
      )
    | T.Tlong (si) -> (
      match si with
      | Ctypes.Signed -> pp_print_string pp "long"
      | Ctypes.Unsigned -> pp_print_string pp "ulong"
      )
    | T.Tfloat (si) ->
      pp_print_string pp "float"; 
      pp_print_string pp (match si with
      | Ctypes.F32 -> "32"
      | Ctypes.F64 -> "64")
    | T.Tfunction (orgs, rels, tl, r, _) ->
      Format.fprintf pp "fn%a(" (pp_print_origins symmap) orgs;
      pp_print_space pp ();
      let _ = List.map
          (fun t -> pp_print_rust_type symmap pp t ;
            pp_print_string pp ",";
            pp_print_space pp ())
          (typelist_to_list tl)
      in
      pp_print_string pp ")->";
      pp_print_space pp ();
      pp_print_rust_type symmap pp r;
      pp_print_origin_relations symmap pp rels
    | T.Tbox (t) ->
      pp_print_string pp "Box(";
      pp_print_rust_type symmap  pp t ;
      pp_print_string pp ")";
    | T.Tstruct (orgs, id) ->      
      pp_print_string pp (IdentMap.find id symmap);
      pp_print_origins symmap pp orgs
    | T.Tvariant (orgs, id) ->
      pp_print_string pp (IdentMap.find id symmap);
      pp_print_origins symmap pp orgs
    | T.Tadt (id) ->
      pp_print_string pp (IdentMap.find id symmap)
    | T.Treference (org, m, t) ->
      pp_print_string pp "&";
      (* print origin *)
      pp_print_string pp (Camlcoq.extern_atom org ^ " ");
      if m = T.Mutable then
        pp_print_string pp "mut ";
      pp_print_rust_type symmap pp t
    | T.Tarray (ty, sz) ->
      pp_print_rust_type symmap pp ty;
      Format.fprintf pp "[%ld]" (Camlcoq.camlint_of_coqint sz)


  let pp_print_unop pp (op: Cop.unary_operation) =
    let module O = Cop in
    let open Format in
    match op with
    | O.Onotbool -> pp_print_string pp "!"
    | O.Onotint -> pp_print_string pp "~"
    | O.Oabsfloat -> pp_print_string pp "abs"
    | O.Oneg -> pp_print_string pp "neg"

  let pp_print_binop pp (op: Cop.binary_operation) =
    let module O = Cop in
    let open Format in
    pp_print_string pp (match op with
    | O.Oadd -> "+" | O.Osub -> "-" | O.Omul -> "*" | O.Odiv -> "/"
    | O.Oand -> "&&" | O.Oor -> "||" | O.Oxor -> "^"
    | O.Oeq -> "==" | O.One -> "!=" | O.Olt -> "<" | O.Ogt -> ">"
    | O.Ole -> "<=" | O.Oge -> ">="
    | O.Oshl -> "<<" | O.Oshr -> ">>"
    | O.Omod -> "%"
    )

  let pp_print_symmap pp (symmap: id IdentMap.t) =
    IdentMap.iter
      (fun k v ->
         let open Format in
         pp_print_int pp (Camlcoq.P.to_int k);
         pp_print_string pp ": ";
         pp_print_string pp v;
         pp_print_string pp "\n"
      )
      symmap

  let pp_print_composite (symmap: id IdentMap.t) pp (c: Rusttypes.composite_definition) =
    let Rusttypes.Composite (i, s_or_v, members,orgs, rels) = c in
    let s_or_v =  match s_or_v with
      | Rusttypes.Struct -> "struct"
      | Rusttypes.TaggedUnion -> "enum"
    in
    let x = IdentMap.find i symmap in
    let rec pp_print_members pp ms =
      match ms with
      | (Rusttypes.Member_plain (i, t)) :: ms' ->
        let x = IdentMap.find i symmap in
        Format.fprintf pp "@ %s: %a,%a" x (pp_print_rust_type symmap) t pp_print_members ms'
      | [] -> ()
    in
    Format.fprintf pp "@[<v 2>%s %s%a %a {%a@;<0 -2>}@]@ @ " s_or_v x (pp_print_origins symmap) orgs (pp_print_origin_relations symmap) rels  pp_print_members members


  let rec pp_print_expr (symmap: id IdentMap.t) pp e =
    let open Format in
    let module S = Rustsyntax in
    let module T = Rusttypes in
    match e with
    | S.Eunit -> fprintf pp "()"
    | S.Eval (v, _) -> fprintf pp "<val>"
    | S.Estruct (i, fields, values, _) ->
      let rec pp_print_fields pp fvs =
        (match fvs with
        | f :: fs' , S.Econs (v, vs') ->
          let fx = IdentMap.find f symmap in
          fprintf pp "@ %s: %a,%a" fx (pp_print_expr symmap) v pp_print_fields (fs', vs')
        | [], S.Enil -> ()
        | _, _ -> failwith "unreachable (Estruct in pp_print_expr)")
      in
      let x = IdentMap.find i symmap in
      fprintf pp "@[<v 2>%s {%a@;<0 -2>}@]" x pp_print_fields (fields, values)
    | S.Eenum (ie, iv, e, _) ->
      let xe = IdentMap.find ie symmap in
      let xv = IdentMap.find iv symmap in
      fprintf pp "%s::%s(%a)" xe xv (pp_print_expr symmap) e
    | S.Evar (i, _) ->
      let x = IdentMap.find i symmap in
      pp_print_string pp x
    | S.Eglobal (i, _) ->
        let x = IdentMap.find i symmap in
        pp_print_string pp x
    | S.Ebox (e, _) ->
      fprintf pp "Box(%a)" (pp_print_expr symmap) e
    | S.Eref (org, T.Mutable, l, _) ->
      fprintf pp "& %s mut %a" (Camlcoq.extern_atom org) (pp_print_expr symmap) l
    | S.Eref (org, T.Immutable, l, ty) ->
      fprintf pp "&%s %a" (Camlcoq.extern_atom org) (pp_print_expr symmap) l
    | S.Efield (l, i, _) ->
      let x = IdentMap.find i symmap in
      fprintf pp "%a.%s" (pp_print_expr symmap) l x
    | S.Ederef (l, _) ->
      fprintf pp "*%a" (pp_print_expr symmap) l
    | S.Eunop (op, r, _) ->
      fprintf pp "%a %a" pp_print_unop op (pp_print_expr symmap) r
    | S.Ebinop (op, r1, r2, _) ->
      fprintf pp "%a %a %a" (pp_print_expr symmap) r1 pp_print_binop op (pp_print_expr symmap) r2
    | S.Eassign (l, r, _) ->
      fprintf pp "%a = %a" (pp_print_expr symmap) l (pp_print_expr symmap) r
    | S.Ecall (r1, rargs, _) ->
      fprintf pp "%a(%a)" (pp_print_expr symmap) r1 (pp_print_exprs symmap ", ") rargs


  and pp_print_exprs (symmap: id IdentMap.t) (sep: string) pp es =
    let module S = Rustsyntax in
    match es with
    | S.Econs (r1, rl) -> Format.fprintf pp "%a%s%a" (pp_print_expr symmap) r1 sep (pp_print_exprs symmap sep) rl
    | S.Enil -> ()

  and pp_print_stmt (symmap: id IdentMap.t) pp s =
    let open Format in
    let module S = Rustsyntax in
    match s with
    | S.Sskip -> ()
    | S.Sdo e ->
      pp_print_expr symmap pp e
    | S.Slet (i, t, Some v, rest) ->
      let x = IdentMap.find i symmap in
      fprintf pp "let %s: %a = %a;@ %a" x (pp_print_rust_type symmap) t
        (pp_print_expr symmap) v (pp_print_stmt symmap) rest
    | S.Slet (i, t, None, rest) ->
      let x = IdentMap.find i symmap in
      fprintf pp "let %s: %a;@ %a" x (pp_print_rust_type symmap) t
        (pp_print_stmt symmap) rest
    | S.Ssequence (s1, s2) ->
      fprintf pp "%a@ %a" (pp_print_stmt symmap) s1 (pp_print_stmt symmap) s2
    | S.Sifthenelse (test, s1, s2) ->
      fprintf pp "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
        (pp_print_expr symmap) test
        (pp_print_stmt symmap) s1
        (pp_print_stmt symmap) s2
    | S.Swhile (test, s) ->
      fprintf pp "@[<v 2>while (%a) {@ %a@;<0 -2>}@]"
        (pp_print_expr symmap) test
        (pp_print_stmt symmap) s
    | S.Sloop s ->
      fprintf pp "@[<v 2>loop {@ %a@;<0 -2>}@]"
        (pp_print_stmt symmap) s
    | S.Sbreak -> pp_print_string pp "break;"
    | S.Scontinue -> pp_print_string pp "continue;"
    (* | S.Sreturn None -> pp_print_string pp "return;" *)
    | S.Sreturn v ->
      fprintf pp "return %a;" (pp_print_expr symmap) v
    | S.Smatch (e, arms) ->
      fprintf pp "@[<v 2>match %a: %a {@ %a@;<0 -2>}@]"
        (pp_print_expr symmap) e
        (pp_print_rust_type symmap) (S.typeof e)
        (pp_print_match_arms symmap) arms

  and pp_print_match_arms (symmap: id IdentMap.t) pp (arms: Rustsyntax.arm_statements) =
    let open Format in
    let module S = Rustsyntax in
    match arms with
    | S.AScons (Some (iv, ib), body, rest) ->
      let xv = IdentMap.find iv symmap in
      let xb = IdentMap.find ib symmap in
      fprintf pp "@[<v 2>case %s as %s => {@ %a@;<0 -2>}@ %a@]" xv xb (pp_print_stmt symmap) body
        (pp_print_match_arms symmap) rest
    | S.AScons (None, body, rest) ->
      fprintf pp "@[<v 2>default => {@ %a@;<0 -2>}@ %a@]" (pp_print_stmt symmap) body
        (pp_print_match_arms symmap) rest
    | S.ASnil -> ()

  let pp_print_function (symmap: id IdentMap.t) pp i (f: Rustsyntax.coq_function) =
    let rec print_args pp args =
      match args with
      | (i, t) :: args' ->
        let x = IdentMap.find i symmap in
        Format.fprintf pp "%s: %a@ %a" x (pp_print_rust_type symmap) t
          print_args args'
      | [] -> ()
    in
    let x = IdentMap.find i symmap in
    let open Rustsyntax in
    Format.fprintf pp "@[<hv 2>fn %s%a(%a) -> %a %a {@ %a@;<0 -2>}@]" x
      (pp_print_origins symmap) f.fn_generic_origins
      print_args f.fn_params (pp_print_rust_type symmap) (snd f.fn_return)
      (pp_print_origin_relations symmap) f.fn_origins_relation (pp_print_stmt symmap) f.fn_body

  (* Print external function *)
  let pp_print_fun_decl (symmap: id IdentMap.t) pp i orgs rels argtys retty =
  let rec print_args pp args =
    match args with
    | t :: args' ->
      let x = IdentMap.find i symmap in
      Format.fprintf pp "%s: %a@ %a" x (pp_print_rust_type symmap) t
        print_args args'
    | [] -> ()
  in
  let x = IdentMap.find i symmap in
  Format.fprintf pp "@[extern fn %s%a(%a) -> %a %a@.@]" x
    (pp_print_origins symmap) orgs
    print_args argtys (pp_print_rust_type symmap) retty
    (pp_print_origin_relations symmap) rels


  let pp_print_error pp err (symmap: id IdentMap.t)=
    let open Format in
    match err with
    | Efield_of_non_struct t ->
      pp_print_string pp "Attempt to read field of non-struct type ";
      pp_print_rust_type symmap pp t 
    | Efield_not_found id -> Format.fprintf pp "Field %s not found" id
    | Ederef_non_deref t ->
      pp_print_string pp "Dereference a non-dereferencable type ";
      pp_print_rust_type symmap pp t 
    | Enot_callable t -> 
      pp_print_string pp "Not callable type ";
      pp_print_rust_type symmap pp t 
    | Eunop_type_error (op, t)->
      pp_print_string pp "Type error in unary operation: ";
      pp_print_unop pp op;
      pp_print_rust_type symmap pp t 
    | Ebinop_type_error (op, t1, t2) ->
      pp_print_string pp "Type error in binary operation: ";
      pp_print_rust_type symmap pp t1;
      pp_print_binop pp op;
      pp_print_rust_type symmap pp t2 
    | Econstructor_alone (xenum, xvar) ->
      Format.fprintf pp "Constructor %s::%s cannot appear alone" xenum xvar
    | Emulti_args_to_constructor (_, xenum, xvar) ->
      Format.fprintf pp "Too many arguments to constructo %s::%s" xenum xvar
    | Enot_a_composite x ->
      Format.fprintf pp "%s is not a composite type" x
    | Ename_not_found x ->
      Format.fprintf pp "%s is neither variable nor function" x
    | Eno_variant (ienum, ivar) ->
      let xenum = IdentMap.find ienum symmap in
      let xvar = IdentMap.find ivar symmap in
      Format.fprintf pp "%s is not a variant of enum %s" xvar xenum;
    | Enot_a_enum t ->
      pp_print_rust_type symmap pp t ;
      pp_print_string pp " is not a enum"
    | Eduplicated_patterns ->
      pp_print_string pp "duplicated patterns"
    | Econstructor_wrong_arity (ienum, ivar, got, expected) ->
      let xenum = IdentMap.find ienum symmap in
      let xvar = IdentMap.find ivar symmap in
      Format.fprintf pp "%s::%s does not take %d arguments, expected %d" xenum xvar got expected;

  type 'a ret = ('a, error) result * state

  type 'a monad = state -> 'a ret

  let backup_locals: (Rusttypes.coq_type IdentMap.t) monad =
    fun (st: state) -> (Result.Ok st.local_types, st)

  let restore_locals (locals: Rusttypes.coq_type IdentMap.t): unit monad =
    fun (st: state) -> (Result.Ok (), { st with local_types = locals })

  let run_monad (m: 'a monad) (st: state) : ('a , error) result * id IdentMap.t =
    let rev_symmap st0 = IdMap.fold (fun k v m -> IdentMap.add v k m)
                                    st0.symmap IdentMap.empty in
    match m st with
    | (Ok r, st) -> (Ok r, rev_symmap st)
    | (Error e, st) -> (Error e, rev_symmap st)

  let (>>=) (x: 'a monad) (f: 'a -> 'b monad): 'b monad =
    fun (st: state) -> match x st with
    | (Result.Error e, st') -> (Result.Error e, st')
    | (Result.Ok x', st') ->
        match f x' st' with
          | (Result.Error e, st') -> (Result.Error e, st')
          | (Result.Ok x'', st'') -> (Result.Ok x'', st'')

  let return x = fun st -> (Result.Ok x, st)


  let rec map_m (xs: 'a list) (f: 'a -> 'b monad): 'b list monad =
    match xs with
    | x::xs' ->
      f x >>= fun y ->
      map_m xs' f >>= fun ys ->
      return (y::ys)
    | [] -> return []

  let throw (e: error) = fun st -> (Result.Error e, st)

  let skeleton_st : state = { symmap = IdMap.empty
                            ; rev_symmap = IdentMap.empty
                            ; local_types = IdentMap.empty
                            ; next_ident = !Camlcoq.next_atom
                            ; funcs = IdentMap.empty
                            ; fun_decls = IdentMap.empty
                            ; enums = IdentMap.empty
                            ; composites = IdentMap.empty
                            ; gvars = [] 
                            ; external_funs = []}
  
        
  let new_ident (x: id): ident monad =
    fun st -> (
        Result.Ok st.next_ident,
        { st with symmap = IdMap.add x st.next_ident st.symmap
                ; rev_symmap = IdentMap.add st.next_ident x st.rev_symmap
                ; next_ident = Camlcoq.P.succ st.next_ident }
      )

  let fresh_ident: ident monad =
    fun st -> (
      Result.Ok st.next_ident,
      { st with symmap = IdMap.add (Int.to_string (Camlcoq.P.to_int st.next_ident)) st.next_ident st.symmap
              ; rev_symmap = IdentMap.add st.next_ident (Int.to_string (Camlcoq.P.to_int st.next_ident)) st.rev_symmap
              ; next_ident = Camlcoq.P.succ st.next_ident }
    )

  let rev_ident (i: ident): id monad =
    fun st -> (Result.Ok (IdentMap.find i st.rev_symmap), st)

  (* If no such id in symmap, throws an error *)
  let get_ident (x: id) : ident monad =
    fun st -> (Result.Ok (IdMap.find x st.symmap), st)

  let get_or_new_ident (x: id): ident monad =
    fun st -> match IdMap.find_opt x st.symmap with
      | Option.Some i ->
        (Result.Ok i, st)
      | None -> (
          Result.Ok st.next_ident,
          { st with symmap = IdMap.add x st.next_ident st.symmap
                  ; rev_symmap = IdentMap.add st.next_ident x st.rev_symmap
                  ; next_ident = Camlcoq.P.succ st.next_ident }
        )

  let dummy_origin = get_or_new_ident dummy_origin_str
  
  let rec repeat n e =
    if n = 0 then [] else e :: repeat (n-1) e

  let dummy_origins n =
    dummy_origin >>= fun org ->
      return (repeat n org)

  let get_st : state monad = fun st -> (Result.Ok st, st)

  let set_st (st: state) : unit monad = fun _ -> (Result.Ok (), st)

  let get_enums: (comp_enum' IdentMap.t) monad =
    get_st >>= fun st -> return st.enums

  let add_fn (x: id) (f: fn) : unit monad =
    get_or_new_ident x >>= fun i ->
    get_st >>= fun st ->
    let funcs' = IdentMap.add i f st.funcs in
    set_st { st with funcs = funcs' }

  let add_gvar (name: string) (v: Rusttypes.coq_type AST.globvar) : ident monad =
    fun st ->
      let i = st.next_ident in
      (Result.Ok i, { st with symmap = IdMap.add name i st.symmap
                             ; rev_symmap = IdentMap.add i name st.rev_symmap
                             ;next_ident = Camlcoq.P.succ i
                             ; gvars = (i, v) :: st.gvars })

(* Adhoc: it is just used to add malloc/free function declarations *)
  let add_external_fun (name: string) (sg: AST.signature) targs tres: ident monad =
    fun st ->
      match IdMap.find_opt name st.symmap with
      | Option.None ->
        let i = st.next_ident in
        let i'' = Camlcoq.coqstring_of_camlstring name in
        (Result.Ok i, 
        { st with symmap = IdMap.add name i st.symmap
        ; rev_symmap = IdentMap.add i name st.rev_symmap
        ; next_ident = Camlcoq.P.succ i
        (* Unsuppored generic origins in external functions *)
        ; external_funs = (i, AST.Gfun (Rusttypes.External([],[], AST.EF_external(i'',sg), targs, tres, sg.AST.sig_cc))) :: st.external_funs })
      | Option.Some i -> (Result.Ok i, st)

  let get_composite (x: id) : (ident * Rusttypes.composite_definition) monad =
    get_or_new_ident x >>= fun i ->
    fun st -> match IdentMap.find_opt i st.composites with
      | Option.None -> (Result.Error (Enot_a_composite x), st)
      | Option.Some comp -> (Result.Ok (i, comp), st)

  let get_fn (x: id) : (ident * fn) monad =
    get_or_new_ident x >>= fun i ->
    fun st -> match IdentMap.find_opt i st.funcs with
      | Option.None -> (Result.Error (Ename_not_found x), st)
      | Option.Some f -> (Result.Ok (i, f), st)

  let get_fn_decl_type (x: id) : (ident * (Rusttypes.coq_type option)) monad =
    get_or_new_ident x >>= fun i ->
    fun st -> match IdentMap.find_opt i st.fun_decls with
      | Option.None -> (Result.Ok(i, None), st)
      | Option.Some tyf -> (Result.Ok(i, Some(tyf)), st)
 

  let reg_local_type (x: id) (t: Rusttypes.coq_type): ident monad =
    get_or_new_ident x >>= fun i ->
    fun st -> (
        Result.Ok i,
        { st with local_types = IdentMap.add i t st.local_types }
      )

  let get_local_type (x: id): Rusttypes.coq_type option monad =
    get_or_new_ident x >>= fun i ->
    fun st -> (
        Result.Ok (IdentMap.find_opt i st.local_types),
        st
      )

  let convert_origins (orgs: id list) : (Rusttypes.origin list) monad =
    map_m orgs
    (fun id ->
      get_or_new_ident id >>= fun org ->
      return org)

  let convert_origin_relations (rels: (id * id) list) : (Rusttypes.origin_rel list) monad =
    map_m rels
    (fun (id1, id2) ->
      get_ident id1 >>= fun org1 ->
      get_ident id2 >>= fun org2 ->
      return (org1, org2))

  let rec exprlist_of xs = match xs with
        |(x::xs) -> Rustsyntax.Econs (x, exprlist_of xs)
        | [] -> Rustsyntax.Enil

  let rec typelist_of xs = match xs with
    | (x::xs) -> Rusttypes.Tcons (x, typelist_of xs)
    | [] -> Rusttypes.Tnil

  let rec transl_ty (t: ty): Rusttypes.coq_type monad =
    let module T = Rusttypes in
    match t with
    | Tunit -> return T.Tunit
    | Tint (size, si) -> return (T.Tint (size, si))
    | Tlong (size) -> return (T.Tlong (size))
    | Tfloat (size) -> return (T.Tfloat (size))
    | Tfunction (params, ret, orgs, rels) ->
      map_m params transl_ty  >>= fun args' ->
      transl_ty ret >>= fun ret' ->
      convert_origins orgs >>= fun orgs ->
      convert_origin_relations rels >>= fun rels ->
      return (T.Tfunction (orgs, rels, typelist_of args', ret', AST.cc_default))
    | Tbox (t) ->
      transl_ty t >>= fun t' ->
      return (T.Tbox (t'))
    | Tadt (x, attr, org_ids) ->
      get_composite x >>= fun (i, T.Composite (_, sv, _, orgs, rels)) ->
       (* Use org_ids as the origins notation for this type or
       generate list of dummy origins *)
      let org_ids = if List.length org_ids = 0 then 
        (List.map (fun _ -> dummy_origin_str) orgs) 
        else if (List.length org_ids) = (List.length orgs) then org_ids 
        else failwith "unreachable (transl_ty)" in
      convert_origins org_ids >>= fun orgs ->
      (match sv with
        | T.Struct -> return (T.Tstruct (orgs, i))
        | T.TaggedUnion -> return (T.Tvariant (orgs, i)))
    | Treference (t, org_id, m) ->
      transl_ty t >>= fun t' ->
      get_or_new_ident org_id >>= fun org ->
      return (T.Treference (org, m, t'))

  (* Add a function declaration to  *)
  let add_fn_decl (x: id) (f: fn_decl) : unit monad =
    get_or_new_ident x >>= fun i ->
    get_st >>= fun st ->
    map_m f.params
      (fun (x, t) ->
          transl_ty t >>= fun t' -> return t') >>= fun arg_tys ->    
    transl_ty f.return >>= fun ret_ty ->
    (* get the char list of the function name *)
    let name = Camlcoq.coqstring_of_camlstring x in
    let arg_tys' = typelist_of arg_tys in
    let sg = Rusttypes.signature_of_type arg_tys' ret_ty AST.cc_default in
    let fun_decl = (i, AST.Gfun (Rusttypes.External([], [], AST.EF_external(name, sg), arg_tys', ret_ty, AST.cc_default))) in
    let tyf = Rusttypes.Tfunction ([], [], arg_tys', ret_ty, AST.cc_default) in
    set_st { st with 
      (* Record the i for this fun_decl *)
      fun_decls = IdentMap.add i tyf st.fun_decls;
      external_funs = fun_decl :: st.external_funs}


  let composite_of_decl i s_or_e a orgs rels =
    match s_or_e with
    | Struct -> Rusttypes.Composite (i, Rusttypes.Struct, [], orgs, rels)
    | Enum -> Rusttypes.Composite (i, Rusttypes.TaggedUnion, [], orgs, rels)

  (* add composite declaration *)
  let add_composite_decl (x: id) (s_or_e: struct_or_enum) (orgs: id list) (rels: (id * id) list) : unit monad =
    get_or_new_ident x >>= fun i ->
    convert_origins orgs >>= fun orgs ->
    convert_origin_relations rels >>= fun rels ->
    let c = composite_of_decl i s_or_e noattr orgs rels in
    get_st >>= fun st ->
    let cos = IdentMap.add i c st.composites in
    set_st { st with composites = cos }

  let add_composite_struc (x: id) (c: comp_struc) (orgs: id list) (rels: (id * id) list) : unit monad =
    get_or_new_ident x >>= fun i ->
    map_m c
      (fun (x, t) ->
         get_or_new_ident x >>= fun i ->
         transl_ty t >>= fun t' ->
         return (Rusttypes.Member_plain (i, t'))) >>= fun members' ->
    convert_origins orgs >>= fun orgs ->
    convert_origin_relations rels >>= fun rels ->
    (* FIXME: if this composite has been declared, we just override
    its origins and relations *)
    let c' = Rusttypes.Composite (i, Rusttypes.Struct, members', orgs, rels) in
    get_st >>= fun st ->
    let cos' = IdentMap.add i c' st.composites in
    set_st { st with composites = cos' }

  let rec composite_stru_for_variant (ts: ty list) (n: int) : comp_struc =
    match ts with
    | t :: ts' ->
      ("_" ^ Int.to_string n, t) :: composite_stru_for_variant ts' (n + 1)
    | [] -> []

  let variant_struc_id (xenum: id) (xvar: id) : id =
    ("_body_of_" ^ xenum ^ "_" ^ xvar)

  let lower_comp_enum (c: comp_enum) : comp_enum' monad =
    map_m c
      (fun (xvar, ts) ->
         map_m ts transl_ty >>= fun ts' ->
         get_or_new_ident xvar >>= fun ivar ->
         return (ivar, ts')
      )

  let type_of_variant_constructor (x: id) (xvar: string) (i: ident) (ts: ty list) orgs rels : Rusttypes.coq_type monad =
    match ts with
     | [] ->  return Rusttypes.Tunit
     | t :: [] -> transl_ty t
     | _ ->
       let variant_struc_id = variant_struc_id x xvar in
       let variant_struc = composite_stru_for_variant ts 0 in
       add_composite_struc variant_struc_id variant_struc orgs rels >>= fun _ ->
       get_or_new_ident variant_struc_id >>= fun variant_struc_ident ->
       convert_origins orgs >>= fun orgs ->
      (* This type is used in composite definition, so the origins are generic *)
       return (Rusttypes.Tstruct (orgs, variant_struc_ident))

  let rec origin_in_ty org ty =
    match ty with
    | Treference(ty', org', _) ->
      org = org' || origin_in_ty org ty'
    | Tbox(ty') ->
      origin_in_ty org ty'
    | Tadt(i, _, orgs) ->
      List.mem org orgs
    | _ -> false
       
  let rec origin_in_ty_list l org =
    match l with
    | [] -> false
    | ty :: l' ->
      origin_in_ty org ty || origin_in_ty_list l' org

  let relation_in_origins orgs (org1, org2) =
    List.mem org1 orgs && List.mem org2 orgs

  let add_composite_enum (x: id) (c: comp_enum) orgs rels : unit monad =
    get_or_new_ident x >>= fun i ->
    map_m c
      (fun (xvar, ts) ->
         (* filter origins appear in ts *)
         let orgs' = List.filter (origin_in_ty_list ts) orgs in
         (* filter relations whose origins appear in orgs' *)
         let rels'  = List.filter (relation_in_origins orgs') rels in
         get_or_new_ident xvar >>= fun i ->
         type_of_variant_constructor x xvar i ts orgs' rels' >>= fun t' ->
         return (Rusttypes.Member_plain (i, t'))) >>= fun members' ->
    lower_comp_enum c >>= fun ce' ->
    convert_origins orgs >>= fun orgs ->
    convert_origin_relations rels >>= fun rels ->
    let c' = Rusttypes.Composite (i, Rusttypes.TaggedUnion, members', orgs, rels) in
    get_st >>= fun st ->
    let cos' = IdentMap.add i c' st.composites in
    set_st { st with composites = cos'
                   ; enums = IdentMap.add i ce' st.enums }

  let rty_bool = Rusttypes.Tint (Ctypes.I32, Ctypes.Signed)

  let infer_unop (op: Cop.unary_operation)
      (t: Rusttypes.coq_type) : Rusttypes.coq_type monad =
    let open Cop in
    let module T = Rusttypes in
    match op with
    | Onotbool ->
      (match t with
       | T.Tint (Ctypes.IBool, Ctypes.Unsigned) -> return rty_bool
       | _ -> throw (Eunop_type_error (op, t)))
    | Onotint ->
      (match t with
       | T.Tint (size, si) -> return (T.Tint (size, si))
       | _ -> throw (Eunop_type_error (op, t)))
    | Oneg ->
      (match t with
       | T.Tint (size1, si1) -> return (T.Tint (size1, si1))
       | T.Tfloat (size1) -> return (T.Tfloat (size1))
       | _ -> throw (Eunop_type_error (op, t)))
    | Oabsfloat ->
      (match t with
       | T.Tfloat (size1) -> return (T.Tfloat (size1))
       | _ -> throw (Eunop_type_error (op, t)))

  let infer_binop (op: Cop.binary_operation)
      (ta: Rusttypes.coq_type) (tb: Rusttypes.coq_type)
    : Rusttypes.coq_type monad =
    let module T = Rusttypes in
    let open Cop in
    match op with
    | Oadd | Osub | Omul | Odiv ->
      (match (ta, tb) with
       | (T.Tint (size1, si1), T.Tint (size2, si2))
         when size1 = size2 && si1 = si2 ->
         return (T.Tint (size1, si1))
       | (T.Tfloat (size1), T.Tfloat (size2))
         when size1 = size2 ->
         return (T.Tfloat (size1))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oand | Oor | Oxor ->
      (match (ta, tb) with
       | (T.Tint (Ctypes.IBool, Ctypes.Unsigned), T.Tint (Ctypes.IBool, Ctypes.Unsigned)) ->
         return rty_bool
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oeq | One | Olt | Ogt | Ole | Oge ->
      (match (ta, tb) with
       | (T.Tint (size1, si1), T.Tint (size2, si2))
         when size1 = size2 && si1 = si2 ->
         return rty_bool
       | (T.Tfloat (size1), T.Tfloat (size2))
         when size1 = size2 ->
         return rty_bool
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Oshl | Oshr ->
      (match (ta, tb) with
       | (T.Tint (size, si), T.Tint (Ctypes.I8, Ctypes.Unsigned)) ->
         return (T.Tint (size, si))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))
    | Omod ->
      (match (ta, tb) with
       | (T.Tint (size1, si1), T.Tint (size2, si2))
         when size1 = size2 ->
         return (T.Tint (size1, si2))
       | _ -> throw (Ebinop_type_error (op, ta, tb)))

   module Trans_match = struct
      (** pattern table looks like:
          a1          a2
          ----------------------
          B1(x, y),   B2(()))  |  body1
          B2(())  ,   y        |  body2
          z       ,   B1(u, v) |  body3

          where a1, a2 are expressions to be deconstructed against patterns stored in rows,
          body1, body2, body3 are expressions to be evaluated after corresponding row is successfully matched
      *)

     type pat_row = pat' list * Rustsyntax.statement
     type pat_table = { header: Rustsyntax.expr list
                      ; rows: pat_row list }

     let row_head_variant_ident (row: pat_row) : ident option =
       let (patterns, _) = row in
       match List.hd patterns with
       | Pconstructor' (_, ic, _) -> Some ic
       | Pbind' _ -> None

     let row_head_args_types (row: pat_row) (header: Rustsyntax.expr list)
         (enums: ((ident * Rusttypes.coq_type list) list) IdentMap.t)
       : (ident * Rusttypes.coq_type list) option =
       let t = Rustsyntax.typeof (List.hd header) in
       match t with
       | Rusttypes.Tvariant (_, ienum) ->
          let (patterns, _) = row in
          (match List.hd patterns with
          | Pconstructor' (ienum', ivar, args) ->
            if Camlcoq.P.(=) ienum ienum' then
              let enum = IdentMap.find ienum enums in
              Some (ienum, List.assoc ivar enum)
            else failwith "Mismatch enum type in match statement"
          | Pbind' _ -> None
          )
       | _ -> None

     let rec con_header_with_field_access_rec (e: Rustsyntax.expr) (header: Rustsyntax.expr list) (types: Rusttypes.coq_type list) (n: int) : Rustsyntax.expr list monad =
      (* consider the size of types is one *)
       match types with
       | t :: types' ->
        (* The field names of generated struct is ascending numbers *)
        con_header_with_field_access_rec e header types' (n + 1) >>= fun header' ->
         get_or_new_ident ("_" ^ (Int.to_string) n) >>= fun i ->
         let access_expr = Rustsyntax.Efield (e, i, t) in
         return (access_expr :: header')
       | [] -> return []

      let con_header_with_field_access (e: Rustsyntax.expr) (header: Rustsyntax.expr list) (types: Rusttypes.coq_type list): Rustsyntax.expr list monad =
       (* consider the size of types is one *)
        match types with
        | [] -> failwith "Do not support zero size type"
        | [t] ->
          (*  no field access *)
          return [e]
        | t :: types' ->
          con_header_with_field_access_rec e header types 0


     let skeleton_table (cases: case' list) (header: Rustsyntax.expr) : pat_table =
       let rows = List.map (fun c -> ([c.pattern'], c.body')) cases in
       { header = [header]; rows = rows }

     (** groups = (variant_groups, matchall_groups)
         rows grouped by each row's head's variant ident.
         If some row's head is a local-bind, it's put in matchall_groups;
         Otherwise it's put in variant_groups by its variant name
     *)
     type groups = (ident * pat_row list) list * (pat_row list)

     let skeleton_groups (header: Rustsyntax.expr list): groups monad =
       let head = List.hd header in
       match Rustsyntax.typeof head with
       | Rusttypes.Tvariant (_, ienum) ->
         get_enums >>= fun enums ->
         let enum = IdentMap.find ienum enums in
         let var_idents = List.map fst enum in
         let var_groups = List.map (fun x -> (x, [])) var_idents in
         return (var_groups, [])
       | _ -> return ([], [])

     let rec insert_to_group (row: pat_row) (gs: groups) : groups =
       let (variant_groups, matchall_groups) = gs in
       match row_head_variant_ident row with
       | Some rhvi ->
         (match variant_groups with
          | g :: groups_left ->
            let (variant_ident, rows) = g in
            if Camlcoq.P.(=) rhvi variant_ident then
              ((variant_ident, row :: rows) :: groups_left, matchall_groups)
            else
              let (variant_groups', matchall_groups') = insert_to_group row (groups_left, matchall_groups) in
             (g :: variant_groups', matchall_groups')
         | [] -> gs
         )
       | None -> (variant_groups, row :: matchall_groups)

     let rec group_rows (rows: pat_row list) (gs: groups): groups =
       match rows with
       | r :: rows_left ->
         insert_to_group r (group_rows rows_left gs)
       | [] -> gs

     let variant_struc_name (ienum: ident) (ivar: ident) : ident monad =
       rev_ident ienum >>= fun xenum ->
       rev_ident ivar >>= fun xvar ->
       get_or_new_ident (variant_struc_id xenum xvar)

     let table_for_variant_group (grp_ivar: ident)
         (grp_rows: pat_row list) (header: Rustsyntax.expr list)
       : (pat_table * ident) monad =
       fresh_ident >>= fun as_var ->
       get_enums >>= fun enums ->
       match row_head_args_types (List.hd grp_rows) header enums with
       | Some (ienum, args_types) ->
         (* replace generic origins in args_types with dummy origins *)
         dummy_origin >>= fun dummy ->
         let args_types = List.map (Rusttypes.replace_type_with_dummy_origin dummy) args_types in
         (* consider the size of args_types is 1 *)
         (match args_types with
         | [] -> failwith "unreachable (table_for_variant_group)"
         | [t] -> return t
         | _ -> 
          (* It depends on the logic that we have generated struct for this enum constructor *)
          variant_struc_name ienum grp_ivar >>= fun vsn ->
          get_st >>= fun st ->
          match IdentMap.find_opt vsn st.composites with
          | None -> failwith "no struct generated for this enum constructor"
          | Some(Rusttypes.Composite(struct_id, _, _, orgs, _)) ->
            (* generate dummy origins *)
            dummy_origins (List.length orgs) >>= fun dummy_origins ->
            return (Rusttypes.Tstruct (dummy_origins, struct_id))
         ) >>= fun as_var_typ ->
         con_header_with_field_access
             (Rustsyntax.Evar (as_var, as_var_typ)) (List.tl header) args_types
             >>= fun header' ->
         let rows' = List.map
                       (fun (patterns, body) ->
                          match List.hd patterns with
                          | Pconstructor' (_, _, args) ->
                            (List.concat [args; (List.tl patterns)], body)
                          | _ -> failwith "unreachable (table_for_variant_group 2)")
                       grp_rows
         in
         return ({ header = header'; rows = rows' }, as_var)
       | None -> failwith "unreachable (table_for_variant_group 3) "

    (* Some helper functions for Pbind *)
    let unwrap_bind_id p =
      match p with
      | Pbind'(_, i) -> i
      | _ -> failwith "unreachable (unwrap_bind_id)"

    let unwrap_bind_type dummy_org p ty =
     match p with
     | Pbind'(None, _) -> ty
     | Pbind'(Some(RefMut), _) -> Rusttypes.Treference(dummy_org, Rusttypes.Mutable, ty)
     | Pbind'(Some(RefImmut), _) -> Rusttypes.Treference(dummy_org, Rusttypes.Immutable, ty)
     | _ -> failwith "unwrap_bind_type error"

    let unwrap_bind_expr_type dummy_org p e =
     let ty = unwrap_bind_type dummy_org p (Rustsyntax.typeof e) in
     match p with
     | Pbind'(None, _) -> (ty, e)
     | Pbind'(Some(RefMut), _) -> (ty, Rustsyntax.Eref(dummy_org, Rusttypes.Mutable, e, ty))
     | Pbind'(Some(RefImmut), _) -> (ty, Rustsyntax.Eref(dummy_org, Rusttypes.Immutable, e, ty))
     | _ -> failwith "unwrap_bind_type error"

     let table_for_matchall_group (grp_rows: pat_row list)
         (header: Rustsyntax.expr list)
         : pat_table monad =
         get_enums >>= fun enums ->
         dummy_origin >>= fun dummy_org ->
         let rows' = List.map
                       (fun (patterns, body) ->
                          let (ty, e) = unwrap_bind_expr_type dummy_org (List.hd patterns) (List.hd header) in
                          (List.tl patterns,
                            (* If Pbind is (ref mut r) then this let stmt is r = &mut ... *)
                             Rustsyntax.Slet (unwrap_bind_id (List.hd patterns),
                                              ty,
                                              Some e,
                                              body
                              )))
                       grp_rows
         in
         return { header = List.tl header; rows = rows' }

     let rec transl_variant_group (grp: ident * pat_row list)
         (header: Rustsyntax.expr list)
         (arms: Rustsyntax.arm_statements)
       : Rustsyntax.arm_statements monad =
       let (grp_ivar, grp_rows) = grp in
       table_for_variant_group grp_ivar grp_rows header 
       >>= fun (tab, as_var) ->
       transl_pat_table tab >>= fun body ->
       return (Rustsyntax.AScons (Some (grp_ivar, as_var), body, arms))

     and transl_matchall_group (grp_rows: pat_row list)
         (header: Rustsyntax.expr list)
         (arms: Rustsyntax.arm_statements)
       : Rustsyntax.arm_statements monad =
       if List.length grp_rows <> 0 then 
         table_for_matchall_group grp_rows header >>= fun tab ->
         transl_pat_table tab >>= fun body ->
         return (Rustsyntax.AScons (None, body, arms))
       else
         return arms

     and transl_variant_groups (grps: (ident * pat_row list) list)
         (header: Rustsyntax.expr list)
       : Rustsyntax.arm_statements monad =
       match grps with
       | grp :: grps' ->
         transl_variant_groups grps' header >>= fun grps' ->
         transl_variant_group grp header grps' >>= fun arms ->
         return arms
       | [] -> return Rustsyntax.ASnil

     and transl_pat_table (tab: pat_table) : Rustsyntax.statement monad =
       match tab.header with
       | [] ->
         if List.length tab.rows > 1 then
           throw Eduplicated_patterns
         else
           let (_, body) = List.hd tab.rows in
           return body
       | _ ->
         skeleton_groups tab.header >>= fun grps ->
         let destructed = List.hd tab.header in
         let (variant_grps, matchall_grp) = group_rows tab.rows grps in
         if List.length variant_grps = 0 then
           table_for_matchall_group matchall_grp tab.header >>= fun tab ->
           transl_pat_table tab
         else
          transl_variant_groups variant_grps tab.header >>= fun arms ->
          transl_matchall_group matchall_grp tab.header arms >>= fun arms ->
          return (Rustsyntax.Smatch (destructed, arms))
   end

   let unwrap_bind_type dummy_org p ty =
    match p with
    | Pbind(None, _) -> ty
    | Pbind(Some(RefMut), _) -> Rusttypes.Treference(dummy_org, Rusttypes.Mutable, ty)
    | Pbind(Some(RefImmut), _) -> Rusttypes.Treference(dummy_org, Rusttypes.Immutable, ty)
    | _ -> failwith "unwrap_bind_type error"

   let rec lower_pat (p: pat) (t: Rusttypes.coq_type) : pat' monad =
     match p with
     | Pconstructor (enum_id, constr_id, args) ->
       (match t with
        | Rusttypes.Tvariant (_, ienum) ->
          get_enums >>= fun enums ->
          get_or_new_ident enum_id >>= fun ienum' ->
          rev_ident ienum >>= fun ienum_str ->
          if not (Camlcoq.P.(=) ienum ienum') then failwith ("lower_pat: " ^ enum_id ^ " and " ^ ienum_str)
          else
          (match IdentMap.find_opt ienum enums with
           | Some enum ->
             get_or_new_ident constr_id >>= fun i ->
             (match List.assoc_opt i enum with
              | Some var_args ->
                if (List.length var_args) <> (List.length args) then
                  throw (Econstructor_wrong_arity (ienum, i, List.length args, List.length var_args))
                else
                  map_m (List.combine args var_args)
                    (fun (arg, t) -> lower_pat arg t)
                  >>= fun args' ->
                  return (Pconstructor' (ienum, i, args'))
              | None ->
                throw (Eno_variant (ienum, i))
             )
           | None -> failwith "unreachable (lower_pat)"
          )
        | _ -> throw (Enot_a_enum t)
       )
    | Pbind(m, x) ->
      dummy_origin >>= fun dummy_org ->
      let t = unwrap_bind_type dummy_org p t in
      reg_local_type x t >>= fun i ->
      return (Pbind'(m,i))


  (* String literals *)

  let stringNum = ref 0   (* number of next global for string literals *)
  let name_for_string_literal s =
    incr stringNum;
    let name = Printf.sprintf "__stringlit_%d" !stringNum in
    name

  let rec transl_expr (e: expr) : Rustsyntax.expr monad =
    match e with
    | Eunit -> return (Rustsyntax.Eunit)
    | Eval (v, t) ->
      transl_ty t >>= fun t ->
      return (Rustsyntax.Eval (v, t))
    | Evar x ->
      get_or_new_ident x >>= fun ix ->
      (* Check that the variable x has been declared in the scope or
      not, if yes, it must be a local variable, if not, it must be a
      global variable. For global variables, we only translate it to
      r-value (Egloabl) *)
      get_local_type x >>= fun tx ->
      (match tx with
      (* x is local *)
      | Option.Some tx -> get_or_new_ident x >>= fun ix ->
        return (Rustsyntax.Evar (ix, tx))
      | Option.None ->
        (* What if x is an external function? *)
        get_fn_decl_type x >>= fun (ix, fty) ->
        match fty with
        | Some(fty) ->
          return (Rustsyntax.Eglobal(ix, fty))
        | None ->
          (* It is not an external function. It must be internal function *)
          get_fn x >>= fun (ix, f) ->
          transl_ty f.return >>= fun tr' ->
          let targs = List.map snd f.params in
          map_m targs transl_ty >>= fun targs' ->
          let targs'' = typelist_of targs' in
          convert_origins f.generic_origins >>= fun orgs ->
          convert_origin_relations f.origin_relations >>= fun rels ->
          let tf' = Rusttypes.Tfunction (orgs, rels, targs'', tr', AST.cc_default) in
          return (Rustsyntax.Eglobal (ix, tf'))
      )
    | Ebox e ->
      transl_expr e >>= fun e ->
      let t = Rustsyntax.typeof e in
      return (Rustsyntax.Ebox (e, Rusttypes.Tbox (t)))
    | Efield (e, x) ->
      transl_expr e >>= fun e' ->
      let te = Rustsyntax.typeof e' in
      (match te with
      | Rusttypes.Tstruct (_, ist) ->
        get_st >>= fun st ->
        let Rusttypes.Composite (_, _, members, _, _) =
          IdentMap.find ist st.composites
        in
        get_or_new_ident x >>= fun ix ->
        (match List.find_opt
          (fun (Rusttypes.Member_plain (im, _)) -> Camlcoq.P.(=) ix im)
          members
        with
        | Option.Some tm ->
          return (Rustsyntax.Efield (e', ix, Rusttypes.type_member tm))
        | Option.None -> throw (Efield_not_found x)
        )
      (* TODO: why? *)
      | Rusttypes.Treference (org, _, (Rusttypes.Tstruct (_, ist) as ts)) ->
        get_st >>= fun st ->
        let Rusttypes.Composite (_, _, members, _, _) =
          IdentMap.find ist st.composites
        in
        get_or_new_ident x >>= fun ix ->
        (match List.find_opt
                 (fun (Rusttypes.Member_plain (im, _)) -> Camlcoq.P.(=) ix im)
                 members
         with
         | Option.Some tm ->
           return (Rustsyntax.Efield
                     (Rustsyntax.Ederef (e', ts), ix, Rusttypes.type_member tm))
         | Option.None -> throw (Efield_not_found x)
        )
      | _ -> throw (Efield_of_non_struct te)
      )
    | Eaccess (xenum, xvar) -> throw (Econstructor_alone (xenum, xvar))
    | Ederef e ->
      transl_expr e >>= fun e' ->
      let te = Rustsyntax.typeof e' in
      (match te with
       | Rusttypes.Tbox (t) -> return (Rustsyntax.Ederef (e', t))
       | Rusttypes.Treference (_, _, t) -> return (Rustsyntax.Ederef (e', t))
       | _ -> throw (Ederef_non_deref te)
      )
    | Eunop (op, e) ->
      transl_expr e >>= fun e' ->
      infer_unop op (Rustsyntax.typeof e') >>= fun t ->
      return (Rustsyntax.Eunop (op, e', t))
    | Ebinop (op, e1, e2) ->
      transl_expr e1 >>= fun e1' ->
      transl_expr e2 >>= fun e2' ->
      infer_binop op (Rustsyntax.typeof e1') (Rustsyntax.typeof e2') >>=
      fun t ->
      return (Rustsyntax.Ebinop (op, e1', e2', t))
    | Eassign (e1, e2) ->
      transl_expr e1 >>= fun e1' ->
      transl_expr e2 >>= fun e2' ->
      return (Rustsyntax.Eassign (e1', e2', Rusttypes.Tunit))
    | Estruct (xstruct, xfl, es) ->
      map_m xfl get_or_new_ident >>= fun ifl ->
      map_m es transl_expr >>= fun es' ->
      get_composite xstruct >>=
      fun (istruct, Rusttypes.Composite (_, _, _, orgs, rels)) ->
      (* FIXME: we should generate list of dummy origins with the same length as orgs *)
      dummy_origins (List.length orgs) >>= fun dummy_orgs ->
      let t = Rusttypes.Tstruct (dummy_orgs, istruct) in
      return (Rustsyntax.Estruct (istruct, ifl, exprlist_of es', t))
    | Ecall (callee, args) ->
      (match callee with
      (* TODO: support external call *)
      | Evar "printf" ->
        map_m args (fun arg -> transl_expr arg)
        >>= fun args' ->
        (* Refer to C2C.ml *)
        let t_byte = Rusttypes.Tint (Ctypes.I8, Ctypes.Unsigned) in
        dummy_origin >>= fun dummy_origin ->
        let targs = typelist_of [Rusttypes.Treference(dummy_origin, Rusttypes.Immutable, t_byte)] in
        let tres =  Rusttypes.type_int32s in
        let sg =
          Rusttypes.signature_of_type targs tres
             { AST.cc_vararg = Some (Camlcoq.coqint_of_camlint 1l); cc_unproto = false; cc_structret = false} in
        add_external_fun "printf" sg targs tres >>= fun i ->
        let fty = (Rusttypes.Tfunction([],[],targs,tres,sg.AST.sig_cc)) in
        let fid = Rustsyntax.Evar(i,fty) in
        return (Rustsyntax.Ecall(fid, exprlist_of args', tres))
      | Eaccess (xenum, xvar) ->
        get_composite xenum >>= fun (ienum, Rusttypes.Composite (_, s_or_v, _, orgs, rels)) ->
        get_or_new_ident xvar >>= fun ivar ->
        (match s_or_v with
        | Rusttypes.Struct -> failwith "unreachable (Eaccess in transl_expr)"
        | Rusttypes.TaggedUnion ->
          (match args with
          | arg::nil ->
            transl_expr arg >>= fun e' ->
            (* construct dummy origins for Eenum type *)
            dummy_origins (List.length orgs) >>= fun dummy_orgs ->
            dummy_origins (List.length orgs) >>= fun dummy_orgs ->
            return (Rustsyntax.Eenum
                      (ienum, ivar, e', Rusttypes.Tvariant (dummy_orgs, ienum)))
          (* TODO: support multiple args to constructor *)
          | _ -> throw (Emulti_args_to_constructor (args, xenum, xvar))))
      | _ ->
        transl_expr callee >>= fun callee' ->
        map_m args (fun arg -> transl_expr arg)
        >>= fun args' ->
        (match Rustsyntax.typeof callee' with
         | Rusttypes.Tfunction (_, _, _, tr, _) ->
           let args'' = exprlist_of args' in
           return (Rustsyntax.Ecall (callee', args'', tr))
         | t -> throw (Enot_callable t)))
    | Eref (e, m) ->
      transl_expr e >>= fun e' ->
      (* The origin of reference expression is always dummy_origin *)
      dummy_origin >>= fun dummy_origin ->
      let t' = Rusttypes.Treference(dummy_origin, m, Rustsyntax.typeof e') in      
      return (Rustsyntax.Eref (dummy_origin, m, e', t'))
    | Estr s ->
      let s = Scanf.unescaped s in
      let t_byte = Rusttypes.Tint (Ctypes.I8, Ctypes.Unsigned) in
      let init_body = Seq.fold_left
                   (fun lst c ->
                     (List.append lst [AST.Init_int8 (Camlcoq.Z.of_uint (Char.code c))]))
                   []
                   (String.to_seq s)
      in
      let init = List.append init_body [AST.Init_int8 (Camlcoq.Z.Z0)]  in
      let var_ty = Rusttypes.Tarray(t_byte, (Camlcoq.Z.of_uint (List.length init))) in
      (* TODO: what is the origin of static string *)
      let global_var = AST.({ gvar_info = var_ty
                            ; gvar_init = init
                            ; gvar_readonly = true
                            ; gvar_volatile = false })
      in
      let str_lit = name_for_string_literal s in
      add_gvar str_lit global_var >>= fun i ->
      return (Rustsyntax.Eglobal (i, var_ty))



  let rec lower_case (c: case) (t: Rusttypes.coq_type) (retv: ident) : case' monad =
     lower_pat c.pattern t >>= fun p ->
     transl_stmt retv c.body >>= fun s ->
     return { pattern' = p; body' = s }

  (* We pass a return variable to the translation *)
  and transl_stmt (retv: ident) (s: stmt)
      : Rustsyntax.statement monad =
    let module S = Rustsyntax in
    let transl_stmt = transl_stmt retv in
    match s with
    | Sskip -> return S.Sskip
    | Sdo e ->
      transl_expr e >>= fun e' ->
      return (S.Sdo e')
    | Slet (x, t, v) ->
      (* If x is required in later statements, then Slet must be part of a Ssequence.
         That case is handled in Ssequence case.
         Here we only need evaluation of e *)
      (match v with
       | Option.Some e ->
         transl_expr e >>= fun e' ->
         return (Rustsyntax.Sdo e')
       | Option.None -> return Rustsyntax.Sskip
      )
    | Slet2 (x, e) ->
      transl_expr e >>= fun e' ->
      return (Rustsyntax.Sdo e')
    | Ssequence (s1, s2) ->
      (match s1 with
       | Slet (x, t, v) ->
         backup_locals >>= fun old_locals ->
         let v' = match v with
           | Option.Some e -> transl_expr e >>= fun e' -> return (Some e')
           | Option.None -> return Option.None
         in
         v' >>= fun v' ->
         transl_ty t >>= fun t' ->
         reg_local_type x t' >>= fun i ->
         transl_stmt s2 >>= fun s' ->
         restore_locals old_locals >>= fun _ ->
         return (S.Slet (i, t', v', s'))
       | Slet2 (x, e) ->
         backup_locals >>= fun old_locals ->
         transl_expr e >>= fun e' ->
         reg_local_type x (S.typeof e') >>= fun i ->
         transl_stmt s2 >>= fun s' ->
         restore_locals old_locals >>= fun _ ->
         return (S.Slet (i, (S.typeof e'), Some e', s'))
       | s1 ->
         transl_stmt s1 >>= fun s1' ->
         transl_stmt s2 >>= fun s2' ->
         return (S.Ssequence (s1', s2'))
      )
    | Sifthenelse (e, s1, s2) ->
      transl_expr e >>= fun e' ->
      backup_locals >>= fun old_locals ->
      transl_stmt s1 >>= fun s1' ->
      restore_locals old_locals >>= fun _ ->
      transl_stmt s2 >>= fun s2' ->
      restore_locals old_locals >>= fun _ ->
      return (S.Sifthenelse (e', s1', s2'))
    | Swhile (e, s) ->
      transl_expr e >>= fun e' ->
      backup_locals >>= fun old_locals ->
      transl_stmt s >>= fun s' ->
      restore_locals old_locals >>= fun _ ->
      return (S.Swhile (e', s'))
    | Sloop s ->
      backup_locals >>= fun old_locals ->
      transl_stmt s >>= fun s' ->
      restore_locals old_locals >>= fun _ ->
      return (S.Sloop s')
    | Sbreak -> return S.Sbreak
    | Scontinue -> return S.Scontinue
    | Sreturn v ->
      (* rete is the return variable, we need to assign the return
      expression to the return variable. Note that this code is not
      debugged yet *)
      (match v with
       | Option.None -> 
        (* FIXME: this inserted assignment can slow down the
          performance because unit value would be compiled to int in
          our compiler. *)
        let rete = S.Evar(retv,Rusttypes.Tunit) in
        let assign_ret = S.Sdo (S.Eassign(rete, S.Eunit, Rusttypes.Tunit)) in
        return (S.Ssequence(assign_ret, (S.Sreturn rete)))
       | Option.Some e ->
         transl_expr e >>= fun e' ->
         let retty = Rustsyntax.typeof e' in
         let rete = S.Evar(retv, retty) in
         let assign_ret = S.Sdo (S.Eassign(rete, e', Rusttypes.Tunit)) in
         return (S.Ssequence(assign_ret, (S.Sreturn rete))))
    | Smatch (e, cases) ->
      transl_expr e >>= fun e' ->
      map_m cases (fun case -> lower_case case (S.typeof e') retv) >>= fun cases' ->
      let table = Trans_match.skeleton_table cases' e' in
      Trans_match.transl_pat_table table
    | Sscope s ->
      backup_locals >>= fun old_locals ->
      transl_stmt s >>= fun s' ->
      restore_locals old_locals >>= fun _ ->
      return s'

  let warp_return_stmt (retv: ident) (rety: Rusttypes.coq_type) (s: Rustsyntax.statement) : Rustsyntax.statement =
    let rete = Rustsyntax.Evar(retv, rety) in
    (* When return type is unit, we should initialize it because the function body may not contain its initialization *)
    match rety with
    | Rusttypes.Tunit ->
      let assign_retv = Rustsyntax.Sdo(Rustsyntax.Eassign(rete, Rustsyntax.Eunit, Rusttypes.Tunit)) in
      Rustsyntax.Ssequence(s,  Rustsyntax.Ssequence(assign_retv, Rustsyntax.Sreturn rete))
    | _ ->
      Rustsyntax.Ssequence(s,  (Rustsyntax.Sreturn rete))

  let transl_fn (f: fn) : Rustsyntax.coq_function monad =
    backup_locals >>= fun old_locals ->
    (* convert origins from string to ident *)
    convert_origins f.generic_origins >>= fun orgs ->
    (* TODO: check the binding of the generic origins  *)
    convert_origin_relations f.origin_relations >>= fun rels ->
    transl_ty f.return >>= fun fn_return ->
    map_m f.params
      (fun (x, t) ->
       transl_ty t >>= fun t' ->
       reg_local_type x t' >>= fun i ->
       return (i, t')) >>= fun fn_params ->
    (* Generate the return variable *)
    get_or_new_ident "_retv" >>= fun retv ->
    transl_stmt retv f.body >>= fun fn_body ->
    restore_locals old_locals >>= fun _ ->
    (* We add return statement to the end to ensure no UB and help the borrow checking *)
    let body = warp_return_stmt retv fn_return fn_body in
    let open Rustsyntax in
    (* We should add explicit return variable in Rustsyntax function
    to prevent from not collecting it in Rustlightgen *)
    return ({fn_generic_origins = orgs; fn_origins_relation = rels; fn_drop_glue = None; fn_return = (retv, fn_return); fn_params; fn_body = body; fn_callconv = AST.cc_default })

  (* Convert state to string tables (Camlcoq.atom_of_string and
  Camcoq.string_of_atom) which are used in the pretty printing in the
  following passes *)
  let convert_strtbls (st: state) =
      IdMap.fold (fun str i _ -> Hashtbl.add Camlcoq.atom_of_string str i) st.symmap ();
      (* set ident -> string tables  *)
      IdentMap.fold (fun i str _ -> Hashtbl.add Camlcoq.string_of_atom i str) st.rev_symmap ();
      Camlcoq.next_atom := st.next_ident

  let create_dropglue_ident (a: ident) : ident monad =
    (* use the name of a in the end of drop in place *)
    rev_ident a  >>= fun str ->
    let name = Printf.sprintf "__drop_in_place_%s" str in
    get_or_new_ident name

  let ident_mem x xs =
    List.exists (fun y -> Camlcoq.P.compare x y = 0) xs

  let rec direct_type_deps (t: Rusttypes.coq_type) : ident list =
    let module T = Rusttypes in
    match t with
    | T.Tstruct (_, id) | T.Tvariant (_, id) -> [id]
    | T.Tarray (t', _) -> direct_type_deps t'
    | T.Tunit | T.Tint (_, _) | T.Tlong _ | T.Tfloat _ -> []
    | T.Tfunction (_, _, _, _, _) | T.Tbox _ | T.Treference (_, _, _) | T.Tadt _ -> []

  let member_deps (m: Rusttypes.member) : ident list =
    direct_type_deps (Rusttypes.type_member m)

  let composite_id (Rusttypes.Composite (id, _, _, _, _)) = id

  let composite_deps (Rusttypes.Composite (id, _, members, _, _)) =
    List.filter (fun dep -> Camlcoq.P.compare dep id <> 0)
      (List.flatten (List.map member_deps members))

  let order_composites (comp_defs: Rusttypes.composite_definition list) =
    (* Emit composites in an order where direct layout dependencies appear
       first. Box/reference edges are ignored because they do not require
       the pointee composite to be complete. *)
    let rec loop done_ids ordered pending =
      match pending with
      | [] -> List.rev ordered
      | _ ->
        let ready, blocked =
          List.partition
            (fun comp -> List.for_all (fun dep -> ident_mem dep done_ids) (composite_deps comp))
            pending in
        match ready with
        | [] -> List.rev ordered @ pending
        | _ ->
          let done_ids' = (List.map composite_id ready) @ done_ids in
          loop done_ids' (List.rev_append ready ordered) blocked
    in
    loop [] [] comp_defs

  let generate_composites_and_empty_drop_glues  =
    get_st >>= fun st ->
    let comp_defs = order_composites (IdentMap.fold (fun _ c cs -> c::cs) st.composites []) in
    map_m comp_defs 
      (fun (Rusttypes.Composite(id,_,_,_,_)) -> 
        create_dropglue_ident id >>= fun drop_id ->
        return ((drop_id, Rustsyntax.empty_drop_globdef id))
      ) >>= fun drops ->
    return (comp_defs, drops)

let destination : string option ref = ref None

let print_Rustsyntax_if rev_symmap comp_defs external_funs fun_defs =
  match !destination with
  | None -> ()
  | Some f ->
    let log = Format.formatter_of_out_channel (open_out f) in
  Format.fprintf log "RustAST: @.";
  Format.fprintf log "@[<v 0>";
  List.iter (pp_print_composite rev_symmap log) comp_defs;
  List.iter
    (fun (i, g) ->
      match g with
      | AST.Gfun (Rusttypes.External (orgs, rels, _, typs, typ, _)) ->
          pp_print_fun_decl rev_symmap log i orgs rels
            (typelist_to_list typs) typ
      | _ -> failwith "unreachable (add_fn_decl)")
    external_funs;
  List.iter
    (fun (i, g) ->
      match g with
      | AST.Gfun (Rusttypes.Internal f) ->
          pp_print_function rev_symmap log i f;
          Format.fprintf log "\n"
      | _ -> failwith "unreachable (transl_fn)")
    fun_defs;
  Format.fprintf log "@]@."


  let transl_prog (p: prog) : (Rustsyntax.coq_function Rusttypes.program) monad =
    (* convert composite declarations to support mutual recursive ADT *)
    map_m (infer_composite_decls p)
      (fun (x, s_or_e, orgs, rels) -> add_composite_decl x s_or_e orgs rels) >>= fun _ ->
    map_m p.funcs
      (fun (x, f) -> add_fn x f) >>= fun _ ->
    map_m p.strucs
      (fun (x, c, orgs, rels) -> add_composite_struc x c orgs rels) >>= fun _ ->
    map_m p.enums
      (fun (x, c, orgs, rels) -> add_composite_enum x c orgs rels) >>= fun _ ->
    (* Add the declarations of externl function *)
    map_m p.fun_decls
      (fun (x, f) -> add_fn_decl x f) >>= fun _ ->
    map_m p.funcs
      (fun (x, f) ->
         transl_fn f >>= fun f' ->
         get_or_new_ident x >>= fun i ->
         return (i, (AST.Gfun (Rusttypes.Internal f')))) >>= fun fun_defs ->
    get_or_new_ident "main" >>= fun main_ident ->
    (* generate empty drop glues *)
    generate_composites_and_empty_drop_glues >>= fun (comp_defs, empty_drops) ->
    get_st >>= fun st ->
    (* set dummy origin for other use *)
    dummy_origin >>= fun dummy ->
    PrintRustsyntax.dummy_origin_ref := dummy;
    (* convert string tables *)
    convert_strtbls st;
    let var_defs = List.map (fun (ident, gvar) -> (ident, AST.Gvar gvar)) st.gvars in
    (* malloc and free empty functions *)
    let empty_malloc = (Dropglue.malloc_id, AST.Gfun(Rusttypes.External([], [], AST.EF_malloc, Rusttypes.Tnil, Rusttypes.Tunit, AST.cc_default))) in
    let empty_free = (Dropglue.free_id, AST.Gfun(Rusttypes.External([], [], AST.EF_free, Rusttypes.Tnil, Rusttypes.Tunit, AST.cc_default))) in
    (* Print AST *)
    print_Rustsyntax_if st.rev_symmap comp_defs st.external_funs fun_defs;
    (* generate prog_comp_env *)
    match Rusttypes.build_composite_env comp_defs with
    | Errors.OK comp_env ->
    return ({ Rusttypes.prog_defs = List.concat [var_defs; fun_defs; st.external_funs; empty_drops; [empty_malloc; empty_free]]
              ; Rusttypes.prog_public = [main_ident]
              ; Rusttypes.prog_main = main_ident
              ; Rusttypes.prog_types = comp_defs
              ; Rusttypes.prog_comp_env = comp_env })
    | Errors.Error msg ->
      Diagnostics.fatal_error Diagnostics.no_loc "%a" Driveraux.print_error msg
end
