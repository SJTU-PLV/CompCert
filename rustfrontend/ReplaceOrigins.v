Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR.
Require Import Errors.

Import ListNotations.
Local Open Scope error_monad_scope.

(** ** Replace origins in RustIR *)

Parameter fresh_atom: unit -> ident.

Fixpoint gensym_list (n: nat) : list ident :=
  match n with
  | O =>  nil
  | S n' =>
      let id := fresh_atom tt in
      let l := gensym_list n' in
      (id :: l)
  end.
    
(* replace origins in type with fresh origins *)

Fixpoint generate_fresh_origin_type (ty: type) : type :=
  match ty with
  | Treference _ mut ty1 =>
      let ty2 := generate_fresh_origin_type ty1 in
      let org := fresh_atom tt in
      Treference org mut ty2
  | Tbox ty1 =>
      let ty2 := generate_fresh_origin_type ty1 in
      Tbox ty2
  | Tstruct orgs id =>
      let orgs' := gensym_list (length orgs) in
      Tstruct orgs' id
  | Tvariant orgs id =>
      let orgs' := gensym_list (length orgs) in
      Tvariant orgs' id
  (* When calling a function, we replace the origins in this function
  signature with some unique origins. For example, we may call f<'a,
  'b> but we should replace 'a and 'b with fresh origins. We should
  check that the region relations are the same as in the function
  declaration when we check the uniqueness of regions names in the
  borrow checking pass *)
  | Tfunction orgs rels tyl rety cc =>
      let orgs1 := gensym_list (length orgs) in      
      let subst_pairs := combine orgs1 orgs in
      replace_origin_in_type (Tfunction orgs rels tyl rety cc) subst_pairs
  | _ => ty
  end.
            
(* replace origins in variables *)

Definition  generate_fresh_origin_var (var: ident * type) (l: list (ident * type)) : list (ident * type) :=
  let (id, ty) := var in
  let ty' :=  generate_fresh_origin_type ty in
  (id, ty') :: l.

Definition generate_fresh_origin_vars (vars: list (ident * type)) : list (ident * type) :=
  fold_right  generate_fresh_origin_var nil vars.


Section TYPE_ENV.

  Variable ce: composite_env.
  (* global variabes: do not replace their origin *)
  Variable gvars: list ident.
  (* map from var/param to its type *)
  Variable e : PTree.t type.

  Fixpoint replace_origin_place (p: place) : res place :=
    (* check whethere this place is global *)
    if in_dec ident_eq (local_of_place p) gvars then OK p
    else
    match p with
    | Plocal id ty =>
        match e!id with
        | Some ty' => OK (Plocal id ty')
        | None => Error [CTX id; MSG ": this variable has unknown type"]
        end
    | Pderef p ty =>
        do p' <- replace_origin_place p;
        match typeof_place p' with
        | Treference _ _ ty'
        | Tbox ty' =>
            OK (Pderef p' ty')
        | _ =>
            Error [CTX (local_of_place p); MSG "dereference a non-deferencable type "]
        end
    | Pfield p fid ty =>
        do p' <- replace_origin_place p;
        match typeof_place p' with
        | Tstruct orgs id =>
            match ce!id with
            | Some co =>
                match find (fun '(Member_plain fid' _) => Pos.eqb fid fid') co.(co_members) with
                | Some memb =>
                    let fty := type_member memb in
                    if Nat.eqb (length orgs) (length co.(co_generic_origins)) then
                      let rels := combine (co.(co_generic_origins)) orgs in
                      let fty' := replace_origin_in_type fty rels in
                      OK (Pfield p' fid fty')
                    else
                      Error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    Error [CTX id; CTX fid; MSG "cannot find this field (replace_origin_place')"]
                end
            | None =>
                Error [CTX id; MSG "no such struct (replace_origin_place')"]
            end
        | _ => Error [CTX (local_of_place p); MSG "place is not a struct (replace_origin_place')"]
        end
    | Pdowncast p fid ty =>
        do p' <- replace_origin_place p;
        match typeof_place p' with
        | Tvariant orgs id =>
            match ce!id with
            | Some co =>
                match find (fun '(Member_plain fid' _) => Pos.eqb fid fid') co.(co_members) with
                | Some memb =>
                    let fty := type_member memb in
                    if Nat.eqb (length orgs) (length co.(co_generic_origins)) then
                      let rels := combine (co.(co_generic_origins)) orgs in
                      let fty' := replace_origin_in_type fty rels in
                      OK (Pdowncast p' fid fty')
                    else
                      Error [CTX id; MSG "different lengths of origins in this struct"]
                | None =>
                    Error [CTX id; CTX fid; MSG "cannot find this constructor (replace_origin_place)"]
                end
            | None =>
                Error [CTX id; MSG "no such variant (replace_origin_place)"]
            end
        | _ => Error [CTX (local_of_place p); MSG "place is not a variant (replace_origin_place)"]
        end
    end.

  (* type rewriting, does it matter? *)
  Fixpoint replace_origin_pure_expr (pe: pexpr) : res pexpr :=
    match pe with
    | Eref _ mut p ty =>
        let org := fresh_atom tt in
        do p' <- replace_origin_place p;
        let ty' := Treference org mut (typeof_place p') in
        OK (Eref org mut p' ty')
    | Eplace p _ =>
        do p' <- replace_origin_place p;
        OK (Eplace p' (typeof_place p'))
    | Ecktag p id =>
        do p' <- replace_origin_place p;
        OK (Ecktag p' id)
    | Eunop uop pe ty =>
        do pe' <- replace_origin_pure_expr pe;
        OK (Eunop uop pe' ty)
    | Ebinop bop pe1 pe2 ty =>
        do pe1' <- replace_origin_pure_expr pe1;
        do pe2' <- replace_origin_pure_expr pe2;
        OK (Ebinop bop pe1' pe2' ty)
    (* Replace regions for function signature *)
    | Eglobal id ty =>
        (* We need to generate fresh origins for each function call we encounter *)
        OK (Eglobal id (generate_fresh_origin_type ty))
    | _ => OK pe
    end.

  Definition replace_origin_expr (e: expr) : res expr :=
    match e with
    | Emoveplace p ty =>
        do p' <- replace_origin_place p;
        OK (Emoveplace p' (typeof_place p'))
    | Epure pe =>
        do pe' <- replace_origin_pure_expr pe;
        OK (Epure pe')
    end.

  Fixpoint replace_origin_exprlist (l: list expr) : res (list expr) :=
    match l with
    | nil => OK nil
    | e :: l' =>
        do e' <- replace_origin_expr e;
        do l'' <- replace_origin_exprlist l';
        OK (e' :: l'')
    end.
               
  
  Fixpoint replace_origin_statement (stmt: statement) : res statement :=
    match stmt with
    | Sassign p e =>
        do p' <- replace_origin_place p;
        do e' <- replace_origin_expr e;
        OK (Sassign p' e')
    | Sassign_variant p enum_id fid e =>
        do p' <- replace_origin_place p;
        do e' <- replace_origin_expr e;
        OK (Sassign_variant p' enum_id fid e')
    | Sbox p e =>
        do p' <- replace_origin_place p;
        do e' <- replace_origin_expr e;
        OK (Sbox p' e')
    | Sdrop p =>
        do p' <- replace_origin_place p;
        OK (Sdrop p')
    | Scall p f l =>
        do p' <- replace_origin_place p;
        do f' <- replace_origin_expr f;         
        do l' <- replace_origin_exprlist l;
        OK (Scall p' f' l')             
    | Sreturn p =>
        do p' <- replace_origin_place p;
        OK (Sreturn p')
    | Ssequence s1 s2 =>
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        OK (Ssequence s1' s2')
    | Sifthenelse e s1 s2 =>
        do e' <- replace_origin_expr e;
        do s1' <- replace_origin_statement s1;
        do s2' <- replace_origin_statement s2;
        OK (Sifthenelse e' s1' s2')
    | Sloop s =>
        do s' <- replace_origin_statement s;
        OK (Sloop s')
    | _ => OK stmt
    end.

End TYPE_ENV.

Open Scope error_monad_scope.

Definition replace_origin_function (ce: composite_env) (gvars: list ident) (f: function) : Errors.res function :=
  let vars := generate_fresh_origin_vars f.(fn_vars) in
  (* We also replace regions in parameter to treat them as local
  variables *)
  let params := generate_fresh_origin_vars f.(fn_params) in
  let locals := params ++ vars in
  if list_norepet_dec ident_eq (map fst locals) then
    let type_env := PTree_Properties.of_list locals in
    do stmt <- replace_origin_statement ce gvars type_env f.(fn_body);
    (* we need to check origins are no repeated *)
    Errors.OK (RustIR.mkfunction
                 f.(fn_generic_origins)
                 f.(fn_origins_relation)
                 f.(fn_drop_glue)
                 f.(fn_param_types)
                 f.(fn_return)
                 f.(fn_callconv)
                 vars
                 params
                 stmt)
  else Errors.Error [MSG "repeated idents in vars and params (replace_origin_function)"]
.


Definition transf_fundef (ce: composite_env) (gvars: list ident) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match replace_origin_function ce gvars f with
      | OK f' => OK (Internal f')
      | Error msg => Error ([MSG "In function "; CTX id; MSG " : "] ++ msg)
      end
  | External orgs rels ef targs tres cconv => Errors.OK (External orgs rels ef targs tres cconv)
  end.

Definition transl_globvar (id: ident) (ty: type) := OK ty.

(* borrow check the whole module *)

Definition transl_program (p: program) : res program :=
  let gvars := map fst p.(prog_defs) in
  do p1 <- transform_partial_program2 (transf_fundef p.(prog_comp_env) gvars) transl_globvar p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
              prog_public := AST.prog_public p1;
              prog_main := AST.prog_main p1;
              prog_types := prog_types p;
              prog_comp_env := prog_comp_env p;
              prog_comp_env_eq := prog_comp_env_eq p |}.
