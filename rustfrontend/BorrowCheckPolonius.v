Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR RustIRcfg.
Require Import Errors.
Require Import ReplaceOrigins.
Require Import RegionLiveness BorrowCheckDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on Polonius (dataflow analysis) *)

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at pc "; POS pc; MSG " : "].

Section COMP_ENV.

Variable (ce: composite_env).

(** Transition *)

(* Support prefixes and support origins *)

Definition support_origins (p: place) : list origin :=
  let support_prefixes := p :: support_parent_paths p in
  fold_right (fun elt acc => match elt with
                          | (Pderef p' ty) =>
                              match typeof_place p' with
                              | Treference org _ _ => org :: acc
                              | _ => acc
                              end
                          | _ => acc
                          end) nil support_prefixes.

Definition aggregate_origin_states (e: LOrgEnv.t) (orgs: list origin) : LOrgSt.t :=
  fold_left (fun acc elt => LOrgSt.lub acc (LOrgEnv.get elt e)) orgs LOrgSt.bot.

Definition map_loan_set (f: loan -> loan) (ls: LoanSet.t) : LoanSet.t :=
  LoanSet.fold (fun ln acc => LoanSet.add (f ln) acc) ls LoanSet.empty.

(** TODO: move this function to Rusttypes and use it to replace some
code in ReplaceOrigins.v *)
Definition place_field_type (ty: type) (fid: ident) : type :=
  match ty with
  | Tstruct orgs id
  | Tvariant orgs id =>
      match ce ! id with
      | Some co =>
          match field_type fid co.(co_members) with
          | OK fty =>
              let rels := combine (co.(co_generic_origins)) orgs in
              replace_origin_in_type fty rels
          (* Impossible: we have done type check *)
          | _ => Tunit
          end
      | _ =>
          (* Impossible: we have done type check *)
          Tunit
      end
  (* Impossible: we have done type check *)
  | _ => Tunit
  end.

(* We need to query the ce to get the right type for this place when
applied with ph. We need to do this because we want to maintain that
all the places in the loans set are well-typed if we want to prove the
invariance property *)
Definition apply_path_to_place (ph: path) (p: place) : place :=
  match ph with
  | ph_deref => Pderef p (deref_type (typeof_place p))
  | ph_field fid => Pfield p fid (place_field_type (typeof_place p) fid)
  | ph_downcast _ fid => Pdowncast p fid (place_field_type (typeof_place p) fid)
  end.

Definition apply_path_to_loan (ph: path) (ln: loan) :=
  match ln with
  | Lintern mut p => Lintern mut (apply_path_to_place ph p)
  | Lextern org => Lextern org
  end.
      
Definition apply_path_to_origin_state (ph: path) (st: LOrgSt.t) : LOrgSt.t :=
  match st with
  | Live ls =>
      Live (map_loan_set (apply_path_to_loan ph) ls)
  | Dead => Dead
  end.


Fixpoint raw_type_eq (ty1 ty2: type) : bool :=
  match ty1, ty2 with
  | Treference _ _ ty1, Treference _ _ ty2 =>
      raw_type_eq ty1 ty2
  | Tbox ty1, Tbox ty2 =>
      raw_type_eq ty1 ty2
  | Tstruct _ id1, Tstruct _ id2
  | Tvariant _ id1, Tvariant _ id2 =>
      ident_eq id1 id2
  | _, _ => type_eq ty1 ty2
  end.

(** Is it OK to use type_eq_except_origins? Because there may be an
region 'a that points to &i32 and &mut i32, should we consider they
may be aliased? *)
Definition filter_type_loan_set (ty: type) (ls: LoanSet.t) : LoanSet.t :=
  LoanSet.filter (fun ln => match ln with
                         | Lintern mut p => raw_type_eq (typeof_place p) ty
                         | Lextern org => true
                         end) ls.

Definition filter_type_origin_state (ty: type) (st: LOrgSt.t) : LOrgSt.t :=
  match st with
  | Live ls => Live (filter_type_loan_set ty ls)
  | Dead => Dead
  end.

(** Unused for now as we do not compute the loan that actually
represents the location of p *)
(* [pty] is the type of the loans that we expect *)
Fixpoint loans_of_place (e: LOrgEnv.t) (mut: mutkind) (p: place) : LOrgSt.t :=
  (* We should make sure that the loans we return must have the same type as typeof(p) *)
  match p with
  | Plocal id ty =>
      (Live (LoanSet.singleton (Lintern mut p)))
  | Pderef p1 ty => 
      match (typeof_place p1) with
      | Treference org Mutable _ => 
          let ls1 := loans_of_place e mut p1 in
          (* apply deref operation in ls1 *)
          (** Once we want to make our proof simple if we can make the
          loan in the region exactly represents the location the place
          may point to. But I find that when considering the
          abstraction and flow performed by function call, it is not
          possible to maintain this property. *)
          (* let ls2 := apply_path_to_origin_state ph_deref ls1 in *)
          (* ensure the type in e!org is correct *)
          let org_ls := filter_type_origin_state ty (LOrgEnv.get org e) in
          let ls3 := (LOrgSt.lub org_ls ls1) in
          LOrgSt.lub ls3 (Live (LoanSet.singleton (Lintern mut p)))
      | Treference org Immutable _ => 
          (** FIXME: for immutable reference, we do not need to
          compute the loans aliased with p1? *)
          let ls1 := LOrgEnv.get org e in
          LOrgSt.lub ls1 (Live (LoanSet.singleton (Lintern mut p)))
      (* Impossible *)
      | _ => (Live (LoanSet.singleton (Lintern mut p)))
      end
  | Pfield p1 fid fty =>
      let ls1 := loans_of_place e mut p1 in
      (* let ls2 := apply_path_to_origin_state (ph_field fid) ls1 in *)
      LOrgSt.lub ls1 (Live (LoanSet.singleton (Lintern mut p)))
  | Pdowncast p1 fid fty =>
      let ls1 := loans_of_place e mut p1 in
      (* let ls2 := apply_path_to_origin_state (ph_downcast (typeof_place p1) fid) ls1 in *)
      LOrgSt.lub ls1 (Live (LoanSet.singleton (Lintern mut p)))
  end.

(* Transition of pure expression *)

Fixpoint transfer_pure_expr (e: LOrgEnv.t) (pe: pexpr) : LOrgEnv.t :=
  match pe with
  | Eref org mut p ty =>
      (* handle reborrow: add all the loans in the support *)
      (* prefix to org *)
      let support_orgs := support_origins p in
      (* aggregate the loans in the support origins *)
      let org_st := aggregate_origin_states e support_orgs in
      let s' := LOrgSt.lub org_st (Live (LoanSet.singleton (Lintern mut p))) in
      (* let st := loans_of_place e mut p in *)
      LOrgEnv.set org s' e
  | Eunop _ pe _ =>
      transfer_pure_expr e pe
  | Ebinop _ pe1 pe2 _ =>
      let e' := transfer_pure_expr e pe1 in
      transfer_pure_expr e' pe2
  (* Other constants *)
  | _ => e
  end.

Fixpoint check_pure_expr (e: LOrgEnv.t) (pe: pexpr) : res unit :=
  match pe with
 | Eplace p ty =>
      if illegal_access e p Adeep Aread then
        Error [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Eplace"]
      else
        OK tt
  | Eref org mut p ty =>
      let ak := match mut with | Mutable => Awrite | Immutable => Aread end in
      if illegal_access e p Adeep ak then
        Error [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Eref"]
      else
        OK tt
  | Ecktag p id =>
      if illegal_access e p Ashallow Aread then
        Error [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Ecktag"]
      else
        OK tt
  | Eunop _ pe _ =>
      check_pure_expr e pe
  | Ebinop _ pe1 pe2 _ =>
      do _ <- check_pure_expr e pe1;
      let e' := transfer_pure_expr e pe1 in
      check_pure_expr e' pe2
  (* Other constants *)
  | _ => OK tt 
  end.

(* transfer expression *)

Definition transfer_expr (oe: LOrgEnv.t) (e: expr) : LOrgEnv.t :=
  match e with
  | Emoveplace p ty =>
      oe
  | Epure pe =>
      transfer_pure_expr oe pe
  end.

Definition check_expr (oe: LOrgEnv.t) (e: expr) : res unit :=
  match e with
  | Emoveplace p ty =>
      if illegal_access oe p Adeep Awrite then
        Error [MSG "access a place (transfer_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Emoveplace"]
      else 
        OK tt
  | Epure pe =>
      check_pure_expr oe pe
  end.


Fixpoint transfer_exprlist (oe: LOrgEnv.t) (l: list expr) : LOrgEnv.t :=
  match l with
  | [] => oe
  | e :: l' =>
      let oe' := transfer_expr oe e in
      transfer_exprlist oe' l'
  end.

Fixpoint check_exprlist (oe: LOrgEnv.t) (l: list expr) : res unit :=
  match l with
  | [] => OK tt
  | e :: l' =>
      do _ <- check_expr oe e;
      let oe' := transfer_expr oe e in
      check_exprlist oe' l'
  end.


(* Flowing loans from source type to destination type *)

Definition flow_loans_by_regions (e: LOrgEnv.t) (org_src org_tgt: origin) (fk: flow_kind) : LOrgEnv.t :=
  match fk with
  | ByVal =>
      let st := LOrgSt.lub (LOrgEnv.get org_src e) (LOrgEnv.get org_tgt e) in
      LOrgEnv.set org_tgt st e
  | ByRef =>
      LOrgEnv.union org_src org_tgt e
  end.

(* Subtyping rules of rust borrow checker *)
Fixpoint flow_loans (e: LOrgEnv.t) (s d: type) (fk: flow_kind) : LOrgEnv.t :=
  match s,d with
  | Treference org1 mut1 ty1, Treference org2 mut2 ty2 =>
      let e1 := flow_loans_by_regions e org1 org2 fk in
      (* Rust does not support "types differ in mutability", so we can
         assume that the type checking has check that mut1 = mut2 *)
      let fk' := match mut1 with
                | Mutable => ByRef
                | Immutable => ByVal
                 end in
      flow_loans e1 ty1 ty2 (meet_flow_kinds fk fk')
  | Tbox ty1, Tbox ty2 =>
      (* Box is covariant over ty1/ty2*)
      flow_loans e ty1 ty2 (meet_flow_kinds fk ByVal)
  | Tstruct orgs1 id1, Tstruct orgs2 id2 
  | Tvariant orgs1 id1 , Tvariant orgs2 id2 =>
      (* type checking must ensure that id1 == id2 and len(orgs1) ==
      len(orgs2). We use id1 below *)
      (** TODO: for now we simplify the subtyping by assuming that the
      user defined type is **invariant** over each of the origin. To
      deal with this restriction, we need to write a function to query
      that what subtyping rule should be applied for a give origin *)
      let orgs := combine orgs1 orgs2 in
      fold_left (fun acc '(o1, o2) => LOrgEnv.union o1 o2 acc) orgs e
  (* scalar type *)
  | _, _ => e
  end.
          
Fixpoint flow_loans_list (e: LOrgEnv.t) (ls ld: list type) (k: flow_kind) : LOrgEnv.t :=
  match ls, ld with
  | s :: ls', d :: ld' =>
      flow_loans_list (flow_loans e s d k) ls' ld' k
  | _, _ =>
      e
  end.

(* Shallow write a place *)

Definition check_shallow_write_place (e: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access e p Ashallow Awrite then
    Error [MSG "access a place (shallow_write_place) which is borrowed; id is "; CTX (local_of_place p)]    
  else
    OK tt.

(* Auxilary functions for transition of statements *)

Definition kill_place_related_loans (p: place) (st: LOrgSt.t) : LOrgSt.t :=
  match st with
  | Live ls =>
      Live (LoanSet.filter (fun elt => match elt with
                              (* Note that we also clear p, so
                              clear_dead_loans should be perfomed
                              after check_shallow_write_place *)
                              | Lintern _ p' => negb (is_prefix p p')
                              | _ => true
                              end) ls)
  | Dead => Dead
  end.

(* When some loan [p] is overwritten, it should be cleared *)
Definition kill_loans (e: LOrgEnv.t) (p: place) : LOrgEnv.t :=
  LOrgEnv.map1 (kill_place_related_loans p) e.

(* Borrow check an assign statement *)

Definition transfer_assign_base (oe: LOrgEnv.t) (p: place) (e: expr) : LOrgEnv.t :=
  transfer_expr oe e.

Definition transfer_assignment (oe: LOrgEnv.t) (p: place) (e: expr) : LOrgEnv.t :=
  (* simple type checking *)
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  let oe1 := transfer_assign_base oe p e in
  (* After checking the evaluation of e *)
  let oe2 := kill_loans oe1 p in
  flow_loans oe2 ty_src ty_dest ByVal.

(* The checking function is used for all kinds of assignment *)
Definition check_assignment (oe: LOrgEnv.t) (p: place) (e: expr) : res unit :=
  do _ <- check_expr oe e;
  let oe1 := transfer_assign_base oe p e in
  check_shallow_write_place oe1 p.


Definition transfer_assign_variant (oe: LOrgEnv.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : LOrgEnv.t :=
  match typeof_place p with
  | Tvariant orgs_dest vid =>
      (* enum_id must be equal to vid, and we use vid below *)
      match ce!vid with
      | Some co =>
          match field_type fid (co_members co) with
          | OK ty_i =>
              let ty_src := typeof e in
              let orgs_src := co.(co_generic_origins) in
              let ty_dest := replace_origin_in_type ty_i (combine orgs_src orgs_dest) in
              let oe1 := transfer_assign_base oe p e in
              (* After checking the evaluation of e *)
              let oe2 := kill_loans oe1 p in
              flow_loans oe2 ty_src ty_dest ByVal
          (* It would cause error before borrow checking *)
          | _ => oe
          end
      (* It would cause error before borrow checking *)            
      | _ => oe
      end
  (* It would cause error before borrow checking *)
  | _ => oe
  end.

Definition transfer_Sbox (oe: LOrgEnv.t) (p: place) (e: expr) : LOrgEnv.t :=
  (* [typeof_place p] must be Tbox, which should be checked at type
  checking phase *)
  let ty_dest := typeof_place p in
  let ty_src := Tbox (typeof e) in
  let oe1 := transfer_assign_base oe p e in
  (* After checking the evaluation of e *)
  let oe2 := kill_loans oe1 p in
  flow_loans oe2 ty_src ty_dest ByVal.

  
(* bind the origins in two type *)
Fixpoint bind_type_origins (ty1 ty2: type) (fk: flow_kind) : list (origin * origin * flow_kind) :=
  match ty1, ty2 with
  | Treference org1 _ ty1, Treference org2 _ ty2 =>
      (org1, org2, fk) :: bind_type_origins ty1 ty2 ByRef
  | Tbox ty1, Tbox ty2 =>
      bind_type_origins ty1 ty2 ByRef
  | Tstruct orgs1 id1, Tstruct orgs2 id2
  | Tvariant orgs1 id1, Tvariant orgs2 id2 =>
      (* TODO: support covariant *)
      let len := length orgs1 in
      (combine (combine orgs1 orgs2) (repeat ByRef len))
      (* else *)
      (*   Error (error_msg pc ++ [MSG "mismatch between the length of origins in type"; CTX id1; MSG "(bind_type_origins)"]) *)
  | _, _ => []
  end.

Fixpoint bind_type_origins_list (tyl: list (type * type)) :=
  match tyl with
  | nil => nil
  | (ty1, ty2) :: tyl =>
      bind_type_origins ty1 ty2 ByVal ++ (bind_type_origins_list tyl)
  end.

Definition flow_loans_origin_to_origin (se te: LOrgEnv.t) (src tgt: origin) : LOrgEnv.t :=
  LOrgEnv.set tgt (LOrgSt.lub (LOrgEnv.get src se) (LOrgEnv.get tgt te)) te.
  (* match LOrgEnv.get src se, LOrgEnv.get tgt te with *)
  (* | Live ls1, Live ls2 => *)
  (*     let te' := LOrgEnv.set tgt (Live (LoanSet.union ls1 ls2)) te in *)
  (*     OK te' *)
  (* | _, _ => *)
  (*     Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin"]) *)
  (* end. *)


Fixpoint flow_loans_bind (se: LOrgEnv.t) (te: LOrgEnv.t) (rels: list origin_rel) (l: list (origin * origin * flow_kind)) : LOrgEnv.t * list origin_rel :=
  match l with
  | nil => (te, rels)
  | (src, tgt, fk) :: l' =>
      let te' := flow_loans_origin_to_origin se te src tgt in
      let rels' := 
        match fk with
        | ByRef =>
            (src, tgt) :: rels
        | ByVal =>
            rels
        end in
      flow_loans_bind se te' rels' l'
  end.

(* flow the loans from parameter to callee arguments and return the
pair of origins for which we should generate invariant constrain *)
Definition bind_param_origins (e: LOrgEnv.t) (fe: LOrgEnv.t) (ptyl ftyl: list type) : (LOrgEnv.t * list origin_rel) :=
  let bind_pairs := bind_type_origins_list (combine ptyl ftyl) in
  flow_loans_bind e fe nil bind_pairs.
  (* else *)
  (*   Error (error_msg pc ++ [MSG "mismatch between the lengths of types (bind_param_origins)"]). *)

(** Assumption: the relations of origin given by the function
signature has been sorted topologically, to ensure that we just need
to flow the origins in one round instead of flowing it until reaching
a fixed point *)
Definition after_call (fe: LOrgEnv.t) (rels: list origin_rel) : LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               (* it may be less efficient *)
               flow_loans_origin_to_origin acc acc src tgt) rels fe.


Definition flow_loans_origin_to_origin_with_alias (fe e: LOrgEnv.t) (forg org: origin) : LOrgEnv.t :=
  LOrgEnv.set org (LOrgSt.lub (LOrgEnv.get forg fe) (LOrgEnv.get org e)) e.

  (* match LOrgEnv.get src se, LOrgEnv.get tgt te with *)
  (* | Live ls1, Live ls2 => *)
  (*     let te' := set_loans_with_alias tgt (LoanSet.union ls1 ls2) te ag in *)
  (*     OK te' *)
  (* | _, _ => *)
  (*     Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin_with_alias"]) *)
  (* end. *)

(* Flow back the loans based on the invariant relation established by
the bind_params_origins *)
Fixpoint flow_alias_after_call (rels: list origin_rel) (fe e: LOrgEnv.t) : LOrgEnv.t :=
  match rels with
  | nil => e
  | (org, forg) :: rels' =>
      flow_alias_after_call rels' fe (flow_loans_origin_to_origin_with_alias fe e forg org)
  end.

Definition flow_return_after_call (fe e: LOrgEnv.t) (frety tgt_ty: type) : LOrgEnv.t :=
  let l := bind_type_origins frety tgt_ty ByVal in
  fst (flow_loans_bind fe e nil l).
  (* (* we do not care the alias relation *) *)
  (* do (te', _) <- fold_left (flow_loans_bind_acc pc se) l (OK (te, nil)); *)
  (* OK te'. *)

(** TODO: to make it simpler  *)
Definition transfer_function_call (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : LOrgEnv.t :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      (* transfer the arguments *)
      let oe2 := transfer_exprlist oe1 args in      
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          oe2
      | None =>
          (* Move it to rusttyping. if forallb (fun '(ty1, ty2) => type_eq_except_origins ty1 ty2) (combine arg_tyl sig_tyl) && type_eq_except_origins tgt_rety rty then *)
          (* construct empty origin environments for function origins *)
          let foe1 := LOrgEnv.bot in
          let (foe2, rels) := bind_param_origins oe2 foe1 args_tyl sig_tyl in
          (* use the origin relation to simulate the flow of loans
             in the caller. foe2 is the initial env in the callee,
             foe3 is the final env *)
          let foe3 := after_call foe2 org_rels in
          (* update the invariant relation established by the
          evaluation of function parameters *)
          let oe3 := flow_alias_after_call rels foe3 oe2 in
          (* shallow write to p *)
          (* do oe4 <- shallow_write_place pc f oe3 p; *)
          (* after check_shallow_write_place *)
          let oe4 := kill_loans oe3 p in
          (flow_return_after_call foe3 oe4 rty tgt_rety)
          (* (* kill relevant loans *) *)
          (*   let live3 := kill_loans live2 p in *)
          (*   (* flow loans to the return type and update alias *) *)
          (*   do oe4 <- flow_alias_after_call pc ag2 rels foe3 oe3; *)
          (*   do oe5 <- flow_return_after_call pc ag2 foe3 oe4 rty tgt_rety; *)
          (*   OK (live3, oe5, ag2) *)
          (* else *)
          (*   Error (error_msg pc ++ [MSG "type checking fails in check_function_call"]) *)
      end
  | _ => oe1
(* Error (error_msg pc ++ [MSG "it is not a function type in check_function_call"])       *)
  end.

Definition check_function_call (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : res unit :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      do _ <- check_exprlist oe1 args;
      (* transfer the arguments *)
      let oe2 := transfer_exprlist oe1 args in      
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          OK tt
      | None =>
          (* Move it to rusttyping. if forallb (fun '(ty1, ty2) => type_eq_except_origins ty1 ty2) (combine arg_tyl sig_tyl) && type_eq_except_origins tgt_rety rty then *)
          (* construct empty origin environments for function origins *)
          let foe1 := LOrgEnv.bot in
          let (foe2, rels) := bind_param_origins oe2 foe1 args_tyl sig_tyl in
          (* use the origin relation to simulate the flow of loans
             in the caller. foe2 is the initial env in the callee,
             foe3 is the final env *)
          let foe3 := after_call foe2 org_rels in
          (* update the invariant relation established by the
          evaluation of function parameters *)
          let oe3 := flow_alias_after_call rels foe3 oe2 in
          (* shallow write to p *)
          (* do oe4 <- shallow_write_place pc f oe3 p; *)
          check_shallow_write_place oe3 p
      end
  | _ => OK tt
  end.

End COMP_ENV.

Definition transfer_storagedead (f: function) (oe1: LOrgEnv.t) (id: ident) : LOrgEnv.t :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      (* After check_shallow_write_place *)
      (kill_loans oe1 (Plocal id ty))
  | None =>
      (* report errors in the type checking *)
      oe1
  end.

Definition check_storagedead (f: function) (oe1: LOrgEnv.t) (id: ident) : res unit :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      check_shallow_write_place oe1 (Plocal id ty)
  | _ =>
      OK tt
  end.

(** TODO: we need to consider p is initialized or not *)
Definition check_drop (oe1: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access oe1 p Adeep Awrite then
    Error [MSG "access a place which is borrowed: "; CTX (local_of_place p); MSG "in (check_drop)"]
  else OK tt.

(** All the relations between the generic origins after the function
call must be declared in the function sigature *)

Definition live_origin (st: origin_state) : bool :=
  match st with
  | Live _ => true
  | Dead => false
  end.

Definition absence_of_internal_loans (st: LOrgSt.t) : bool :=
  match st with
  | Live ls =>
      LoanSet.for_all (fun ln => match ln with
                              | Lintern _ _ => false
                              | Lextern _ => true
                              end) ls
  (* Impossible *)
  | _ => true
  end.

(* Check if there is a generic region containing some internal loans
at the function return *)
Definition check_dangling (f: function) (e: LOrgEnv.t) : bool :=
  forallb (fun org => absence_of_internal_loans (LOrgEnv.get org e)) f.(fn_generic_origins).

Definition check_generic_origins_relations (f: function) (e: LOrgEnv.t) : bool :=
  (* This property can be guaranteed by the liveness analysis: All the
  generic origin must not be dead otherwise we are returing a dangling
  pointer *)
  (* forallb (fun org => live_origin (LOrgEnv.get org e)) f.(fn_generic_origins) && *)
  forallb (fun org1 =>
             forallb (fun org2 =>
                        if Pos.eqb org1 org2 then true
                        else match LOrgEnv.get org1 e, LOrgEnv.get org2 e with
                             | Live ls1, Live ls2 =>
                                 if LoanSet.subset ls1 ls2 then
                                   in_dec origin_rel_eq_dec (org1, org2) f.(fn_origins_relation)
                                 else if LoanSet.subset ls2 ls1 then
                                        in_dec origin_rel_eq_dec (org2, org1) f.(fn_origins_relation)
                                      else true
                             (* generic origins must be live which
                             should be already checked *)
                             | _, _ => false
                             end) f.(fn_generic_origins)) f.(fn_generic_origins).
  
(* We need to transfer the loans from the return variable to the
return type of this function *)
Definition transfer_return (oe1: LOrgEnv.t) (p: place) (rety: type) : LOrgEnv.t :=
  flow_loans oe1 (typeof_place p) rety ByVal.

Definition check_return (f: function) (oe1: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access oe1 p  Adeep Aread then
    (* Question: this error should be impossible (or the error has
    been found before this return statement)? Because there is no live
    regions (except generic regions) after the return statement. *)
    Error [MSG "access a place which is borrowed"; CTX (local_of_place p); MSG "in (transfer_return)"]
  else
    let oe2 := transfer_return oe1 p f.(fn_return) in
    (** TODO: we still do not know how to check generic origins
        at the end of the function using the Rustcfg
        framework.... *)
    if check_dangling f oe2 then
      if check_generic_origins_relations f oe2 then
        OK tt
      else
        Error [MSG "some relations in function return are not declared in the function signature"]
    else
      Error [MSG "Dangling pointer! There should not be internal loans in the generic regions at the function return"].

(* Transition of statements *)
        
Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (live: PMap.t RegionSet.t) (generic_regions: RegionSet.t) (pc: node) (before: LoansEnv.t) : LoansEnv.t :=
  match before with
  | LoansEnv.Bot => before
  | LoansEnv.State oe =>
      (* apply liveness result before transfer *)
      let live_after := PMap.get pc live in
      let live_before := RegionLiveness.transfer f cfg generic_regions pc live_after in
      let oe := LOrgEnv.apply_liveness live_before oe in
      let finish_transfer oe := (LoansEnv.State (LOrgEnv.apply_liveness live_after oe)) in
      match cfg ! pc with
      | None => LoansEnv.Bot
      | Some (Inop _) => before
      | Some (Icond e _ _) => LoansEnv.State (transfer_expr oe e)
      | Some Iend => before
      | Some (Isel sel next) =>
          match select_stmt f.(fn_body) sel with
          | None => LoansEnv.Bot
          | Some s =>
              match s with
              | Sassign p e => 
                  finish_transfer (transfer_assignment oe p e)
              | Sassign_variant p enum_id fid e =>
                  finish_transfer (transfer_assign_variant ce oe p enum_id fid e)
              | Sbox p e =>
                  finish_transfer (transfer_Sbox oe p e)
              | Scall p e l =>
                  finish_transfer (transfer_function_call oe p e l)
              | Sstoragedead id =>
                  finish_transfer (transfer_storagedead f oe id)
              (** Because our drop cannot access the region (i.e., the
              reference), so there is no need to make the region live
              until this drop statement. We do not need the technique
              of drop check for now. *)
              | Sreturn p =>
                  (* This transfer may be useless as we do not look up
                  the abstract state after the return *)
                  LoansEnv.State (transfer_return oe p f.(fn_return))
              | _ => before
              end 
          end
      end
  end.

Module LoansFlow := Dataflow_Solver(LoansEnv)(NodeSetForward).


(** Initialization *)

(* The rule I-Fun. Maybe we should just initialize the generic origins
that appear in the arguments? *)
Definition init_function (f: function) : LOrgEnv.t :=
  (* initialize the loans of generic regions *)
  let oe1 := fold_left (fun acc elt =>
                          let os := Live (LoanSet.singleton (Lextern elt)) in
                          LOrgEnv.set elt os acc) f.(fn_generic_origins) LOrgEnv.bot in
  (* flow the loans from the function arguments to the parameters *)
  flow_loans_list oe1 f.(fn_param_types) (map snd f.(fn_params)) ByVal.
  
(** Run Liveness analysis and Loans-flow analysis *)

Definition loans_flow_analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t RegionSet.t * (PMap.t LoansEnv.t)) :=
  (* Liveness analysis for regions *)
  let generic_regions := live_generic_regions (fn_generic_origins f) in
  match RegionLiveness.analyze f cfg with
  | Some live =>
      let init_oe := init_function f in
      match LoansFlow.fixpoint cfg successors_instr (transfer ce f cfg live generic_regions) entry (LoansEnv.State init_oe) with
      (* For now we return liveness result for debug purpose *)
      | Some m => OK (live, m)
      | None =>
          Error [MSG "The loans-flow analysis fails with unknown reason"]
      end
  | None => 
      Error [MSG "The loans-flow analysis fails due to the failure of liveness analysis"]
  end.

(** Checking functions that are used in the transl_on_cfg *)

Definition borrow_check_stmt_aux (f: function) (le: LoansEnv.t) (stmt: statement) : res unit :=
  match le with
  | LoansEnv.State oe =>
      match stmt with
      | Sassign p e
      | Sassign_variant p _ _ e
      | Sbox p e =>
          check_assignment oe p e
      | Scall p e l =>
          check_function_call oe p e l
      | Sstoragedead id =>
          check_storagedead f oe id
      | Sdrop p =>
          check_drop oe p
      | Sreturn p =>
          check_return f oe p
      | _ =>
          OK tt
      end
  (* Impossible execution, but we should not report error *)
  | _ =>
      (* Error [MSG "Impossible: it is unreachable point"] *)
      OK tt
  end.
  
Definition borrow_check_stmt (f: function) (le: LoansEnv.t) (stmt: statement) : res statement :=
  do _ <- borrow_check_stmt_aux f le stmt;
  OK stmt.

Definition borrow_check_cond_expr (le: LoansEnv.t) (e: expr) : res unit :=
  match le with
  | LoansEnv.State oe =>
      check_expr oe e
  (* Impossible *)
  | _ =>
      (* Error [MSG "Impossible: it is unreachable point"] *)
      OK tt
  end.

Definition get_borck_result (borck_res: (PMap.t LoansEnv.t)) (pc: node) : LoansEnv.t :=
  borck_res !! pc.

(* After calling borrow_check, we should find if there is any borrow
check error *)
Definition collect_borrow_check_result (ce: composite_env) (f: function) (cfg: rustcfg) (loans_flow_res: (PMap.t RegionSet.t * (PMap.t LoansEnv.t))) : res unit :=
  do _ <- transl_on_cfg get_borck_result (snd loans_flow_res) (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg;
  OK tt.

(** TODO: we should combine it with move_check_function *)

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** 1. Loans-flow analysis *)
  do loans_flow_res <- loans_flow_analyze ce f cfg entry;
  (** 2. Collect result of the borrow checking ! *)
  collect_borrow_check_result ce f cfg loans_flow_res.

Definition transf_fundef (ce: composite_env) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match borrow_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error ([MSG "In function "; CTX id; MSG " : "] ++ msg)
      end
  | External orgs rels ef targs tres cconv => Errors.OK (External orgs rels ef targs tres cconv)
  end.

Definition transl_globvar (id: ident) (ty: type) := OK ty.

(** TODO  *)
Definition check_origins_well_formedness (p: program) : bool :=
  true.

(* borrow check the whole module *)

Definition borrow_check_program (p: program) : res unit :=
  (* ensure that replaceOrigins has been executed before borrow checking *)
  if check_origins_well_formedness p then
    do _ <- transform_partial_program2 (transf_fundef p.(prog_comp_env)) transl_globvar p;
    OK tt
  else
    Error (msg "Origins in the program are not well formed").
