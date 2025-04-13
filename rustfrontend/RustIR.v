Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight Rustlight Rustlightown.
Require Import InitDomain.

Import ListNotations.

(** * Rust Intermediate Rrepresentation  *)

(** To compile Rustlight to RustIR, we replace the scopes (let stmt)
with StorageLive (StorageDead) statements, use AST to represent the
program, analyze the AST by first transforming it to CFG (using
selector technique) and insert explicit drop operations (so that the
RustIR has no ownership semantics) *)


(* The definitions of expression and place are the same as Rustlight *)

(** Statement: we add [Storagelive] and [Storagedead] to indicate the
lifetime of a local variable, because all the variables are declared
in the entry of function which is different from Rustlight. For now,
this two statements have no semantics. They are used for borrow
checking. We use [drop(p)] statement to indicate that we may need to
drop the content of [p] depending on the ownership environment. The
[Sreturn] returns the a predefined return variable instead of an
expression because we need to insert drop between the evaluation of
the returned expression and the return statement *)

Inductive statement : Type :=
| Sskip: statement                   (**r do nothing *)
| Sassign: place -> expr -> statement (**r assignment [place = rvalue] *)
| Sassign_variant : place -> ident -> ident -> expr -> statement (**r [place] = [ident(expr)] *)
| Sbox: place -> expr -> statement       (**r [place = Box::new(expr)]  *)
| Sstoragelive: ident -> statement       (**r id becomes avalible *)
| Sstoragedead: ident -> statement       (**r id becomes un-avalible *)
| Sdrop: place -> statement             (**r conditionally drop the place [p]. [p] must be an ownership pointer. *)
| Scall: place -> expr -> list expr -> statement (**r function call, p = f(...). It is a abbr. of let p = f() in *)
| Ssequence: statement -> statement -> statement  (**r sequence *)
| Sifthenelse: expr  -> statement -> statement -> statement (**r conditional *)
| Sloop: statement -> statement (**r infinite loop *)
| Sbreak: statement                      (**r [break] statement *)
| Scontinue: statement                   (**r [continue] statement *)
| Sreturn: place -> statement.      (**r [return p] statement. [p] is the specific return variable. *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue: option ident;
  fn_return: type;
  fn_callconv: calling_convention;
  fn_vars: list (ident * type);
  fn_params: list (ident * type);
  fn_body: statement
}.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc
  end.

(* A good interal function must be not the drop glue function holder,
a good external function must not be malloc/free *)
Definition function_not_drop_glue fd : Prop :=
  match fd with
  | Internal f =>
    match fn_drop_glue f with
    | None => True
    | Some _ => False
    end
  | External _ _ EF _ _ _ =>
    match EF with
    | EF_malloc => False
    | EF_free => False
    | _ => True
    end
  end.

(* some helper function *)

Fixpoint makeseq (l: list statement) : statement :=
  match l with
  (* To ensure that target program must move at least one step. It is used to handle the empty list execution in dropplace. Because we should use plus simulation diagram so we should let target program makes a step. *)
  | nil => (Ssequence Sskip Sskip)
  | s :: l' => Ssequence s (makeseq l')
  end.

Local Open Scope error_monad_scope.

(** Genenrate drop map which maps composite id to its drop glue id *)


(* Extract composite id to drop glue id list *)
Definition extract_drop_id (g: ident * globdef fundef type) : ident * ident :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => (comp_id, glue_id)
      | None => (1%positive, glue_id)
      end
  | _ => (1%positive, glue_id)
  end.

Definition check_drop_glue (g: ident * globdef fundef type) : bool :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => true
      | None => false
      end
  | _ => false
  end.

Definition generate_dropm (p: program) :=
  let drop_glue_ids := map extract_drop_id (filter check_drop_glue p.(prog_defs)) in
  PTree_Properties.of_list drop_glue_ids.


(** General semantics definitions *)

Section SEMANTICS.

(** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.


Inductive function_entry (ce: composite_env) (f: function) (vargs: list val) (m: mem) (e: env) (m': mem) : Prop :=
| function_entry_intro: forall m1,
    list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
    alloc_variables ce empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
    bind_parameters ce e m1 f.(fn_params) vargs m' ->
    function_entry ce f vargs m e m'.

End SEMANTICS.

(* Used in RustIRown and InitAnalysis *)

Section COMP_ENV.

Variable ce : composite_env.

Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign_variant p _ _ e
  | Sassign p e
  | Sbox p e =>
      collect_place ce p (collect_expr ce e m)
  | Scall p _ al =>
      collect_place ce p (collect_exprlist ce al m)
  | Sreturn p =>
      collect_place ce p m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_stmt s1 (collect_stmt s2 (collect_expr ce e m))
  | Sloop s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
  (** TODO: add all the parameters and variables to l (may be useless?) *)
  let init_map := fold_right (collect_place ce) (PTree.empty LPaths.t) l in
  OK (collect_stmt f.(fn_body) init_map).

End COMP_ENV.

(* Repeated definitions from Rustlightown because the genvs are
different *)
Section DROPMEMBER.

Variable ge: genv.

(** Some definitions for dropstate and dropplace *)

(* It corresponds to drop_glue_for_member in Clightgen *)
Definition type_to_drop_member_state (fid: ident) (fty: type) : option drop_member_state :=
  if own_type ge fty then
    let tys := drop_glue_children_types fty in
    match tys with
    | nil => None
    | ty :: tys' =>
        match ty with       
        | Tvariant _ id
        | Tstruct _ id =>
            (* provide evidence for the simulation *)
            match ge.(genv_dropm) ! id with
            | Some _ =>
                Some (drop_member_comp fid fty ty tys')
            | None => None
            end
        | _ => Some (drop_member_box fid fty tys)
        end
    end
  else None.


(* big step to recursively drop boxes [Tbox (Tbox (Tbox
...))]. (b,ofs) is the address of the starting block *)
Inductive drop_box_rec (b: block) (ofs: ptrofs) : mem -> list type -> mem -> Prop :=
| drop_box_rec_nil: forall m,
    drop_box_rec b ofs m nil m
| drop_box_rec_cons: forall m m1 m2 b1 ofs1 ty tys b2 ofs2,
    (* (b1, ofs1) is the address of [ty], we want to free the memory
    location stored in (b1,ofs1) *)
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    (* if the result of deref_loc is not a pointer, it must be memory
    error!!! It is because in Compcert memory model, freeing a nullptr
    is not considerd U.B. Or we can just prove that drop_box_rec is
    total (has no any UB) ? *)
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    (* if v is nullptr, can we treat it as memory error? *)
    extcall_free_sem ge [(Vptr b2 ofs2)] m E0 Vundef m1 ->
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m (ty :: tys) m2
.


(* drop_box_rec is deterministic *)
Lemma drop_box_rec_det: forall tys b ofs m1 m2 m3,
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m1 tys m3 ->
    m2 = m3.
Proof.
  induction tys; intros.
  - inv H. inv H0. auto.
  - inv H. inv H0.
    exploit deref_loc_rec_det. eapply H3. eapply H2.
    intros A. inv A.
    exploit deref_loc_det. eapply H4. eapply H5. intros B. inv B.
    exploit extcall_free_sem_det. eapply H6. eapply H9.
    intros (C1 & C2). subst.
    eauto.
Qed.

Inductive drop_box_rec_mem_error (b: block) (ofs: ptrofs) : mem -> list type -> Prop :=
| drop_box_rec_error1: forall m ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error2: forall m ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc_mem_error ty m b1 ofs1 ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error3: forall m ty tys b1 ofs1 b2 ofs2,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    extcall_free_sem_mem_error [Vptr b2 ofs2] m ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error4: forall m m1 ty tys b1 ofs1 b2 ofs2,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    extcall_free_sem ge [Vptr b2 ofs2] m E0 Vundef m1 ->
    drop_box_rec_mem_error b ofs m1 tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
.

End DROPMEMBER.

(** Put some auxilary lemmas here *)

Lemma PTree_elements_one (A: Type) : forall id (elt: A),
    PTree.elements (PTree.set id elt (PTree.empty A)) = (id, elt) :: nil.
Proof.
  intros.
  generalize (PTree.elements_correct (PTree.set id elt (PTree.empty A)) id (PTree.gss _ _ _)).
  intros IN.
  generalize (PTree.elements_keys_norepet (PTree.set id elt (PTree.empty A))).
  intros NOREPEAT.
  destruct (PTree.elements (PTree.set id elt (PTree.empty A))) eqn: LIST.
  inv IN.
  destruct p. 
  inv IN.
  - inv H.
    destruct l. auto. destruct p.
    assert (IN1: In (p,a) ((id,elt)::(p,a)::l)).
    eapply in_cons. econstructor. auto.
    simpl in NOREPEAT. inv NOREPEAT. 
    generalize (PTree.elements_complete (PTree.set id elt (PTree.empty A)) p a).
    rewrite LIST. intros B. apply B in IN1.
    erewrite PTree.gsspec in IN1.
    destruct (peq p id) eqn: PEQ. inv IN1.
    exfalso. eapply H1. econstructor. auto.
    rewrite PTree.gempty in IN1. congruence.
  - simpl in NOREPEAT. inv NOREPEAT.
    assert (GP: (PTree.set id elt (PTree.empty A))! p = Some a).
    eapply PTree.elements_complete. rewrite LIST.
    econstructor. auto.
    erewrite PTree.gsspec in GP.
    destruct (peq p id) eqn: PEQ. inv GP.
    exfalso. eapply H2. replace id with (fst (id, a)). eapply in_map.
    auto. auto.
    rewrite PTree.gempty in GP. congruence.
Qed.

Lemma list_norepet_append_commut2 {A: Type} : forall (a b c: list A),
    list_norepet (a++b++c) ->
    list_norepet (a++c++b).
Proof.
  intros. apply list_norepet_app in H.
  destruct H as (A1 & A2 & A3).
  eapply list_norepet_app. split; auto.
  split. apply list_norepet_append_commut. auto.
  red. intros. apply A3. auto. 
  apply in_app in H0. apply in_app. destruct H0; auto.
Qed.

(* Used in ElaborateDropProof and Clightgenproof *)
Lemma alloc_variables_in: forall l ge e1 m1 e2 m2 id b ty,
    alloc_variables ge e1 m1 l e2 m2 ->
    e2 ! id = Some (b,ty) ->
    e1 ! id = Some (b,ty) \/ In (id, ty) l.
Proof.
  induction l; intros.
  - inv H. auto.
  - inv H. exploit IHl; eauto. intros [A|B]; auto.
    rewrite PTree.gsspec in A. destruct peq in A. inv A.
    right. econstructor. auto.
    auto.
    right. eapply in_cons. auto.
Qed.    

                                       
Lemma length_S_inv : forall A n (l: list A),
    length l = S n ->
    exists l' a, l = l' ++ [a] /\ length l' = n.
Proof.
  induction n.
  - intros. destruct l. cbn in *.
    congruence.
    cbn in H. inv H.
    rewrite length_zero_iff_nil in H1.
    subst. exists nil. cbn. eauto.
  - intros. simpl in *. 
    destruct l. cbn in H. congruence.
    cbn in H. inv H.
    generalize (IHn _ H1).
    destruct 1 as (l' & a0 & eq & LEN). subst.
    exists (a :: l'). cbn. eexists; split; eauto.
Qed.

(* Properties about drop_glue_children_types *)

Lemma drop_glue_children_types_last: forall tys ty hty,
    drop_glue_children_types ty = hty :: tys ->
    ty = last tys hty.
Proof.
  destruct tys.
  simpl. intros.
  destruct ty; simpl in H; inv H; auto.
  destruct (drop_glue_children_types ty). simpl in *. inv H1. auto.
  simpl in H1. inv H1. exfalso.
  eapply app_cons_not_nil. eauto.
  intros.
  intros. destruct ty; simpl in H; inv H.
  assert (last (hty::t::tys) hty = Tbox ty).
  rewrite <- H1. eapply last_last.
  simpl in *. auto.
Qed.


Lemma app_not_nil {A: Type}:  forall (l1 l2: list A) (a b: A),
    l1 ++ (a :: nil) = b :: l2 ->
    (a = b /\ l1 = nil /\ l2 = nil)
    \/ (exists l1', l1 = b :: l1' /\ l2 = l1' ++ (a::nil)).
Proof.
  induction l1; simpl; intros.
  - destruct l2; inv H. auto.
  - inv H. destruct l1.
    + exploit (IHl1 nil a0 a0). auto.
      intros [(A1 & A2 & A3)|(A3 & A4 & A5)]; subst.
      * right. eauto.
      * inv A4.
    + exploit (IHl1 (l1 ++ [b]) b a). auto.
      intros [(A1 & A2 & A3)|(A3 & A4 & A5)]; subst.
      inv A2. inv A4.
      right. exists (a::A3). auto.
Qed.

Lemma app_not_nil_gen {A: Type}:  forall (l1 l2 l3: list A) (a b: A),
    l1 ++ (a :: nil) = l3 ++ b :: l2 ->
    (a = b /\ l1 = l3 /\ l2 = nil)
    \/ (exists l1', l1 = l3 ++ b :: l1' /\ l2 = l1' ++ (a::nil)).
Proof.
(*   induction l1; simpl; intros. *)
(*   - destruct l2; inv H. *)
(*     destruct l3; inv H1. eauto. eapply app_n *)
(*     auto. *)
(*   - inv H. destruct l1. *)
(*     + exploit (IHl1 nil a0 a0). auto. *)
(*       intros [(A1 & A2 & A3)|(A3 & A4 & A5)]; subst. *)
(*       * right. eauto. *)
(*       * inv A4. *)
(*     + exploit (IHl1 (l1 ++ [b]) b a). auto. *)
(*       intros [(A1 & A2 & A3)|(A3 & A4 & A5)]; subst. *)
(*       inv A2. inv A4. *)
(*       right. exists (a::A3). auto. *)
  (* Qed. *)
Admitted.
  
(* The first element must be struct/variant/box, the rest of the list must be box *)
Lemma drop_glue_children_types_wf: forall ty tys hty,
    drop_glue_children_types ty = hty :: tys ->
    ((exists orgs id, hty = Tstruct orgs id) \/
       (exists orgs id, hty = Tvariant orgs id) \/
       (exists ty', hty = Tbox ty'))
    /\ (forall t, In t tys -> exists ty', t = Tbox ty').
Proof.
  induction ty; simpl; intros; try congruence.
  - eapply app_not_nil in H.
    destruct H as [(A1 & A2 & A3)| (A1 & A2 & A3)]; subst.
    + split. eauto. intros. inv H.
    + exploit IHty. eauto. intros (B1 & B2).
      split. auto.
      intros. eapply in_app in H. destruct H; eauto.
      inv H; eauto. inv H0.
  - inv H. split; eauto.
    intros. inv H.
  - inv H. split; eauto.
    intros. inv H.
Qed.
    
