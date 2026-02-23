Require Import Coqlib.
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import Errors.
Require Import Listmisc.
Require Import InitDomain InitAnalysis.
Require Import RustIRown.
Require Import Wfsimpl.
Require Import Separation.
Require Import RustIRspec.

Import ListNotations.
Local Open Scope sep_scope.
Local Open Scope error_monad_scope.

(* Useful tactic to destruct get_loc_footprint. *)

Ltac destr_fp_box fp H :=
  destruct fp; try congruence.
  (* match type of H with *)
  (* | (if ?not_fp_emp then _ else _) = _  =>       *)
  (*     destruct not_fp_emp eqn: ?NOTEMP in H; try congruence *)
  (* end. *)


Ltac destr_fp_enum fp H :=
  destruct fp; try congruence;
  destruct ident_eq in H; try congruence; subst.


Ltac destr_fp_field fp H :=
  let A1 := fresh "A" in
  let A2 := fresh "A" in
  let p := fresh "p" in
  let FIND := fresh "FIND" in
  destruct fp; try congruence;
  destruct find_field as [p|] eqn: FIND; try congruence;
  repeat destruct p; simpl in H;
  exploit find_field_some; eauto; intros A2; subst.



Definition spure := Separation.pure.

Definition STrue := spure True.


Inductive Forall_sep {A : Type} (P : A -> massert -> Prop) : list A -> massert -> Prop :=
    Forall_sep_nil : forall mass,
      massert_eqv STrue mass ->
      Forall_sep P nil mass
  | Forall_sep_cons : forall (x : A) (l : list A) mass1 mass2 mass3,
      P x mass1 -> 
      Forall_sep P l mass2 -> 
      massert_eqv (mass1 ** mass2) mass3 ->
      Forall_sep P (x :: l) mass3.

Lemma Forall_sep_app {A: Type} : forall (l1 l2: list A) P mass,
    Forall_sep P (l1 ++ l2) mass <-> 
      (exists mass1 mass2, Forall_sep P l1 mass1 /\ Forall_sep P l2 mass2 /\ mass = mass1 ** mass2).
Admitted.

Fixpoint range_list (l: list (block * Z * Z)) : massert :=
  match l with
  | nil => STrue
  | (b, lo, hi) :: l1 =>
      range b lo hi ** range_list l1
  end.



Section ADT_ENV.

(* I think this environment is a premise for the whole borrow checking
proof. When we want to use the borow checking proof, we must provide
its instance. *)
Context {ame: adt_mem_env}.
Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).


(* Induction principle for footprint *)
Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPuninit: forall sz al, P (fp_uninit sz al))
  (HPscalar: forall chunk v, P (fp_scalar chunk v))
  (HPbox: forall (b : block) (fp : footprint), P fp -> P (fp_box b fp))
  (HPstruct: forall id fpl, (forall fid base fofs ffp, In (fid, ((base, fofs), ffp)) fpl -> P ffp) -> P (fp_struct id fpl))
  (HPenum: forall id (tag : Z) fid fofs (ffp : footprint), P ffp -> P (fp_enum id tag fid fofs ffp))
  (HPref: forall mut b ofs ref_owner vs, P (fp_ref mut b ofs ref_owner vs))
  (HPobj: forall id obj bors, (forall fid b ofs ffp, In (fid, (b, ofs, ffp)) bors -> P ffp) -> P (fp_object id obj bors)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPuninit.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as (fid1 & ofs1 & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid base fofs ffp H). 
  - apply HPenum. apply strong_footprint_ind.
  - apply HPref. 
  - eapply HPobj. induction exposed.
    + intros. inv H.
    + intros. destruct a as (fid1 & ((b1 & ofs1) & fp1)). simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
      * apply (IHexposed fid b ofs ffp H). 
Qed.
    
End FP_IND.


(* We cannot write Forall (fun ... => sem_wt_loc ... in sem_wt_struct)
which would report error that sem_wt_loc does not occur positively, so
we define it here to make sem_wt_loc occurs positively in
sem_wt_struct case *)
Inductive fields_loc_sep (b: block) (ofs: Z) (P: footprint -> block -> Z -> massert -> Prop) : list ffpty -> massert -> Prop :=
| fields_loc_sep_nil: forall mp
    (EQV: massert_eqv mp STrue),
    fields_loc_sep b ofs P nil mp
| fields_loc_sep_cons: forall fid base fofs ffp l mass1 mass2 padmp mp
    (IND: fields_loc_sep b ofs P l mass2)
    (FWT: P ffp b (ofs + fofs) mass1)
    (ALPERM: padmp = range b (ofs + base) (ofs + fofs))
    (EQV: massert_eqv mp (padmp ** mass1 ** mass2)),
    fields_loc_sep b ofs P ((fid, ((base, fofs), ffp)) :: l) mp.

Inductive fields_fp_sep (P: footprint -> massert -> Prop) : list ffpty -> massert -> Prop :=
| fields_val_sep_nil: forall mp
    (EQV: massert_eqv mp STrue),
    fields_fp_sep P nil mp
| fields_val_sep_cons: forall fid base fofs ffp l mass1 mass2 mp
    (IND: fields_fp_sep P l mass2)
    (FWT: P ffp mass1)
    (EQV: massert_eqv mp (mass1 ** mass2)),
    fields_fp_sep P ((fid, ((base, fofs), ffp)) :: l) mp.

Inductive exposed_loc_sep (P: footprint -> block -> Z -> massert -> Prop) : list (ident * ((block * Z) * type * footprint)) -> massert -> Prop :=
| exposed_loc_sep_nil: forall mp
    (EQV: massert_eqv mp STrue),
    exposed_loc_sep P nil mp
| exposed_loc_sep_cons: forall fid b ofs fty ffp l mass1 mass2 mp
    (IND: exposed_loc_sep P l mass2)
    (FWT: P ffp b ofs mass1)
    (EQV: massert_eqv mp (mass1 ** mass2)),
    exposed_loc_sep P ((fid, (b, ofs, fty, ffp)) :: l) mp.


Section COMP_ENV.

Variable ce: composite_env.

(** * Definitions of semantics typedness *)

Definition box_pred (fp: footprint) b mp :=
  (* Remember that if we can move the permission of some field of
  (b,0), e.g., via passing by reference, then shallow_owned is false
  but we should still own the remaining location! *) 
  (contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (sizeof_footprint ce fp))))) ** mp.

Inductive sem_wt_loc : footprint -> block -> Z -> massert -> Prop :=
| sem_wt_emp: forall b ofs mp
(* We need fp_emp here as if we set some field of a struct to fp_emp
(e.g., by passing the location to callee via reference), we need to
say this location is still sem_wt_loc *)
    (EQV: massert_eqv mp STrue),
    sem_wt_loc fp_emp b ofs mp
| sem_wt_uninit: forall b ofs sz al mp
    (* This location is not initialized, but it should be aligned *)
(*     properly and have enough permission *)
    (* (AL: (al | ofs)) *)
    (EQV: massert_eqv mp ((range b ofs (ofs + sz)) ** (spure (al | ofs)))),
    sem_wt_loc (fp_uninit sz al) b ofs mp
| sem_wt_scalar: forall b ofs chunk v mp
    (* (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk), *)
    (* hasvalue already contain the align requirement *)
    (EQV: massert_eqv mp (hasvalue chunk b ofs v)),
    sem_wt_loc (fp_scalar chunk v) b ofs mp
| sem_wt_ref: forall b1 b2 ofs1 ofs2 ph mp mut vs
    (EQV: massert_eqv mp (hasvalue Mptr b1 ofs1 (Vptr b2 (Ptrofs.repr ofs2)))),
    sem_wt_loc (fp_ref mut b2 ofs2 ph vs) b1 ofs1 mp
| sem_wt_box: forall b ofs fp b1 nextmp mp mp1
    (* (WTVAL: sem_wt_val (fp_box b1 sz1 fp) v mass), *)
    (* When this box pointer is not moved from (i.e., shallow_init is
    false), its point-to location is freeable and sem_wt_loc *)
    (FREE: massert_eqv mp (box_pred fp b1 nextmp))
    (WTLOC: sem_wt_loc fp b1 0 nextmp)
    (EQV: massert_eqv mp1 ((hasvalue Mptr b ofs (Vptr b1 Ptrofs.zero)) ** mp)),
    sem_wt_loc (fp_box b1 fp) b ofs mp1

| sem_wt_struct: forall b ofs fpl id mass mp
    (FWT: fields_loc_sep b ofs sem_wt_loc fpl mass)
    (* (AL: (alignof_comp ce id | ofs)) *)
    (* The reason why we do not add range here is that splitting
    fields w.r.t. the range is very difficult. *)
    (EQV: massert_eqv mp (* (mconj mass (range b ofs (ofs + sizeof_comp ce id)))) *) (mass ** (spure (alignof_comp ce id | ofs)))),
    sem_wt_loc (fp_struct id fpl) b ofs mp
| sem_wt_enum: forall fp b ofs tagz fid fofs id mass1 mass2 mp padmp
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: mass1 = hasvalue Mint32 b ofs (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc fp b (ofs + fofs) mass2)
    (* (AL: (alignof_comp ce id | ofs)) *)
    (* permission for the padding location *)
    (ALPERM: padmp = range b (ofs + size_chunk Mint32) (ofs + fofs))
    (EQV: massert_eqv mp (mass1 ** padmp ** mass2 ** (spure (alignof_comp ce id | ofs)))),
    sem_wt_loc (fp_enum id tagz fid fofs fp) b ofs mp
| sem_wt_object: forall id obj mp1 mp2 mp3 b ofs exposed
    (PRED: (ame id).(mem_pred) obj b ofs mp1)
    (EXPOSED: exposed_loc_sep sem_wt_loc exposed mp2)
    (EQV: massert_eqv (mp1 ** mp2) mp3),
    sem_wt_loc (fp_object id obj exposed) b ofs mp3
.

(* The interpretation of footprint *)
Inductive sem_wt_fp : footprint -> massert -> Prop :=
| sem_fp_emp: forall mp
    (EQV: massert_eqv mp (spure True)),
    sem_wt_fp fp_emp mp
| sem_fp_uninit: forall sz al mp
    (EQV: massert_eqv mp (spure True)),
    sem_wt_fp (fp_uninit sz al) mp
| sem_fp_scalar: forall chunk v mp
    (* We should ensure that the value in the footprint is loaded from memory *)
    (EQV: massert_eqv mp (spure True)),
    sem_wt_fp (fp_scalar chunk v) mp
| sem_fp_ref: forall phs b ofs mp mut vs
    (EQV: massert_eqv mp (spure True)),
    sem_wt_fp (fp_ref mut b ofs phs vs) mp
| sem_fp_box: forall b fp nextmp mp
    (WTLOC: sem_wt_loc fp b 0 nextmp)
    (EQV: massert_eqv mp (box_pred fp b nextmp)),
    sem_wt_fp (fp_box b fp) mp
| sem_fp_struct: forall id fpl mp1 mp
    (FFP: fields_fp_sep sem_wt_fp fpl mp1)
    (* (* We use magic wand to capture the by_copy notion *) *)
    (* (SHALLOW: sem_wt_loc (clear_footprint_rec ce (fp_struct id fpl)) b (Ptrofs.unsigned ofs) mp1) *)
    (* (* Since it is difficult to define magic-wand in CompCert's *)
    (* separation library (the footprint must be provided explicitly), we *)
    (* use (mp1 ** mp2) to simulate that the footprint of this struct can *)
    (* be divided into the location part and the next-level part. *) *)
    (* (WTLOC: sem_wt_loc (fp_struct id fpl) b (Ptrofs.unsigned ofs) (mp1 ** mp2)) *)
    (EQV: massert_eqv mp mp1),
    sem_wt_fp (fp_struct id fpl) mp
| sem_fp_enum: forall fp tagz fid fofs id mp1 mp
    (FFP: sem_wt_fp fp mp1)
    (* (SHALLOW: sem_wt_loc (clear_footprint_rec ce (fp_enum id tagz fid fofs fp)) b (Ptrofs.unsigned ofs) mp1) *)
    (* (WTLOC: sem_wt_loc (fp_enum id tagz fid fofs fp) b (Ptrofs.unsigned ofs) (mp1 ** mp2)) *)
    (EQV: massert_eqv mp mp1),
    sem_wt_fp (fp_enum id tagz fid fofs fp) mp.


Inductive sem_wt_val : footprint -> val -> massert -> Prop :=
| wt_val_scalar: forall chunk v1 v2 mp
    (* We should ensure that the value in the footprint is loaded from memory *)
    (MP: sem_wt_fp (fp_scalar chunk v1) mp)
    (* We require that the loaded result of v2 at semantics (which
    should be stored into the memory) is equal to v1 (which is loaded
    from memory) *)
    (VEQ: v1 = Val.load_result chunk v2),
    sem_wt_val (fp_scalar chunk v1) v2 mp
| wt_val_ref: forall phs b ofs mp mut vs
    (MP: sem_wt_fp (fp_ref mut b ofs phs vs) mp),
    sem_wt_val (fp_ref mut b ofs phs vs) (Vptr b (Ptrofs.repr ofs)) mp
| wt_val_box: forall b fp mp
    (MP: sem_wt_fp (fp_box b fp) mp),
    sem_wt_val (fp_box b fp) (Vptr b Ptrofs.zero) mp.
(** We do not support copying struct/enum for now  *)
(* | wt_val_struct: forall b ofs id fpl mp *)
(*     (MP: sem_wt_fp (fp_struct id fpl) mp) *)
(*     (WTLOC: forall mp1,  *)
(*         sem_wt_loc (clear_footprint_rec (fp_struct id fpl)) b (Ptrofs.unsigned ofs) mp1 -> *)
(*         sem_wt_loc (fp_struct id fpl) b (Ptrofs.unsigned ofs) (mp1 ** mp)), *)
(*     sem_wt_val (fp_struct id fpl) (Vptr b ofs) mp *)
(* | wt_val_enum: forall b ofs fp tagz fid fofs id mp *)
(*     (MP: sem_wt_fp (fp_enum id tagz fid fofs fp) mp) *)
(*     (WTLOC: forall mp1,  *)
(*         sem_wt_loc (clear_footprint_rec (fp_enum id tagz fid fofs fp)) b (Ptrofs.unsigned ofs) mp1 -> *)
(*         sem_wt_loc (fp_enum id tagz fid fofs fp) b (Ptrofs.unsigned ofs) (mp1 ** mp)), *)
(*     sem_wt_val (fp_enum id tagz fid fofs fp) (Vptr b ofs) mp. *)

Inductive sem_wt_val_list : list footprint -> list val -> massert -> Prop :=
| sem_wt_val_nil: sem_wt_val_list nil nil STrue
| sem_wt_val_cons: forall fp fpl v vl mp1 mp
     (WTVAL_LIST: sem_wt_val_list fpl vl mp)
     (WTVAL: sem_wt_val fp v mp1),
     sem_wt_val_list (fp::fpl) (v::vl) (mp1 ** mp).

Inductive sem_wt_loc_list : list (block * Z) -> list footprint  -> massert -> Prop :=
| sem_wt_loc_nil: sem_wt_loc_list nil nil STrue
| sem_wt_loc_cons: forall b ofs locl fp fpl mp1 mp
     (WTLOC_LIST: sem_wt_loc_list locl fpl mp)
     (WTLOC: sem_wt_loc fp b ofs mp1),
     sem_wt_loc_list ((b, ofs) :: locl) (fp::fpl) (mp1 ** mp).


(* Lemma fields_loc_sep_equiv: forall fpl b ofs P mass, *)
(*     fields_loc_sep b ofs P fpl mass <-> *)
(*       Forall_sep (fun '(fid, ((base, fofs), ffp)) => P ffp b (ofs + fofs)) fpl mass. *)
(* Proof. *)
(*   induction fpl; intros. *)
(*   - split; intros. *)
(*     + inv H. econstructor. *)
(*     + inv H. econstructor. *)
(*   - split; intros. *)
(*     + inv H. econstructor; eauto.  *)
(*       eapply IHfpl. auto. *)
(*     + inv H. destruct a. destruct p. econstructor; eauto.  *)
(*       eapply IHfpl. auto. *)
(* Qed. *)

(* Lemma fields_loc_sep_app : forall l1 l2 P mass b ofs, *)
(*     fields_loc_sep b ofs P (l1 ++ l2) mass <->  *)
(*       (exists mass1 mass2, fields_loc_sep b ofs P l1 mass1 /\ fields_loc_sep b ofs P l2 mass2 /\ mass = mass1 ** mass2). *)
(* Proof. *)
(*   intros. split; intros. *)
(*   - eapply fields_loc_sep_equiv in H. *)
(*     eapply Forall_sep_app in H as (mass1 & mass2 & A1 & A2 & A3). subst. *)
(*     exists mass1, mass2. *)
(*     repeat apply conj; eauto; eapply fields_loc_sep_equiv; eauto. *)
(*   - destruct H as (mass1 & mass2 & A1 & A2 & A3); subst. *)
(*     eapply fields_loc_sep_equiv. *)
(*     eapply Forall_sep_app. *)
(*     exists mass1, mass2. *)
(*     repeat apply conj; eauto; eapply fields_loc_sep_equiv; eauto. *)
(* Qed. *)


Inductive coherent_var (elt: (ident * (block * Z *  option origin * type * footprint))) : massert -> Prop :=
| coherent_var_intro: forall id b ofs ty mass fp opt_reg
    (ELTEQ: elt = (id, (b, ofs, opt_reg, ty, fp)))
    (* What if fpm contains more variables than local env? *)
    (MASS: sem_wt_loc fp b ofs mass),
    (* How to express the ownership of external locations passed by reference? *)
    coherent_var elt mass.

(* The separation predicate for (local env, footprint map) *)
Inductive coherent_fpm (fpm: fp_map) : massert -> Prop :=
| coherent_fpm_intro: forall mass
    (ALLSEP: Forall_sep coherent_var (PTree.elements fpm) mass),
    coherent_fpm fpm mass.

End COMP_ENV.

(* Morphism for sem_wt_loc/val *)

Global Instance sem_wt_loc_eqv ce b ofs fp : Proper (massert_eqv ==> iff) (sem_wt_loc ce fp b ofs).
Proof.
  intros mp1 mp2 EQV. 
  split; intros WTLOC.
  - destruct fp; inv WTLOC; econstructor; try rewrite EQV in *; try subst_dep;eauto.
  - destruct fp; inv WTLOC; econstructor; try rewrite EQV in *; try subst_dep;eauto.
Qed.

Global Instance fields_loc_sep_eqv ce b ofs fpl : Proper (massert_eqv ==> iff) (fields_loc_sep b ofs (sem_wt_loc ce) fpl).
Proof.
  induction fpl; intros mp1 mp2 EQV; split; intros WTLOC.
  - inv WTLOC. econstructor. rewrite EQV in EQV0. auto.
  - inv WTLOC. econstructor. rewrite EQV. auto.
  - inv WTLOC. econstructor; eauto.
    rewrite EQV in EQV0. auto.
  - inv WTLOC. econstructor; eauto.
    rewrite EQV. auto.
Qed.


Global Instance sem_wt_fp_eqv ce fp : Proper (massert_eqv ==> iff) (sem_wt_fp ce fp).
Proof.
  intros mp1 mp2 EQV. 
  split; intros WTVAL.
  - destruct fp; inv WTVAL; econstructor; try rewrite EQV in *; eauto.
  - destruct fp; inv WTVAL; econstructor; try rewrite EQV in *; eauto.
Qed.

(* Too slow, just admit it for efficiency *)
Global Instance sem_wt_val_eqv ce v fp : Proper (massert_eqv ==> iff) (sem_wt_val ce fp v).
Proof.
Admitted.
(*   intros mp1 mp2 EQV. *)
(*   split; intros WTVAL. *)
(*   - destruct fp; inv WTVAL; econstructor; try rewrite EQV in *; auto. *)
(*     intros. rewrite <- EQV. exploit WTLOC. eauto. intros. eauto. *)
(*     intros. rewrite <- EQV. exploit WTLOC. eauto. intros. eauto. *)
(*   - destruct fp; inv WTVAL; econstructor; try rewrite EQV in *; auto. *)
(*     intros. rewrite EQV. exploit WTLOC. eauto. intros. eauto. *)
(*     intros. rewrite EQV. exploit WTLOC. eauto. intros. eauto. *)
(* Qed. *)


Global Instance massert_imp_po :
  PartialOrder (massert_eqv) (massert_imp).
Proof.
  firstorder.
Qed.

(* Lemma fields_loc_sep_in: forall fpl fid fofs ffp mp P b ofs *)
(*         (SEP: fields_loc_sep b ofs P fpl mp) *)
(*         (IN: In (fid, (fofs, ffp)) fpl), *)
(*         exists mpi mp', P ffp b (ofs + fofs) mpi *)
(*                    /\ massert_eqv mp (mpi ** mp'). *)
(* Admitted. *)

(* The predicates evaluated from sem_wt_loc/fp/val are equivalent *)

Lemma fields_loc_sep_unique : forall fpl b ofs mp1 mp2 (P: footprint -> block -> Z -> massert -> Prop)
    (EQVP: forall fid base fofs ffp, In (fid, ((base, fofs), ffp)) fpl ->
                           forall mp1 mp2 b ofs, 
                             P ffp b ofs mp1 ->
                             P ffp b ofs mp2 ->
                             massert_eqv mp1 mp2)
    (F1: fields_loc_sep b ofs P fpl mp1)
    (F2: fields_loc_sep b ofs P fpl mp2),
    massert_eqv mp1 mp2.
Proof.
  induction fpl; intros.
  - inv F1. inv F2. rewrite EQV, EQV0. reflexivity.
  - inv F1. inv F2. rewrite EQV, EQV0.
    eapply sepconj_morph_2. reflexivity. 
    eapply sepconj_morph_2.
    eapply EQVP. simpl. left. reflexivity.
    eauto. eauto.
    eapply IHfpl; eauto.
    intros. eapply EQVP. simpl. right. eauto.
    eauto. auto.
Qed.

Lemma sem_wt_loc_unique ce: forall fp mp1 mp2 b ofs
    (WTLOC1: sem_wt_loc ce fp b ofs mp1)
    (WTLOC2: sem_wt_loc ce fp b ofs mp2),
    massert_eqv mp1 mp2.
Proof.
  induction fp using strong_footprint_ind; intros; inv WTLOC1; inv WTLOC2; try (rewrite EQV; rewrite EQV0; reflexivity).
  - rewrite EQV, EQV0. rewrite FREE, FREE0. 
    exploit IHfp. eauto. eapply WTLOC. intros. unfold box_pred.
    rewrite H. reflexivity. 
  - rewrite EQV, EQV0.
    eapply sepconj_morph_2.
    eapply fields_loc_sep_unique; eauto.
    reflexivity.
  - rewrite EQV, EQV0. eapply sepconj_morph_2. reflexivity.
    eapply sepconj_morph_2. reflexivity.
    eapply sepconj_morph_2. 
    eapply IHfp; eauto. reflexivity.
  - subst_dep.
    admit.
Admitted.

Lemma fields_fp_sep_unique : forall fpl mp1 mp2 (P: footprint -> massert -> Prop)
    (EQVP: forall fid base fofs ffp, In (fid, ((base, fofs), ffp)) fpl ->
                           forall mp1 mp2, 
                             P ffp mp1 ->
                             P ffp mp2 ->
                             massert_eqv mp1 mp2)
    (F1: fields_fp_sep P fpl mp1)
    (F2: fields_fp_sep P fpl mp2),
    massert_eqv mp1 mp2.
Proof.
  induction fpl; intros.
  - inv F1. inv F2. rewrite EQV, EQV0. reflexivity.
  - inv F1. inv F2. rewrite EQV, EQV0.
    eapply sepconj_morph_2. eapply EQVP. simpl. left. reflexivity.
    eauto. eauto.
    eapply IHfpl; eauto.
    intros. eapply EQVP. simpl. right. eauto.
    eauto. auto.
Qed.


Lemma sem_wt_fp_unique ce: forall fp mp1 mp2
    (WTLOC1: sem_wt_fp ce fp mp1)
    (WTLOC2: sem_wt_fp ce fp mp2),
    massert_eqv mp1 mp2.
Proof.
  induction fp using strong_footprint_ind; intros; inv WTLOC1; inv WTLOC2; try (rewrite EQV; rewrite EQV0; reflexivity).
  - rewrite EQV, EQV0. 
    exploit sem_wt_loc_unique. eapply WTLOC. eauto. intros.
    unfold box_pred. rewrite H. reflexivity.
  - rewrite EQV, EQV0. 
    eapply fields_fp_sep_unique; eauto.
  - rewrite EQV, EQV0. eapply IHfp; eauto.
Qed.

Lemma sem_wt_val_unique ce: forall fp mp1 mp2 v
    (WTVAL1: sem_wt_val ce fp v mp1)
    (WTVAL2: sem_wt_val ce fp v mp2),
    massert_eqv mp1 mp2.
Proof.
  destruct fp; intros; inv WTVAL1; inv WTVAL2; subst; try (rewrite EQV; rewrite EQV0; reflexivity); try eapply sem_wt_fp_unique; eauto.
Qed.


(** ** Typing of the footprint: used to make sure the footprint is well-formed *)

Definition fpm_to_tenv (fpm: fp_map) : typenv :=
  PTree.map1 (fun '(b, ofs, r, ty, fp) => ty) fpm.

Section COMP_ENV.

Variable ce: composite_env.
Variable fpm: fp_map.
(** Move it to Rusttypes.v  *)

(* We define a new field_offset which returns the starting offset of a
field that does not consider the alignment. *)


Inductive fp_match_field (co: composite) (P: type -> footprint -> Prop): ffpty -> member -> Prop :=
| fp_match_field_intro: forall fid base fofs ffp fty
    (FOFS: field_noalign_offset ce fid (co_members co) = OK (base, fofs))
    (WTFP: P fty ffp),
    fp_match_field co P (fid, ((base, fofs), ffp)) (Member_plain fid fty).

Inductive obj_exposed_wf (P: type -> footprint -> Prop): (ident * (block * Z * Z * type)) -> (ident * (block * Z * type * footprint)) -> Prop :=
| obj_exposed_wf_intro: forall fid b lo ty ffp
    (WTFP: P ty ffp),
    obj_exposed_wf P (fid, (b, lo, lo + sizeof ce ty, ty)) (fid, ((b, lo), ty, ffp)).


(* Definition of wt_footprint (well-typed footprint). Intuitively, it
says that the footprint is an abstract form of the syntactic type. *)
Inductive wt_footprint : type -> footprint -> Prop :=
(* fp_emp can only appear when we pass inout parameters to the
callee. In a well-formed footprint/fp_map, it should not appear. *)
(* | wt_fp_emp: forall ty, *)
(*     wt_footprint ty fp_emp *)
| wt_fp_uninit: forall ty
    (* It means that the location with this type is not initialized or
        this location is scalar type. We require that [ty] is not
        structure because we do not want to dynamically unpack the
        struct when setting footprint (e.g., by set_loc_footprint) to
        some field of this struct. But to ensure this properties, we
        need to carefully set fp_emp to place with structure type. *)
    (WF: forall orgs id, ty <> Tstruct orgs id),
    wt_footprint ty (fp_uninit (sizeof ce ty) (alignof ce ty))
| wt_fp_scalar: forall ty v chunk
    (WF: scalar_type ty = true)
    (MODE: access_mode ty = Ctypes.By_value chunk),
    wt_footprint ty (fp_scalar chunk v)
| wt_fp_struct: forall orgs id fpl co
    (CO: ce ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (MATCH: Forall2 (fp_match_field co wt_footprint) fpl (co_members co))
    (FLAT: field_idents fpl = name_members (co_members co)),
    wt_footprint (Tstruct orgs id) (fp_struct id fpl)
| wt_fp_enum: forall orgs id tagz fid fty fofs fp co
    (CO: ce ! id = Some co)
    (ENUM: co_sv co = TaggedUnion)
    (TAG: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty))
    (* avoid some norepet properties *)
    (FTY: place_field_type co fid orgs = OK fty)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: wt_footprint fty fp),
    wt_footprint (Tvariant orgs id) (fp_enum id tagz fid fofs fp)
| wt_fp_box: forall ty b fp
    (* this is ensured by bm_box *)
    (WT: wt_footprint ty fp),
    (* It is used to make sure that dropping any location within a
    block does not cause overflow *)
    wt_footprint (Tbox ty) (fp_box b fp)
| wt_fp_ref_some: forall ty b ofs ph org mut vs fp pty
    (** [ty] is equal to the type in [ph] *)
    (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK pty)
    (TYEQ: type_eq_except_origins ty pty = true)
    (** The memory location stored in this reference is equal to the
    location of [ph] *)
    (LOCEQ: get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp)),    
    wt_footprint (Treference org mut ty) (fp_ref mut b ofs (Some ph) vs)
| wt_fp_ref_none: forall ty b ofs org mut vs,
    wt_footprint (Treference org mut ty) (fp_ref mut b ofs None vs)
| wt_fp_object: forall id obj exposed
    (WF: Forall2 (obj_exposed_wf wt_footprint) (mem_exposed_borrow (ame id) obj) exposed)
    (* The object always satisfies the representation invariant (this
    invariant should not depend on the properties of borrowable
    subparts) *)
    (REPR_INV: repr_inv (ame id) obj),
    wt_footprint (Tadt id) (fp_object id obj exposed)
.

Definition wt_footprint_list tyl fpl :=
  list_forall2 wt_footprint tyl fpl.

End COMP_ENV.

Definition wt_fpm ce (fpm: fp_map) : Prop :=
  forall id b ofs r ty fp,
    fpm ! id = Some (b, ofs, r, ty, fp) ->
    wt_footprint ce fpm ty fp.


(* Properties of fields_sep *)

Lemma fields_loc_sep_split: forall b ofs base fofs fid ffp l mass P,
    fields_loc_sep b ofs P l mass ->
    In (fid, ((base, fofs), ffp)) l ->
    exists mass1 mass2 mass3, 
      P ffp b (ofs + fofs) mass2 
      /\ mass = mass1 ** mass2 ** mass3.
  (* use Forall_sep properties to prove fields_sep properties *)
Admitted.

(* set a found field would update the massert predicate *)
Lemma Forall_sep_find_set_field {A: Type}: forall mp (l: list (ident * A)) P id a f,
    find_field id l = Some a ->
    Forall_sep P l mp ->
    exists mp1 mp2 mpi l1 l2,
      Forall_sep P l1 mp1
      /\ Forall_sep P l2 mp2
      /\ P (id, a) mpi
      /\ l = l1 ++ (id, a) :: l2
      /\ mp = mp1 ** mpi ** mp2
      (* Properties of setting a new footprint into id *)
      /\ (forall mpi', 
            P (id, (f a)) mpi' ->
            Forall_sep P (set_field id f l) (mp1 ** mpi' ** mp2)).
Proof.
  Admitted.

Lemma fields_loc_sep_find_set: forall l fid P mp ffp b ofs base fofs,
    find_field fid l = Some ((base,fofs), ffp) ->
    fields_loc_sep b ofs P l mp ->
    exists mp1 mp2 mpi l1 l2,
      fields_loc_sep b ofs P l1 mp1
      /\ fields_loc_sep b ofs P l2 mp2
      /\ P ffp b (ofs + fofs) mpi
      /\ l = l1 ++ (fid, ((base, fofs), ffp)) :: l2
      /\ massert_eqv mp (mp1 ** ((range b (ofs + base) (ofs + fofs)) ** mpi) ** mp2)
      (* Properties of setting a new footprint into id *)
      /\ (forall ffp' mpi', 
            P ffp' b (ofs + fofs) mpi' ->
            exists mp',
              fields_loc_sep b ofs P (set_field_fp fid ffp' l) mp'
              /\ massert_eqv mp' (mp1 ** ((range b (ofs + base) (ofs + fofs)) ** mpi') ** mp2)).
Proof.
Admitted.

(** Basic rules for coherent relation (e.g., store and load rules) *)

(** TODO: move it to Separation.v  *)

Lemma massert_eqv_pure_l: forall P,
    massert_eqv P (Separation.pure True ** P).
Proof.
  intros. split.
  red; split; [intros; eapply sep_pure; auto|simpl; intros; destruct H; try contradiction; auto].
  red. split. intros. eapply sep_pure in H. destruct H; auto.
  intros. simpl. auto.
Qed.

Lemma massert_eqv_pure_r: forall P,
    massert_eqv P (P ** Separation.pure True).
Proof.
  intros. etransitivity.
  eapply massert_eqv_pure_l.
  eapply sep_comm.
Qed.  

Lemma massert_eqv_prop_l: forall P (Q: Prop),
    Q -> 
    massert_eqv P (Separation.pure Q ** P).
Proof.
  intros. split.
  red; split; [intros; eapply sep_pure; auto|simpl; intros; destruct H0; try contradiction; auto].
  red. split. intros. eapply sep_pure in H0. destruct H0; auto.
  intros. simpl. auto.
Qed.

Lemma massert_eqv_prop_r: forall P (Q: Prop),
    Q ->
    massert_eqv P (P ** Separation.pure Q).
Proof.
  intros. etransitivity.
  eapply massert_eqv_prop_l. eauto.
  eapply sep_comm.
Qed.  


Lemma contains_range: forall chunk b ofs P,
    massert_imp (contains chunk b ofs P) (range b ofs (ofs + size_chunk chunk)).
Admitted.

Lemma mconj_comm: forall P Q, massert_eqv (mconj P Q) (mconj Q P).
Proof. 
  intros. split.
  - red. split. intros. simpl in *. destruct H; auto.
    intros. simpl in *. destruct H; auto.
  - red. split. intros. simpl in *. destruct H; auto.
    intros. simpl in *. destruct H; auto.
Qed.

Lemma mconj_proj1_massert: forall P Q , massert_imp (mconj P Q) P.
Proof.
  intros. red. split.
  - intros. eapply sep_pick1 with (Q:= STrue).
    eapply mconj_proj1. erewrite <- massert_eqv_pure_r. eauto.
  - intros. simpl. left. auto.
Qed.

Lemma mconj_proj2_massert: forall P Q , massert_imp (mconj P Q) Q.
Proof.
  intros. 
  etransitivity. eapply mconj_comm. eapply mconj_proj1_massert.
Qed.

Lemma massert_imp_proj1: forall P Q , massert_imp (P ** Q) P.
Proof.
  intros. red. split.
  - intros. eapply sep_proj1. eauto.
  - intros. simpl. left. auto.
Qed.

Lemma massert_imp_proj2: forall P Q , massert_imp (P ** Q) Q.
Proof.
  intros. red. split.
  - intros. eapply sep_proj2. eauto.
  - intros. simpl. right. auto.
Qed.

Lemma store_range_rule: forall chunk m b ofs v (spec: val -> Prop) P,
    m |= range b ofs (ofs + size_chunk chunk) ** P ->
    (align_chunk chunk | ofs) ->
    spec (Val.load_result chunk v) ->
    exists m',
      Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
Admitted.

Lemma store_range_unchanged: forall m1 m2 b lo hi chunk b1 ofs1 v,
    m1 |= range b lo hi ->
    Mem.store chunk m1 b1 ofs1 v = Some m2 ->
    m2 |= range b lo hi.
Proof.
  intros.
  simpl. repeat apply conj; try eapply H.
  intros.
  eapply Mem.perm_store_1; eauto. eapply H; eauto.
Qed.

Lemma storebytes_range_unchanged: forall m1 m2 b lo hi b1 ofs1 bytes,
    m1 |= range b lo hi ->
    Mem.storebytes m1 b1 ofs1 bytes = Some m2 ->
    m2 |= range b lo hi.
Proof.
  intros.
  simpl. repeat apply conj; try eapply H.
  intros.
  eapply Mem.perm_storebytes_1; eauto. eapply H; eauto.
Qed.


(* The opposite direction is not correct as we cannot prove Q and R
are disjoint *)
Lemma mconj_absorb1: forall P Q R,
    massert_imp ((mconj P Q) ** R) (mconj (P ** R) Q).
Proof. 
  intros. 
  red. split.
  - intros. simpl in *. 
    destruct H as ((A1 & A2) & A3 & A4).
    red in A4. 
    repeat apply conj; eauto.
    + red. intros. eapply A4. simpl. left. eauto.
      auto.
  - intros. simpl in *. destruct H as [[A1 | A2] | A3]; auto.
Qed.

Lemma mconj_absorb2: forall P Q R,
    massert_imp ((mconj P Q) ** R) (mconj P (Q ** R)).
Proof. 
  intros. 
  etransitivity. eapply sepconj_morph_1.
  eapply mconj_comm. reflexivity.
  erewrite mconj_absorb1. eapply mconj_comm.
Qed.

Lemma ptr_modv: Ptrofs.modulus = 18446744073709551616.
reflexivity.
Qed.

Lemma range_hasvalue: forall m b ofs chunk P v,
    m |= range b ofs (ofs + size_chunk chunk) ** P ->
    Mem.load chunk m b ofs = Some v ->
    m |= hasvalue chunk b ofs v ** P.
Proof.
  intros until v. intros MP LOAD.
  simpl in *. destruct MP as ((A1 & A2 & A3) & A4 & A5).
  repeat apply conj; eauto.
  generalize (size_chunk_pos chunk). intros. unfold Ptrofs.max_unsigned.
  rewrite ptr_modv in *. lia.
  red. intros. eapply A3; eauto.
  eapply Mem.load_valid_access; eauto.
Qed.

(* Lemma sepconj_eqv_split: forall mp1 mp1' mp2 mp2', *)
(*     massert_eqv mp1 mp1' -> *)
(*     massert_eqv (mp1 ** mp2) (mp1' ** mp2') -> *)
(*     disjoint_footprint mp1 mp2 -> *)
(*     massert_eqv mp2 mp2'. *)
(* Proof. *)
(*   intros until mp2'. intros E1 E2 DIS. *)
(*   destruct E1 as (E11 & E12). *)
(*   destruct E2 as (E21 & E22). *)
(*   red. split; red. *)
(*   - split. *)
(*     + intros. destruct E21. eapply H0. simpl.  *)
  

(********* End of properties of the separation predicate ********************  *)

 (* TODO: broken proof about memory operation *)

(* Properties of get/set footprint map w.r.t. sem_wt_loc *)

(* Split and merge sub-footprint from/to the footprint map and derive
the correspoinding separation predicates *)

(* A generalization of sem_wt_loc_split.

Difference between this lemma and sem_wt_loc_split: in this lemma, we
separate the location and its content from the footprint map (see
sem_wt_loc ce fp2 b2 ofs2 mp2 in the conclusion). We need this because
we may do memory copy operation for struct/enum. In sem_wt_loc_split,
we just split the value footprint from the footprint map. This idea
can be found in the "higher-order representation predicate" paper. *)
Lemma get_owner_loc_footprint_sem_wt_split ce: forall phl b1 ofs1 b2 ofs2 fp1 fp2 mp
      (* Most of the time (b2,ofs2) is the location to be stored *)
      (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = OK (b2, ofs2, fp2))
      (* setting fp_emp to this location is equivalent to splitting
      out this location predicate *)      
      (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mp),
    exists mp1 mp1' mp2 fp1', 
      (* Why we set fp_emp here instead of (clear_footprint_rec fp2),
      because we want to separate the whole location of (b2, ofs2)
      instead of just separting its contained value. *)
      set_footprint phl fp_emp fp1 = OK fp1'
      /\ sem_wt_loc ce fp1' b1 ofs1 mp1
      (* separate mp2 from mp *)
      /\ sem_wt_loc ce fp2 b2 ofs2 mp2
      (* mp1' is used to record the lost permission of (-Mptr, 0) of a
      heap block which cannot be expressed in mp1 and mp2 *)
      /\ massert_eqv mp (mp1 ** mp1' ** mp2)
      (* setting a new footprint into this location *)
      /\ (forall fp3 mp3, 
            (* We cannot set fp_emp as it would eliminate some
            predicate *)
            (* not_fp_emp fp3 = true -> *)
            sem_wt_loc ce fp3 b2 ofs2 mp3 ->
            exists mp' fp1'', 
              set_footprint phl fp3 fp1 = OK fp1''
              /\ sem_wt_loc ce fp1'' b1 ofs1 mp'
              /\ massert_eqv mp' (mp1 ** mp1' ** mp3)).
Proof.
  induction phl; intros.
  - inv GFP.
    exists STrue, STrue, mp, fp_emp.
    do 4 (try apply conj).
    reflexivity.
    econstructor. reflexivity.
    auto.
    rewrite <- !massert_eqv_pure_l. reflexivity.
    intros. exists mp3, fp3.
    do 3 (try apply conj).
    reflexivity.
    auto.
    rewrite <- !massert_eqv_pure_l. reflexivity.
    rewrite <- !massert_eqv_pure_l. reflexivity.
  - simpl in GFP.
    destruct a.
    + destr_fp_box fp1 GFP.
      inv WTLOC.
      exploit IHphl; eauto. intros (mp1 & mp1' & mp2 & fp1' & A1 & A2 & A3 & A4 & A5).
      (* destruct (not_fp_emp fp1') eqn: NOTEMP1. *)
    (*   * exists (hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero) ** box_pred fp1' b sz mp1).  *)
    (*     exists mp1'. *)
    (*     exists mp2, (fp_box b sz fp1'). *)
    (*     do 4 (try apply conj). *)
    (*     ++ simpl. rewrite A1. reflexivity. *)
    (*     ++ econstructor; eauto.  *)
    (*     ++ auto. *)
    (*     ++ rewrite EQV, FREE. unfold box_pred. *)
    (*        erewrite set_footprint_not_emp_inv; eauto. rewrite NOTEMP1. *)
    (*        rewrite A4.  *)
    (*        rewrite !sep_assoc. reflexivity.  *)
    (*     ++ intros. *)
    (*        exploit A5; eauto. intros (mp' & fp1'' & B1 & B2 & B3). *)
    (*        exists (hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero) ** box_pred fp1'' b sz mp'), (fp_box b sz fp1''). *)
    (*        do 2 (try apply conj). *)
    (*        ** simpl. rewrite B1. reflexivity. *)
    (*        ** econstructor; eauto.  *)
    (*        ** unfold box_pred. rewrite NOTEMP1.  *)
    (*           erewrite set_footprint_not_emp; eauto. rewrite B3. *)
    (*           rewrite !sep_assoc. reflexivity.  *)
    (*   (* if fp1' is fp_emp, we need to put more predicate on mp1' *) *)
    (*   * inv A1. inv GFP. *)
    (*     exists (hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero)).  *)
    (*     exists (contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz))) ** *)
    (*          mp1 ** mp1'). *)
    (*     exists mp2, (fp_box b sz fp1'). *)
    (*     do 4 (try apply conj). *)
    (*     ++ simpl. rewrite H0. reflexivity. *)
    (*     ++ econstructor; eauto. unfold box_pred. rewrite NOTEMP1.  *)
    (*        eapply massert_eqv_pure_r. *)
    (*     ++ auto. *)
    (*     ++ rewrite EQV, FREE. unfold box_pred. *)
    (*        rewrite NOTEMP. rewrite A4. rewrite !sep_assoc. reflexivity. *)
    (*     ++ intros. *)
    (*        exploit A5; eauto. intros (mp' & fp1'' & B1 & B2 & B3). *)
    (*        exists (hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero) ** box_pred fp1'' b sz mp'), (fp_box b sz fp1''). *)
    (*        do 2 (try apply conj). *)
    (*        ** simpl. rewrite B1. reflexivity. *)
    (*        ** econstructor; eauto.  *)
    (*        ** unfold box_pred. erewrite set_footprint_not_emp; eauto. rewrite B3. *)
    (*           rewrite !sep_assoc. reflexivity.  *)
    (* + destr_fp_field fp1 GFP. *)
    (*   simpl. rewrite FIND. *)
      (** Difficult !!  *)
Admitted.


(* Lemma get_owner_loc_footprint_sem_wt_split ce: forall phl b1 ofs1 b2 ofs2 fp1 fp1' fp2 mp *)
(*       (* Most of the time (b2,ofs2) is the location to be stored *) *)
(*       (GFP: get_owner_loc_footprint_map phl fp1 b1 ofs1 = Some (b2, ofs2, fp2)) *)
(*       (CLR: set_footprint phl fp_emp fp1 = Some fp1') *)
(*       (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mp), *)
(*     exists mp1 mp2,  *)
(*       sem_wt_loc ce fp1' b1 ofs1 mp1 *)
(*       /\ sem_wt_fp ce fp2 mp2 *)
(*       /\ massert_eqv mp (mp1 ** mp2). *)
(* Proof. *)
(* Admitted. *)

(* Used to do memory read in fp *)
Lemma get_owner_loc_footprint_map_sem_wt_split ce: forall phl id b ofs fp mp fpm1
      (GFP: get_owner_loc_footprint_map (id, phl) fpm1 = OK (b, ofs, fp))
      (COH: coherent_fpm ce fpm1 mp),
    exists mp1 mp2, sem_wt_loc ce fp b ofs mp1
               /\ massert_eqv mp (mp2 ** mp1).
Proof.
Admitted.


(************* End of properties of get/set_footprint_map ******************  *)

Lemma wt_footprint_size_eq ce : forall ty fp fpm,
    wt_footprint ce fpm ty fp ->
    sizeof ce ty = sizeof_footprint ce fp.
Admitted.

Lemma wt_footprint_align_eq ce : forall ty fp fpm,
    wt_footprint ce fpm ty fp ->
    alignof ce ty = alignof_footprint ce fp.
Admitted.


Definition fp_match_chunk (fp: footprint) chunk : Prop :=
  match fp with
  | fp_uninit sz al =>
      sz = size_chunk chunk /\ al = align_chunk chunk
  | fp_scalar chunk1 _ =>
      chunk1 = chunk
  | fp_box _ _
  | fp_ref _ _ _ _ _ => chunk = Mptr
  | fp_emp
  | fp_struct _ _
  | fp_enum _ _ _ _ _ 
  | fp_object _ _ _ => False
  end.


Lemma fp_match_chunk_size ce: forall fp chunk,
    fp_match_chunk fp chunk ->
    sizeof_footprint ce fp = size_chunk chunk.
Proof.
  destruct fp; simpl; intros; try contradiction; subst; auto.
  destruct H. auto.
Qed.  


Lemma fp_match_chunk_align ce: forall fp chunk,
    fp_match_chunk fp chunk ->
    alignof_footprint ce fp = align_chunk chunk.
Proof.
  destruct fp; simpl; intros; try contradiction; subst; auto.
  destruct H. auto.
Qed.

Inductive fp_field_in_range_aligned ce (sz al: Z) (f: footprint -> Prop) : ffpty -> Prop :=
| fp_field_in_range_aligned_intro: forall fid base fofs ffp
  (R1: 0 < fofs)
  (R2: (fofs + sizeof_footprint ce ffp) < sz)
  (R3: (alignof_footprint ce ffp | fofs))
  (R4: f ffp)
  (R5: (al | fofs)),
    fp_field_in_range_aligned ce sz al f (fid, ((base, fofs), ffp)).

(* This property should be implied by wt_footprint: the field offset must
be in range and aligned *)

Inductive fields_fp_well_formed ce : footprint -> Prop :=
| fp_emp_wf: fields_fp_well_formed ce fp_emp
| fp_uninit_wf sz al: fields_fp_well_formed ce (fp_uninit sz al)
| fp_scalar_wf chunk v: fields_fp_well_formed ce (fp_scalar chunk v)
| fp_box_wf b fp: fields_fp_well_formed ce (fp_box b fp)
| fp_ref_wf mut b ofs phs vs: fields_fp_well_formed ce (fp_ref mut b ofs phs vs)
| fp_object_wf id obj exposed: fields_fp_well_formed ce (fp_object id obj exposed)
| fp_struct_wf: forall id fpl
     (* This property says that all fields are within the size of this
     footprint *)
    (FWF: Forall (fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce)) fpl)
    (* This property says that all the location of the size of this footprint can be capatured by one of the fields *)
    (COMPLETE: forall ofs, 0 <= ofs < sizeof_comp ce id -> 
                      exists fid base fofs ffp, 
                        In (fid, ((base, fofs), ffp)) fpl
                        /\ base <= ofs < fofs + sizeof_footprint ce ffp),
  fields_fp_well_formed ce (fp_struct id fpl)
| fp_enum_wf: forall id tagz fid fofs ffp
    (FWF: fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce) (fid, ((size_chunk Mint32, fofs), ffp)))
    (COMPLETE: sizeof_comp ce id <= fofs + sizeof_footprint ce ffp),
  fields_fp_well_formed ce (fp_enum id tagz fid fofs ffp).

Lemma fp_match_chunk_well_formed ce: forall fp chunk,
    fp_match_chunk fp chunk ->
    fields_fp_well_formed ce fp.
Proof.
  destruct fp; intros; simpl in *; try contradiction; econstructor.
Qed.

(* Lemma fp_match_chunk_shallow_owned: forall fp chunk, *)
(*     fp_match_chunk fp chunk -> *)
(*     shallow_owned fp = true. *)
(* Proof. *)
(*   destruct fp; intros; simpl in *; try contradiction; try reflexivity. *)
(* Qed. *)

(* Lemma fp_match_chunk_not_emp: forall fp chunk, *)
(*     fp_match_chunk fp chunk -> *)
(*     not_fp_emp fp = true. *)
(* Proof. *)
(*   destruct fp; intros; simpl in *; try contradiction; try reflexivity. *)
(* Qed. *)

(** TODO  *)
(* Lemma fields_loc_sep_range_perm ce: forall fpl b ofs mp1 mp2 mp id *)
(*     (IH: forall (fid : ident) (base fofs : Z) (ffp : footprint), *)
(*         In (fid, (base, fofs, ffp)) fpl -> *)
(*         forall (mass : massert) (b : block) (ofs : Z), *)
(*           shallow_owned ffp = true -> *)
(*           fields_fp_well_formed ce ffp -> *)
(*           sem_wt_loc ce ffp b ofs mass ->       *)
(*             massert_imp mass (range b ofs (ofs + sizeof_footprint ce ffp))) *)
(*      (FWT: Forall *)
(*           (fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) *)
(*              (fields_fp_well_formed ce)) fpl) *)
(*      (COMPLETE: forall ofs1 : Z, *)
(*              0 <= ofs1 < sizeof_comp ce id -> *)
(*              (* It cannot be proved solely in induction case *) *)
(*              (exists (fid : ident) (base fofs : Z) (ffp : footprint), *)
(*                In (fid, (base, fofs, ffp)) fpl /\ base <= ofs1 < fofs + sizeof_footprint ce ffp) *)
(*              (* Or we already know that mass implies the range of [ofs, ofs+1) *) *)
(*              \/ massert_imp mp1 (range b (ofs + ofs1) (ofs + ofs1 + 1))) *)
(*      (SHALLOW: forall fid base fofs ffp, In (fid, (base, fofs, ffp)) fpl -> *)
(*                                     shallow_owned ffp = true) *)
(*      (FSEP: fields_loc_sep b ofs (sem_wt_loc ce) fpl mp2) *)
(*      (EQV: massert_eqv mp (mp1 ** mp2)),      *)
(*        massert_imp mp (range b ofs (ofs + sizeof_comp ce id)). *)
(* Proof. *)
(*   induction fpl; intros. *)
(*   - admit. *)
(*   - inv FSEP. inv FWT. *)
(*     exploit IH. simpl. left. reflexivity.  *)
(*     eapply SHALLOW. simpl. left. reflexivity. *)
(*     inv H1. auto. *)
(*     eauto. intros (mass1' & IMP1). *)
(*     rewrite <- sep_assoc in EQV0. *)
(*     set (mp1' := range b (ofs + base) (ofs + fofs) ** mass1) in *. *)
(*     assert (MP1RANG: massert_imp mp1' (range b (ofs + base) (ofs + fofs + sizeof_footprint ce ffp))) by admit. *)
(*     (* We want to put mp1' to mp1 when using IHfpl *) *)
(*     exploit (IHfpl b ofs (mp1 ** mp1') mass2 mp id). admit. *)
(*     eauto.  *)
(*     (** Most difficult part *) *)
(*     { intros. exploit COMPLETE; eauto. *)
(*       intros [(fid1 & base1 & fofs1 & ffp1 & A1 & A2) | IMP3]. *)
(*       - inv A1. *)
(*         + inv H0. right.  *)
(*           (* use MP1RANG and A2 *) *)
(*           etransitivity. eapply massert_imp_proj2. *)
(*           etransitivity. eapply MP1RANG. *)
(*           admit. *)
(*         + left. exists fid1, base1, fofs1, ffp1. split; auto. *)
(*       - right. *)
(*         etransitivity. eapply massert_imp_proj1. eauto. } *)
(*     admit. *)
(*     auto. *)
(*     admit. *)
(*     eauto. *)
(* Admitted. *)

(* We need to say that sem_wt_loc is readable/storable/freeable *)
Lemma sem_wt_loc_range_perm ce: forall fp mass b ofs ty fpm
      (* This place is not moved out (or borrowed out to
      callee). Maybe we should directly write wt_footprint here? *)
      (* (SHALLOW: shallow_owned fp = true) *)
      (* (FPWF: fields_fp_well_formed ce fp) *)
      (WTFP: wt_footprint ce fpm ty fp)
      (WTLOC: sem_wt_loc ce fp b ofs mass),
  (* We cannot prove their equivalence as mass may contain the value *)
(*   spec in this location which cannot be expressed by range. *)
    massert_imp mass (range b ofs (ofs + sizeof ce ty)).
Proof.
(*   induction fp using strong_footprint_ind; intros; inv WTLOC. *)
(*   - inv SHALLOW. *)
(*   - rewrite EQV. rewrite massert_imp_proj1. reflexivity. *)
(*   - rewrite EQV. etransitivity. eapply contains_range. *)
(*     reflexivity. *)
(*   - rewrite EQV. setoid_rewrite contains_range. eapply massert_imp_proj1. *)
(*   - inv FPWF. simpl in SHALLOW. erewrite forallb_forall in SHALLOW. *)
(*     eapply fields_loc_sep_range_perm. eauto. auto. auto. *)
(*     intros. eapply SHALLOW in H0. auto. *)
(*     eauto. rewrite EQV. instantiate (1 := spure (alignof_comp ce id | ofs)). *)
(*     rewrite sep_comm. reflexivity. *)
(*   - admit. *)
(*   - admit. *)
(*   - subst_dep. *)
(*     (* eapply mem_pred_range. *) *)
(*     admit. *)
(* Admitted. *)
Admitted.

Lemma sem_wt_loc_align ce: forall fp b ofs mass m ty fpm
    (WTLOC: sem_wt_loc ce fp b ofs mass)    
    (MPRED: m |= mass)
    (WTFP: wt_footprint ce fpm ty fp),
    (* (FPMAT: fp_match_chunk fp chunk), *)
    (ofs | alignof ce ty).
Proof.
Admitted.

(* Use sem_wt_loc_align to prove it? *)
Lemma sem_wt_loc_valid_access ce: forall fp b ofs mass m p chunk ty fpm
    (WTLOC: sem_wt_loc ce fp b ofs mass)    
    (MPRED: m |= mass)
    (WTFP: wt_footprint ce fpm ty fp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    (* (FPMAT: fp_match_chunk fp chunk), *)
    Mem.valid_access m chunk b ofs p.
Proof.
  (* induction fp using strong_footprint_ind; intros; red; inv WTLOC; simpl in FPMAT; try contradiction; rewrite EQV in *. *)
  (* - destruct FPMAT. subst. split. *)
  (*   + red. intros. eapply MPRED. simpl. eauto. *)
  (*   + eapply MPRED. *)
  (* - admit. *)
  (* - admit. *)
  (* - admit.    *)
Admitted.

(* After storing a semantically well-typed value into a location with
   range permissionm, this location becomes a semantically well-typed
   location. *)
Lemma store_sem_wt_val ce: forall fp mass MP chunk v b ofs m1 ty fpm
    (WTVAL: sem_wt_val ce fp v mass)
    (MPRED: m1 |= range b ofs (ofs + size_chunk chunk) ** mass ** MP)
    (AL: (align_chunk chunk | ofs))
    (* (MATCH: fp_match_chunk fp chunk), *)
    (WTFP: wt_footprint ce fpm ty fp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),    
    exists m2 mass', 
      Mem.store chunk m1 b ofs v = Some m2
      /\ sem_wt_loc ce fp b ofs mass'
      /\ m2 |= mass' ** MP. 
Proof.
  intros.
  destruct fp; inv WTVAL; inv WTFP.
  (* - inv MP0.  *)
  (*   eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result chunk v)) (v:= v) in MPRED; auto. *)
  (*   destruct MPRED as (m2 & STORE & MPRED). (* rewrite <- VEQ in *. *) *)
  (*   exists m2, (hasvalue chunk b ofs (Val.load_result chunk v)). split; auto. *)
  (*   split; auto. *)
  (*   econstructor. reflexivity.  *)
  (*   rewrite sep_swap in MPRED. eapply sep_proj2 in MPRED.  *)
  (*   auto.  *)
  (* - admit. *)
  (* - admit. *)
Admitted.

Lemma store_sem_wt_loc ce: forall fp vfp b ofs mass1 mass2 v m1 MP chunk ty fpm
    (WTLOC: sem_wt_loc ce fp b ofs mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (AL: (align_chunk chunk | ofs))
    (MPRED: m1 |= mass1 ** mass2 ** MP)
    (WTFP1: wt_footprint ce fpm ty fp)
    (WTFP2: wt_footprint ce fpm ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    exists m2 mass3, 
      Mem.store chunk m1 b ofs v = Some m2      
      /\ sem_wt_loc ce vfp b ofs mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros. eapply store_sem_wt_val; eauto.
  (* prove a lemma that extract the range from sem_wt_loc *)
  eapply sep_imp. eapply MPRED.
  (* erewrite <- (fp_match_chunk_size ce fp); eauto.  *)
  erewrite sizeof_by_value.
  eapply sem_wt_loc_range_perm. eapply WTFP1. all: eauto.
  (* eapply fp_match_chunk_shallow_owned; eauto. *)
  (* eapply fp_match_chunk_well_formed; eauto. *)
  (* auto. reflexivity. *)
Qed.  


Lemma store_coherent_var: forall phl m ce mass1 mass2 v vfp fp1 pfp chunk b1 ofs1 b2 ofs2 MP ty fpm
    (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (MPRED: m |= mass1 ** mass2 ** MP)
    (* id may denote an external owner? *)
    (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = OK (b2, ofs2, pfp))
    (* (SHALLOW: shallow_owned pfp = true) *)
    (* The following properties should be derived from wt_footprint *)
    (AL: (alignof ce ty | ofs2))
    (* (MAT1: fp_match_chunk pfp chunk) *)
    (* (MAT2: fp_match_chunk vfp chunk), *)
    (WTFP1: wt_footprint ce fpm ty pfp)
    (WTFP2: wt_footprint ce fpm ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    exists m1 fp2 mass3,
      Mem.store chunk m b2 ofs2 v = Some m1
      /\ set_footprint phl vfp fp1 = OK fp2
      /\ sem_wt_loc ce fp2 b1 ofs1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros.
  exploit get_owner_loc_footprint_sem_wt_split; eauto.
  intros (mp1 & mp1' & mp2 & fp1' & A1 & A2 & A3 & A4 & A5).
  rewrite A4 in MPRED.
  assert (MPRED1: m|= mp2 ** mass2 ** (mp1 ** mp1' ** MP)) by admit.
  exploit store_sem_wt_loc. eapply A3. all: eauto.
  eapply Z.divide_trans; try eapply alignof_by_value; eauto.
  intros (m2 & mass3 & B1 & B2 & B3).
  exploit A5.
  (* eapply fp_match_chunk_not_emp; eauto. *)
  eapply B2. intros (mp' & fp1'' &  C1 & C2 & C3).
  exists m2, fp1'', mp'. do 3 (try apply conj); eauto.
  rewrite C3. admit.
Admitted.

(*   induction phl; intros. *)
(*   - inv GFP.  *)
(*     exploit store_sem_wt_loc; eauto. *)
(*     intros (m2 & mass3 & STORE & WTLOC1 & MPRED1). *)
(*     exists m2, vfp, mass3. split; try split; auto.  *)
(*   - simpl in GFP. destruct a; try congruence. *)
(*     + destr_fp_box fp1 GFP. *)
(*       inv WTLOC. rewrite EQV in *. rewrite FREE in *. *)
(*       set (MP1 := hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero)) in *. *)
(*       unfold box_pred in MPRED. rewrite SHALLOW in MPRED. *)
(*       set (MP2 := contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz)))) in *. *)
(*       (* prove it with commutative lemmas of sepconj *) *)
(*       assert (MPRED1: m|= nextmp ** mass2 ** (MP ** MP1 ** MP2)) by admit. *)
(*       exploit IHphl; eauto. intros (m1 & fp2 & mass3 & A1 & A2 & A3 & A4). *)
(*       exists m1, (fp_box b sz fp2), (MP1 ** MP2 ** mass3). *)
(*       do 3 (try apply conj); eauto. *)
(*       * simpl. rewrite A2. reflexivity. *)
(*       * econstructor; eauto. unfold box_pred.  *)
(*       (** TODO: use WTVAL to show that vfp is not fp_emp and A2 to show that fp2 is shallow_init  *) admit. *)
(*       * admit. *)
(*     + destr_fp_field fp1 GFP. *)
(*       inv WTLOC. rewrite EQV in *. *)
(*       (* split fields_sep *) *)
(*       exploit fields_loc_sep_find_set; eauto. *)
(*       intros (mp1 & mp2 & mpi & l1 & l2 & A1 & A2 & A3 & A4 & A5 & A6). subst. *)
(*       eapply mconj_proj1 in MPRED as MPRED1. *)
(*       (* change only mpi *) *)
(*       assert (MPRED1': m|= mpi ** mass2 ** mp1 ** mp2 ** MP) by admit.       *)
(*       exploit IHphl; eauto. *)
(*       intros (m1 & fp2 & mpi' & C1 & C2 & C3 & C4). *)
(*       (* adhoc: we know that storing a location does not change its *)
(*       permission. *) *)
(*       assert (MPRED2: m |= range b1 ofs1 (ofs1 + sizeof_comp ce id)) by eapply MPRED. *)
(*       eapply store_range_unchanged in MPRED2 as MPRED2'; eauto.       *)
(*       rewrite <- sep_assoc in MPRED. rewrite (mconj_absorb1 _ _ mass2) in MPRED.       *)
(*       exploit frame_mconj. eapply MPRED.  *)
(*       rewrite <- !sep_assoc in C4. *)
(*       eapply C4. eauto. intros MPRED3. *)
(*       rewrite sep_assoc, (sep_swap mpi' mp1 _) in MPRED3. *)
(*       exists m1, (fp_struct id (set_field_fp fid fp2 (l1 ++ (fid, (z, f)) :: l2))), (mconj (mp1 ** mpi' ** mp2) (range b1 ofs1 (ofs1 + sizeof_comp ce id))).  *)
(*       split; try split; eauto. *)
(*       simpl. rewrite FIND. rewrite C2. reflexivity. *)
(*       split. *)
(*       econstructor; eauto. *)
(*       eauto. *)
(*     + destr_fp_enum fp1 GFP. *)
(*       inv WTLOC. rewrite EQV in *. clear EQV mass1. *)
(*       eapply mconj_proj1 in MPRED as MPRED1. *)
(*       set (mass1 := hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag))) in *. *)
(*       (* change only mpi *) *)
(*       assert (MPRED1': m|= mass3 ** mass2 ** mass1 ** MP) by admit. *)
(*       exploit IHphl; eauto. *)
(*       intros (m1 & fp2 & mass2' & C1 & C2 & C3 & C4). *)
(*       assert (MPRED2: m |= range b1 ofs1 (ofs1 + sizeof_comp ce id)) by eapply MPRED. *)
(*       eapply store_range_unchanged in MPRED2 as MPRED2'; eauto.       *)
(*       rewrite <- sep_assoc in MPRED. rewrite (mconj_absorb1 _ _ mass2) in MPRED.       *)
(*       exploit frame_mconj. eapply MPRED.  *)
(*       rewrite <- !sep_assoc in C4. *)
(*       eapply C4. eauto. intros MPRED3. *)
(*       rewrite (sep_comm mass2' mass1) in MPRED3. *)
(*       exists m1, (fp_enum id tag fid0 ofs fp2), (mconj (mass1 ** mass2') (range b1 ofs1 (ofs1 + sizeof_comp ce id))).  *)
(*       split; try split; eauto. *)
(*       simpl. rewrite dec_eq_true. rewrite C2. reflexivity. *)
(*       split. *)
(*       econstructor; eauto. *)
(*       eauto. *)
(* Admitted. *)

Lemma coherent_fpm_split ce: forall id fpm mp fp b ofs ty
      (B: fpm ! id = Some (b, ofs, ty, fp))
      (COH: coherent_fpm ce fpm mp),
      exists l1 l2 mp1 mp2 mpi, 
        Forall_sep (coherent_var ce) l1 mp1
        /\ Forall_sep (coherent_var ce) l2 mp2
        /\ coherent_var ce (id, (b, ofs, ty, fp)) mpi
        /\ PTree.elements fpm = l1 ++ (id, (b, ofs, ty, fp)) :: l2
        /\ massert_eqv mp (mp1 ** mpi ** mp2).
Proof.
  intros.
  exploit PTree.elements_remove. eapply B. intros (l1 & l2 & C1 & C2). 
  inv COH. rewrite C1 in ALLSEP. 
  erewrite Forall_sep_app in ALLSEP. 
  destruct ALLSEP as (mass11 & mass12 & D1 & D2 & D3). subst.
  inv D2. inv H1. inv ELTEQ.
  exists l1, l2. exists mass11, mass2, mass1.
  do 4 (try apply conj); eauto.
  econstructor; eauto.
  rewrite H4. reflexivity.
Qed.


(* We prove a strong version, i.e., the store operation can always succeed *)
Lemma store_coherent_fpm: forall phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty
    (COH: coherent_fpm ce fpm mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (MPRED: m |= mass1 ** mass2 ** MP)
    (* id may denote an external owner? We reduce all store for
    reference into store for their referred owner *)
    (GFP: get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, pfp))
    (* The following properties should be derived from wt_footprint *)
    (AL: (alignof ce ty | ofs))
    (* (MAT1: fp_match_chunk pfp chunk) *)
    (* (MAT2: fp_match_chunk vfp chunk),     *)
    (WTFP1: wt_footprint ce fpm ty pfp)
    (WTFP2: wt_footprint ce fpm ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    exists m1 fpm1 mass3,
      Mem.store chunk m b ofs v = Some m1
      /\ set_footprint_map (id, phl) vfp fpm = OK fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros. simpl in GFP. simpl.
  destruct (fpm ! id) as [(((b1 & ofs1) & ty1) & fp)|] eqn: B; try congruence.
  (* We should split the footprint for the id from mass1 *)
  exploit coherent_fpm_split; eauto.
  intros (l1 & l2 & mp1 & mp2 & mpi & A1 & A2 & A3 & A4 & A5). subst.
  (* apply store_coherent_var *)
  inv A3. inv ELTEQ.
  assert (MPRED1: m |= mpi ** mass2 ** (mp1 ** mp2 ** MP)) by admit.
  exploit store_coherent_var; eauto. 
  intros (m1 & fp2 & mp3 & B1 & B2 & B3 & B4).
  rewrite B2. simpl.
  do 3 eexists. do 3 (try eapply conj); eauto.
  - instantiate (1 := mp1 ** mp3 ** mp2).
    econstructor. 
    assert (TODO: PTree.elements (PTree.set id0 (b0, ofs0, opt_reg, ty0, fp2) fpm) = l1 ++ (id0, (b0, ofs0, opt_reg, ty, fp2)) :: l2) by admit.
    rewrite TODO.
    eapply Forall_sep_app. exists mp1, (mp3 ** mp2). 
    split; eauto. split. econstructor; eauto.
    econstructor; eauto. reflexivity.
  - rewrite sep_swap12 in B4. 
    rewrite <- !sep_assoc, (sep_assoc mp1) in B4.
    eauto.
Admitted.


Lemma assign_loc_by_value_coherent_fpm: forall phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty
    (COH: coherent_fpm ce fpm mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (MPRED: m |= mass1 ** mass2 ** MP)
    (* id may denote an external owner? We reduce all store for
    reference into store for their referred owner *)
    (GFP: get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, pfp))
    (* The following properties should be derived from wt_footprint *)
    (AL: (alignof ce ty | ofs))
    (* (MAT1: fp_match_chunk pfp chunk) *)
    (* (MAT2: fp_match_chunk vfp chunk),     *)
    (WTFP1: wt_footprint ce fpm ty pfp)
    (WTFP2: wt_footprint ce fpm ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    exists m1 fpm1 mass3,
      assign_loc ce ty m b (Ptrofs.repr ofs) v m1
      /\ set_footprint_map (id, phl) vfp fpm = OK fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros. 
  exploit store_coherent_fpm; eauto.
  intros (m1 & fpm1 & mass3 & A1 & A2 & A3 & A4).
  do 4 eexists; eauto.
  econstructor. eauto. simpl.
  rewrite Ptrofs.unsigned_repr. auto.
Admitted.


(*
(* storebytes rules *)

Lemma sem_wt_loc_merge ce: forall fp mp1 mp2 b ofs
    (WTFP: sem_wt_fp ce fp mp1)
    (WTLOC: sem_wt_loc ce (clear_footprint_rec ce fp) b ofs mp2),
    sem_wt_loc ce fp b ofs (mp2 ** mp1).
Proof.
  induction fp using strong_footprint_ind; intros; simpl in *; inv WTFP; inv WTLOC.
  - econstructor. auto. rewrite EQV, EQV0. symmetry.
    eapply massert_eqv_pure_r.
  - econstructor. auto. rewrite EQV, EQV0. symmetry.
    eapply massert_eqv_pure_r.
  - econstructor. rewrite EQV, EQV0. symmetry.
    eapply massert_eqv_pure_r.
  - unfold box_pred in FREE. simpl in FREE. 
    econstructor; eauto.
    rewrite EQV, EQV0. rewrite FREE. eapply sepconj_morph_2.
    symmetry. eapply massert_eqv_pure_r. reflexivity.
  - econstructor.
    (** TODO: write a helper function for fields_fp_sep *)
Admitted.

Definition pin_footprint (fp: footprint) : bool :=
  match fp with
  | fp_object _ _ _ => true
  | _ => false
  end.

Lemma sem_wt_loc_split ce: forall fp mp b ofs
    (* We assume fp must not be opaque object *)
    (UNPIN: pin_footprint fp = false)
    (WTLOC: sem_wt_loc ce fp b ofs mp),
    exists mp1 mp2, sem_wt_loc ce (clear_footprint_rec fp) b ofs mp1
               /\ sem_wt_fp ce fp mp2
               /\ massert_eqv mp (mp1 ** mp2).
Proof.
  induction fp using strong_footprint_ind; intros; simpl in *; inv UNPIN; inv WTLOC.
  - exists STrue, STrue. split. econstructor. reflexivity.
    split. econstructor. reflexivity. rewrite EQV.
    eapply massert_eqv_pure_r.
  - exists ((range b ofs (ofs + sz)) ** spure (al | ofs)), STrue.
    do 2 try apply conj. econstructor; auto.
    econstructor. reflexivity.
    rewrite EQV. eapply massert_eqv_pure_r.
  - exists (hasvalue chunk b ofs v), STrue.
    do 2 try apply conj. econstructor; auto.
    econstructor. reflexivity.
    rewrite EQV. eapply massert_eqv_pure_r.
  - exists (hasvalue Mptr b0 ofs (Vptr b Ptrofs.zero)), mp0.
    do 2 try apply conj.
    + econstructor; auto. econstructor. reflexivity.
      unfold box_pred. simpl. 
      eapply massert_eqv_pure_r.
    + econstructor. eauto. auto.
    + auto.
  (** TODO: write helper for fields_loc_sep  *)
  - admit.
  - admit.
  - admit.
Admitted.


(************** End of split rules ********************** *)


Lemma storebytes_fields_loc_sep ce: forall fpl tb tofs sb sofs mp1 mp2 mp3 MP m1 m2 bytes (P1: footprint -> massert -> Prop) (P2: (footprint -> block -> Z -> massert -> Prop)) sz al
     (* induciton priciple from storebytes_sem_wt_loc  *)
    (IH: forall (fid : ident) base (ofs : Z) (fp : footprint),
        In (fid, ((base, ofs), fp)) fpl ->
        forall (tb : block) (tofs : Z) (sb : block) (sofs : Z) (mp1 mp2 mp3 MP : massert)
          (m1 m2 : mem) (bytes : list memval),
          P1 fp mp2 ->
          P2 (clear_footprint_rec fp) sb sofs mp3 ->
          massert_imp mp1 (range tb tofs (tofs + sizeof_footprint ce fp)) ->
          massert_imp (mp1 ** MP) mp3 ->
          m1 |= mp1 ** mp2 ** MP ->
          (alignof_footprint ce fp | tofs) ->
          Mem.loadbytes m1 sb sofs (sizeof_footprint ce fp) = Some bytes ->
          Mem.storebytes m1 tb tofs bytes = Some m2 ->
          fields_fp_well_formed ce fp ->
          exists mass3 : massert, P2 fp tb tofs mass3 /\ m2 |= mass3 ** MP)
    (SEMWTFP: fields_fp_sep P1 fpl mp2)
    (SHALLOW: fields_loc_sep sb sofs P2 ((map (fun '(fid, (fofs, ffp)) => (fid, (fofs, clear_footprint_rec ffp))) fpl)) mp3)
    (RANGE: massert_imp mp1 (range tb tofs (tofs + sz)))
    (MPIMP: massert_imp (mp1 ** MP) mp3)
    (MPRED : m1 |= mp1 ** mp2 ** MP)
    (AL: (al | tofs))
    (LOAD: Mem.loadbytes m1 sb sofs sz = Some bytes)
    (STORE: Mem.storebytes m1 tb tofs bytes = Some m2)
    (WF: Forall (fp_field_in_range_aligned ce sz al
                   (fields_fp_well_formed ce)) fpl),
  exists (mass3 : massert), 
      fields_loc_sep tb tofs P2 fpl mass3 /\ m2 |= mass3 ** MP.
Proof.
Admitted.

Lemma storebytes_sem_wt_loc ce: forall sfp tb tofs sb sofs mp1 mp2 mp3 MP m1 m2 bytes
    (* Since (sb, sofs) may be overlapped with the footprint of (mp1
    ** MP), so we just provide the footprint of the value stored in
    (sb, sofs), i.e., mp2. When (mp1 ** MP) implies mp3, we know the
    value loaded from (sb, sofs) and stored into (tb, tofs) can make
    this location sem_wt_loc. *)
    (SEMWTFP: sem_wt_fp ce sfp mp2)
    (SHALLOW: sem_wt_loc ce (clear_footprint_rec sfp) sb sofs mp3)
    (* (WTVALLOC : sem_wt_loc ce sfp sb sofs (mp2 ** mp3)) *)
    (* We prove a more general version without WTLOC of (tb, tofs),
    meaning that we do not care what footprint was in the target
    location (which would be overwritten after storing the bytes, so
    it is also safe to drop its footprint). We just need to know that
    the target location is storable and aligned. *)
    (RANGE: massert_imp mp1 (range tb tofs (tofs + sizeof_footprint ce sfp)))
    (MPIMP: massert_imp (mp1 ** MP) mp3)
    (MPRED : m1 |= mp1 ** mp2 ** MP)
    (AL: (alignof_footprint ce sfp | tofs))
    (LOAD: Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes)
    (* since (sb, sofs) is sem_wt_loc, the progress of storebytes is
    straightforward *)
    (STORE: Mem.storebytes m1 tb tofs bytes = Some m2)
    (WF: fields_fp_well_formed ce sfp),
  exists (mass3 : massert), 
      sem_wt_loc ce sfp tb tofs mass3 /\ m2 |= mass3 ** MP.
Proof.
  induction sfp using strong_footprint_ind; intros.
  - erewrite Mem.loadbytes_empty in LOAD. 2: simpl; try lia.
    inv LOAD.
    exploit Mem.storebytes_empty; eauto. intros. subst.
    exists STrue. split. econstructor. reflexivity.
    eapply sepconj_morph_1. 3: eapply MPRED.
    rewrite massert_eqv_pure_r. eapply massert_imp_proj2.
    eapply massert_imp_proj2.
  - exists ((range tb tofs (tofs + sizeof_footprint ce (fp_uninit sz al))) ** (spure (alignof_footprint ce (fp_uninit sz al) | tofs))).
    split. econstructor. reflexivity.
    rewrite RANGE in MPRED. eapply sep_drop2 in MPRED.
    assert (MPRED1: m1 |= range tb tofs (tofs + sizeof_footprint ce (fp_uninit sz al)) ** spure (alignof_footprint ce (fp_uninit sz al) | tofs) ** MP).
    { rewrite sep_swap.
      rewrite <- massert_eqv_prop_l; auto. }
    rewrite sep_assoc.
    eapply sep_preserved. eauto. intros. eapply storebytes_range_unchanged; eauto.
    intros. eapply m_invar. eauto.
    eapply Mem.storebytes_unchanged_on. eauto.
    intros. intro. simpl in H1. 
    destruct H1; try contradiction.
    eapply MPRED; eauto. simpl. 
    admit.
  (* TODO: scalar,box and ref may share same proof structure. Maybe we
  should write a lemma for them *)
  - inv SHALLOW. 
    (* We cannot use store_sem_wt_val to prove this lemma because we
    only know (decode_val bytes = v) from MPRED and LOAD, but [store]
    operation in store_sem_wt_val would store [encode_val v] into the
    memory which may not equal to [bytes]. We can use
    [Mem.load_loadbytes] to prove [v = decode_val bytes],
    [Mem.loadbytes_storebytes_same] to prove that bytes loaded from m2
    at (tb, tofs) is [bytes], and [Mem.loadbytes_load] to prove value
    loaded from m2 at (tb, tofs) is [v], which can derive [hasvalue] *)
    assert (LOAD': Mem.load chunk m1 sb sofs = Some v) by admit.
    exploit Mem.load_loadbytes; eauto. intros (bytes' & LOAD'' & VEQ). 
    simpl in LOAD.
    rewrite LOAD'' in LOAD. inv LOAD.
    exploit Mem.loadbytes_storebytes_same; eauto. intros LOAD2.
    assert (SZEQ: Z.of_nat (length bytes) = size_chunk chunk) by admit.
    rewrite SZEQ in *.
    exploit Mem.loadbytes_load; eauto. intros LOAD2'.
    (* prove m1 |= hasvalue tb tofs v *)
    rewrite RANGE in MPRED.
    eapply (sep_preserved m1 m2) in MPRED as MPRED1.
    exploit range_hasvalue. eapply MPRED1. eauto. intros MPRED2.
    exists (hasvalue chunk tb tofs (decode_val chunk bytes)). split.
    econstructor. reflexivity. eapply sep_drop2 in MPRED2. eauto.
    (* range unchanged *)
    intros. eapply storebytes_range_unchanged; eauto.
    (* frame-preserving update *)
    intros. eapply m_invar. eauto.
    eapply Mem.storebytes_unchanged_on. eauto.
    intros. simpl. intro. rewrite SZEQ in *. 
    eapply MPRED. simpl. split; eauto. 
    simpl. eauto. 
  (* similar to fp_scalar, but we need to consider the value footprint (mp2) *)
  - inv SHALLOW. 
    assert (LOAD': Mem.load Mptr m1 sb sofs = Some (Vptr b Ptrofs.zero)) by admit.
    exploit Mem.load_loadbytes; eauto. intros (bytes' & LOAD'' & VEQ). 
    simpl in LOAD.
    rewrite LOAD'' in LOAD. inv LOAD.
    exploit Mem.loadbytes_storebytes_same; eauto. intros LOAD2.
    assert (SZEQ: Z.of_nat (length bytes) = size_chunk Mptr) by admit.
    rewrite SZEQ in *.
    exploit Mem.loadbytes_load; eauto. intros LOAD2'.
    (* prove m1 |= hasvalue tb tofs v *)
    generalize MPRED as MPRED'. intros.
    rewrite RANGE in MPRED.
    eapply (sep_preserved m1 m2) in MPRED as MPRED1.
    exploit range_hasvalue. eapply MPRED1. eauto. intros MPRED2. 
    (* get the structure of mp2 *)
    inv SEMWTFP. 
    exists (hasvalue Mptr tb tofs (decode_val Mptr bytes) ** mp2).
    split.
    econstructor; eauto. rewrite VEQ. reflexivity. rewrite sep_assoc. eapply MPRED2.
    (* range unchanged *)
    intros. eapply storebytes_range_unchanged; eauto.
    (* frame-preserving update *)
    intros. eapply m_invar. eauto.
    eapply Mem.storebytes_unchanged_on. eauto.
    intros. simpl. intro. rewrite SZEQ in *. 
    eapply MPRED. simpl. split; eauto. 
    simpl. eauto. 
  (* fp_struct: we need a premise to ensure that all fields are within
  the range of this struct *)
  - simpl in RANGE. 
    (* alignment (alignof_comp ce id | tofs) can be proved by WTLOC as
    (alignof_footprint tfp) is equal to (alignof_comp ce id) *)
    inv SEMWTFP. inv SHALLOW.
    rewrite EQV in MPRED. 
    (** storebytes_fields_loc_sep: the most difficult part of
    storebytes rules: Proof strategy: split mass and (range tb tofs)
    into fields. Then we can split the loadbytes and storebytes into
    sequence of loadbytes/storebytes *)
    exploit storebytes_fields_loc_sep; eauto.
    etransitivity. eauto. rewrite EQV0. eapply massert_imp_proj1.
    inv WF. eauto.
    intros (mass3 & FLOCSEP & MPRED2).
    exists mass3.
    split. econstructor; eauto. 
    eapply massert_eqv_prop_r. auto. auto.
  - admit.
  - admit.
  - inv SEMWTFP.
Admitted.


Lemma storebytes_coherent_var: forall phl m1 ce mass1 mp2 mp3 sfp sb sofs fp1 tfp b1 ofs1 tb tofs MP
    (SEMWTFP : sem_wt_fp ce sfp mp2)
    (SHALLOW: sem_wt_loc ce (clear_footprint_rec sfp) sb sofs mp3)
    (* The variable address *)
    (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mass1)
    (MPIMP: massert_imp (mass1 ** MP) mp3)
    (MPRED: m1 |= mass1 ** mp2 ** MP)
    (* id may denote an external owner? *)
    (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = Some (tb, tofs, tfp))
    (ALEQ: alignof_footprint ce sfp = alignof_footprint ce tfp)
    (SZEQ: sizeof_footprint ce sfp = sizeof_footprint ce tfp)
    (AL: (alignof_footprint ce sfp | tofs))
    (WF1: fields_fp_well_formed ce sfp)
    (WF2: fields_fp_well_formed ce tfp)
    (* As we need to load bytes from sfp so it must imply range_perm *)
    (OWN1: shallow_owned sfp = true)
    (OWN2: shallow_owned tfp = true),
    exists bytes m2 fp2 mass3,
      Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes
      /\ Mem.storebytes m1 tb tofs bytes = Some m2
      /\ set_footprint phl sfp fp1 = Some fp2
      /\ sem_wt_loc ce fp2 b1 ofs1 mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros.
  (* progress of loadbytes and storebytes *)
  exploit sem_wt_loc_merge; eauto. intros SRCWTLOC.
  exploit sem_wt_loc_range_perm. eapply OWN1. all: eauto. 
  intros MIMP.
  assert (MPRED': m1 |= mp3 ** mp2) by admit.
  rewrite MIMP in MPRED'.
  exploit Mem.range_perm_loadbytes. 
  red. intros. eapply MPRED'; eauto.
  intros (bytes & LOAD).
  exploit Mem.loadbytes_length; eauto. intros LEN.
  (* storebytes *)
  exploit get_owner_loc_footprint_sem_wt_split; eauto.
  intros (mp1 & mp1' & mp4 & fp1' & A1 & A2 & A3 & A4 & A5).
  exploit sem_wt_loc_range_perm. eapply OWN2. all: eauto. 
  intros MIMP2.
  assert (MPRED1: m1 |= mp4). rewrite A4 in MPRED. eapply MPRED.
  rewrite MIMP2 in MPRED1.
  edestruct Mem.range_perm_storebytes with (b:= tb) (ofs := tofs) as (m2 & STORE).
  red. intros. eapply MPRED1; eauto. rewrite <- SZEQ. rewrite LEN in *.
  rewrite Z_to_nat_max in H. 
  (* show sizeof_footprint is positive *)
  admit.
  exploit (storebytes_sem_wt_loc ce sfp tb tofs sb sofs mp4 mp2 mp3 (mp1 ** mp1' ** MP)); eauto. 
  rewrite SZEQ. auto. 
  rewrite A4 in MPIMP. 
  (* prove by MPIMP *)
  admit.
  rewrite A4 in MPRED. 
  (* prove by MPRED *)
  admit.
  intros (mass3 & B1 & B2).
  exploit A5; eauto. 
  eapply shallow_owned_not_emp; eauto.
intros (mp' & fp1'' & SET & C1 & C2).  
  exists bytes, m2, fp1'', mp'. 
  do 4 (try apply conj); eauto.
  rewrite C2. admit.
Admitted.


(*   (** We may use get_owner_loc_footprint_sem_wt_split to prove this *)
(*   lemma, instead of doing induction on phl like *)
(*   store_coherent_var. But the difficult part is how to write a *)
(*   set_footprint rule after storing the bytes and prove sem_wt_loc *)
(*   again? *) *)
(*   (* assert (CLR: exists fp1', clear_owner_footprint ce fp1 phl = Some fp1') by admit. *) *)
(*   (* destruct CLR as (fp1' & CLR). *) *)
(*   (* exploit get_owner_loc_footprint_sem_wt_split; eauto. *) *)
(*   (* intros (mp1 & mp4 & mp5 & A1 & A2 & A3 & A4). *) *)
(*   (* assert (LOAD: exists bytes, Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes) by admit. *) *)
(*   (* destruct LOAD as (bytes & LOAD). *) *)
(*   (* assert (STORE: exists m2, Mem.storebytes m1 tb tofs bytes = Some m2) by admit. *) *)
(*   (* destruct STORE as (m2 & STORE). *) *)
(*   (* exploit (storebytes_sem_wt_loc ce sfp tb tofs sb sofs mp4 mp2 mp3 (mp1 ** mp5 **  MP)); eauto.  *) *)
(*   (* admit.  admit. admit. intros (mass3 & B1 & B2). *) *)
(*   (* (** TODO: set_ootprint *) *)   *)
(*   induction phl; intros. *)
(*   - inv GFP.  *)
(*     (* use storebytes_sem_wt_loc *) *)
(*     admit. *)
(*   (* similar to store_coherent_var *) *)
(*   - simpl in GFP. destruct a; try congruence. *)
(*     + destr_fp_box fp1 GFP. *)
(*       inv WTLOC. rewrite EQV in *. rewrite FREE in *. *)
(*       set (MP1 := hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero)) in *. *)
(*       unfold box_pred in *. rewrite SHALLOW0 in *. *)
(*       set (MP2 := contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz)))) in *. *)
(*       (* prove it with commutative lemmas of sepconj *) *)
(*       assert (MPRED1: m1 |= nextmp ** mp2 ** (MP ** MP1 ** MP2)) by admit.       *)
(*       exploit IHphl. eapply SEMWTFP.  all: eauto. admit. *)
(*       intros (bytes & m2 & fp2 & mass3 & A1 & A2 & A3 & A4 & A5). *)
(*       exists bytes, m2, (fp_box b sz fp2), (MP1 ** box_pred fp2 b sz mass3). *)
(*       do 4 (try apply conj); eauto. *)
(*       * simpl. rewrite A3. reflexivity. *)
(*       * econstructor; eauto.  *)
(*       * unfold box_pred. destruct (shallow_init fp2). admit. admit.                *)
(*     + destr_fp_field fp1 GFP. *)
(*       inv WTLOC. rewrite EQV in *. *)
(*       (* split fields_sep *) *)
(*       exploit fields_loc_sep_find_set; eauto. *)
(*       intros (mp1 & mp4 & mpi & l1 & l2 & A1 & A2 & A3 & A4 & A5 & A6). subst. *)
(*       eapply mconj_proj1 in MPRED as MPRED1. *)
(*       (* change only mpi *) *)
(*       assert (MPRED1': m1|= mpi ** mp4 ** mp1 ** mp2 ** MP) by admit.       *)
(*       exploit IHphl. eapply SEMWTFP. eapply SHALLOW.  *)
(*       massert_imp *)
(* eapply  *)

(* all: eauto. *)
(*       intros (bytes & m2 & fp2 & mpi' & C1 & C2 & C3 & C4 & C5). *)
(*       (* adhoc: we know that storing a location does not change its *)
(*       permission. *) *)
(*       assert (MPRED2: m1 |= range b1 ofs1 (ofs1 + sizeof_comp ce id)) by eapply MPRED. *)
(*       eapply storebytes_range_unchanged in MPRED2 as MPRED2'; eauto.       *)
(*       rewrite <- sep_assoc in MPRED. rewrite (mconj_absorb1 _ _ mass2) in MPRED.       *)
(*       exploit frame_mconj. eapply MPRED.  *)
(*       rewrite <- !sep_assoc in C5. *)
(*       eapply C5. eauto. intros MPRED3. *)
(*       rewrite sep_assoc, (sep_swap mpi' mp1 _) in MPRED3. *)
(*       exists bytes, m2, (fp_struct id (set_field_fp fid fp2 (l1 ++ (fid, (z, f)) :: l2))), (mconj (mp1 ** mpi' ** mp2) (range b1 ofs1 (ofs1 + sizeof_comp ce id))).  *)
(*       do 4 (try apply conj); eauto. *)
(*       simpl. rewrite FIND. rewrite C3. reflexivity. *)
(*       econstructor; eauto. *)
(*     + destr_fp_enum fp1 GFP. *)
(*       inv WTLOC. *)
(*       eapply mconj_proj1 in MPRED as MPRED1. *)
(*       set (mass1 := hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag))) in *. *)
(*       (* change only mpi *) *)
(*       assert (MPRED1': m1|= mass3 ** mass2 ** mass1 ** MP) by admit. *)
(*       exploit IHphl. eapply FWT. eapply WTVAL. all: eauto. *)
(*       intros (bytes & m2 & fp2 & mass2' & C1 & C2 & C3 & C4 & C5). *)
(*       assert (MPRED2: m1 |= range b1 ofs1 (ofs1 + sizeof_comp ce id)) by eapply MPRED. *)
(*       eapply storebytes_range_unchanged in MPRED2 as MPRED2'; eauto.       *)
(*       rewrite <- sep_assoc in MPRED. rewrite (mconj_absorb1 _ _ mass2) in MPRED.       *)
(*       exploit frame_mconj. eapply MPRED.  *)
(*       rewrite <- !sep_assoc in C5. *)
(*       eapply C5. eauto. intros MPRED3. *)
(*       rewrite (sep_comm mass2' mass1) in MPRED3. *)
(*       exists bytes, m2, (fp_enum id tag fid0 ofs fp2), (mconj (mass1 ** mass2') (range b1 ofs1 (ofs1 + sizeof_comp ce id))).  *)
(*       do 4 (try apply conj); eauto. *)
(*       simpl. rewrite dec_eq_true. rewrite C3. reflexivity. *)
(*       econstructor; eauto. *)
(* Admitted. *)

(* Some work around for not defining sem_wt_bytes (which may require
 slicing bytes when defining the struct case which is complicated):
 since loading bytes and storing bytes can only happen in assign_loc,
 we can use the sem_wt_loc fact (provided by sem_wt_val for
 struct/enum footprint) of the assigner and prove that when storing
 its bytes into the assignee, the target location is sem_wt_loc. *)
Lemma storebytes_coherent_fpm: forall phl m1 ce fpm mass1 mp2 mp3 sfp tfp sb sofs tb tofs id MP
    (COH: coherent_fpm ce fpm mass1)
    (* note that sfp is separated from fpm, meaning that it has been
    moved from *)
    (** It is not correct! because mass2 also contains the location of
    (sb, sofs). We should define a new-version of sem_wt_loc to only
    express the value spec of this location. *)
    (* mp1 is the predicate for the value stored in (sb, sofs) and mp2
    is the footprint of this value *)
    (SEMWTFP : sem_wt_fp ce sfp mp2)
    (SHALLOW: sem_wt_loc ce (clear_footprint_rec sfp) sb sofs mp3)
    (MPIMP: massert_imp (mass1 ** MP) mp3)
    (MPRED: m1 |= mass1 ** mp2 ** MP)
    (* id may denote an external owner? We reduce all store for
    reference into store for their referred owner *)
    (* properties of get_owner_loc_footprint?  *)
    (GFP: get_owner_loc_footprint_map (id, phl) fpm = Some (tb, tofs, tfp))
    (* The following properties should be derived from wt_footprint *)
    (ALEQ: alignof_footprint ce sfp = alignof_footprint ce tfp)
    (SZEQ: sizeof_footprint ce sfp = sizeof_footprint ce tfp)
    (AL: (alignof_footprint ce sfp | tofs))
    (WF1: fields_fp_well_formed ce sfp)
    (WF2: fields_fp_well_formed ce tfp)
    (* As we need to load bytes from sfp so it must imply range_perm *)
    (OWN1: shallow_owned sfp = true)
    (OWN2: shallow_owned tfp = true),
    exists bytes m2 fpm1 mass3,
      Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes
      /\ Mem.storebytes m1 tb tofs bytes = Some m2
      /\ set_footprint_map (id, phl) sfp fpm = Some fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros. simpl in GFP. 
  destruct (fpm ! id) as [(((b1 & ofs1) & ty1) & fp)|] eqn: B; try congruence.
  (* We should split the footprint for the id from mass1 *)
  exploit coherent_fpm_split; eauto.
  intros (l1 & l2 & mp1 & mp4 & mpi & A1 & A2 & A3 & A4 & A5). subst.
  (* apply storebytes_coherent_var *)
  inv A3. inv ELTEQ.
  assert (MPRED1: m1 |= mpi ** mp2 ** (mp1 ** mp4 ** MP)) by admit.
  exploit storebytes_coherent_var. eauto. eapply SHALLOW. eapply MASS. 
  2: eapply MPRED1. admit.      (* easy *)
  all: eauto.
  intros (bytes & m2 & fp2 & mass3 & B1 & B2 & B3 & B4 & B5).
  cbn [set_footprint_map]. rewrite B. rewrite B3.
  exists bytes, m2.
  exists (PTree.set id0 (b, ofs, opt_reg, ty, fp2) fpm), (mass3 ** mp1 ** mp4).
  do 4 (try eapply conj); eauto.
  - econstructor. 
    assert (TODO: PTree.elements (PTree.set id0 (b, ofs, opt_reg, ty, fp2) fpm) = l1 ++ (id0, (b, ofs, opt_reg, ty, fp2)) :: l2) by admit.
    (* rewrite TODO. *)
    (* eapply Forall_sep_app. exists mp1, (mp3 ** mp2).  *)
    (* split; eauto. split. econstructor; eauto. *)
    (* econstructor; eauto. reflexivity. *)
    admit.
  - rewrite !sep_assoc. auto.
Admitted.

(** TODO: assign_loc rule  *)


(** Define functions for extracting the footprint that represents the
locations passed by reference *)

(* Assume that we have the list of argument footprints *)

(* input: footprint 

output: list (path, footprint) satisfying：

1. all paths are disjoint
2. (fpm, output) should satisfying that:
  2.1 all the footprint of the path in output is fp_emp in fpm
  2.2 when we set all the footprint of the output back to fpm, we can the original fpm
  2.3 

 *)

(*

(* collect the owner paths stored in the leaf nodes that are fp_ref *)
Fixpoint collect_footprint_ref_paths (fp: footprint) : list path :=
  match fp with
  | fp_struct _ fpl =>
      flat_map  (fun '(_, (_, ffp)) => collect_footprint_ref_paths ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      collect_footprint_ref_paths ffp
  | fp_box _ fp1 =>
      collect_footprint_ref_paths fp1
  | fp_ref _ _ ph =>
      ph :: nil
  | _ => nil
  end.

Definition collect_fpm_ref_paths (fpm: fp_map) : list path :=
  let fpl := map (fun '(_, (_, _, _, _, fp)) => fp) (PTree.elements fpm) in
  flat_map collect_footprint_ref_paths fpl.


Definition get_owner_footprint_map_ref_paths (fpm: fp_map) (ph: path) : res (list path) :=
  match get_owner_footprint_map ph fpm with
  | Some fp =>
      OK (collect_footprint_ref_paths fp)
  | None =>
      Error nil
  end.


(* We need to ensure that all the returned paths are disjoint, its
located note contain deep_init footprint, and form a closure *)
Definition collect_fpm_args_ref_paths (fpm: fp_map) (args: list footprint) : res (list path) :=
  let not_visited := collect_fpm_ref_paths fpm in
  let to_visit := flat_map collect_footprint_ref_paths args in
  collect_ref_paths_generic (get_owner_footprint_map_ref_paths fpm) nil to_visit not_visited (lex_ord_lt_acc_intro _ _).

Fixpoint generate_new_suffix_path_footprint (l: list path) (fp: footprint) : res footprint :=
  match fp with
  | fp_ref b ofs ph =>
      do ph1 <- generate_new_suffix_path l ph;
      OK (fp_ref b ofs ph1)
  | fp_box b fp1 =>
      do fp1' <- generate_new_suffix_path_footprint l fp1;
      OK (fp_box b fp1')
  | fp_struct id fpl =>
      do fpl1 <- (mmap (fun '(fid, ((base, fofs), ffp)) => 
                            do ffp1 <- generate_new_suffix_path_footprint l ffp;
                            OK (fid, ((base, fofs), ffp1))) fpl);
      OK (fp_struct id fpl1)
  | fp_enum id tagz fid fofs ffp =>
      do ffp1 <- generate_new_suffix_path_footprint l ffp;
      OK (fp_enum id tagz fid fofs ffp1)
  | fp_object id obj exposed =>
      do exposed1 <- (mmap (fun '(fid, ((b, ofs), ffp)) =>
                             do ffp1 <- generate_new_suffix_path_footprint l ffp;
                             OK (fid, ((b, ofs), ffp1))) exposed);
      OK (fp_object id obj exposed)
  | _ => OK fp
  end.

(* Collect the footprints that are passed via reference to the environment *)
Definition collect_fpm_passed_ref_footprint (fpm: fp_map) (l: list path) : res (list footprint) :=
  mmap (fun ph => match get_owner_footprint_map ph fpm with
              | Some fp => 
                  do fp1 <- (generate_new_suffix_path_footprint l fp);
                  OK fp1
              | None =>
                  Error nil
              end) l.

*) 
(* set fp_emp to the location that passed via reference *)
Fixpoint clear_fpm_passed_ref_footprint (fpm: fp_map) (l: list path) : res fp_map :=
  match l with
  | nil => OK fpm
  | ph :: phl =>
      match set_footprint_map ph fp_emp fpm with
      | Some fpm1 =>
          clear_fpm_passed_ref_footprint fpm1 phl
      | None =>
          Error nil
      end
  end.


(*
(* The output parameters contain two parts: one for the normal
arguments and the others are the memory locations passed via
reference *)
Definition generate_call_parameters (fpm: fp_map) (args: list footprint) : res (list footprint * list footprint * list path) :=
  do extern_paths <- collect_fpm_args_ref_paths fpm args;
  do args1 <- mmap (generate_new_suffix_path_footprint extern_paths) args;
  do extern_fps <- collect_fpm_passed_ref_footprint fpm extern_paths;
  OK (args1, extern_fps, extern_paths).


(* For funciton return, we need to reset the path name of the external
reference location to its normalized forms (i.e., the ordinal in the
list passed by caller). We can reuse the generate_new_suffix_path_footprint
to do this work. *)
Definition generate_return_parameters (fpm: fp_map) (retv: footprint) (ns: list ident) : res (footprint * list footprint) :=
  let phs := map (fun id => (id, nil)) ns in
  do retv1 <- generate_new_suffix_path_footprint phs retv;
  do out_params <- collect_fpm_passed_ref_footprint fpm phs;
  OK (retv1, out_params).


(* When receive return value/input arguments from environment, the
current function should recover the normalized names that are passed
to environment (or generate new names to avoid name conflict with the
current variable names at function entry). These two kinds of
operations can be done using recover_sval_ref_paths. *)

Fixpoint recover_footprint_ref_paths (l: list path) (fp: footprint)  : res footprint :=
  match fp with
  | fp_ref b ofs ph =>
      do ph1 <- recover_ref_path l ph;
      OK (fp_ref b ofs ph1)
  | fp_box b fp1 =>
      do fp1' <- recover_footprint_ref_paths l fp1;
      OK (fp_box b fp1')
  | fp_struct id fpl =>
      do fpl1 <- mmap (fun '(fid, ((base, fofs), ffp)) => 
                        do ffp1 <- recover_footprint_ref_paths l ffp;
                        OK (fid, ((base, fofs), ffp1))) fpl;
      OK (fp_struct id fpl1)
  | fp_enum id tagz fid fofs ffp =>
      do ffp1 <- recover_footprint_ref_paths l ffp;
      OK (fp_enum id tagz fid fofs ffp1)
  | fp_object id obj exposed =>
      do exposed1 <- mmap (fun '(fid, ((b, ofs), ffp)) => 
                        do ffp1 <- recover_footprint_ref_paths l ffp;
                        OK (fid, ((b, ofs), ffp1))) exposed;
      OK (fp_object id obj exposed1)
  | _ =>
      OK fp
  end.


(* When the caller receives the returned footprint and the
reference-passed footprint list, it updates their reference paths and
then putback to the fpm. The caller should guarantee that the external
footprints are normalized into the form same as those passed by the
caller *)
Definition receive_return_footprint (fpm: fp_map) (l: list path) (retv: footprint) (externs: list footprint) : res (footprint * fp_map) :=
  do retv1 <- recover_footprint_ref_paths l retv;
  do externs1 <- mmap (recover_footprint_ref_paths l) externs;
  let phs_externs := combine l externs1 in
  (* TODO: make get/set return res instead of option *)
  do fpm1 <- mfold_left (fun acc '(ph, fp) => match set_footprint_map ph fp acc with
                                         | Some acc1 => OK acc1
                                         | None => Error nil
                                         end) phs_externs fpm;
  OK (retv1, fpm1).
*) 

*)

End ADT_ENV.

Coercion fpm_to_env : fp_map >-> env.
