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
Require Import RustIRspec BorrowCheckInv.

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

(* AI-generated. *)
Lemma Forall_sep_eqv {A: Type}: forall (P: A -> massert -> Prop) l mass1 mass2,
    Forall_sep P l mass1 ->
    massert_eqv mass1 mass2 ->
    Forall_sep P l mass2.
Proof.
  intros P l mass1 mass2 SEP EQV.
  destruct SEP.
  - econstructor. etransitivity; eauto.
  - econstructor; eauto. etransitivity; eauto.
Qed.

(* AI-generated. *)
Lemma massert_eqv_STrue_l: forall P,
    massert_eqv P (STrue ** P).
Proof.
  intros. unfold STrue, spure.
  split.
  - red; split.
    + intros. eapply sep_pure; auto.
    + simpl. intros. destruct H; try contradiction; auto.
  - red; split.
    + intros. eapply sep_pure in H. destruct H; auto.
    + simpl. auto.
Qed.

(* AI-generated. *)
Lemma Forall_sep_app {A: Type} : forall (l1 l2: list A) P mass,
    Forall_sep P (l1 ++ l2) mass <-> 
      (exists mass1 mass2,
          Forall_sep P l1 mass1 /\ Forall_sep P l2 mass2
          /\ massert_eqv mass (mass1 ** mass2)).
Proof.
  induction l1 as [|x l1 IH]; intros l2 P mass; split.
  - intros SEP. simpl in SEP.
    exists STrue, mass. split.
    + econstructor. reflexivity.
    + split; [exact SEP|]. eapply massert_eqv_STrue_l.
  - intros (mass1 & mass2 & SEP1 & SEP2 & EQV). simpl.
    inversion SEP1 as [mass0 EMPTY|]; subst.
    eapply Forall_sep_eqv; [exact SEP2|].
    etransitivity.
    + eapply massert_eqv_STrue_l.
    + etransitivity.
      * eapply sepconj_morph_2; [exact EMPTY|reflexivity].
      * symmetry. exact EQV.
  - intros SEP. simpl in SEP.
    inversion SEP as [|x0 l0 head tail whole HEAD TAIL JOIN]; subst.
    destruct (proj1 (IH l2 P tail) TAIL)
      as (mass1 & mass2 & SEP1 & SEP2 & TAIL_EQV).
    exists (head ** mass1), mass2. split.
    + econstructor; eauto.
    + split; [exact SEP2|]. etransitivity.
      * symmetry. exact JOIN.
      * rewrite TAIL_EQV. rewrite <- sep_assoc. reflexivity.
  - intros (mass1 & mass2 & SEP1 & SEP2 & EQV). simpl.
    inversion SEP1 as [|x0 l0 head tail whole HEAD TAIL JOIN]; subst.
    econstructor; [exact HEAD| |].
    + eapply (proj2 (IH l2 P (tail ** mass2))).
      exists tail, mass2. split; [exact TAIL|].
      split; [exact SEP2|reflexivity].
    + etransitivity.
      * symmetry. eapply sep_assoc.
      * etransitivity.
        -- eapply sepconj_morph_2; [exact JOIN|reflexivity].
        -- symmetry. exact EQV.
Qed.

Fixpoint range_list (l: list (block * Z * Z)) : massert :=
  match l with
  | nil => STrue
  | (b, lo, hi) :: l1 =>
      range b lo hi ** range_list l1
  end.



(* Object support currently disabled.
I think this environment is a premise for the whole borrow checking
proof. When we want to use the borrow checking proof, we must provide
its instance.
Context {ame: adt_mem_env}.
Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
*)

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
| sem_wt_emp: forall sz al b ofs mp
(* We need fp_emp here as if we set some field of a struct to fp_emp
(e.g., by passing the location to callee via reference), we need to
say this location is still sem_wt_loc *)
    (EQV: massert_eqv mp STrue),
    sem_wt_loc (fp_emp sz al) b ofs mp
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
| sem_wt_box: forall b ofs fp b1 nextmp mp1
    (* (WTVAL: sem_wt_val (fp_box b1 sz1 fp) v mass), *)
    (* When this box pointer is not moved from (i.e., shallow_init is
    false), its point-to location is freeable and sem_wt_loc *)
    (* (EQV: massert_eqv mp (box_pred fp b1 nextmp)) *)
    (* (NEQ: b1 <> b) *)
    (* (BOXFP: forall b' ofs', m_footprint nextmp b' ofs' -> b' <> b) *)
    (WTLOC: sem_wt_loc fp b1 0 nextmp)
    (EQV: massert_eqv mp1 ((hasvalue Mptr b ofs (Vptr b1 Ptrofs.zero)) ** (box_pred fp b1 nextmp))),
    sem_wt_loc (fp_box b1 fp) b ofs mp1

| sem_wt_struct: forall b ofs fpl id mass mp padmp
    (FWT: fields_loc_sep b ofs sem_wt_loc fpl mass)
    (* (AL: (alignof_comp ce id | ofs)) *)
    (* The field region is described by [fields_loc_sep], and the
    trailing padding up to the aligned object size is described here. *)
    (PAD: padmp = range b (ofs + sizeof_struct_comp ce id) (ofs + sizeof_comp ce id))
    (EQV: massert_eqv mp (mass ** padmp ** (spure (alignof_comp ce id | ofs)))),
    sem_wt_loc (fp_struct id fpl) b ofs mp
| sem_wt_enum: forall fp b ofs tagz fid fofs id mass1 mass2 mp padmp tailpad
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: mass1 = hasvalue Mint32 b ofs (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc fp b (ofs + fofs) mass2)
    (* (AL: (alignof_comp ce id | ofs)) *)
    (* permission for the padding location before the variant field *)
    (ALPERM: padmp = range b (ofs + size_chunk Mint32) (ofs + fofs))
    (* permission for the trailing padding after the variant field *)
    (TAIL: tailpad = range b (ofs + fofs + sizeof_footprint ce fp) (ofs + sizeof_comp ce id))
    (EQV: massert_eqv mp (mass1 ** padmp ** mass2 ** tailpad ** (spure (alignof_comp ce id | ofs)))),
    sem_wt_loc (fp_enum id tagz fid fofs fp) b ofs mp
(* | sem_wt_object: forall id obj mp1 mp2 mp3 b ofs exposed
    (PRED: (ame id).(mem_pred) obj b ofs mp1)
    (EXPOSED: exposed_loc_sep sem_wt_loc exposed mp2)
    (EQV: massert_eqv (mp1 ** mp2) mp3),
    sem_wt_loc (fp_object id obj exposed) b ofs mp3 *)
.

(* The interpretation of footprint *)
Inductive sem_wt_fp : footprint -> massert -> Prop :=
| sem_fp_emp: forall sz al mp
    (EQV: massert_eqv mp (spure True)),
    sem_wt_fp (fp_emp sz al) mp
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


Inductive coherent_var (elt: (ident * (block * Z * type * footprint))) : massert -> Prop :=
| coherent_var_intro: forall id b ofs ty mass fp
    (ELTEQ: elt = (id, (b, ofs, ty, fp)))
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

(* Keep the map-to-environment conversion with the semantic definitions. *)
Coercion fpm_to_env : fp_map >-> env.

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

(* ** Dependencies shared by the assignment and byte-store proof chains *)

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
  - rewrite EQV, EQV0. 
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
Qed.

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


(* Properties of fields_sep *)

(* AI-generated. *)
Lemma fields_loc_sep_split: forall b ofs base fofs fid ffp l mass P,
    fields_loc_sep b ofs P l mass ->
    In (fid, ((base, fofs), ffp)) l ->
    exists mass1 mass2 mass3, 
      P ffp b (ofs + fofs) mass2 
      /\ massert_eqv mass (mass1 ** mass2 ** mass3).
  (* use Forall_sep properties to prove fields_sep properties *)
Proof.
  intros b ofs base fofs fid ffp l mass P SEP IN.
  induction SEP as
      [mp EMPTY
      |fid0 base0 fofs0 ffp0 l head tail pad whole
         TAIL IH HEAD PAD JOIN].
  - contradiction.
  - simpl in IN. destruct IN as [SAME|IN].
    + inv SAME.
      exists (range b (ofs + base) (ofs + fofs)), head, tail.
      split; [exact HEAD|exact JOIN].
    + destruct (IH IN) as (prefix & field & suffix & FIELD & SPLIT).
      exists (pad ** head ** prefix), field, suffix. split; auto.
      etransitivity.
      * exact JOIN.
      * rewrite SPLIT. rewrite ! sep_assoc. reflexivity.
Qed.

(* set a found field would update the massert predicate *)
(* AI-generated. *)
Lemma Forall_sep_find_set_field {A: Type}: forall mp (l: list (ident * A)) P id a f,
    find_field id l = Some a ->
    Forall_sep P l mp ->
    exists mp1 mp2 mpi l1 l2,
      Forall_sep P l1 mp1
      /\ Forall_sep P l2 mp2
      /\ P (id, a) mpi
      /\ l = l1 ++ (id, a) :: l2
      /\ massert_eqv mp (mp1 ** mpi ** mp2)
      (* Properties of setting a new footprint into id *)
      /\ (forall mpi', 
            P (id, (f a)) mpi' ->
            Forall_sep P (set_field id f l) (mp1 ** mpi' ** mp2)).
Proof.
  intros mp l P id a f FIND SEP.
  destruct (find_field_split _ _ _ _ FIND) as (l1 & l2 & LIST & FRESH).
  subst l.
  apply Forall_sep_app in SEP.
  destruct SEP as (mp1 & tail & SEP1 & SEPTAIL & WHOLE).
  inversion SEPTAIL as [|id_a l2' mpi mp2 tail' FIELD SEP2 TAIL]; subst.
  exists mp1, mp2, mpi, l1, l2. split; [exact SEP1|].
  split; [exact SEP2|]. split; [exact FIELD|]. split; [reflexivity|]. split.
  - etransitivity; [exact WHOLE|].
    eapply sepconj_morph_2; [reflexivity|]. symmetry. exact TAIL.
  - intros mpi' FIELD'. rewrite set_field_split by exact FRESH.
    eapply Forall_sep_app. exists mp1, (mpi' ** mp2). split; [exact SEP1|].
    split.
    + econstructor; [exact FIELD'|exact SEP2|reflexivity].
    + reflexivity.
Qed.

(* AI-generated. *)
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
  intros l fid P mp ffp b ofs base fofs FIND SEP.
  induction SEP as
      [mass EMPTY
      |fid0 base0 fofs0 ffp0 l head tail pad whole
         TAIL IH HEAD PAD JOIN].
  - unfold find_field in FIND. simpl in FIND. congruence.
  - rewrite find_field_cons in FIND.
    destruct (ident_eq fid fid0) as [SAME|OTHER].
    + subst fid0. inv FIND.
      exists STrue, tail, head, nil, l. split.
      * econstructor. reflexivity.
      * split; [exact TAIL|]. split; [exact HEAD|]. split; [reflexivity|].
        split.
        -- etransitivity; [exact JOIN|]. rewrite sep_assoc.
           eapply massert_eqv_STrue_l.
        -- intros ffp' mpi' FIELD.
           exists (STrue **
             ((range b (ofs + base) (ofs + fofs) ** mpi') ** tail)).
           split.
           ++ unfold set_field_fp. simpl.
              destruct (ident_eq fid fid); [|congruence].
              econstructor; [exact TAIL|exact FIELD|reflexivity|].
              etransitivity.
              ** symmetry. eapply massert_eqv_STrue_l.
              ** eapply sep_assoc.
           ++ reflexivity.
    + destruct (IH FIND) as
          (mp1 & mp2 & mpi & l1 & l2 & SEP1 & SEP2 & FIELD & LIST & SPLIT &
           UPDATE).
      subst l.
      exists (pad ** head ** mp1), mp2, mpi,
        ((fid0, ((base0, fofs0), ffp0)) :: l1), l2.
      split.
      * econstructor; [exact SEP1|exact HEAD|exact PAD|reflexivity].
      * split; [exact SEP2|]. split; [exact FIELD|]. split; [reflexivity|].
        split.
        -- etransitivity; [exact JOIN|]. rewrite SPLIT.
           rewrite ! sep_assoc. reflexivity.
        -- intros ffp' mpi' FIELD'.
           destruct (UPDATE ffp' mpi' FIELD') as (tail' & UPDATED & UPDATED_EQV).
           exists (pad ** head ** tail'). split.
           ++ unfold set_field_fp in *. simpl.
              destruct (ident_eq fid fid0); [congruence|].
              econstructor; [exact UPDATED|exact HEAD|exact PAD|reflexivity].
           ++ rewrite UPDATED_EQV. rewrite ! sep_assoc. reflexivity.
Qed.

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


(* AI-generated. *)
Lemma contains_range: forall chunk b ofs P,
    ofs + size_chunk chunk <= Ptrofs.modulus ->
    massert_imp (contains chunk b ofs P) (range b ofs (ofs + size_chunk chunk)).
Proof.
  intros chunk b ofs P BOUND. unfold massert_imp. split.
  - intros m CONTAINS. simpl in CONTAINS |- *.
    destruct CONTAINS as ((OFS_LO & OFS_HI) & ACCESS & VALUE).
    destruct ACCESS as (PERMS & ALIGN).
    split; [lia|]. split; [exact BOUND|].
    intros i k p IN_RANGE.
    eapply Mem.perm_implies with (p1 := Freeable).
    + eapply Mem.perm_cur. eapply PERMS. exact IN_RANGE.
    + constructor.
  - intros b' ofs' IN_RANGE. exact IN_RANGE.
Qed.

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

(* AI-generated. *)
Lemma store_range_rule: forall chunk m b ofs v (spec: val -> Prop) P,
    m |= range b ofs (ofs + size_chunk chunk) ** P ->
    (align_chunk chunk | ofs) ->
    spec (Val.load_result chunk v) ->
    exists m',
      Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
  intros chunk m b ofs v spec P RANGE ALIGN SPEC.
  eapply store_rule; [|exact SPEC].
  eapply range_contains; eauto.
Qed.

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


Lemma free_rule: forall chunk m b ofs (spec: Values.val -> Prop) P,
    m |= contains chunk b ofs spec ** P ->
    exists m', Mem.free m b ofs (ofs + size_chunk chunk) = Some m'
          /\ m' |= P.
Proof.
  intros until P. intros MP.
  edestruct Mem.range_perm_free as (m1 & FREE1).
  eapply MP. exists m1. split; auto.
  eapply m_invar. eapply MP.
  eapply Mem.free_unchanged_on. eauto.
  intros. intro.
  eapply MP; eauto.
  simpl. auto.
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

(* Along a non-empty path, [set_footprint] rebuilds the same outer
   constructor.  Consequently both the size used by [box_pred] and the
   composite layout surrounding a nested update are preserved. *)
Lemma set_footprint_sizeof_cons ce: forall pj phl vfp fp fp2,
    set_footprint (pj :: phl) vfp fp = OK fp2 ->
    sizeof_footprint ce fp = sizeof_footprint ce fp2.
Proof.
  intros pj phl vfp fp fp2 SET. simpl in SET.
  destruct pj; destruct fp; try congruence.
  - monadInv SET. reflexivity.
  - destruct (find_field fid fpl) as [[[base fofs] ffp]|]; try congruence.
    monadInv SET. reflexivity.
  - destruct (ident_eq fid fid0); try congruence.
    monadInv SET. reflexivity.
Qed.

Lemma set_footprint_sizeof_eq ce: forall phl vfp fp fp2 pfp b ofs b' ofs',
    get_owner_loc_footprint phl fp b ofs = OK (b', ofs', pfp) ->
    set_footprint phl vfp fp = OK fp2 ->
    sizeof_footprint ce pfp = sizeof_footprint ce vfp ->
    sizeof_footprint ce fp = sizeof_footprint ce fp2.
Proof.
  intros phl. destruct phl as [|pj phl].
  - simpl. intros. inv H. inv H0. exact H1.
  - intros. eapply set_footprint_sizeof_cons; eauto.
Qed.

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
  destruct ALLSEP as (mass11 & mass12 & D1 & D2 & D3).
  inv D2. inv H1. inv ELTEQ.
  exists l1, l2. exists mass11, mass2, mass1.
  do 4 (try apply conj); eauto.
  econstructor; eauto.
  etransitivity; [exact D3|].
  eapply sepconj_morph_2; [reflexivity|]. symmetry. exact H4.
Qed.

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
      (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = OK (b2, ofs2, fp2))
      (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mp),
    exists mp1 mp2 fp1',
      set_footprint phl
        (fp_emp (sizeof_footprint ce fp2) (alignof_footprint ce fp2)) fp1 = OK fp1'
      /\ sem_wt_loc ce fp1' b1 ofs1 mp1
      /\ sem_wt_loc ce fp2 b2 ofs2 mp2
      /\ massert_eqv mp (mp1 ** mp2)
      /\ (forall fp3 mp3,
            sizeof_footprint ce fp3 = sizeof_footprint ce fp2 ->
            sem_wt_loc ce fp3 b2 ofs2 mp3 ->
            exists mp' fp1'',
              set_footprint phl fp3 fp1 = OK fp1''
              /\ sem_wt_loc ce fp1'' b1 ofs1 mp'
              /\ massert_eqv mp' (mp1 ** mp3)).
Proof.
  induction phl as [|pj phl IH]; intros.
  - inv GFP.
    exists STrue, mp,
      (fp_emp (sizeof_footprint ce fp2) (alignof_footprint ce fp2)).
    split; [reflexivity|].
    split; [constructor; reflexivity|].
    split; [exact WTLOC|].
    split; [eapply massert_eqv_STrue_l|].
    intros fp3 mp3 _ WT3. exists mp3, fp3.
    split; [reflexivity|]. split; [exact WT3|].
    eapply massert_eqv_STrue_l.
  - simpl in GFP. destruct pj as [|fid|fid].
    + destruct fp1 as [esz eal | sz al | chunk v | hb inner | sid fpl
        | eid tag efid fofs inner | mut rb rofs ph vs]; try congruence.
      inv WTLOC.
      destruct (IH hb 0 b2 ofs2 inner fp2 nextmp GFP WTLOC0)
        as (inner_rest & target & inner_empty & SET_EMPTY & WT_EMPTY &
            WT_TARGET & INNER_SPLIT & PLUG).
      assert (SIZE_EMPTY:
        sizeof_footprint ce inner = sizeof_footprint ce inner_empty).
      { eapply set_footprint_sizeof_eq; eauto. }
      set (head := hasvalue Mptr b1 ofs1 (Vptr hb Ptrofs.zero)).
      set (outer_rest := head ** box_pred ce inner_empty hb inner_rest).
      exists outer_rest, target, (fp_box hb inner_empty).
      split.
      { simpl. rewrite SET_EMPTY. reflexivity. }
      split.
      { unfold outer_rest, head. econstructor; eauto. }
      split; [exact WT_TARGET|].
      split.
      { rewrite EQV. unfold outer_rest, head, box_pred.
        rewrite INNER_SPLIT.
        rewrite <- SIZE_EMPTY. rewrite !sep_assoc. reflexivity. }
      intros fp3 mp3 SIZE3 WT3.
      destruct (PLUG fp3 mp3 SIZE3 WT3)
        as (inner_mp & inner_new & SET_NEW & WT_NEW & INNER_EQV).
      assert (SIZE_NEW:
        sizeof_footprint ce inner = sizeof_footprint ce inner_new).
      { eapply set_footprint_sizeof_eq; eauto. }
      set (outer_mp := head ** box_pred ce inner_new hb inner_mp).
      exists outer_mp, (fp_box hb inner_new).
      split.
      { simpl. rewrite SET_NEW. reflexivity. }
      split.
      { unfold outer_mp, head. econstructor; eauto. }
      unfold outer_mp, outer_rest, head, box_pred.
      rewrite INNER_EQV. rewrite <- SIZE_NEW, <- SIZE_EMPTY.
      rewrite !sep_assoc. reflexivity.
    + destruct fp1 as [esz eal | sz al | chunk v | hb inner | sid fpl
        | eid tag efid efofs inner | mut rb rofs ph vs]; try congruence.
      destruct (find_field fid fpl) as [[[base fofs] fieldfp]|] eqn:FIND;
        try congruence.
      inv WTLOC.
      destruct (fields_loc_sep_find_set fpl fid (sem_wt_loc ce) mass
        fieldfp b1 ofs1 base fofs FIND FWT)
        as (prefix & suffix & field_mass & l1 & l2 & SEP1 & SEP2 &
            FIELD & LIST & FIELD_SPLIT & UPDATE).
      destruct (IH b1 (ofs1 + fofs) b2 ofs2 fieldfp fp2 field_mass GFP FIELD)
        as (field_rest & target & field_empty & SET_EMPTY & WT_EMPTY &
            WT_TARGET & INNER_SPLIT & PLUG).
      destruct (UPDATE field_empty field_rest WT_EMPTY)
        as (fields_empty_mass & FIELDS_EMPTY & EMPTY_EQV).
      set (outer_rest := fields_empty_mass **
        range b1 (ofs1 + sizeof_struct_comp ce sid) (ofs1 + sizeof_comp ce sid) **
        spure (alignof_comp ce sid | ofs1)).
      exists outer_rest, target,
        (fp_struct sid (set_field_fp fid field_empty fpl)).
      split.
      { simpl. rewrite FIND, SET_EMPTY. reflexivity. }
      split.
      { unfold outer_rest. econstructor; eauto. }
      split; [exact WT_TARGET|].
      split.
      { rewrite EQV, FIELD_SPLIT, INNER_SPLIT.
        unfold outer_rest. rewrite EMPTY_EQV.
        rewrite !sep_assoc.
        rewrite (sep_comm target
          (suffix **
           range b1 (ofs1 + sizeof_struct_comp ce sid)
             (ofs1 + sizeof_comp ce sid) **
           spure (alignof_comp ce sid | ofs1))).
        rewrite !sep_assoc. reflexivity. }
      intros fp3 mp3 SIZE3 WT3.
      destruct (PLUG fp3 mp3 SIZE3 WT3)
        as (field_mp & field_new & SET_NEW & WT_NEW & INNER_EQV).
      destruct (UPDATE field_new field_mp WT_NEW)
        as (fields_new_mass & FIELDS_NEW & NEW_EQV).
      set (outer_mp := fields_new_mass **
        range b1 (ofs1 + sizeof_struct_comp ce sid) (ofs1 + sizeof_comp ce sid) **
        spure (alignof_comp ce sid | ofs1)).
      exists outer_mp, (fp_struct sid (set_field_fp fid field_new fpl)).
      split.
      { simpl. rewrite FIND, SET_NEW. reflexivity. }
      split.
      { unfold outer_mp. econstructor; eauto. }
      unfold outer_mp, outer_rest.
      rewrite NEW_EQV, INNER_EQV, EMPTY_EQV.
      rewrite !sep_assoc.
      rewrite (sep_comm mp3
        (suffix **
         range b1 (ofs1 + sizeof_struct_comp ce sid)
           (ofs1 + sizeof_comp ce sid) **
         spure (alignof_comp ce sid | ofs1))).
      rewrite !sep_assoc. reflexivity.
    + destruct fp1 as [esz eal | sz al | chunk v | hb boxed | sid fpl
        | eid tag efid efofs inner | mut rb rofs ph vs]; try congruence.
      destruct (ident_eq fid efid) as [SAME|DIFF]; try congruence.
      subst efid. inv WTLOC.
      destruct (IH b1 (ofs1 + efofs) b2 ofs2 inner fp2 mass2 GFP FWT)
        as (inner_rest & target & inner_empty & SET_EMPTY & WT_EMPTY &
            WT_TARGET & INNER_SPLIT & PLUG).
      assert (SIZE_EMPTY:
        sizeof_footprint ce inner = sizeof_footprint ce inner_empty).
      { eapply set_footprint_sizeof_eq; eauto. }
      set (outer_rest :=
        hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag)) **
        range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs) **
        inner_rest **
        range b1 (ofs1 + efofs + sizeof_footprint ce inner)
          (ofs1 + sizeof_comp ce eid) **
        spure (alignof_comp ce eid | ofs1)).
      exists outer_rest, target,
        (fp_enum eid tag fid efofs inner_empty).
      split.
      { simpl. destruct (ident_eq fid fid); [rewrite SET_EMPTY; reflexivity|congruence]. }
      split.
      { unfold outer_rest.
        eapply (sem_wt_enum ce inner_empty b1 ofs1 tag fid efofs eid
          (hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag))) inner_rest
          (hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag)) **
           range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs) **
           inner_rest **
           range b1 (ofs1 + efofs + sizeof_footprint ce inner)
             (ofs1 + sizeof_comp ce eid) **
           spure (alignof_comp ce eid | ofs1))
          (range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs))
          (range b1 (ofs1 + efofs + sizeof_footprint ce inner)
             (ofs1 + sizeof_comp ce eid)));
          try reflexivity; eauto.
        rewrite <- SIZE_EMPTY. reflexivity. }
      split; [exact WT_TARGET|].
      split.
      { rewrite EQV, INNER_SPLIT. unfold outer_rest.
        rewrite !sep_assoc.
        rewrite (sep_comm target
          (range b1 (ofs1 + efofs + sizeof_footprint ce inner)
             (ofs1 + sizeof_comp ce eid) **
           spure (alignof_comp ce eid | ofs1))).
        rewrite !sep_assoc. reflexivity. }
      intros fp3 mp3 SIZE3 WT3.
      destruct (PLUG fp3 mp3 SIZE3 WT3)
        as (inner_mp & inner_new & SET_NEW & WT_NEW & INNER_EQV).
      assert (SIZE_NEW:
        sizeof_footprint ce inner = sizeof_footprint ce inner_new).
      { eapply set_footprint_sizeof_eq; eauto. }
      set (outer_mp :=
        hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag)) **
        range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs) **
        inner_mp **
        range b1 (ofs1 + efofs + sizeof_footprint ce inner)
          (ofs1 + sizeof_comp ce eid) **
        spure (alignof_comp ce eid | ofs1)).
      exists outer_mp, (fp_enum eid tag fid efofs inner_new).
      split.
      { simpl. destruct (ident_eq fid fid); [rewrite SET_NEW; reflexivity|congruence]. }
      split.
      { unfold outer_mp.
        eapply (sem_wt_enum ce inner_new b1 ofs1 tag fid efofs eid
          (hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag))) inner_mp
          (hasvalue Mint32 b1 ofs1 (Vint (Int.repr tag)) **
           range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs) **
           inner_mp **
           range b1 (ofs1 + efofs + sizeof_footprint ce inner)
             (ofs1 + sizeof_comp ce eid) **
           spure (alignof_comp ce eid | ofs1))
          (range b1 (ofs1 + size_chunk Mint32) (ofs1 + efofs))
          (range b1 (ofs1 + efofs + sizeof_footprint ce inner)
             (ofs1 + sizeof_comp ce eid)));
          try reflexivity; eauto.
        rewrite <- SIZE_NEW. reflexivity. }
      unfold outer_mp, outer_rest.
      rewrite INNER_EQV. rewrite !sep_assoc.
      rewrite (sep_comm mp3
        (range b1 (ofs1 + efofs + sizeof_footprint ce inner)
           (ofs1 + sizeof_comp ce eid) **
         spure (alignof_comp ce eid | ofs1))).
      rewrite !sep_assoc. reflexivity.
Qed.


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
  intros phl id b ofs fp mp fpm1 GFP COH.
  unfold get_owner_loc_footprint_map in GFP.
  destruct (fpm1 ! id) as [(((b1, ofs1), ty), fp1)|] eqn:GET;
    try discriminate.
  destruct (coherent_fpm_split ce id fpm1 mp fp1 b1 ofs1 ty GET COH)
    as (l1 & l2 & prefix & suffix & root_mass & SEP1 & SEP2 &
        ROOT & ELEMENTS & OUTER_SPLIT).
  inversion ROOT as
    [id0 b0 ofs0 ty0 root_mass0 fp0 ELTEQ ROOT_LOC]; subst.
  inv ELTEQ.
  destruct (get_owner_loc_footprint_sem_wt_split
    ce phl b0 ofs0 b ofs fp0 fp root_mass GFP ROOT_LOC)
    as (local_rest & target_mass & fp1' & SET_EMP & REST_LOC &
        TARGET_LOC & LOCAL_SPLIT & RE_SET).
  exists target_mass, (prefix ** local_rest ** suffix).
  split; [exact TARGET_LOC|].
  rewrite OUTER_SPLIT, LOCAL_SPLIT.
  rewrite !sep_assoc.
  rewrite (sep_comm target_mass suffix).
  reflexivity.
Qed.


(************* End of properties of get/set_footprint_map ******************  *)

(* Lemma wt_footprint_size_eq ce : forall ty fp fpm, *)
(*     wt_footprint ce fpm ty fp -> *)
(*     sizeof ce ty = sizeof_footprint ce fp. *)
(* Admitted. *)

(* Lemma wt_footprint_align_eq ce : forall ty fp fpm, *)
(*     wt_footprint ce fpm ty fp -> *)
(*     alignof ce ty = alignof_footprint ce fp. *)
(* Admitted. *)


Definition fp_match_chunk (fp: footprint) chunk : Prop :=
  match fp with
  | fp_uninit sz al =>
      sz = size_chunk chunk /\ al = align_chunk chunk
  | fp_scalar chunk1 _ =>
      chunk1 = chunk
  | fp_box _ _
  | fp_ref _ _ _ _ _ => chunk = Mptr
  | fp_emp _ _
  | fp_struct _ _
  | fp_enum _ _ _ _ _ => False
  (* | fp_object _ _ _ => False *)
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
  (R0: 0 <= base)
  (R1: base <= fofs)
  (R2: 0 <= fofs)
  (R3: fofs + sizeof_footprint ce ffp <= sz)
  (R4: (alignof_footprint ce ffp | fofs))
  (R5: f ffp),
    fp_field_in_range_aligned ce sz al f (fid, ((base, fofs), ffp)).

Inductive fp_field_in_range ce (sz: Z) (f: footprint -> Prop) : ffpty -> Prop :=
| fp_field_in_range_intro: forall fid base fofs ffp
  (R1: base <= fofs)
  (R2: 0 <= fofs)
  (R3: fofs + sizeof_footprint ce ffp <= sz)
  (R5: f ffp),
    fp_field_in_range ce sz f (fid, ((base, fofs), ffp)).

Inductive fields_after ce (d: Z) : list ffpty -> Prop :=
| fields_after_nil : fields_after ce d nil
| fields_after_cons : forall fid base fofs ffp l,
    base = d ->
    d <= fofs ->
    0 <= sizeof_footprint ce ffp ->
    fields_after ce (fofs + sizeof_footprint ce ffp) l ->
    fields_after ce d ((fid, ((base, fofs), ffp)) :: l).

Definition fields_sorted ce (l: list ffpty) : Prop := fields_after ce 0 l.

Lemma fp_field_in_range_aligned_impl ce: forall sz al f x,
    fp_field_in_range_aligned ce sz al f x ->
    fp_field_in_range ce sz f x.
Proof.
  intros sz al f x H. destruct x as [fid [[base fofs] ffp]]. inv H. econstructor; eauto.
Qed.

(* This property should be implied by wt_footprint: the field offset must
be in range and aligned *)

Inductive fields_fp_well_formed ce : footprint -> Prop :=
(* | fp_emp_wf: fields_fp_well_formed ce fp_emp *)
| fp_uninit_wf sz al: fields_fp_well_formed ce (fp_uninit sz al)
| fp_scalar_wf chunk v: fields_fp_well_formed ce (fp_scalar chunk v)
| fp_box_wf b fp: fields_fp_well_formed ce (fp_box b fp)
| fp_ref_wf mut b ofs phs vs: fields_fp_well_formed ce (fp_ref mut b ofs phs vs)
(* | fp_object_wf id obj exposed:
    fields_fp_well_formed ce (fp_object id obj exposed) *)
| fp_struct_wf: forall id fpl
     (* This property says that all fields are within the size of this
     footprint *)
    (FWF: Forall (fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce)) fpl)
    (* This property says that all the location of the field region can be
       captured by one of the fields.  The trailing padding between
       [sizeof_struct_comp ce id] and [sizeof_comp ce id] is handled by the
       interpretation of [fp_struct]. *)
    (COMPLETE: forall ofs, 0 <= ofs < sizeof_comp ce id ->
                      (exists fid base fofs ffp,
                         In (fid, ((base, fofs), ffp)) fpl
                         /\ base <= ofs < fofs + sizeof_footprint ce ffp)
                      \/ sizeof_struct_comp ce id <= ofs),
  fields_fp_well_formed ce (fp_struct id fpl)
| fp_enum_wf: forall id tagz fid fofs ffp
    (FWF: fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce) (fid, ((size_chunk Mint32, fofs), ffp)))
    (COMPLETE: fofs + sizeof_footprint ce ffp <= sizeof_comp ce id),
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

Lemma range_join: forall b a c d,
    massert_imp (range b a c ** range b c d) (range b a d).
Proof.
  intros b a c d. red. split.
  - intros m H. simpl in H |- *. destruct H as ((A1 & A2 & A3) & (B1 & B2 & B3) & DISJ).
    repeat split; [lia|lia|].
    intros i k p IN. destruct (Z.lt_ge_cases i c).
    + eapply A3; lia.
    + eapply B3; lia.
  - intros b' ofs' H. simpl in H |- *. destruct H as (EQ & LO & HI). subst.
    destruct (Z.lt_ge_cases ofs' c).
    + left. repeat split; auto; lia.
    + right. repeat split; auto; lia.
Qed.

Lemma range_impl: forall b lo hi lo' hi',
    lo <= lo' -> hi' <= hi ->
    massert_imp (range b lo hi) (range b lo' hi').
Proof.
  intros b lo hi lo' hi' H1 H2. red. split.
  - intros m H. simpl in H |- *. destruct H as (A & B & C).
    repeat split; [lia|lia|].
    intros i k p IN. eapply C; lia.
  - intros b' ofs' H. simpl in H |- *. destruct H as (EQ & LO & HI). subst.
    repeat split; auto; lia.
Qed.

Lemma range_empty_imp: forall (P : massert) b ofs,
    0 <= ofs -> ofs <= Ptrofs.max_unsigned ->
    massert_imp P (range b ofs ofs).
Proof.
  intros P b ofs H1 H2. red. split.
  - intros m H. simpl. repeat split; [lia | | intros; lia].
    unfold Ptrofs.max_unsigned in H2. unfold Ptrofs.modulus in H2. unfold Ptrofs.modulus. lia.
  - intros b' ofs' H. simpl in H. destruct H as (EQ & LO & HI). lia.
Qed.

Lemma range_from_units: forall (P : massert) b lo n,
    0 < n ->
    (forall i, 0 <= i < n ->
       massert_imp P (range b (lo + i) (lo + i + 1))) ->
    massert_imp P (range b lo (lo + n)).
Proof.
  intros P b lo n HN Hunit. red. split.
  - intros m Hm.
    assert (UB: lo + n <= Ptrofs.modulus).
    { destruct (Hunit (n - 1)) as [IM _]; [lia|].
      destruct (IM m Hm) as (A & B & C). lia. }
    assert (LB: 0 <= lo).
    { destruct (Hunit 0) as [IM _]; [lia|].
      destruct (IM m Hm) as (A & B & C). lia. }
    repeat split; [lia|lia|].
    intros i k p IN.
    assert (HI: 0 <= i - lo < n) by lia.
    destruct (Hunit (i - lo)) as [IM _]; auto.
    destruct (IM m Hm) as (A & B & C).
    eapply C; lia.
  - intros b' ofs' H. simpl in H.
    destruct H as (EQ & LO & HI). subst.
    destruct (Hunit (ofs' - lo)) as [_ FIN]; [lia|].
    apply FIN. simpl. repeat split; auto; lia.
Qed.

Lemma fields_loc_sep_range_perm ce: forall fpl b ofs mp1 mp2 mp id
    (IH: forall (fid : ident) (base fofs : Z) (ffp : footprint),
        In (fid, (base, fofs, ffp)) fpl ->
        forall mass : massert,
          sem_wt_loc ce ffp b (ofs + fofs) mass ->
            massert_imp mass (range b (ofs + fofs) (ofs + fofs + sizeof_footprint ce ffp)))
     (FWT: Forall
          (fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id)
             (fields_fp_well_formed ce)) fpl)
     (COMPLETE: forall ofs1 : Z,
             0 <= ofs1 < sizeof_comp ce id ->
             (exists (fid : ident) (base fofs : Z) (ffp : footprint),
               In (fid, (base, fofs, ffp)) fpl /\ base <= ofs1 < fofs + sizeof_footprint ce ffp)
             \/ massert_imp mp1 (range b (ofs + ofs1) (ofs + ofs1 + 1)))
     (RANGE: 0 <= ofs /\ ofs + sizeof_comp ce id <= Ptrofs.max_unsigned)
     (FSEP: fields_loc_sep b ofs (sem_wt_loc ce) fpl mp2)
     (EQV: massert_eqv mp (mp1 ** mp2)),
       massert_imp mp (range b ofs (ofs + sizeof_comp ce id)).
Proof.
  induction fpl; intros.
  - inv FSEP.
    assert (IMP: massert_imp mp mp1).
    { assert (EQV': massert_eqv mp mp1).
      { rewrite EQV. rewrite EQV0. symmetry. apply massert_eqv_pure_r. }
      destruct EQV' as [H _]. exact H. }
    assert (SIZEGEN: 0 <= sizeof_comp ce id).
    { unfold sizeof_comp. destruct (ce ! id) as [c|].
      - generalize (co_sizeof_pos c). lia.
      - lia. }
    destruct (Z.lt_ge_cases 0 (sizeof_comp ce id)).
    + eapply massert_imp_trans. exact IMP.
      eapply range_from_units; [lia|].
      intros i IN. destruct (COMPLETE i IN) as [BAD | IMPi].
      * destruct BAD as (fid0 & base0 & fofs0 & ffp0 & INNIL & _). inversion INNIL.
      * exact IMPi.
    + assert (SIZEEQ: sizeof_comp ce id = 0) by lia.
      eapply massert_imp_trans. exact IMP.
      rewrite SIZEEQ. rewrite Z.add_0_r.
      eapply range_empty_imp; lia.
  - inv FSEP. inv FWT.
    assert (IMP1: massert_imp mass1 (range b (ofs + fofs) (ofs + fofs + sizeof_footprint ce ffp))).
    { eapply IH.
      - simpl. left. reflexivity.
      - exact FWT0. }
    rewrite <- sep_assoc in EQV0.
    set (mp1' := range b (ofs + base) (ofs + fofs) ** mass1) in *.
    assert (MP1RANG: massert_imp mp1' (range b (ofs + base) (ofs + fofs + sizeof_footprint ce ffp))).
    { unfold mp1'.
      eapply massert_imp_trans.
      eapply sepconj_morph_1; [reflexivity | exact IMP1].
      eapply range_join. }
    eapply (IHfpl b ofs (mp1 ** mp1') mass2 mp id).
    { intros fid0 base0 fofs0 ffp0 IN0 mass0' WT0.
      eapply IH.
      - simpl. right. exact IN0.
      - exact WT0. }
    exact H2.
    { intros ofs1 IN. destruct (COMPLETE ofs1 IN) as [(fid1 & base1 & fofs1 & ffp1 & A1 & A2) | IMP3].
      - inversion A1 as [HE | TAIL]; subst.
        + inversion HE; subst. right.
          eapply massert_imp_trans.
          eapply massert_imp_proj2.
          eapply massert_imp_trans. eapply MP1RANG.
          eapply range_impl; lia.
        + left. exists fid1, base1, fofs1, ffp1. split; auto.
      - right.
        eapply massert_imp_trans. eapply massert_imp_proj1. exact IMP3. }
    exact RANGE.
    exact IND.
    { rewrite EQV. rewrite EQV0. unfold mp1'. symmetry. apply sep_assoc. }
Qed.


Lemma wt_footprint_size_eq ce: forall ty fp fpm,
    wt_footprint ce fpm ty fp ->
    sizeof ce ty = sizeof_footprint ce fp.
Proof.
  intros ty fp fpm H. inv H; simpl.
  - reflexivity.
  - symmetry. eapply sizeof_by_value; eauto.
  - unfold sizeof_comp. rewrite CO. reflexivity.
  - unfold sizeof_comp. rewrite CO. reflexivity.
  - unfold Mptr; destruct Archi.ptr64; reflexivity.
  - unfold Mptr; destruct Archi.ptr64; reflexivity.
  - unfold Mptr; destruct Archi.ptr64; reflexivity.
Qed.

Lemma fp_match_field_In_wt:
  forall (ce: composite_env) (co: composite) (P: type -> footprint -> Prop) fpl mbs fid base fofs ffp,
    Forall2 (fp_match_field ce co P) fpl mbs ->
    In (fid, (base, fofs, ffp)) fpl ->
    exists fty, P fty ffp.
Proof.
  intros ce co P fpl mbs. revert mbs. induction fpl as [|a l IH]; intros mbs fid base fofs ffp MATCH IN.
  - inversion IN.
  - destruct mbs as [|m ms]; inv MATCH.
    destruct a as [fid1 [[base1 fofs1] ffp1]].
    simpl in IN. destruct IN as [SAME|IN].
    + inv SAME. inv H2. eexists; eauto.
    + exact (IH ms fid base fofs ffp H4 IN).
Qed.

(* Extract the chunk-alignment fact embedded in [hasvalue] (via
   [contains]'s [Mem.valid_access] component). *)
Lemma hasvalue_align: forall m chunk b ofs v,
    m |= hasvalue chunk b ofs v ->
    (align_chunk chunk | ofs).
Proof.
  intros m chunk b ofs v MPRED.
  destruct MPRED as (_ & VA & _). exact (proj2 VA).
Qed.

Lemma sem_wt_loc_align ce: forall fp b ofs mass m ty fpm
    (WTLOC: sem_wt_loc ce fp b ofs mass)
    (MPRED: m |= mass)
    (WTFP: wt_footprint ce fpm ty fp),
    (* (FPMAT: fp_match_chunk fp chunk), *)
    (alignof_footprint ce fp | ofs).
Proof.
  intros.
  destruct fp; inv WTLOC; simpl.
  (* fp_emp: ruled out, wt_footprint has no constructor for it *)
  - inv WTFP.
  (* fp_uninit: the alignment is carried by the [spure] conjunct *)
  - rewrite EQV in MPRED. eapply sep_proj2 in MPRED. exact MPRED.
  (* fp_scalar *)
  - rewrite EQV in MPRED. eapply hasvalue_align; eauto.
  (* fp_box: alignment of the stored pointer *)
  - rewrite EQV in MPRED. eapply sep_proj1 in MPRED.
    eapply hasvalue_align; eauto.
  (* fp_struct: [spure (alignof_comp ce id | ofs)] is the last conjunct *)
  - rewrite EQV in MPRED.
    eapply sep_proj2 in MPRED. eapply sep_proj2 in MPRED. exact MPRED.
  (* fp_enum: [spure (alignof_comp ce id | ofs)] is the last conjunct *)
  - rewrite EQV in MPRED.
    eapply sep_proj2 in MPRED. eapply sep_proj2 in MPRED.
    eapply sep_proj2 in MPRED. eapply sep_proj2 in MPRED. exact MPRED.
  (* fp_ref: alignment of the stored pointer *)
  - rewrite EQV in MPRED. eapply hasvalue_align; eauto.
Qed.

(* [BYVAL] restricts [fp] to the four by-value shapes: [fp_uninit]
   supplies the permissions through its [range] conjunct, while
   [fp_scalar]/[fp_box]/[fp_ref] supply a full [Mem.valid_access _ _ _ _
   Freeable] through [hasvalue] (= [contains]), which weakens to any
   permission by [perm_F_any]. [fp_struct]/[fp_enum] are [By_copy] and
   [fp_emp] has no [wt_footprint] constructor, so all three are
   discharged. Note this needs neither [sem_wt_loc_range_perm] nor its
   [composite_env_consistent]/range side conditions. *)
Lemma sem_wt_loc_valid_access ce: forall fp b ofs mass m p chunk ty fpm
    (WTLOC: sem_wt_loc ce fp b ofs mass)
    (MPRED: m |= mass)
    (WTFP: wt_footprint ce fpm ty fp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk),
    (* (FPMAT: fp_match_chunk fp chunk), *)
    Mem.valid_access m chunk b ofs p.
Proof.
  intros.
  destruct fp; inv WTLOC.
  (* fp_emp: no wt_footprint constructor *)
  - inv WTFP.
  (* fp_uninit: permissions from [range]; the recorded alignment is
  [alignof ce ty], which the chunk's alignment divides. *)
  - inv WTFP. rewrite EQV in MPRED.
    destruct MPRED as (RNG & ALIGN & _).
    destruct RNG as (_ & _ & PERM).
    split.
    + red. intros ofs0 RANGE0.
      eapply PERM. erewrite <- (sizeof_by_value ce ty chunk BYVAL). exact RANGE0.
    + eapply Z.divide_trans.
      eapply alignof_by_value; eauto. exact ALIGN.
  (* fp_scalar *)
  - inv WTFP.
    assert (CHUNK: chunk0 = chunk) by congruence. subst chunk0.
    rewrite EQV in MPRED.
    destruct MPRED as (_ & VA & _).
    eapply Mem.valid_access_implies. exact VA. constructor.
  (* fp_box: chunk is Mptr; the pointer cell is the first conjunct.
  [inv WTFP] must precede [inv BYVAL]: only then is [ty] known to be
  [Tbox _], which forces [chunk = Mptr]. *)
  - inv WTFP. simpl in BYVAL. inv BYVAL.
    rewrite EQV in MPRED.
    destruct MPRED as (HV & _ & _).
    destruct HV as (_ & VA & _).
    eapply Mem.valid_access_implies. exact VA. constructor.
  (* fp_struct: By_copy, contradiction *)
  - inv WTFP. simpl in BYVAL. congruence.
  (* fp_enum: By_copy, contradiction *)
  - inv WTFP. simpl in BYVAL. congruence.
  (* fp_ref: chunk is Mptr (both wt_fp_ref_some and wt_fp_ref_none) *)
  - inv WTFP; simpl in BYVAL; inv BYVAL;
      rewrite EQV in MPRED;
      destruct MPRED as (_ & VA & _);
      eapply Mem.valid_access_implies; [exact VA | constructor | exact VA | constructor].
Qed.

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
  destruct fp as [esz eal | sz al | chunk0 v0 | pb fp0 | id fpl
                 | id tagz fid fofs fp0 | mut rb rofs rph rvs];
    inv WTVAL; inv WTFP.
  (* fp_scalar: the value spec recorded in the footprint is exactly the
  loaded result of the stored value. *)
  - assert (CHUNK: chunk0 = chunk) by congruence. subst chunk0.
    inv MP0.
    eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result chunk v)) (v:= v) in MPRED; auto.
    destruct MPRED as (m2 & STORE & MPRED).
    exists m2, (hasvalue chunk b ofs (Val.load_result chunk v)). split; auto.
    split.
    econstructor. reflexivity.
    rewrite sep_swap in MPRED. eapply sep_proj2 in MPRED.
    auto.
  (* fp_box: the pointer is stored in (b, ofs) and the ownership of the
  pointed-to block is carried over unchanged from sem_wt_fp. *)
  - simpl in BYVAL. inv BYVAL.
    inv MP0. rewrite EQV in MPRED.
    eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result Mptr (Vptr pb Ptrofs.zero))) (v:= Vptr pb Ptrofs.zero) in MPRED; auto.
    destruct MPRED as (m2 & STORE & MPRED).
    replace (Val.load_result Mptr (Vptr pb Ptrofs.zero)) with (Vptr pb Ptrofs.zero) in * by auto.
    exists m2, (hasvalue Mptr b ofs (Vptr pb Ptrofs.zero) ** box_pred ce fp0 pb nextmp).
    split; auto.
    split.
    econstructor. eauto. reflexivity.
    rewrite sep_assoc. auto.
  (* fp_ref with Some path: storing a reference only records the
  pointer value; sem_wt_fp of a reference owns nothing. *)
  - simpl in BYVAL. inv BYVAL.
    inv MP0.
    eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result Mptr (Vptr rb (Ptrofs.repr rofs)))) (v:= Vptr rb (Ptrofs.repr rofs)) in MPRED; auto.
    destruct MPRED as (m2 & STORE & MPRED).
    replace (Val.load_result Mptr (Vptr rb (Ptrofs.repr rofs))) with (Vptr rb (Ptrofs.repr rofs)) in * by auto.
    exists m2, (hasvalue Mptr b ofs (Vptr rb (Ptrofs.repr rofs))). split; auto.
    split.
    econstructor. reflexivity.
    rewrite sep_swap in MPRED. eapply sep_proj2 in MPRED.
    auto.
  (* fp_ref with None: same as the previous case. *)
  - simpl in BYVAL. inv BYVAL.
    inv MP0.
    eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result Mptr (Vptr rb (Ptrofs.repr rofs)))) (v:= Vptr rb (Ptrofs.repr rofs)) in MPRED; auto.
    destruct MPRED as (m2 & STORE & MPRED).
    replace (Val.load_result Mptr (Vptr rb (Ptrofs.repr rofs))) with (Vptr rb (Ptrofs.repr rofs)) in * by auto.
    exists m2, (hasvalue Mptr b ofs (Vptr rb (Ptrofs.repr rofs))). split; auto.
    split.
    econstructor. reflexivity.
    rewrite sep_swap in MPRED. eapply sep_proj2 in MPRED.
    auto.
Qed.

(* Moved up from later in the file: these are needed by
   [sem_wt_loc_range_perm] below, which in turn feeds the store
   chain ([store_sem_wt_loc] -> [store_coherent_var] -> ...). *)

Lemma wt_footprint_align_divides ce:
  forall ty fp fpm,
    wt_footprint ce fpm ty fp ->
    (alignof_footprint ce fp | alignof ce ty).
Proof.
  intros ty fp fpm H. inv H; simpl.
  - apply Z.divide_refl.
  - apply alignof_by_value; eauto.
  - unfold alignof_comp. rewrite CO. apply Z.divide_refl.
  - unfold alignof_comp. rewrite CO. apply Z.divide_refl.
  - apply Z.divide_refl.
  - apply Z.divide_refl.
  - apply Z.divide_refl.
Qed.

Lemma field_noalign_offset_rec_base_nonneg:
  forall ce fid ms pos base fofs,
    field_noalign_offset_rec ce fid ms pos = OK (base, fofs) ->
    0 <= pos ->
    0 <= base.
Proof.
  induction ms as [| m ms IH]; intros; simpl in *.
  - discriminate.
  - destruct m as [id ty].
    change (name_member (Member_plain id ty)) with id in *.
    destruct (ident_eq fid id) eqn:ID.
    + destruct (layout_field ce pos (Member_plain id ty)) eqn:L; try discriminate.
      inv H. apply Z.div_pos; [exact H0 | lia].
    + apply (IH (next_field ce pos (Member_plain id ty)) base fofs H).
      apply Z.le_trans with pos; [exact H0 | apply (next_field_incr ce pos (Member_plain id ty))].
Qed.

Lemma field_noalign_offset_base_nonneg ce: forall fid ms base fofs,
    field_noalign_offset ce fid ms = OK (base, fofs) ->
    0 <= base.
Proof.
  unfold field_noalign_offset. intros. eapply field_noalign_offset_rec_base_nonneg; eauto. lia.
Qed.


Lemma Forall2_nth:
  forall A B (P: A -> B -> Prop) l l' n x,
    Forall2 P l l' -> nth_error l n = Some x ->
    exists y, nth_error l' n = Some y /\ P x y.
Proof.
  intros A B P l. induction l as [|a l IH]; intros l' n x F NTH; inv F; simpl in *.
  - destruct n; simpl in NTH; discriminate.
  - destruct n as [|n']; simpl in NTH.
    + inv NTH. eexists; split; [simpl; reflexivity | eauto].
    + destruct (IH _ _ _ H3 NTH) as (y0 & NTHY & PY). eexists; split; [simpl; exact NTHY | exact PY].
Qed.



Definition bytes_of_bits_local (n: Z) : Z := (n + 7) / 8.

Definition size_from (ce: composite_env) (pos: Z) (ms: members) : Z :=
  bytes_of_bits_local (bitsizeof_struct ce pos ms).




Lemma Forall2_nth_r:
  forall A B (P: A -> B -> Prop) l l' n y,
    Forall2 P l l' -> nth_error l' n = Some y ->
    exists x, nth_error l n = Some x /\ P x y.
Proof.
  intros A B P l. induction l as [|a l IH]; intros l' n y F NTH; inv F; simpl in *.
  - destruct n; simpl in NTH; discriminate.
  - destruct n as [|n']; simpl in NTH.
    + inv NTH. eexists; split; [simpl; reflexivity | eauto].
    + destruct (IH _ _ _ H3 NTH) as (x & NTHX & PX). eexists; split; [simpl; exact NTHX | exact PX].
Qed.

Lemma Forall2_member_fp:
  forall ce co P fpl fid base fofs fty,
    Forall2 (fp_match_field ce co P) fpl (co_members co) ->
    field_noalign_offset ce fid (co_members co) = OK (base, fofs) ->
    In (Member_plain fid fty) (co_members co) ->
    exists ffp, In (fid, ((base, fofs), ffp)) fpl /\ P fty ffp.
Proof.
  intros ce co P fpl fid base fofs fty MATCH FOFS IN.
  apply In_nth_error in IN as (n & NTH).
  destruct (Forall2_nth_r ffpty member (fp_match_field ce co P) fpl (co_members co) n (Member_plain fid fty) MATCH NTH) as (fp & NTHF & MATCH1).
  inv MATCH1.
  rewrite FOFS in FOFS0. inv FOFS0.
  apply nth_error_In in NTHF. eexists; split; eauto.
Qed.


Lemma type_eq_alignof_eq ce:
  forall ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    alignof ce ty1 = alignof ce ty2.
Proof.
  intros ty1 ty2 TEQ; induction ty1; destruct ty2; simpl in TEQ; try congruence.
  all: try eapply proj_sumbool_true in TEQ; inv TEQ.
  all: try reflexivity.
Qed.

Lemma next_field_div:
  forall ce pos m fofs,
    layout_field ce pos m = OK fofs ->
    next_field ce pos m / 8 = fofs + sizeof ce (type_member m).
Proof.
  intros ce pos m fofs L. destruct m as [id ty].
  unfold layout_field, next_field in *. inv L.
  assert (DIVAL: Z.divide 8 (align pos (bitalignof ce ty))).
  { apply Z.divide_trans with (bitalignof ce ty).
    - unfold bitalignof. exists (alignof ce ty). rewrite Z.mul_comm. reflexivity.
    - apply align_divides. unfold bitalignof. generalize (alignof_pos ce ty); lia. }
  assert (ALIGN_EQ: align pos (bitalignof ce ty) = 8 * (align pos (bitalignof ce ty) / 8)).
  { apply Z_div_exact_full_2; [lia |].
    apply Z.mod_divide; [lia | exact DIVAL]. }
  rewrite ALIGN_EQ.
  rewrite Z.mul_comm.
  rewrite (Z_div_plus_full_l (align pos (bitalignof ce ty) / 8) 8 (bitsizeof ce ty)) by lia.
  rewrite (Z.div_mul (align pos (bitalignof ce ty) / 8) 8) by lia.
  unfold bitsizeof. rewrite (Z.div_mul (sizeof ce ty) 8) by lia.
  simpl. lia.
Qed.

Lemma next_field_div8:
  forall ce pos m,
    Z.divide 8 (next_field ce pos m).
Proof.
  destruct m as [id ty]. unfold next_field.
  apply Z.divide_add_r.
  - apply Z.divide_trans with (bitalignof ce ty).
    + unfold bitalignof. exists (alignof ce ty). rewrite Z.mul_comm. reflexivity.
    + apply align_divides. unfold bitalignof. generalize (alignof_pos ce ty); lia.
  - unfold bitsizeof. exists (sizeof ce ty). lia.
Qed.

Lemma size_from_0:
  forall ce ms, size_from ce 0 ms = sizeof_struct ce ms.
Proof.
  intros. unfold size_from, sizeof_struct, bytes_of_bits_local. reflexivity.
Qed.

Lemma field_noalign_offset_rec_cover:
  forall ce ms pos ofs,
    list_norepet (name_members ms) ->
    (8 | pos) ->
    pos / 8 <= ofs ->
    ofs < size_from ce pos ms ->
    exists fid base fofs fty,
      In (Member_plain fid fty) ms /\
      field_noalign_offset_rec ce fid ms pos = OK (base, fofs) /\
      base <= ofs < fofs + sizeof ce fty.
Proof.
  induction ms as [|m ms IH]; intros; simpl in *.
  - exfalso.
    unfold size_from, bytes_of_bits_local in H2.
    simpl in H2.
    assert (SZ: (pos + 7) / 8 = pos / 8).
    { destruct H0 as [n HN]. subst pos.
      rewrite (Z_div_plus_full_l n 8 7) by lia.
      rewrite (Z.div_small 7 8) by lia.
      rewrite (Z.div_mul n 8) by lia. lia. }
    rewrite SZ in H2. lia.
  - destruct m as [id ty].
    change (name_member (Member_plain id ty)) with id in *.
    inversion H as [| ? ? NOREP_HEAD NOREP_TAIL]; subst.
    destruct (layout_field ce pos (Member_plain id ty)) as [z|] eqn:L; try discriminate.
    assert (HEAD: field_noalign_offset_rec ce id (Member_plain id ty :: ms) pos = OK (pos / 8, z)).
    { unfold field_noalign_offset_rec.
      change (name_member (Member_plain id ty)) with id.
      destruct (ident_eq id id) eqn:E; try congruence.
      rewrite L. reflexivity. }
    destruct (Z.lt_ge_cases ofs (z + sizeof ce ty)) as [LT | GE].
    + exists id, (pos / 8), z, ty.
      split; [simpl; auto | split; [destruct (ident_eq id id) eqn:E; try congruence; simpl; reflexivity | split; [exact H1 | exact LT]]].
    + assert (DIVPOS: Z.divide 8 (next_field ce pos (Member_plain id ty))).
      { apply next_field_div8. }
      assert (POSLE: next_field ce pos (Member_plain id ty) / 8 <= ofs).
      { rewrite (next_field_div ce pos (Member_plain id ty) z L).
        change (type_member (Member_plain id ty)) with ty.
        lia. }
      assert (SIZEFROM: size_from ce pos (Member_plain id ty :: ms) =
                        size_from ce (next_field ce pos (Member_plain id ty)) ms).
      { reflexivity. }
      rewrite SIZEFROM in H2.
      destruct (IH (next_field ce pos (Member_plain id ty)) ofs NOREP_TAIL DIVPOS POSLE H2)
        as (fid & base & fofs & fty & IN0 & REC0 & COV0).
      exists fid, base, fofs, fty. split; [right; exact IN0 | split].
      * simpl. destruct (ident_eq fid id) eqn:E.
        -- subst fid. exfalso. apply NOREP_HEAD. unfold name_members.
           rewrite in_map_iff. exists (Member_plain id fty). split; auto.
        -- exact REC0.
      * exact COV0.
Qed.

Lemma members_cover_struct:
  forall ce ms ofs,
    list_norepet (name_members ms) ->
    0 <= ofs < sizeof_struct ce ms ->
    exists fid base fofs fty,
      In (Member_plain fid fty) ms /\
      field_noalign_offset ce fid ms = OK (base, fofs) /\
      base <= ofs < fofs + sizeof ce fty.
Proof.
  intros ce ms ofs NOREP IN.
  unfold field_noalign_offset.
  eapply field_noalign_offset_rec_cover; eauto.
  - apply Z.divide_0_r.
  - rewrite (Z.div_0_l 8) by lia. lia.
  - rewrite size_from_0. exact (proj2 IN).
Qed.


Lemma wt_footprint_fields_well_formed ce te:
  forall ty fp,
    composite_env_consistent ce ->
    (forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co))) ->
    wt_footprint ce te ty fp ->
    fields_fp_well_formed ce fp.
Proof.
  intros ty fp CONS NOREP.
  revert ty.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros ty WTFP.
  - inv WTFP.
  - inv WTFP. econstructor.
  - inv WTFP. econstructor.
  - inv WTFP. econstructor; eauto.
  - inv WTFP. econstructor.
    + apply Forall_forall. intros x IN. destruct x as [fid [[base fofs] ffp]].
      apply In_nth_error in IN as (n & NTHF).
      destruct (Forall2_nth ffpty member (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) n (fid, ((base, fofs), ffp)) MATCH NTHF) as (m & NTHM & MATCH1).
      inv MATCH1.
      apply nth_error_In in NTHM as INM.
      apply nth_error_In in NTHF as INFP.
      assert (NOREPM: list_norepet (name_members (co_members co))) by (apply (NOREP id co CO)).
      assert (FTY: field_type fid (co_members co) = OK fty).
      { eapply field_noalign_offset_In_field_type.
        - exact NOREPM.
        - exact INM.
        - exact FOFS. }
      pose proof (field_noalign_offset_range_aligned ce fid (co_members co) base fofs fty FOFS FTY) as RANGE.
      pose proof (wt_footprint_size_eq ce fty ffp te WTFP) as SIZEEQ.
      pose proof (wt_footprint_align_divides ce fty ffp te WTFP) as ALIGNDIV.
      pose proof (IHfields fid base fofs ffp INFP fty WTFP) as WF.
      destruct RANGE as (BASELE & ZR & RANGESZ & ALIGN).
      assert (RANGECO: fofs + sizeof_footprint ce ffp <= sizeof_comp ce id).
      { rewrite <- SIZEEQ.
        destruct (CONS id co CO) as [COMPL ALG SZ RANK].
        unfold sizeof_comp. rewrite CO. rewrite SZ.
        rewrite STRUCT. simpl.
        apply Z.le_trans with (sizeof_struct ce (co_members co)); [exact RANGESZ |].
        apply align_le. apply co_alignof_pos. }
      assert (BASE0 : 0 <= base) by (eapply field_noalign_offset_base_nonneg; eauto).
      apply fp_field_in_range_aligned_intro; auto.
      * apply Z.divide_trans with (alignof ce fty); auto.
    + intros ofs IN.
      assert (SZSTR: sizeof_struct_comp ce id = sizeof_struct ce (co_members co)).
      { unfold sizeof_struct_comp. rewrite CO. rewrite STRUCT. reflexivity. }
      destruct (Z.lt_ge_cases ofs (sizeof_struct_comp ce id)) as [LT | GE].
      * left.
        assert (INM: 0 <= ofs < sizeof_struct ce (co_members co)).
        { destruct IN as [LO HI]. rewrite SZSTR in LT. split; auto. }
        destruct (members_cover_struct ce (co_members co) ofs (NOREP id co CO) INM) as (fid0 & base0 & fofs0 & fty0 & INM0 & FOFS0 & COV0).
        destruct (Forall2_member_fp ce co (wt_footprint ce te) fpl fid0 base0 fofs0 fty0 MATCH FOFS0 INM0) as (ffp0 & INFP0 & WTFP0').
        exists fid0, base0, fofs0, ffp0. split; auto.
        pose proof (wt_footprint_size_eq ce fty0 ffp0 te WTFP0') as SIZEEQ0.
        rewrite <- SIZEEQ0. exact COV0.
      * right. exact GE.
  - inv WTFP.
    pose proof (IHenum fty WT) as WFENUM.
    assert (SZM: size_chunk Mint32 = 4) by reflexivity.
    destruct (place_field_type_res co fid orgs fty FTY) as (fty' & FTY' & TEQ).
    pose proof (variant_field_offset_in_range ce (co_members co) fid fofs fty' FOFS FTY') as RANGEV.
    pose proof (variant_field_offset_aligned ce fid (co_members co) fofs fty' FOFS FTY') as ALIGNV.
    pose proof (wt_footprint_size_eq ce fty fp1 te WT) as SIZEEQF.
    pose proof (wt_footprint_align_divides ce fty fp1 te WT) as ALIGNDIVF.
    pose proof (type_eq_sizeof_eq fty fty' ce TEQ) as SIZEEQTY.
    pose proof (type_eq_alignof_eq ce fty fty' TEQ) as ALIGNEQTY.
    econstructor.
    + apply fp_field_in_range_aligned_intro.
      * rewrite SZM. lia.
      * rewrite SZM. destruct RANGEV as [A _]. exact A.
      * destruct RANGEV as [A _]. lia.
      * rewrite <- SIZEEQF. rewrite SIZEEQTY.
        destruct RANGEV as [_ B].
        destruct (CONS id co CO) as [COMPL ALG SZ RANK].
        unfold sizeof_comp. rewrite CO. rewrite SZ. rewrite ENUM. simpl.
        apply Z.le_trans with (sizeof_variant ce (co_members co)); [exact B |].
        apply align_le. apply co_alignof_pos.
      * rewrite ALIGNEQTY in ALIGNDIVF.
        apply Z.divide_trans with (alignof ce fty'); [exact ALIGNDIVF | exact ALIGNV].
      * exact WFENUM.
    + rewrite <- SIZEEQF. rewrite SIZEEQTY.
      destruct RANGEV as [_ B].
      destruct (CONS id co CO) as [COMPL ALG SZ RANK].
      unfold sizeof_comp. rewrite CO. rewrite SZ. rewrite ENUM. simpl.
      apply Z.le_trans with (sizeof_variant ce (co_members co)); [exact B |].
      apply align_le. apply co_alignof_pos.
  - inv WTFP; econstructor.
Qed.

Lemma sem_wt_loc_range_perm ce: forall fp mass b ofs ty fpm
      (CONS: composite_env_consistent ce)
      (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
      (WTFP: wt_footprint ce fpm ty fp)
      (RANGE: 0 <= ofs /\ ofs + sizeof ce ty <= Ptrofs.max_unsigned)
      (WTLOC: sem_wt_loc ce fp b ofs mass),
    massert_imp mass (range b ofs (ofs + sizeof ce ty)).
Proof.
  intros fp mass b ofs ty fpm CONS NOREP WTFP RANGE WTLOC.
  revert mass b ofs ty fpm WTFP RANGE WTLOC.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros mass b ofs ty fpm WTFP RANGE WTLOC; inv WTLOC.
  - inv WTFP.
  - rewrite EQV. inv WTFP. eapply massert_imp_proj1.
  - rewrite EQV. inv WTFP.
    eapply massert_imp_trans.
    { eapply contains_range.
      destruct RANGE as [A B].
      rewrite <- (sizeof_by_value ce ty chunk MODE) in B.
      unfold Ptrofs.max_unsigned in B. unfold Ptrofs.modulus in B. unfold Ptrofs.modulus. lia. }
    { rewrite (sizeof_by_value ce ty chunk MODE). reflexivity. }
  - rewrite EQV. inv WTFP.
    eapply massert_imp_trans.
    { eapply massert_imp_proj1. }
    { eapply massert_imp_trans.
      { eapply contains_range.
        assert (MODE: access_mode (Tbox ty0) = Ctypes.By_value Mptr) by reflexivity.
        destruct RANGE as [A B].
        rewrite <- (sizeof_by_value ce (Tbox ty0) Mptr MODE) in B.
        unfold Ptrofs.max_unsigned in B. unfold Ptrofs.modulus in B. unfold Ptrofs.modulus. lia. }
      { assert (MODE: access_mode (Tbox ty0) = Ctypes.By_value Mptr) by reflexivity.
        rewrite (sizeof_by_value ce (Tbox ty0) Mptr MODE). reflexivity. } }
  - assert (FPWF: fields_fp_well_formed ce (fp_struct id fpl)) by (eapply wt_footprint_fields_well_formed; eauto).
    inv WTFP. inv FPWF.
    assert (SIZEEQ_STRUCT: sizeof ce (Tstruct orgs id) = sizeof_comp ce id).
    { unfold sizeof, sizeof_comp. rewrite CO. reflexivity. }
    rewrite SIZEEQ_STRUCT in *.
    set (tail := range b (ofs + sizeof_struct_comp ce id) (ofs + sizeof_comp ce id)) in *.
    eapply fields_loc_sep_range_perm with (mp1 := tail ** spure (alignof_comp ce id | ofs)) (mp2 := mass0) (mp := mass).
    { intros fid0 base0 fofs0 ffp0 IN0 mass0' WT0.
      destruct (fp_match_field_In_wt ce co (wt_footprint ce fpm) fpl (co_members co) fid0 base0 fofs0 ffp0 MATCH IN0) as [fty WTFP0].
      assert (SIZEEQ_F: sizeof ce fty = sizeof_footprint ce ffp0) by (eapply wt_footprint_size_eq; eauto).
      eapply Forall_forall in FWF; eauto.
      inv FWF.
      assert (RANGEF: 0 <= ofs + fofs0 /\ (ofs + fofs0) + sizeof ce fty <= Ptrofs.max_unsigned).
      { destruct RANGE as [A B]. split.
        - lia.
        - rewrite SIZEEQ_F. lia. }
      pose proof (IHfields fid0 base0 fofs0 ffp0 IN0 mass0' b (ofs + fofs0) fty fpm WTFP0 RANGEF WT0) as Hfield.
      rewrite SIZEEQ_F in Hfield. exact Hfield. }
    exact FWF.
    { intros ofs1 IN. destruct (COMPLETE ofs1 IN) as [FIELD | TAIL].
      - left. exact FIELD.
      - right.
        eapply massert_imp_trans.
        eapply massert_imp_proj1.
        eapply range_impl; unfold tail; lia. }
    exact RANGE.
    exact FWT.
    { subst. unfold tail in *.
      rewrite EQV.
      apply sep_comm. }
  - assert (FPWF: fields_fp_well_formed ce (fp_enum id tagz fid fofs fp1)) by (eapply wt_footprint_fields_well_formed; eauto).
    inv FPWF. inv FWF. inv WTFP.
    assert (SIZEEQ_ENUM: sizeof ce (Tvariant orgs id) = sizeof_comp ce id).
    { unfold sizeof, sizeof_comp. rewrite CO. reflexivity. }
    rewrite SIZEEQ_ENUM in *.
    assert (SZM: size_chunk Mint32 = 4) by reflexivity.
    rewrite SZM in *.
    assert (SIZEEQ_F: sizeof ce fty = sizeof_footprint ce fp1) by (eapply wt_footprint_size_eq; eauto).
    assert (RANGEF: 0 <= ofs + fofs /\ (ofs + fofs) + sizeof ce fty <= Ptrofs.max_unsigned).
    { destruct RANGE as [A B]. split.
      - lia.
      - rewrite SIZEEQ_F. lia. }
    assert (FIELDRANGE: massert_imp mass2 (range b (ofs + fofs) (ofs + fofs + sizeof_footprint ce fp1))).
    { rewrite <- SIZEEQ_F.
      eapply IHenum; eauto. }
    assert (TAGRANGE: massert_imp (hasvalue Mint32 b ofs (Vint (Int.repr tagz))) (range b ofs (ofs + size_chunk Mint32))).
    { unfold hasvalue. eapply contains_range.
      destruct RANGE as [A B].
      assert (LE4: size_chunk Mint32 <= sizeof_comp ce id).
      { assert (FPOS: 0 <= sizeof_footprint ce fp1).
        { rewrite <- SIZEEQ_F. apply Z.ge_le. apply (sizeof_pos ce fty). }
        lia. }
      unfold Ptrofs.max_unsigned in *. unfold Ptrofs.modulus in *. lia. }
    assert (JOIN_FIELD: massert_imp
       (range b (ofs + fofs) (ofs + fofs + sizeof_footprint ce fp1) **
        range b (ofs + fofs + sizeof_footprint ce fp1) (ofs + sizeof_comp ce id))
       (range b (ofs + fofs) (ofs + sizeof_comp ce id))).
    { eapply range_join. }
    assert (JOIN_PAD: massert_imp
       (range b (ofs + 4) (ofs + fofs) **
        range b (ofs + fofs) (ofs + sizeof_comp ce id))
       (range b (ofs + 4) (ofs + sizeof_comp ce id))).
    { eapply range_join. }
    assert (JOIN_TAG: massert_imp
       (range b ofs (ofs + 4) **
        range b (ofs + 4) (ofs + sizeof_comp ce id))
       (range b ofs (ofs + sizeof_comp ce id))).
    { eapply range_join. }
    rewrite EQV.
    eapply massert_imp_trans.
    { eapply sepconj_morph_1; [eapply TAGRANGE |].
      eapply sepconj_morph_1; [reflexivity |].
      eapply sepconj_morph_1; [eapply FIELDRANGE |].
      eapply massert_imp_proj1. }
    eapply massert_imp_trans.
    { eapply sepconj_morph_1; [reflexivity |].
      eapply sepconj_morph_1; [reflexivity |].
      eapply JOIN_FIELD. }
    eapply massert_imp_trans.
    { eapply sepconj_morph_1; [reflexivity |].
      eapply JOIN_PAD. }
    eapply JOIN_TAG.
  - inv WTFP.
    { rewrite EQV.
      eapply massert_imp_trans.
      { eapply contains_range.
        assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
        destruct RANGE as [A B].
        rewrite <- (sizeof_by_value ce (Treference org mut ty0) Mptr MODE) in B.
        unfold Ptrofs.max_unsigned in B. unfold Ptrofs.modulus in B. unfold Ptrofs.modulus. lia. }
      { assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
        rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). reflexivity. } }
    { rewrite EQV.
      eapply massert_imp_trans.
      { eapply contains_range.
        assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
        destruct RANGE as [A B].
        rewrite <- (sizeof_by_value ce (Treference org mut ty0) Mptr MODE) in B.
        unfold Ptrofs.max_unsigned in B. unfold Ptrofs.modulus in B. unfold Ptrofs.modulus. lia. }
      { assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
        rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). reflexivity. } }
Qed.

Lemma store_sem_wt_loc ce: forall fp vfp b ofs mass1 mass2 v m1 MP chunk ty fpm
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (WTLOC: sem_wt_loc ce fp b ofs mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (AL: (align_chunk chunk | ofs))
    (MPRED: m1 |= mass1 ** mass2 ** MP)
    (WTFP1: wt_footprint ce fpm ty fp)
    (WTFP2: wt_footprint ce fpm ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk)
    (RANGE: 0 <= ofs /\ ofs + sizeof ce ty <= Ptrofs.max_unsigned),
    exists m2 mass3,
      Mem.store chunk m1 b ofs v = Some m2
      /\ sem_wt_loc ce vfp b ofs mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros. eapply store_sem_wt_val; eauto.
  eapply sep_imp. eapply MPRED.
  erewrite sizeof_by_value.
  eapply (sem_wt_loc_range_perm ce fp mass1 b ofs ty fpm); eauto.
  all: eauto.
Qed.


Lemma store_coherent_var: forall phl m ce mass1 mass2 v vfp fp1 pfp chunk b1 ofs1 b2 ofs2 MP ty fpm
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
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
    (BYVAL: access_mode ty = Ctypes.By_value chunk)
    (RANGE: 0 <= ofs2 /\ ofs2 + sizeof ce ty <= Ptrofs.max_unsigned),
    exists m1 fp2 mass3,
      Mem.store chunk m b2 ofs2 v = Some m1
      /\ set_footprint phl vfp fp1 = OK fp2
      /\ sem_wt_loc ce fp2 b1 ofs1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  (* [pfp] and [vfp] are well-typed footprints of the same [ty], hence
  have the same size. Needed to feed [set_footprint_sizeof_eq] in the
  box case, where the recursive call may be at the empty path. *)
  assert (SZEQ: forall ce0 fpm0 ty0 pfp0 vfp0,
             wt_footprint ce0 fpm0 ty0 pfp0 -> wt_footprint ce0 fpm0 ty0 vfp0 ->
             sizeof_footprint ce0 pfp0 = sizeof_footprint ce0 vfp0).
  { intros. erewrite <- (wt_footprint_size_eq ce0 ty0 pfp0); eauto.
    erewrite <- (wt_footprint_size_eq ce0 ty0 vfp0); eauto. }
  induction phl as [|pj phl IH]; intros.
  (* nil: the target location is right here, delegate to the
  single-location store rule. [alignof_by_value] bridges the [alignof]
  hypothesis to the [align_chunk] one that rule wants. *)
  - inv GFP.
    exploit store_sem_wt_loc; eauto.
    { eapply Z.divide_trans; [eapply alignof_by_value; eauto | exact AL]. }
    intros (m2 & mass3 & STORE & WTLOC1 & MPRED1).
    exists m2, vfp, mass3. split; auto.
  - simpl in GFP. destruct pj as [| fid | fid]; destruct fp1; try congruence.
    (* proj_deref / fp_box: the pointer cell [HV] and the size cell [SZ]
    are untouched by the store, so park them in the frame, recurse into
    the pointed-to footprint, then restore them. *)
    + inv WTLOC.
      unfold box_pred in EQV. rewrite EQV in MPRED.
      set (HV := hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero)) in *.
      set (SZ := contains_neg Mptr b (- size_chunk Mptr)
                   (eq (Vptrofs (Ptrofs.repr (sizeof_footprint ce fp1))))) in *.
      rewrite ! sep_assoc in MPRED.
      rewrite (sep_swap3 HV SZ nextmp) in MPRED.
      rewrite (sep_swap23 nextmp SZ HV) in MPRED.
      rewrite (sep_swap34 nextmp HV SZ mass2) in MPRED.
      rewrite (sep_swap23 nextmp HV mass2) in MPRED.
      rewrite <- (sep_assoc HV SZ MP) in MPRED.
      exploit IH; eauto.
      intros (m1 & fp2 & mass3 & STORE & SET & WTLOC1 & MPRED1).
      exists m1, (fp_box b fp2), (HV ** box_pred ce fp2 b mass3).
      split; auto.
      split. { simpl. rewrite SET. reflexivity. }
      split. { econstructor; eauto. }
      (* the size cell [SZ] still records the right size *)
      assert (SIZE: sizeof_footprint ce fp1 = sizeof_footprint ce fp2).
      { eapply set_footprint_sizeof_eq; eauto. }
      unfold box_pred. rewrite <- SIZE. fold SZ.
      rewrite ! sep_assoc.
      rewrite ! sep_assoc in MPRED1.
      rewrite (sep_swap mass3 HV) in MPRED1.
      rewrite (sep_swap23 HV mass3 SZ) in MPRED1.
      exact MPRED1.
    (* proj_field / fp_struct: split [fields_loc_sep] at [fid] with
    [fields_loc_sep_find_set], recurse into the field footprint, and
    rebuild with its [UPDATE] continuation. *)
    + destruct (find_field fid fpl) as [[[base fofs] ffp]|] eqn:FIND; try congruence.
      inv WTLOC.
      exploit fields_loc_sep_find_set; eauto.
      intros (mp1 & mp2 & mpi & l1 & l2 & SEP1 & SEP2 & FIELD & LIST & SPLIT & UPDATE).
      set (PAD := range b1 (ofs1 + base) (ofs1 + fofs)) in *.
      set (TAIL := range b1 (ofs1 + sizeof_struct_comp ce id) (ofs1 + sizeof_comp ce id)) in *.
      set (ALP := spure (alignof_comp ce id | ofs1)) in *.
      rewrite EQV, SPLIT in MPRED.
      assert (PERM: massert_eqv ((mp1 ** (PAD ** mpi) ** mp2) ** TAIL ** ALP)
                                (mpi ** (mp1 ** PAD ** mp2 ** TAIL ** ALP))).
      { rewrite ! sep_assoc.
        rewrite (sep_swap3 mp1 PAD mpi (mp2 ** TAIL ** ALP)).
        rewrite (sep_swap23 mpi PAD mp1 (mp2 ** TAIL ** ALP)).
        reflexivity. }
      rewrite PERM in MPRED.
      set (FRAME := mp1 ** PAD ** mp2 ** TAIL ** ALP) in *.
      assert (MPRED': m |= mpi ** mass2 ** (FRAME ** MP)).
      { fold FRAME in MPRED.
        rewrite (sep_assoc mpi FRAME (mass2 ** MP)) in MPRED.
        rewrite (sep_swap FRAME mass2 MP) in MPRED.
        exact MPRED. }
      exploit IH. 1-2: eauto. eapply FIELD. eapply WTVAL. eapply MPRED'.
      eapply GFP. all: eauto.
      intros (m1 & ffp2 & mpi' & STORE & SET & WTLOC1 & MPRED1).
      destruct (UPDATE ffp2 mpi' WTLOC1) as (mp' & SEP' & EQV').
      exists m1, (fp_struct id (set_field_fp fid ffp2 fpl)),
        (mp' ** TAIL ** ALP).
      split; auto.
      split. { simpl. rewrite FIND. rewrite SET. reflexivity. }
      split. { econstructor; [exact SEP' | reflexivity | reflexivity]. }
      rewrite EQV'.
      assert (PERM2: massert_eqv
        (mpi' ** FRAME ** MP)
        (((mp1 ** (PAD ** mpi') ** mp2) ** TAIL ** ALP) ** MP)).
      { unfold FRAME.
        rewrite ! sep_assoc.
        rewrite <- (sep_assoc mp1 PAD (mp2 ** TAIL ** ALP ** MP)).
        rewrite (sep_swap mpi' (mp1 ** PAD) (mp2 ** TAIL ** ALP ** MP)).
        rewrite (sep_assoc mp1 PAD (mpi' ** mp2 ** TAIL ** ALP ** MP)).
        reflexivity. }
      rewrite PERM2 in MPRED1.
      exact MPRED1.
    (* proj_downcast / fp_enum *)
    + destruct (ident_eq fid fid0) eqn:EQFID in GFP; try congruence.
      subst fid0.
      inv WTLOC.
      set (TAG := hasvalue Mint32 b1 ofs1 (Vint (Int.repr tagz))) in *.
      set (PRE := range b1 (ofs1 + size_chunk Mint32) (ofs1 + fofs)) in *.
      set (TAIL := range b1 (ofs1 + fofs + sizeof_footprint ce fp1)
                         (ofs1 + sizeof_comp ce id)) in *.
      set (ALP := spure (alignof_comp ce id | ofs1)) in *.
      rewrite EQV in MPRED.
      set (FRAME := TAG ** PRE ** TAIL ** ALP) in *.
      assert (PERM: massert_eqv
        (TAG ** PRE ** mass3 ** TAIL ** ALP)
        (mass3 ** FRAME)).
      { unfold FRAME.
        rewrite (sep_swap3 TAG PRE mass3 (TAIL ** ALP)).
        rewrite (sep_swap PRE TAG (TAIL ** ALP)).
        reflexivity. }
      rewrite PERM in MPRED.
      assert (MPRED': m |= mass3 ** mass2 ** (FRAME ** MP)).
      { rewrite (sep_assoc mass3 FRAME (mass2 ** MP)) in MPRED.
        rewrite (sep_swap FRAME mass2 MP) in MPRED.
        exact MPRED. }
      exploit IH. 1-2: eauto. exact FWT. exact WTVAL. exact MPRED'.
      exact GFP. all: eauto.
      intros (m1 & fp2 & mass4 & STORE & SET & WTLOC1 & MPRED1).
      assert (SIZE: sizeof_footprint ce fp1 = sizeof_footprint ce fp2).
      { eapply set_footprint_sizeof_eq.
        - exact GFP.
        - exact SET.
        - eapply SZEQ; eauto. }
      exists m1, (fp_enum id tagz fid fofs fp2),
        (TAG ** PRE ** mass4 ** TAIL ** ALP).
      split; [exact STORE |].
      split.
      { simpl. rewrite EQFID. rewrite SET. reflexivity. }
      split.
      { econstructor.
        - reflexivity.
        - exact WTLOC1.
        - reflexivity.
        - rewrite <- SIZE. reflexivity.
        - reflexivity. }
      assert (PERM2: massert_eqv
        (mass4 ** FRAME ** MP)
        ((TAG ** PRE ** mass4 ** TAIL ** ALP) ** MP)).
      { unfold FRAME.
        rewrite ! sep_assoc.
        rewrite <- (sep_assoc TAG PRE (TAIL ** ALP ** MP)).
        rewrite (sep_swap mass4 (TAG ** PRE) (TAIL ** ALP ** MP)).
        rewrite (sep_assoc TAG PRE (mass4 ** TAIL ** ALP ** MP)).
        reflexivity. }
      rewrite PERM2 in MPRED1.
      exact MPRED1.
Qed.

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
(*       assert (MPREDA: m|= mpi ** mass2 ** mp1 ** mp2 ** MP) by admit.       *)
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
(*       assert (MPREDA: m|= mass3 ** mass2 ** mass1 ** MP) by admit. *)
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

(* Removing the binding being replaced gives the same ordered list before and
   after [PTree.set].  Both coherence-preservation proofs use this fact. *)
Lemma PTree_remove_elements_eq {A: Type}: forall id (v: A) m,
    PTree.elements (PTree.remove id m) =
    PTree.elements (PTree.remove id (PTree.set id v m)).
Proof.
  intros.
  eapply PTree.elements_extensional.
  intros. rewrite !PTree.grspec.
  destruct PTree.elt_eq; subst; auto.
  rewrite PTree.gso; auto.
Qed.


(* ** Assignment coherence proof chain *)

(* We prove a strong version, i.e., the store operation can always succeed *)
Lemma store_coherent_fpm: forall phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
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
    (WTFP1: wt_footprint ce (fpm_to_tenv fpm) ty pfp)
    (WTFP2: wt_footprint ce (fpm_to_tenv fpm) ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk)
    (RANGE: 0 <= ofs /\ ofs + sizeof ce ty <= Ptrofs.max_unsigned),
    exists m1 fpm1 mass3,
      Mem.store chunk m b ofs v = Some m1
      /\ set_footprint_map (id, phl) vfp fpm = OK fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros.
  unfold get_owner_loc_footprint_map in GFP.
  destruct (fpm ! id) as [(((b1, ofs1), ty1), fp1) | ] eqn:B; try discriminate.
  inv COH.
  exploit PTree.elements_remove. exact B.
  intros (l1 & l2 & ELEMS_OLD & ELEMS_REM_OLD).
  rewrite ELEMS_OLD in ALLSEP.
  apply Forall_sep_app in ALLSEP as (mp_l & mp_rest & SEP_L & SEP_MID & EQV_L_REST).
  inversion SEP_MID as [| x0 l0 mhead mtail mwhole HEAD TAIL EQV_MID]; subst.
  inv HEAD; inv ELTEQ.
  assert (EQV_MASS1: massert_eqv mass1 (mp_l ** mhead ** mtail)).
  { etransitivity; [exact EQV_L_REST |].
    apply sepconj_morph_2; [reflexivity |]. symmetry. exact EQV_MID. }
  assert (EQV_FRAME: massert_eqv
    ((mp_l ** mhead ** mtail) ** mass2 ** MP)
    (mhead ** mass2 ** (mp_l ** mtail ** MP))).
  { rewrite !sep_assoc.
    rewrite (sep_swap mp_l mhead (mtail ** mass2 ** MP)).
    rewrite (sep_swap3 mp_l mtail mass2 MP).
    rewrite (sep_swap mtail mp_l MP).
    reflexivity. }
  assert (MPRED_VAR: m |= mhead ** mass2 ** (mp_l ** mtail ** MP)).
  { rewrite EQV_MASS1 in MPRED. rewrite EQV_FRAME in MPRED. exact MPRED. }
  exploit (store_coherent_var phl m ce mhead mass2 v vfp fp pfp chunk b0 ofs0 b ofs
             (mp_l ** mtail ** MP) ty (fpm_to_tenv fpm)); eauto.
  intros (m1 & fp2 & mass3 & STORE & SET_FOOT & WTLOC_FP2 & MPRED_M1).
  remember (PTree.set id0 (b0, ofs0, ty0, fp2) fpm) as fpm1 eqn:FPM1.
  assert (SET_MAP: set_footprint_map (id0, phl) vfp fpm = OK fpm1).
  { unfold set_footprint_map. simpl. rewrite B. rewrite SET_FOOT.
    simpl. rewrite <- FPM1. reflexivity. }
  assert (FPM1_GET: fpm1 ! id0 = Some (b0, ofs0, ty0, fp2)).
  { rewrite FPM1. apply PTree.gss. }
  exploit PTree.elements_remove. exact FPM1_GET.
  intros (l1' & l2' & ELEMS_NEW & ELEMS_REM_NEW).
  assert (REM_ELEMS_EQ:
    PTree.elements (PTree.remove id0 fpm1) =
    PTree.elements (PTree.remove id0 fpm)).
  { rewrite FPM1. symmetry. apply PTree_remove_elements_eq. }
  assert (L_EQ: l1' ++ l2' = l1 ++ l2).
  { rewrite <- ELEMS_REM_NEW. rewrite REM_ELEMS_EQ. exact ELEMS_REM_OLD. }
  assert (SEP_OLD:
    Forall_sep (coherent_var ce) (l1 ++ l2) (mp_l ** mtail)).
  { eapply Forall_sep_app. exists mp_l, mtail.
    split; [exact SEP_L |].
    split; [exact TAIL |].
    apply massert_eqv_refl. }
  assert (SEP_NEW_TAIL:
    Forall_sep (coherent_var ce) (l1' ++ l2') (mp_l ** mtail)).
  { rewrite L_EQ. exact SEP_OLD. }
  apply Forall_sep_app in SEP_NEW_TAIL as
    (mp_l' & mp_r' & SEP_L' & SEP_R' & EQV_LR').
  assert (COH_NEW_HEAD:
    coherent_var ce (id0, (b0, ofs0, ty0, fp2)) mass3).
  { econstructor; [reflexivity | exact WTLOC_FP2]. }
  assert (SEP_NEW_MID:
    Forall_sep (coherent_var ce) ((id0, (b0, ofs0, ty0, fp2)) :: l2')
      (mass3 ** mp_r')).
  { econstructor; [exact COH_NEW_HEAD | exact SEP_R' | apply massert_eqv_refl]. }
  assert (EQV_NEW_LIST:
    massert_eqv (mass3 ** mp_l ** mtail) (mp_l' ** (mass3 ** mp_r'))).
  { etransitivity; [apply sepconj_morph_2; [reflexivity | exact EQV_LR'] |].
    apply sep_swap. }
  assert (SEP_NEW_LIST:
    Forall_sep (coherent_var ce)
      (l1' ++ (id0, (b0, ofs0, ty0, fp2)) :: l2')
      (mass3 ** mp_l ** mtail)).
  { eapply Forall_sep_app. exists mp_l', (mass3 ** mp_r').
    split; [exact SEP_L' |].
    split; [exact SEP_NEW_MID |].
    exact EQV_NEW_LIST. }
  assert (COH_FPM1: coherent_fpm ce fpm1 (mass3 ** mp_l ** mtail)).
  { apply coherent_fpm_intro. rewrite ELEMS_NEW. exact SEP_NEW_LIST. }
  exists m1, fpm1, (mass3 ** mp_l ** mtail).
  split; [exact STORE |].
  split; [exact SET_MAP |].
  split; [exact COH_FPM1 |].
  rewrite (sep_assoc mass3 (mp_l ** mtail) MP).
  rewrite (sep_assoc mp_l mtail MP).
  exact MPRED_M1.
Qed.


Lemma assign_loc_by_value_coherent_fpm: forall phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
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
    (WTFP1: wt_footprint ce (fpm_to_tenv fpm) ty pfp)
    (WTFP2: wt_footprint ce (fpm_to_tenv fpm) ty vfp)
    (BYVAL: access_mode ty = Ctypes.By_value chunk)
    (* (SHALLOW: shallow_init pfp = true) *)
    (* (FPWF: fields_fp_well_formed ce pfp) *)
    (RANGE: 0 <= ofs /\ ofs + sizeof ce ty <= Ptrofs.max_unsigned),
    exists m1 fpm1 mass3,
      assign_loc ce ty m b (Ptrofs.repr ofs) v m1
      /\ set_footprint_map (id, phl) vfp fpm = OK fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros.
  exploit (store_coherent_fpm phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty); eauto.
  intros (m1 & fpm1 & mass3 & STORE & SET & COH1 & MPRED1).
  exists m1, fpm1, mass3.
  split.
  { econstructor.
    - exact BYVAL.
    - simpl. rewrite Ptrofs.unsigned_repr.
      + exact STORE.
      + destruct RANGE as [LO HI].
        assert (SIZE: 0 <= sizeof ce ty).
        { apply Z.ge_le. apply sizeof_pos. }
        lia. }
  split; [exact SET |].
  split; [exact COH1 | exact MPRED1].
Qed.


(* ** Byte-store coherence proof chain *)

(* storebytes rules *)

(* Lemma sem_wt_loc_merge ce: forall fp mp1 mp2 b ofs *)
(*     (WTFP: sem_wt_fp ce fp mp1) *)
(*     (WTLOC: sem_wt_loc ce (clear_footprint_rec ce fp) b ofs mp2), *)
(*     sem_wt_loc ce fp b ofs (mp2 ** mp1). *)
(* Proof. *)
(*   induction fp using strong_footprint_ind; intros; simpl in *; inv WTFP; inv WTLOC. *)
(*   - econstructor. auto. rewrite EQV, EQV0. symmetry. *)
(*     eapply massert_eqv_pure_r. *)
(*   - econstructor. auto. rewrite EQV, EQV0. symmetry. *)
(*     eapply massert_eqv_pure_r. *)
(*   - econstructor. rewrite EQV, EQV0. symmetry. *)
(*     eapply massert_eqv_pure_r. *)
(*   - unfold box_pred in FREE. simpl in FREE.  *)
(*     econstructor; eauto. *)
(*     rewrite EQV, EQV0. rewrite FREE. eapply sepconj_morph_2. *)
(*     symmetry. eapply massert_eqv_pure_r. reflexivity. *)
(*   - econstructor. *)
(*     (** TODO: write a helper function for fields_fp_sep *) *)
(* Admitted. *)

Definition pin_footprint (fp: footprint) : bool :=
  match fp with
  (* | fp_object _ _ _ => true *)
  | _ => false
  end.

(* Lemma sem_wt_loc_split ce: forall fp mp b ofs *)
(*     (* We assume fp must not be opaque object *) *)
(*     (UNPIN: pin_footprint fp = false) *)
(*     (WTLOC: sem_wt_loc ce fp b ofs mp), *)
(*     exists mp1 mp2, sem_wt_loc ce (clear_footprint_rec fp) b ofs mp1 *)
(*                /\ sem_wt_fp ce fp mp2 *)
(*                /\ massert_eqv mp (mp1 ** mp2). *)
(* Proof. *)
(*   induction fp using strong_footprint_ind; intros; simpl in *; inv UNPIN; inv WTLOC. *)
(*   - exists STrue, STrue. split. econstructor. reflexivity. *)
(*     split. econstructor. reflexivity. rewrite EQV. *)
(*     eapply massert_eqv_pure_r. *)
(*   - exists ((range b ofs (ofs + sz)) ** spure (al | ofs)), STrue. *)
(*     do 2 try apply conj. econstructor; auto. *)
(*     econstructor. reflexivity. *)
(*     rewrite EQV. eapply massert_eqv_pure_r. *)
(*   - exists (hasvalue chunk b ofs v), STrue. *)
(*     do 2 try apply conj. econstructor; auto. *)
(*     econstructor. reflexivity. *)
(*     rewrite EQV. eapply massert_eqv_pure_r. *)
(*   - exists (hasvalue Mptr b0 ofs (Vptr b Ptrofs.zero)), mp0. *)
(*     do 2 try apply conj. *)
(*     + econstructor; auto. econstructor. reflexivity. *)
(*       unfold box_pred. simpl.  *)
(*       eapply massert_eqv_pure_r. *)
(*     + econstructor. eauto. auto. *)
(*     + auto. *)
(*   (** TODO: write helper for fields_loc_sep  *) *)
(*   - admit. *)
(*   - admit. *)
(*   - admit. *)
(* Admitted. *)


(************** End of split rules ********************** *)




(* Storebytes: a store at a prefix range does not affect the contents
   of the region stored by a later store at a disjoint suffix range,
   so the two memories after storing only the suffix differ only at
   the prefix. *)

Lemma setN_get_in_range:
  forall A (l: list A) p q (c: ZMap.t A) d,
    p <= q < p + Z.of_nat (length l) ->
    ZMap.get q (Mem.setN l p c) = nth (Z.to_nat (q - p)) l d.
Proof.
  induction l; intros; simpl in *.
  - lia.
  - destruct (Z.eq_dec p q).
    + subst.
      rewrite (Mem.setN_outside A l (ZMap.set q a c) (q + 1) q) by lia.
      rewrite ZMap.gss.
      rewrite Z.sub_diag. simpl. reflexivity.
    + assert (Hp: p < q) by lia.
      rewrite (IHl (p + 1) q (ZMap.set p a c) d); [|lia].
      assert (HAR: q - (p + 1) = q - p - 1) by lia.
      rewrite HAR.
      replace (Z.to_nat (q - p)) with (Z.to_nat (Z.succ (q - p - 1))) by (f_equal; lia).
      rewrite Z2Nat.inj_succ by lia.
      simpl. reflexivity.
Qed.

Lemma storebytes_prefix_contents:
  forall m1 m1p m2h m1' b ofs fofs bytesP bytesH1,
    Z.of_nat (length bytesP) = fofs ->
    Mem.storebytes m1 b ofs bytesP = Some m1p ->
    Mem.storebytes m1 b (ofs + fofs) bytesH1 = Some m2h ->
    Mem.storebytes m1p b (ofs + fofs) bytesH1 = Some m1' ->
    NMap.get _ b (Mem.mem_contents m1') = Mem.setN bytesH1 (ofs + fofs) (Mem.setN bytesP ofs (NMap.get _ b (Mem.mem_contents m1)))
    /\ NMap.get _ b (Mem.mem_contents m2h) = Mem.setN bytesH1 (ofs + fofs) (NMap.get _ b (Mem.mem_contents m1)).
Proof.
  intros m1 m1p m2h m1' b ofs fofs bytesP bytesH1 LENP STOREP STOREH STOREHP.
  split.
  - rewrite (Mem.storebytes_mem_contents m1p b (ofs + fofs) bytesH1 m1' STOREHP).
    rewrite (Mem.storebytes_mem_contents m1 b ofs bytesP m1p STOREP).
    rewrite NMap.gsspec. rewrite NMap.gsspec.
    destruct (NMap.elt_eq b b) as [EQ | NE].
    + reflexivity.
    + exfalso; exact (NE eq_refl).
  - rewrite (Mem.storebytes_mem_contents m1 b (ofs + fofs) bytesH1 m2h STOREH).
    rewrite NMap.gsspec.
    destruct (NMap.elt_eq b b) as [EQ | NE].
    + reflexivity.
    + exfalso; exact (NE eq_refl).
Qed.

(* [storebytes_prefix_unchanged] *)
Lemma storebytes_prefix_unchanged:
  forall m1 m1p m2h m1' b ofs fofs bytesP bytesH1,
    Z.of_nat (length bytesP) = fofs ->
    Mem.storebytes m1 b ofs bytesP = Some m1p ->
    Mem.storebytes m1 b (ofs + fofs) bytesH1 = Some m2h ->
    Mem.storebytes m1p b (ofs + fofs) bytesH1 = Some m1' ->
    forall P: block -> Z -> Prop, (forall b0 ofs0, P b0 ofs0 -> ~ (b0 = b /\ ofs <= ofs0 < ofs + fofs)) ->
    Mem.unchanged_on P m2h m1'.
Proof.
  intros m1 m1p m2h m1' b ofs fofs bytesP bytesH1 LENP STOREP STOREH STOREHP P PFORBID.
  constructor.
  - (* support *)
    intros b0 SUPPORT.
    rewrite (Mem.support_storebytes m1 b (ofs + fofs) bytesH1 m2h STOREH) in SUPPORT.
    rewrite (Mem.support_storebytes m1p b (ofs + fofs) bytesH1 m1' STOREHP).
    rewrite (Mem.support_storebytes m1 b ofs bytesP m1p STOREP).
    exact SUPPORT.
  - (* perm *)
    intros b0 ofs0 k p0 PB0 VALID. split; intro PERM.
    + eapply Mem.perm_storebytes_1; [exact STOREHP |].
      eapply Mem.perm_storebytes_1; [exact STOREP |].
      eapply Mem.perm_storebytes_2; [exact STOREH | exact PERM].
    + eapply Mem.perm_storebytes_1; [exact STOREH |].
      eapply Mem.perm_storebytes_2; [exact STOREP |].
      eapply Mem.perm_storebytes_2; [exact STOREHP | exact PERM].
  - (* contents *)
    intros b0 ofs0 PB0 READABLE.
    destruct (peq b0 b) as [EQ | NEQ].
    + subst b0.
      destruct (storebytes_prefix_contents m1 m1p m2h m1' b ofs fofs bytesP bytesH1 LENP STOREP STOREH STOREHP) as [C1 C2].
      rewrite C1. rewrite C2.
      destruct (Z_lt_ge_dec ofs0 (ofs + fofs)) as [LTS | GES].
      * assert (OFSS: ofs0 < ofs).
        { destruct (Z_lt_ge_dec ofs0 ofs); [auto | exfalso].
          apply (PFORBID b ofs0 PB0). split; auto. lia. }
        rewrite (Mem.setN_outside memval bytesH1 _ (ofs + fofs) ofs0) by lia.
        rewrite (Mem.setN_outside memval bytesH1 _ (ofs + fofs) ofs0) by lia.
        rewrite (Mem.setN_outside memval bytesP _ ofs ofs0) by lia.
        auto.
      * destruct (Z_lt_ge_dec ofs0 (ofs + fofs + Z.of_nat (length bytesH1))) as [LT2 | GE2].
        -- assert (RNGH: ofs + fofs <= ofs0 /\ ofs0 < ofs + fofs + Z.of_nat (length bytesH1)).
           { split; [apply Z.ge_le; exact GES | exact LT2]. }
           rewrite (setN_get_in_range memval bytesH1 (ofs + fofs) ofs0 _ Undef RNGH).
           rewrite (setN_get_in_range memval bytesH1 (ofs + fofs) ofs0 _ Undef RNGH).
           reflexivity.
        -- rewrite (Mem.setN_outside memval bytesH1 _ (ofs + fofs) ofs0) by lia.
           rewrite (Mem.setN_outside memval bytesH1 _ (ofs + fofs) ofs0) by lia.
           rewrite (Mem.setN_outside memval bytesP _ ofs ofs0) by lia.
           auto.
    + (* b0 <> b *)
      unfold NMap.get.
      rewrite (Mem.storebytes_mem_contents m1p b (ofs + fofs) bytesH1 m1' STOREHP).
      rewrite (Mem.storebytes_mem_contents m1 b ofs bytesP m1p STOREP).
      rewrite (Mem.storebytes_mem_contents m1 b (ofs + fofs) bytesH1 m2h STOREH).
      rewrite NMap.gso by auto.
      rewrite NMap.gso by auto.
      rewrite NMap.gso by auto.
      reflexivity.
Qed.


(* The footprint of a well-typed [fields_loc_sep] is contained in the
   region [ofs, ofs+sz), except that box fields may point to other
   blocks. *)

(* Lemma fields_loc_sep_footprint_bounded ce: forall fpl b ofs mass sz al, *)
(*     fields_loc_sep b ofs (sem_wt_loc ce) fpl mass -> *)
(*     Forall (fp_field_in_range_aligned ce sz al (fields_fp_well_formed ce)) fpl -> *)
(*     (forall fid base fofs ffp, *)
(*         In (fid, ((base, fofs), ffp)) fpl -> *)
(*         0 <= sizeof_footprint ce ffp /\ *)
(*         (forall b0 ofs0 m', *)
(*            sem_wt_loc ce ffp b (ofs + fofs) m' -> *)
(*            m_footprint m' b0 ofs0 -> *)
(*            (b0 = b /\ ofs + fofs <= ofs0 < ofs + fofs + sizeof_footprint ce ffp) \/ b0 <> b)) -> *)
(*     forall b0 ofs0, *)
(*       m_footprint mass b0 ofs0 -> *)
(*       (b0 = b /\ ofs <= ofs0 < ofs + sz) \/ b0 <> b. *)
(* Proof. *)
(*   intros fpl b ofs mass sz al FSEP FWF HFIELD. *)
(*   induction FSEP; intros b0 ofs0 FOOT. *)
(*   - (* nil *) *)
(*     destruct EQV as [_ EQ2]. *)
(*     destruct EQ2 as [_ FP]. *)
(*     destruct (FP b0 ofs0 FOOT). *)
(*   - (* cons *) *)
(*     pose proof (Forall_inv FWF) as FWF0. pose proof (Forall_inv_tail FWF) as FWF1. *)
(*     inv FWF0. *)
(*     destruct (HFIELD fid base fofs ffp (or_introl eq_refl)) as [HSIZE0 HBOUND0]. *)
(*     destruct EQV as [_ EQ2]. *)
(*     destruct EQ2 as [_ FP]. *)
(*     pose proof (FP b0 ofs0 FOOT) as FOOTX. *)
(*     simpl in FOOTX. *)
(*     destruct FOOTX as [FOOTP | [FOOT1 | FOOT2]]. *)
(*     + (* padding *) *)
(*       destruct FOOTP as [HEQ HRANGE]. subst b0. *)
(*       left. split; [reflexivity | split; lia]. *)
(*     + (* head field *) *)
(*       destruct (HBOUND0 b0 ofs0 mass1 FWT FOOT1) as [BND | NEQ]. *)
(*       * destruct BND as [HEQ2 HRANGE2]. subst b0. *)
(*         left. split; [reflexivity | split; lia]. *)
(*       * right. exact NEQ. *)
(*     + (* tail *) *)
(*       exact (IHFSEP FWF1 (fun fid0 base0 fofs0 ffp0 IN0 => HFIELD fid0 base0 fofs0 ffp0 (or_intror IN0)) b0 ofs0 FOOT2). *)
(* Qed. *)

(* The footprint of a well-typed location is contained in its region,
   except that a box may point to (other) heap blocks. *)
(* Lemma sem_wt_loc_footprint_bounded ce te: forall ty fp, *)
(*     composite_env_consistent ce -> *)
(*     (forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co))) -> *)
(*     wt_footprint ce te ty fp -> *)
(*     fields_fp_well_formed ce fp -> *)
(*     forall b ofs mass, *)
(*       sem_wt_loc ce fp b ofs mass -> *)
(*       forall b' ofs', *)
(*         m_footprint mass b' ofs' -> *)
(*         (b' = b /\ ofs <= ofs' < ofs + sizeof_footprint ce fp) \/ b' <> b. *)
(* Proof. *)
(*   intros ty fp CONS NOREP WTFP FPWF. revert ty WTFP FPWF. *)
(*   induction fp as [| sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b2 ofs2 ph0 vs] using strong_footprint_ind; *)
(*     intros ty WTFP FPWF b ofs mass WTLOC b' ofs' FOOT; inv WTLOC. *)
(*   - (* fp_emp *) *)
(*     destruct EQV as [EQV1 IMP]. destruct IMP as [IMPP FP]. simpl in FP. *)
(*     destruct (FP b' ofs' FOOT). *)
(*   - (* fp_uninit *) *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     destruct (FP b' ofs' FOOT) as [INR | INSP]. *)
(*     + simpl in INR. destruct INR as [EQ [LO HI]]. subst. left. split; [auto | simpl; lia]. *)
(*     + unfold spure in INSP. simpl in INSP. contradiction. *)
(*   - (* fp_scalar *) *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     unfold hasvalue, contains in FP. cbn in FP. *)
(*     destruct (FP b' ofs' FOOT) as [EQ [LO HI]]. subst. *)
(*     left. split; [auto | simpl; lia]. *)
(*   - (* fp_box *) *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     destruct (FP b' ofs' FOOT) as [INH | INBOX]. *)
(*     + unfold hasvalue, contains in INH. cbn in INH. *)
(*       destruct INH as [EQ [LO HI]]. subst. *)
(*       left. split; [auto | simpl; lia]. *)
(*     + unfold box_pred in INBOX. *)
(*       destruct INBOX as [INNEG | INNEXT]. *)
(*       * unfold contains_neg in INNEG. simpl in INNEG. *)
(*         destruct INNEG as [EQ _]. subst b'. right. (* exact NEQ. *) admit. *)
(*       * right. (* exact (BOXFP b' ofs' INNEXT). *) admit. *)
(*   - (* fp_struct *) *)
(*     inv WTFP. *)
(*     inv FPWF. *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     destruct (FP b' ofs' FOOT) as [INMASS | [INPAD | INSP]]. *)
(*     + (* fields *) *)
(*       eapply fields_loc_sep_footprint_bounded with (sz := sizeof_comp ce id) (al := alignof_comp ce id); eauto. *)
(*       { intros fid0 base0 fofs0 ffp0 IN0. split. *)
(*         - destruct (fp_match_field_In_wt ce co (wt_footprint ce te) fpl (co_members co) fid0 base0 fofs0 ffp0 MATCH IN0) as [fty0 WTFP0]. *)
(*           pose proof (wt_footprint_size_eq ce fty0 ffp0 te WTFP0) as SIZEEQ. *)
(*           rewrite <- SIZEEQ. apply Z.ge_le. apply (sizeof_pos ce fty0). *)
(*         - intros b0 ofs0 m' WTLOC0 FOOT0. *)
(*           destruct (fp_match_field_In_wt ce co (wt_footprint ce te) fpl (co_members co) fid0 base0 fofs0 ffp0 MATCH IN0) as [fty0 WTFP0]. *)
(*           assert (FWF0: fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce) (fid0, ((base0, fofs0), ffp0))). *)
(*           { apply (proj1 (Forall_forall (fp_field_in_range_aligned ce (sizeof_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce)) fpl)); [exact FWF | exact IN0]. } *)
(*           inv FWF0. *)
(*           exact (IHfields fid0 base0 fofs0 ffp0 IN0 fty0 WTFP0 R5 b (ofs + fofs0) m' WTLOC0 b0 ofs0 FOOT0). } *)
(*     + (* trailing padding *) *)
(*       subst. unfold range in INPAD. cbn in INPAD. *)
(*       destruct INPAD as [EQ [LO HI]]. subst. *)
(*       assert (SZC: 0 <= sizeof_struct_comp ce id). *)
(*       { unfold sizeof_struct_comp. destruct (ce ! id) as [co0|]; [|lia]. *)
(*         destruct (co_sv co0); simpl; [|lia]. *)
(*         exact (sizeof_composite_pos ce Struct (co_members co0)). } *)
(*       left. split; [auto | simpl; lia]. *)
(*     + unfold spure in INSP. simpl in INSP. contradiction. *)
(*   - (* fp_enum *) *)
(*     inv WTFP. *)
(*     inv FPWF. inv FWF. *)
(*     pose proof (wt_footprint_size_eq ce fty fp1 te WT) as SIZEEQ. *)
(*     assert (FPOS: 0 <= sizeof_footprint ce fp1). *)
(*     { rewrite <- SIZEEQ. apply Z.ge_le. apply (sizeof_pos ce fty). } *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     destruct (FP b' ofs' FOOT) as [INM1 | [INPAD | [INM2 | [INTAIL | INSP]]]]. *)
(*     + (* tag *) *)
(*       subst. unfold hasvalue, contains in INM1. cbn in INM1. *)
(*       destruct INM1 as [EQ [LO HI]]. subst. *)
(*       left. split; [auto |]. *)
(*       assert (SZM: size_chunk Mint32 = 4) by reflexivity. *)
(*       assert (LE4: size_chunk Mint32 <= sizeof_comp ce id). *)
(*       { rewrite SZM. lia. } *)
(*       simpl. lia. *)
(*     + (* padmp *) *)
(*       subst. unfold range in INPAD. cbn in INPAD. *)
(*       destruct INPAD as [EQ [LO HI]]. subst. *)
(*       left. split; [auto | simpl; lia]. *)
(*     + (* variant field *) *)
(*       destruct (IHenum fty WT R5 b (ofs + fofs) mass2 FWT b' ofs' INM2) as [BND | NEQ]. *)
(*       * left. destruct BND as [EQ [LO HI]]. subst. split; [auto | simpl; lia]. *)
(*       * right. exact NEQ. *)
(*     + (* tailpad *) *)
(*       subst. unfold range in INTAIL. cbn in INTAIL. *)
(*       destruct INTAIL as [EQ [LO HI]]. subst. *)
(*       left. split; [auto | simpl; lia]. *)
(*     + unfold spure in INSP. simpl in INSP. contradiction. *)
(*   - (* fp_ref *) *)
(*     destruct EQV as [EQV1 EQV2]. destruct EQV2 as [EQV2P FP]. *)
(*     simpl in FP. *)
(*     unfold hasvalue, contains in FP. cbn in FP. *)
(*     destruct (FP b' ofs' FOOT) as [EQ [LO HI]]. subst. *)
(*     left. split; [auto | simpl; lia]. *)
(* (* Qed. *) *)
(* Admitted. *)

(* Given a well-typed struct footprint [fpl], storing the struct bytes
   into the target location makes each field of the target location
   semantically well-typed.  We split the source bytes and the target
   stores field by field and apply [storebytes_sem_wt_loc] to each
   field. *)



(* Re-base a [fields_loc_sep] derivation by shifting the base offset
   by [d]; the field offsets in the list are shifted by [-d] so that
   the absolute locations of the fields stay the same. *)
Definition shift_ffp (d : Z) (x : ffpty) : ffpty :=
  match x with
  | (fid, ((base, fofs), ffp)) => (fid, ((base - d, fofs - d), ffp))
  end.

Lemma fields_loc_sep_shift: forall b ofs P d fpl mass,
    fields_loc_sep b ofs P fpl mass ->
    fields_loc_sep b (ofs + d) P (map (shift_ffp d) fpl) mass.
Proof.
  intros b ofs P d fpl mass F.
  induction F as [mp EQV | fid base fofs ffp l mass1 mass2 padmp mp IND IHF WT1 ALPERM EQV].
  - simpl. econstructor. exact EQV.
  - simpl.
    apply (fields_loc_sep_cons b (ofs + d) P fid (base - d) (fofs - d) ffp
                               (map (shift_ffp d) l) mass1 mass2 padmp mp);
    [ exact IHF
    | replace (ofs + d + (fofs - d)) with (ofs + fofs) by lia; exact WT1
    | rewrite ALPERM; f_equal; lia
    | exact EQV ].
Qed.


(* The per-field absolute alignment predicate is invariant under the
   [shift_ffp d] re-basing, provided the target base is shifted by [d]. *)
Lemma Forall_align_shift: forall ce tofs d fpl,
    Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | tofs + fofs)) fpl ->
    Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + d) + fofs))
           (map (shift_ffp d) fpl).
Proof.
  intros ce tofs d fpl. induction fpl as [| a l IH]; intros H.
  - simpl. econstructor.
  - simpl. inv H.
    destruct a as [fid [[base fofs] ffp]].
    simpl in *.
    econstructor.
    + replace ((tofs + d) + (fofs - d)) with (tofs + fofs) by lia. exact H2.
    + apply IH. exact H3.
Qed.

Lemma Forall_range_shift ce: forall sz d f fpl,
    Forall (fun '(fid', ((base', fofs'), ffp')) => d <= fofs') fpl ->
    Forall (fp_field_in_range ce sz f) fpl ->
    Forall (fp_field_in_range ce (sz - d) f) (map (shift_ffp d) fpl).
Proof.
  intros sz d f fpl. revert f. induction fpl as [| a l IH]; intros f HEAD WF.
  - simpl. constructor.
  - destruct a as [fid [[base fofs] ffp]].
    simpl in *.
    inversion HEAD as [| ? ? HHEAD HTAIL]; subst.
    inversion WF as [| ? ? WFHEAD WFTAIL]; subst.
    inversion WFHEAD as [fid0 base0 fofs0 ffp0 R1 R2 R3 R5]; subst.
    constructor.
    + apply fp_field_in_range_intro.
      * lia.
      * lia.
      * lia.
      * exact R5.
    + exact (IH f HTAIL WFTAIL).
Qed.

Lemma Forall_wtfootprint_shift ce: forall te d fpl,
    Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) fpl ->
    Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp)
           (map (shift_ffp d) fpl).
Proof.
  intros te d fpl. induction fpl as [| a l IH]; intros H.
  - simpl. constructor.
  - destruct a as [fid [[base fofs] ffp]].
    simpl in *.
    inversion H as [| ? ? HHEAD HTAIL]; subst.
    constructor; [exact HHEAD | exact (IH HTAIL)].
Qed.

Lemma shift_ffp_involutive: forall d l,
    map (shift_ffp (- d)) (map (shift_ffp d) l) = l.
Proof.
  intros d l. induction l as [| a l IH]; simpl; auto.
  rewrite IH. destruct a as [fid [[base fofs] ffp]]. simpl. repeat f_equal; lia.
Qed.

Lemma in_map_shift_ffp_inv: forall d l fid base fofs ffp,
    In (fid, ((base, fofs), ffp)) (map (shift_ffp d) l) ->
    In (fid, ((base + d, fofs + d), ffp)) l.
Proof.
  intros d l fid base fofs ffp H.
  apply in_map_iff in H as [y [INY EQ]].
  destruct y as [fidy [[basey fofsy] ffpy]].
  simpl in INY.
  injection INY as Hfid Hbase.
  subst fidy.
  subst ffpy.
  assert (Hb : basey = base + d) by lia.
  assert (Hf : fofsy = fofs + d) by lia.
  rewrite <- Hb, <- Hf. exact EQ.
Qed.

Lemma range_split_imp: forall b lo mid hi P,
    lo <= mid <= hi ->
    massert_imp (range b lo hi ** P) (range b lo mid ** range b mid hi ** P).
Proof.
  intros b lo mid hi P H. split.
  - intros m MPRED. eapply range_split; [exact H | exact MPRED].
  - intros b0 ofs0 FOOT. simpl in FOOT.
    destruct FOOT as [F1 | [F2 | FP]].
    + simpl in F1. destruct F1 as [EQ [LO' HI']]. subst. left. simpl. split; [reflexivity | lia].
    + simpl in F2. destruct F2 as [EQ [LO' HI']]. subst. left. simpl. split; [reflexivity | lia].
    + right. exact FP.
Qed.

Lemma fields_after_d_le ce: forall d l,
    fields_after ce d l ->
    Forall (fun '(fid', ((base', fofs'), ffp')) => d <= fofs') l.
Proof.
  intros d l. revert d.
  induction l as [| a l IHl]; intros d H.
  - constructor.
  - destruct a as [fid [[base fofs] ffp]].
    inversion H as [| fid0 base0 fofs0 ffp0 l0 HBASE HLE HSIZE HA]; subst.
    constructor; [exact HLE |].
    apply Forall_forall. intros x IN.
    pose proof (IHl (fofs + sizeof_footprint ce ffp) HA) as IHT.
    apply (proj1 (Forall_forall (fun '(fid', ((base', fofs'), ffp')) => fofs + sizeof_footprint ce ffp <= fofs') l) IHT) in IN.
    destruct x as [fid' [[base' fofs'] ffp']]. simpl in IN. lia.
Qed.

Lemma fields_after_shift ce: forall d d' l,
    fields_after ce d l ->
    fields_after ce (d - d') (map (shift_ffp d') l).
Proof.
  intros d d' l. revert d d'.
  induction l as [| a l IHl]; intros d d' H.
  - simpl. constructor.
  - destruct a as [fid [[base fofs] ffp]].
    inversion H as [| fid0 base0 fofs0 ffp0 l0 HBASE HLE HSIZE HA]; subst.
    simpl. constructor.
    + lia.
    + lia.
    + exact HSIZE.
    + assert (HEQ : (fofs - d') + sizeof_footprint ce ffp = (fofs + sizeof_footprint ce ffp) - d') by lia.
      rewrite HEQ. exact (IHl (fofs + sizeof_footprint ce ffp) d' HA).
Qed.


(* [storebytes_fields_loc_sep]: storing the bytes of a well-typed field
   list [fpl] into a target location makes that target location
   semantically well-typed, field by field.

   Concretely, suppose the source location [sem_wt_loc]-describes [fpl]
   at [(sb, sofs)] with assertion [mass], and we load [sz] bytes from
   the source, then store those same bytes at [(tb, tofs)] using the
   target permission [mp2] (which covers [tofs, tofs + sz)).  Given
   that the field list is range-bounded ([WF]), sorted ([SORTED]), and
   absolutely aligned at [tofs] ([ABS_ALIGN]), the conclusion produces a
   [fields_loc_sep] for [fpl] at [(tb, tofs)] whose assertion holds in
   the resulting memory [m2] together with the frame [MP].

   The proof is by well-founded induction on [length fpl].  The nil case
   is immediate.  In the cons case we split the loaded bytes into the
   padding before the head field, the head field bytes, and the tail
   bytes; the per-field IH [IH] turns the head field bytes into a
   [sem_wt_loc] for [ffp] at [tofs + fofs].  We then shift the tail
   field list by [d := fofs + sizeof_footprint ce ffp] with [shift_ffp],
   which keeps the absolute field locations unchanged, and recurse on
   [map (shift_ffp d) l] using the tail's [SORTED]/[WF]/[ABS_ALIGN]
   invariants.  Finally we re-base the recursive [fields_loc_sep] back
   to [tofs] and reassemble the whole field list with
   [fields_loc_sep_cons]. *)
Lemma storebytes_fields_loc_sep ce: forall fpl tb tofs sb sofs mass mp2 MP m1_src m1 m2 bytes te sz
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (IH: forall fid base fofs ffp,
        In (fid, ((base, fofs), ffp)) fpl ->
        forall tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te,
        sem_wt_loc ce ffp sb sofs mp1 ->
        massert_imp mp2 (range tb tofs (tofs + sizeof_footprint ce ffp)) ->
        (alignof_footprint ce ffp | tofs) ->
        m1_src |= mp1 ->
        m1 |= mp2 ** MP ->
        Mem.loadbytes m1_src sb sofs (sizeof_footprint ce ffp) = Some bytes ->
        Mem.storebytes m1 tb tofs bytes = Some m2 ->
        wt_footprint ce te ty ffp ->
        exists mass3, sem_wt_loc ce ffp tb tofs mass3 /\ m2 |= mass3 ** MP)
    (FWT: fields_loc_sep sb sofs (sem_wt_loc ce) fpl mass)
    (SORTED: fields_sorted ce fpl)
    (RANGE: massert_imp mp2 (range tb tofs (tofs + sz)))
    (SZPOS: 0 <= sz)
    (MPRED_SRC: m1_src |= mass)
    (MPRED: m1 |= mp2 ** MP)
    (LOAD: Mem.loadbytes m1_src sb sofs sz = Some bytes)
    (STORE: Mem.storebytes m1 tb tofs bytes = Some m2)
    (WF: Forall (fp_field_in_range ce sz (fields_fp_well_formed ce)) fpl)
    (WTFPS: Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) fpl)
    (ABS_ALIGN: Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + fofs))) fpl),
  exists mass3, fields_loc_sep tb tofs (sem_wt_loc ce) fpl mass3 /\ m2 |= mass3 ** MP.
Proof.
  intros.
  cut (forall n fpl, length fpl = n -> forall tb tofs sb sofs mass mp2 MP m1_src m1 m2 bytes te sz,
      (forall fid base fofs ffp, In (fid, ((base, fofs), ffp)) fpl -> forall tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te, sem_wt_loc ce ffp sb sofs mp1 -> massert_imp mp2 (range tb tofs (tofs + sizeof_footprint ce ffp)) -> (alignof_footprint ce ffp | tofs) -> m1_src |= mp1 -> m1 |= mp2 ** MP -> Mem.loadbytes m1_src sb sofs (sizeof_footprint ce ffp) = Some bytes -> Mem.storebytes m1 tb tofs bytes = Some m2 -> wt_footprint ce te ty ffp -> exists mass3, sem_wt_loc ce ffp tb tofs mass3 /\ m2 |= mass3 ** MP) ->
      fields_sorted ce fpl ->
      massert_imp mp2 (range tb tofs (tofs + sz)) ->
      0 <= sz ->
      m1_src |= mass ->
      m1 |= mp2 ** MP ->
      Mem.loadbytes m1_src sb sofs sz = Some bytes ->
      Mem.storebytes m1 tb tofs bytes = Some m2 ->
      Forall (fp_field_in_range ce sz (fields_fp_well_formed ce)) fpl ->
      Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) fpl ->
      Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + fofs))) fpl ->
      fields_loc_sep sb sofs (sem_wt_loc ce) fpl mass ->
      exists mass3, fields_loc_sep tb tofs (sem_wt_loc ce) fpl mass3 /\ m2 |= mass3 ** MP).
  { intros H. apply (H (length fpl) fpl eq_refl tb tofs sb sofs mass mp2 MP m1_src m1 m2 bytes te sz IH SORTED RANGE SZPOS MPRED_SRC MPRED LOAD STORE WF WTFPS ABS_ALIGN FWT). }
  clear - CONS NOREP.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros fpl HLEN tb tofs sb sofs mass mp2 MP m1_src m1 m2 bytes te sz IH SORTED RANGE SZPOS MPRED_SRC MPRED LOAD STORE WF WTFPS ABS_ALIGN FWT.
  destruct fpl as [| a l].
  - (* nil case *)
    exists STrue.
    split; [econstructor; reflexivity |].
    destruct RANGE as [RANGE_P RANGE_F].
    pose proof (RANGE_P m1 (proj1 MPRED)) as RANGE_M1. unfold range in RANGE_M1. simpl in RANGE_M1.
    destruct RANGE_M1 as [RP SZLE].
    assert (LEN_EQ: Z.of_nat (length bytes) = sz).
    { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
      apply Z2Nat.id. exact SZPOS. }
    assert (MPRED_MP: m1 |= MP).
    { eapply massert_imp_proj2. exact MPRED. }
    assert (MPRED_MP2: m2 |= MP).
    { eapply (m_invar MP). exact MPRED_MP.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros i IN. intro HF.
      destruct MPRED as [MP2PRED [MPPRED DISJ]].
      apply (DISJ tb i).
      - apply (RANGE_F tb i). simpl. split; [reflexivity | split].
        + exact (proj1 IN).
        + rewrite <- LEN_EQ. exact (proj2 IN).
      - exact HF. }
    rewrite <- (massert_eqv_STrue_l MP). exact MPRED_MP2.
  - (* cons case *)
    destruct a as [fid [[base fofs] ffp]].
    inversion FWT as [ | fid0 base0 fofs0 ffp0 l0 mass1 mass2 padmp0 mp0 IND FWT0 ALPERM EQV]; subst.
    pose (SIZE := sizeof_footprint ce ffp).
    pose (d := fofs + SIZE).
    inversion SORTED as [ | fid0 base0 fofs0 ffp0 l0 HBASE HLE HSIZE HEAD_AFTER]; subst.
    inversion WF as [| xwf lwf WFHEAD WFTAIL]; subst.
    inversion WFHEAD as [fidwf basewf fofswf ffpwf R1 R2 R3 R5]; subst.
    inversion WTFPS as [| xwt lwt WTHEAD WTTAIL]; subst.
    simpl in WTHEAD. destruct WTHEAD as [fty WTFP0].
    inversion ABS_ALIGN as [| xab lab ALHEAD ALTAIL]; subst.
    simpl in ALHEAD.
    assert (LEN_EQ: Z.of_nat (length bytes) = sz).
    { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
      apply Z2Nat.id. exact SZPOS. }
    pose proof (wt_footprint_size_eq ce fty ffp te WTFP0) as SIZEEQ.
    assert (SIZE_POS: 0 <= SIZE).
    { unfold SIZE. rewrite <- SIZEEQ. apply Z.ge_le. apply (sizeof_pos ce fty). }
    (* split the source loadbytes into padding / head field / tail *)
    assert (LOAD_EQ: Mem.loadbytes m1_src sb sofs (d + (sz - d)) = Some bytes).
    { replace (d + (sz - d)) with sz by lia. exact LOAD. }
    exploit (Mem.loadbytes_split m1_src sb sofs d (sz - d) bytes LOAD_EQ); [lia | lia |].
    intros (bytesA & bytesT & LOAD_A & LOAD_T & B_EQA).
    exploit (Mem.loadbytes_split m1_src sb sofs fofs SIZE bytesA LOAD_A); [lia | lia |].
    intros (bytesP & bytesH1 & LOAD_P & LOAD_H & B_EQP).
    assert (LENP: Z.of_nat (length bytesP) = fofs).
    { pose proof (Mem.loadbytes_length m1_src sb sofs fofs bytesP LOAD_P) as LEN.
      rewrite LEN. apply Z2Nat.id. lia. }
    assert (LENH: Z.of_nat (length bytesH1) = SIZE).
    { pose proof (Mem.loadbytes_length m1_src sb (sofs + fofs) SIZE bytesH1 LOAD_H) as LEN.
      rewrite LEN. apply Z2Nat.id. lia. }
    assert (B_EQ: bytes = bytesP ++ bytesH1 ++ bytesT).
    { rewrite B_EQA, B_EQP. rewrite app_assoc. reflexivity. }
    exploit (Mem.storebytes_split m1 tb tofs bytesP (bytesH1 ++ bytesT) m2).
    { rewrite <- B_EQ. exact STORE. }
    intros (m1p & STORE_P & STORE_HT).
    rewrite LENP in STORE_HT.
    exploit (Mem.storebytes_split m1p tb (tofs + fofs) bytesH1 bytesT m2).
    { exact STORE_HT. }
    intros (m1' & STORE_H & STORE_T).
    rewrite LENH in STORE_T.
    replace (tofs + fofs + SIZE) with (tofs + d) in STORE_T by (unfold d; lia).
    (* source field predicate *)
    assert (MPRED_SRC_HEAD: m1_src |= mass1).
    { rewrite EQV in MPRED_SRC.
      rewrite Z.add_0_r in MPRED_SRC.
      apply (massert_imp_proj1 mass1 mass2).
      apply (massert_imp_proj2 (range sb sofs (sofs + fofs)) (mass1 ** mass2)).
      exact MPRED_SRC. }
    (* target permission for the head field *)
    assert (MPRED_RANGE0: m1 |= range tb tofs (tofs + sz) ** MP).
    { eapply sep_imp; [exact MPRED | exact RANGE | apply massert_imp_refl]. }
    assert (MPRED_RANGE1: m1 |= range tb tofs (tofs + fofs) ** range tb (tofs + fofs) (tofs + sz) ** MP).
    { eapply range_split; [lia | exact MPRED_RANGE0]. }
    assert (MPRED_RANGE2: m1 |= range tb tofs (tofs + fofs) ** range tb (tofs + fofs) (tofs + d) ** range tb (tofs + d) (tofs + sz) ** MP).
    { eapply sep_imp; [exact MPRED_RANGE1 | apply massert_imp_refl |].
      apply (range_split_imp tb (tofs + fofs) (tofs + d) (tofs + sz) MP). unfold d, SIZE in *. lia. }
    assert (MP_DISJ_RANGE: forall i, tofs <= i < tofs + sz -> ~ m_footprint MP tb i).
    { intros i IN. intro HF.
      destruct MPRED as [MP2PRED [MPPRED DISJ]].
      destruct RANGE as [RANGE_P RANGE_F].
      apply (DISJ tb i).
      - apply (RANGE_F tb i). simpl. split; [reflexivity | exact IN].
      - exact HF. }
    set (FRAME := range tb (tofs + d) (tofs + sz) ** MP).
    assert (MPRED_HEAD: m1 |= range tb (tofs + fofs) (tofs + d) ** (range tb tofs (tofs + fofs) ** FRAME)).
    { unfold FRAME.
      rewrite <- (sep_swap (range tb tofs (tofs + fofs)) (range tb (tofs + fofs) (tofs + d))
                       (range tb (tofs + d) (tofs + sz) ** MP)).
      exact MPRED_RANGE2. }
    assert (STORE_H_FROM_M1: exists m2h, Mem.storebytes m1 tb (tofs + fofs) bytesH1 = Some m2h).
    { edestruct (Mem.range_perm_storebytes m1 tb (tofs + fofs) bytesH1) as [m2h STOREH].
      - red. intros i IN.
        destruct MPRED_HEAD as [MPRED_HEAD_R _].
        eapply Mem.perm_implies.
        * eapply MPRED_HEAD_R. simpl. split; [lia |]. rewrite LENH in IN. unfold d, SIZE in *. lia.
        * constructor.
      - eexists. exact STOREH. }
    destruct STORE_H_FROM_M1 as [m2h STOREH].
    assert (FIELD: exists massA, sem_wt_loc ce ffp tb (tofs + fofs) massA /\                m2h |= massA ** (range tb tofs (tofs + fofs) ** FRAME)).
    { eapply (IH fid 0 fofs ffp (or_introl eq_refl)).
      - exact FWT0.
      - apply (range_impl tb (tofs + fofs) (tofs + d) (tofs + fofs) (tofs + fofs + SIZE)); [lia | unfold d, SIZE in *; lia].
      - exact ALHEAD.
      - exact MPRED_SRC_HEAD.
      - exact MPRED_HEAD.
      - exact LOAD_H.
      - exact STOREH.
      - exact WTFP0. }
    destruct FIELD as [massA WTLOCA_MPREDA]; destruct WTLOCA_MPREDA as [WTLOCA MPREDA].
    assert (MPREDA_M1: m1' |= massA).
    { apply (m_invar massA) with (m := m2h) (m' := m1').
      - exact (sep_proj1 _ _ _ MPREDA).
      - eapply (storebytes_prefix_unchanged m1 m1p m2h m1' tb tofs fofs bytesP bytesH1 LENP STORE_P STOREH STORE_H (m_footprint massA)).
        intros b0 ofs0 FOOT. intro HCONTR.
        eapply MPREDA. eauto. simpl. left. auto. }
    destruct MPREDA as [_ [_ DISJ_MASSA_FRAME]].
    (* tail recursion setup *)
    assert (IND_SHIFT: fields_loc_sep sb (sofs + d) (sem_wt_loc ce) (map (shift_ffp d) l) mass2).
    { apply (fields_loc_sep_shift sb sofs (sem_wt_loc ce) d l mass2). exact IND. }
    assert (HEAD_AFTER_DLE: Forall (fun '(fid', ((base', fofs'), ffp')) => d <= fofs') l).
    { exact (fields_after_d_le ce d l HEAD_AFTER). }
    assert (WF_TAIL: Forall (fp_field_in_range ce (sz - d) (fields_fp_well_formed ce)) (map (shift_ffp d) l)).
    { exact (Forall_range_shift ce sz d (fields_fp_well_formed ce) l HEAD_AFTER_DLE WFTAIL). }
    assert (ABS_ALIGN_TAIL: Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | ((tofs + d) + fofs))) (map (shift_ffp d) l)).
    { exact (Forall_align_shift ce tofs d l ALTAIL). }
    assert (WTFPS_TAIL: Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) (map (shift_ffp d) l)).
    { exact (Forall_wtfootprint_shift ce te d l WTTAIL). }
    assert (SORTED_TAIL: fields_sorted ce (map (shift_ffp d) l)).
    { unfold fields_sorted. replace 0 with (d - d) by lia.
      exact (fields_after_shift ce d d l HEAD_AFTER). }
    assert (MPRED_SRC_TAIL: m1_src |= mass2).
    { rewrite EQV in MPRED_SRC.
      rewrite Z.add_0_r in MPRED_SRC.
      rewrite <- sep_assoc in MPRED_SRC.
      apply (massert_imp_proj2 (range sb sofs (sofs + fofs) ** mass1) mass2).
      exact MPRED_SRC. }
    (* target permission for the tail *)
    assert (MPRED_RANGE_DROP: m1 |= range tb tofs (tofs + fofs) ** range tb (tofs + d) (tofs + sz) ** MP).
    { eapply sep_imp; [exact MPRED_RANGE2 | apply massert_imp_refl | apply massert_imp_proj2]. }
    assert (MPRED_RANGE_DROP_M1P: m1p |= range tb tofs (tofs + fofs) ** (range tb (tofs + d) (tofs + sz) ** MP)).
    { eapply sep_preserved. exact MPRED_RANGE_DROP.
      - intros H. eapply storebytes_range_unchanged; eauto.
      - intros H. eapply (m_invar (range tb (tofs + d) (tofs + sz) ** MP)). exact H.
        eapply Mem.storebytes_unchanged_on; eauto.
        intros i INP. intro HF.
        destruct MPRED_RANGE_DROP as [MPRED_PAD [MPRED_TAILMP DISJ]].
        exact (DISJ tb i ltac:(simpl; split; [reflexivity |]; rewrite <- LENP; exact INP) HF). }
    assert (MPRED_RANGE_DROP_M1': m1' |= range tb tofs (tofs + fofs) ** (range tb (tofs + d) (tofs + sz) ** MP)).
    { eapply sep_preserved. exact MPRED_RANGE_DROP_M1P.
      - intros H. eapply (m_invar (range tb tofs (tofs + fofs))). exact H.
        eapply Mem.storebytes_unchanged_on; eauto.
        intros i INP. intro HF.
        simpl in HF. destruct HF as [HEQ HRANGE]. lia.
      - intros H. eapply (m_invar (range tb (tofs + d) (tofs + sz) ** MP)). exact H.
        eapply Mem.storebytes_unchanged_on; eauto.
        intros i INP. intro HF.
        destruct HF as [HFT | HFMP].
        + rewrite LENH in INP. unfold d, SIZE in *. simpl in HFT. destruct HFT as [HEQ HRANGE]. lia.
        + exact (MP_DISJ_RANGE i ltac:(rewrite LENH in INP; unfold d, SIZE in *; lia) HFMP). }
    assert (MPRED_MASSA_FRAME: m1' |= massA ** (range tb tofs (tofs + fofs) ** range tb (tofs + d) (tofs + sz) ** MP)).
    { change (m_pred massA m1' /\ m_pred (range tb tofs (tofs + fofs) ** range tb (tofs + d) (tofs + sz) ** MP) m1' /\ disjoint_footprint massA (range tb tofs (tofs + fofs) ** range tb (tofs + d) (tofs + sz) ** MP)).
      split.
      - exact MPREDA_M1.
      - split.
        * exact MPRED_RANGE_DROP_M1'.
        * exact DISJ_MASSA_FRAME. }
    assert (MPRED_TAIL: m1' |= range tb (tofs + d) (tofs + sz) ** (range tb tofs (tofs + fofs) ** massA ** MP)).
    { rewrite (sep_swap3 massA (range tb tofs (tofs + fofs)) (range tb (tofs + d) (tofs + sz)) MP) in MPRED_MASSA_FRAME.
      exact MPRED_MASSA_FRAME. }
    assert (SZPOS_TAIL: 0 <= sz - d). { unfold d, SIZE in *. lia. }
    pose (IH_l := fun (fid0: ident) (base0 fofs0: Z) (ffp0: footprint)
                      (IN0: In (fid0, ((base0, fofs0), ffp0)) (map (shift_ffp d) l)) =>
                    IH fid0 (base0 + d) (fofs0 + d) ffp0
                       (or_intror (in_map_shift_ffp_inv d l fid0 base0 fofs0 ffp0 IN0))).
    assert (TAIL: exists mass3_tail, fields_loc_sep tb (tofs + d) (sem_wt_loc ce) (map (shift_ffp d) l) mass3_tail
                    /\ m2 |= mass3_tail ** (range tb tofs (tofs + fofs) ** massA ** MP)).
    { apply (IHn (length l) (Nat.lt_succ_diag_r (length l)) (map (shift_ffp d) l) (map_length (shift_ffp d) l) tb (tofs + d) sb (sofs + d) mass2 (range tb (tofs + d) (tofs + sz)) (range tb tofs (tofs + fofs) ** massA ** MP) m1_src m1' m2 bytesT te (sz - d) IH_l SORTED_TAIL (range_impl tb (tofs + d) (tofs + sz) (tofs + d) ((tofs + d) + (sz - d)) ltac:(lia) ltac:(lia)) SZPOS_TAIL MPRED_SRC_TAIL MPRED_TAIL LOAD_T STORE_T WF_TAIL WTFPS_TAIL ABS_ALIGN_TAIL IND_SHIFT). }
    destruct TAIL as [mass3_tail WTLOC_TAIL_MPRED]; destruct WTLOC_TAIL_MPRED as [WTLOC_TAIL MPRED_TAIL2].
    assert (WTLOC_TAIL0: fields_loc_sep tb tofs (sem_wt_loc ce) l mass3_tail).
    { rewrite <- (shift_ffp_involutive d l).
      replace tofs with (tofs + d - d) by lia.
      apply (fields_loc_sep_shift tb (tofs + d) (sem_wt_loc ce) (- d) (map (shift_ffp d) l) mass3_tail).
      exact WTLOC_TAIL. }
    exists (range tb tofs (tofs + fofs) ** massA ** mass3_tail).
    split; [ apply (fields_loc_sep_cons tb tofs (sem_wt_loc ce) fid 0 fofs ffp l massA mass3_tail (range tb tofs (tofs + fofs)) (range tb tofs (tofs + fofs) ** massA ** mass3_tail) WTLOC_TAIL0 WTLOCA); [rewrite Z.add_0_r; reflexivity | apply massert_eqv_refl]
            | rewrite sep_assoc; rewrite sep_assoc; rewrite (sep_swap (range tb tofs (tofs + fofs)) massA (mass3_tail ** MP)); rewrite <- (sep_swap3 mass3_tail (range tb tofs (tofs + fofs)) massA MP); exact MPRED_TAIL2 ].
Qed.

(* We need to say that sem_wt_loc is readable/storable/freeable *)

Lemma range_empty_sep_l: forall P b ofs,
    0 <= ofs -> ofs <= Ptrofs.modulus ->
    massert_eqv (range b ofs ofs ** P) P.
Proof.
  intros P b ofs BOUND1 BOUND2. split.
  - apply (massert_imp_proj2 (range b ofs ofs) P).
  - red; split.
    + intros m HP. split; [| split].
      * simpl. split; [lia | split; [lia |]]. intros i k p IN. lia.
      * exact HP.
      * red; simpl; intros b0 ofs0 [EQ [LO HI]]. lia.
    + intros b0 ofs0 HF. simpl in HF. destruct HF as [HF1 | HF2].
      * destruct HF1 as [EQ [LO HI]]. lia.
      * exact HF2.
Qed.

Lemma storebytes_scalar_sem_wt_loc ce: forall chunk v tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes,
    (align_chunk chunk | tofs) ->
    sem_wt_loc ce (fp_scalar chunk v) sb sofs mp1 ->
    massert_imp mp2 (range tb tofs (tofs + size_chunk chunk)) ->
    m1_src |= mp1 ->
    m1 |= mp2 ** MP ->
    Mem.loadbytes m1_src sb sofs (size_chunk chunk) = Some bytes ->
    Mem.storebytes m1 tb tofs bytes = Some m2 ->
    exists mass3, sem_wt_loc ce (fp_scalar chunk v) tb tofs mass3 /\ m2 |= mass3 ** MP.
Proof.
  intros chunk v tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ALIGN SRC_LOC TGT_LOC_PERM MPRED_SRC MPRED LOAD STORE.
  inv SRC_LOC.
  assert (LEN_EQ: Z.of_nat (length bytes) = size_chunk chunk).
  { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN. apply Z2Nat.id. pose proof (size_chunk_pos chunk). lia. }
  assert (MPRED_HAS: m1_src |= hasvalue chunk sb sofs v).
  { rewrite EQV in MPRED_SRC. exact MPRED_SRC. }
  exploit load_rule. exact MPRED_HAS. intros (vload & LOAD1 & HVEQ).
  exploit Mem.load_loadbytes; eauto. intros (bytes' & LB' & VEQBYTES).
  rewrite LOAD in LB'. injection LB' as Hbytes; subst bytes.
  assert (MPRED_RANGE: m1 |= range tb tofs (tofs + size_chunk chunk) ** MP).
  { eapply sep_imp; [exact MPRED | exact TGT_LOC_PERM | apply massert_imp_refl]. }
  assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + size_chunk chunk) ** MP).
  { eapply sep_preserved. exact MPRED_RANGE.
    - intros H1. eapply storebytes_range_unchanged; eauto.
    - intros HMP. eapply (m_invar MP). exact HMP.
      eapply Mem.storebytes_unchanged_on; eauto.
      intros i IN. intro HF.
      destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
      destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
      apply (DISJ tb i).
      * unfold range in TGTRANGE_FP. apply (TGTRANGE_FP tb i). simpl. split; auto. rewrite <- LEN_EQ. exact IN.
      * exact HF. }
  assert (LOAD2: Mem.load chunk m2 tb tofs = Some (decode_val chunk bytes')).
  { eapply Mem.loadbytes_load.
    - rewrite <- LEN_EQ. eapply Mem.loadbytes_storebytes_same; eauto.
    - exact ALIGN. }
  exists (hasvalue chunk tb tofs v).
  split.
  econstructor. reflexivity.
  eapply range_hasvalue.
  exact MPRED_RANGE2.
  rewrite <- VEQBYTES in LOAD2. rewrite HVEQ in LOAD2. exact LOAD2.
Qed.

Lemma wt_struct_fields_in_range ce te: forall id fpl co,
    composite_env_consistent ce ->
    (forall id0 co0, ce ! id0 = Some co0 -> list_norepet (name_members (co_members co0))) ->
    ce ! id = Some co ->
    co_sv co = Struct ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) ->
    Forall (fp_field_in_range ce (sizeof_struct_comp ce id) (fields_fp_well_formed ce)) fpl.
Proof.
  intros id fpl co CONS NOREP CO STRUCT MATCH.
  apply Forall_forall. intros x IN. destruct x as [fid [[base fofs] ffp]]. simpl.
  apply In_nth_error in IN as (n & NTHF).
  destruct (Forall2_nth ffpty member (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) n (fid, ((base, fofs), ffp)) MATCH NTHF) as (m & NTHM & MATCH1).
  inv MATCH1.
  apply nth_error_In in NTHM as INM.
  assert (FTY: field_type fid (co_members co) = OK fty).
  { eapply field_noalign_offset_In_field_type.
    - apply (NOREP id co CO).
    - exact INM.
    - exact FOFS. }
  pose proof (field_noalign_offset_range_aligned ce fid (co_members co) base fofs fty FOFS FTY) as RANGE.
  destruct RANGE as [BASELE [ZR [RANGESZ ALIGNF]]].
  pose proof (wt_footprint_size_eq ce fty ffp te WTFP) as SIZEEQ.
  pose proof (wt_footprint_fields_well_formed ce te fty ffp CONS NOREP WTFP) as WF_FFP.
  apply fp_field_in_range_intro.
  - exact BASELE.
  - exact ZR.
  - rewrite <- SIZEEQ. unfold sizeof_struct_comp. rewrite CO. rewrite STRUCT. exact RANGESZ.
  - exact WF_FFP.
Qed.

Lemma wt_struct_fields_in_range_aligned ce te: forall id fpl co,
    composite_env_consistent ce ->
    (forall id0 co0, ce ! id0 = Some co0 -> list_norepet (name_members (co_members co0))) ->
    ce ! id = Some co ->
    co_sv co = Struct ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) ->
    Forall (fp_field_in_range_aligned ce (sizeof_struct_comp ce id) (alignof_comp ce id) (fields_fp_well_formed ce)) fpl.
Proof.
  intros id fpl co CONS NOREP CO STRUCT MATCH.
  apply Forall_forall. intros x IN. destruct x as [fid [[base fofs] ffp]]. simpl.
  apply In_nth_error in IN as (n & NTHF).
  destruct (Forall2_nth ffpty member (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) n (fid, ((base, fofs), ffp)) MATCH NTHF) as (m & NTHM & MATCH1).
  inv MATCH1.
  apply nth_error_In in NTHM as INM.
  assert (FTY: field_type fid (co_members co) = OK fty).
  { eapply field_noalign_offset_In_field_type.
    - apply (NOREP id co CO).
    - exact INM.
    - exact FOFS. }
  pose proof (field_noalign_offset_range_aligned ce fid (co_members co) base fofs fty FOFS FTY) as RANGE.
  destruct RANGE as [BASELE [ZR [RANGESZ ALIGNF]]].
  pose proof (wt_footprint_size_eq ce fty ffp te WTFP) as SIZEEQ.
  pose proof (wt_footprint_align_divides ce fty ffp te WTFP) as ALIGNDIV.
  pose proof (wt_footprint_fields_well_formed ce te fty ffp CONS NOREP WTFP) as WF_FFP.
  pose proof (field_noalign_offset_base_nonneg ce fid (co_members co) base fofs FOFS) as BASENN.
  apply fp_field_in_range_aligned_intro.
  - exact BASENN.
  - exact BASELE.
  - exact ZR.
  - rewrite <- SIZEEQ. unfold sizeof_struct_comp. rewrite CO. rewrite STRUCT. exact RANGESZ.
  - apply Z.divide_trans with (alignof ce fty); auto.
  - exact WF_FFP.
Qed.

Lemma struct_fields_abs_align ce te: forall id fpl co tofs,
    composite_env_consistent ce ->
    (forall id0 co0, ce ! id0 = Some co0 -> list_norepet (name_members (co_members co0))) ->
    ce ! id = Some co ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) ->
    (alignof_comp ce id | tofs) ->
    Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + fofs))) fpl.
Proof.
  intros id fpl co tofs CONS NOREP CO MATCH AL_TOFS.
  apply Forall_forall. intros x IN. destruct x as [fid [[base fofs] ffp]]. simpl.
  apply In_nth_error in IN as (n & NTHF).
  destruct (Forall2_nth ffpty member (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) n (fid, ((base, fofs), ffp)) MATCH NTHF) as (m & NTHM & MATCH1).
  inv MATCH1.
  apply nth_error_In in NTHM as INM.
  assert (FTY: field_type fid (co_members co) = OK fty).
  { eapply field_noalign_offset_In_field_type.
    - apply (NOREP id co CO).
    - exact INM.
    - exact FOFS. }
  pose proof (wt_footprint_align_divides ce fty ffp te WTFP) as ALIGNDIV.
  pose proof (field_noalign_offset_range_aligned ce fid (co_members co) base fofs fty FOFS FTY) as RANGE.
  destruct RANGE as [_ [_ [_ ALIGNF]]].
  pose proof (field_alignof_divide_composite fty fid co ce FTY) as ALIGNDIV2.
  destruct (CONS id co CO) as [_ ALIGNC _ _].
  assert (ALIGN_ALOF: (alignof_footprint ce ffp | alignof_comp ce id)).
  { eapply Z.divide_trans; [exact ALIGNDIV |].
    eapply Z.divide_trans; [exact ALIGNDIV2 |].
    rewrite <- ALIGNC. unfold alignof_comp. rewrite CO. apply Z.divide_refl. }
  assert (ALIGN_TOFS: (alignof_footprint ce ffp | tofs)).
  { eapply Z.divide_trans; [exact ALIGN_ALOF | exact AL_TOFS]. }
  assert (ALIGN_FOFS: (alignof_footprint ce ffp | fofs)).
  { eapply Z.divide_trans; [exact ALIGNDIV | exact ALIGNF]. }
  eapply Z.divide_add_r; [exact ALIGN_TOFS | exact ALIGN_FOFS].
Qed.




(* [field_noalign_offset_rec] skips over the head member, shifting the bit
   position by [next_field]. *)
Lemma field_noalign_offset_rec_skip ce: forall fid fty m ms pos,
    list_norepet (name_members (m :: ms)) ->
    In (Member_plain fid fty) ms ->
    field_noalign_offset_rec ce fid (m :: ms) pos =
    field_noalign_offset_rec ce fid ms (next_field ce pos m).
Proof.
  intros fid fty m ms pos NOREP IN.
  destruct m as [mid mty].
  simpl.
  change (name_member (Member_plain mid mty)) with mid.
  destruct (ident_eq fid mid) as [EQ | NEQ].
  - subst fid. exfalso.
    inversion NOREP as [| ? ? HNH HNT]; subst.
    apply HNH. unfold name_members. rewrite in_map_iff. exists (Member_plain mid fty); split; [reflexivity | exact IN].
  - simpl. reflexivity.
Qed.

(* Destructure the head of an [fp_match_field] relation with the exact
   constructor fields. *)
Lemma fp_match_field_head ce co P fp m:
    fp_match_field ce co P fp m ->
    exists fid base fofs ffp fty,
      fp = (fid, ((base, fofs), ffp)) /\
      m = Member_plain fid fty /\
      field_noalign_offset ce fid (co_members co) = OK (base, fofs) /\
      P fty ffp.
Proof.
  inversion 1; subst.
  do 5 eexists. repeat split; eauto.
Qed.

Lemma fp_match_field_fields_sorted_aux ce co te:
  forall fpl ms pos,
    list_norepet (name_members ms) ->
    (8 | pos) ->
    (forall fid fty, In (Member_plain fid fty) ms ->
        field_noalign_offset_rec ce fid ms pos = field_noalign_offset ce fid (co_members co)) ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl ms ->
    fields_after ce (pos / 8) fpl.
Proof.
  induction fpl as [| fp fpl' IH]; intros ms pos NOREP DIV HCONT MATCH.
  - inversion MATCH; subst. apply fields_after_nil.
  - destruct ms as [| m ms']; [inversion MATCH |].
    inv MATCH.
    destruct (fp_match_field_head ce co (wt_footprint ce te) fp m H2) as (fid & base & fofs & ffp & fty & EQFP & EQM & FOFS & WTFP); subst.
    (* Head offset computed at [pos] over [m :: ms'] equals the full offset. *)
    pose proof (HCONT fid fty (or_introl eq_refl)) as HC.
    rewrite FOFS in HC.
    (* Extract the head layout and [base = pos / 8]. *)
    pose proof (field_noalign_offset_rec_field_offset_rec ce fid (Member_plain fid fty :: ms') pos base fofs HC) as [_ LE].
    unfold field_noalign_offset_rec in HC.
    change (name_member (Member_plain fid fty)) with fid in HC.
    destruct (ident_eq fid fid) as [EQ | NEQ].
    + destruct (layout_field ce pos (Member_plain fid fty)) as [z|] eqn:L; try discriminate.
      inversion HC; subst.
      eapply fields_after_cons.
      * reflexivity.
      * exact LE.
      * pose proof (wt_footprint_size_eq ce fty ffp te WTFP) as SIZEEQ.
        pose proof (sizeof_pos ce fty) as SZPOS. lia.
      * (* tail *)
        assert (DIVP: Z.divide 8 (next_field ce pos (Member_plain fid fty))) by (apply next_field_div8).
        assert (NOREP_T: list_norepet (name_members ms')).
        { inversion NOREP as [| ? ? HNH HNT]; subst. exact HNT. }
        assert (HCONT': forall fid0 fty0, In (Member_plain fid0 fty0) ms' ->
            field_noalign_offset_rec ce fid0 ms' (next_field ce pos (Member_plain fid fty)) =
            field_noalign_offset ce fid0 (co_members co)).
        { intros fid0 fty0 IN0.
          pose proof (HCONT fid0 fty0 (or_intror IN0)) as HC0.
          rewrite (field_noalign_offset_rec_skip ce fid0 fty0 (Member_plain fid fty) ms' pos NOREP IN0) in HC0.
          exact HC0. }
        assert (SIZEEQ': next_field ce pos (Member_plain fid fty) / 8 = fofs + sizeof_footprint ce ffp).
        { rewrite (next_field_div ce pos (Member_plain fid fty) fofs L).
          change (type_member (Member_plain fid fty)) with fty.
          rewrite <- (wt_footprint_size_eq ce fty ffp te WTFP). reflexivity. }
        pose proof (IH ms' (next_field ce pos (Member_plain fid fty)) NOREP_T DIVP HCONT' H4) as IH_T.
        rewrite SIZEEQ' in IH_T. exact IH_T.
    + exfalso. apply NEQ. reflexivity.
Qed.

Lemma fp_match_field_fields_sorted_strong ce co te: forall fpl,
    list_norepet (name_members (co_members co)) ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl (co_members co) ->
    fields_sorted ce fpl.
Proof.
  intros fpl NOREP MATCH.
  unfold fields_sorted.
  assert (DIV: Z.divide 8 0) by (exists 0; ring).
  assert (HCONT: forall fid fty, In (Member_plain fid fty) (co_members co) ->
      field_noalign_offset_rec ce fid (co_members co) 0 =
      field_noalign_offset ce fid (co_members co)).
  { intros fid fty IN. unfold field_noalign_offset. reflexivity. }
  pose proof (fp_match_field_fields_sorted_aux ce co te fpl (co_members co) 0 NOREP DIV HCONT MATCH) as H.
  simpl in H. exact H.
Qed.


Lemma storebytes_sem_wt_loc_fp ce: forall sfp tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (SRC_LOC: sem_wt_loc ce sfp sb sofs mp1)
    (TGT_LOC_PERM: massert_imp mp2 (range tb tofs (tofs + sizeof ce ty)))
    (AL: (alignof_footprint ce sfp | tofs))
    (* Since (sb, sofs) may be overlapped with the footprint of (mp2
    ** MP), we cannot show their disjointness. We only require that
    the source location is semantically well-typed in m1_src, i.e.,
    m1_src |= mp1, so that the value loaded from (sb, sofs) is
    well-typed.  The source memory m1_src is where we load the bytes,
    and m1 is where we store them; in practice they are the same
    memory at the top level but differ when we store into a field of
    a struct while loading the bytes from the original source. *)
    (* (MPRED_IMP: massert_imp (mp2 ** MP) mp1) *)
    (MPRED_SRC: m1_src |= mp1)
    (MPRED: m1 |= mp2 ** MP)
    (LOAD: Mem.loadbytes m1_src sb sofs (sizeof ce ty) = Some bytes)
    (* since (sb, sofs) is sem_wt_loc, the progress of storebytes is
    straightforward *)
    (STORE: Mem.storebytes m1 tb tofs bytes = Some m2)
    (* Well formedness of sfp. The most important property is that
    this well-formedness should imply that the permission of sfp cover
    its the location of its size. *)
    (WTFP: wt_footprint ce te ty sfp),
  exists (mass3 : massert),
      sem_wt_loc ce sfp tb tofs mass3 /\ m2 |= mass3 ** MP.
Proof.
  intros sfp tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te CONS NOREP SRC_LOC TGT_LOC_PERM AL MPRED_SRC MPRED LOAD STORE WTFP.
  revert tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te SRC_LOC TGT_LOC_PERM AL MPRED_SRC MPRED LOAD STORE WTFP.
  induction sfp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b2 ofs2 ph vs] using strong_footprint_ind;
    intros tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te SRC_LOC TGT_LOC_PERM AL MPRED_SRC MPRED LOAD STORE WTFP; inv SRC_LOC.
  - inv WTFP.
  - inv WTFP. simpl in AL.
    assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce ty).
    { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
      apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }
    exists ((range tb tofs (tofs + sizeof ce ty)) ** (spure (alignof ce ty | tofs))).
    split. econstructor. reflexivity.
    assert (MPRED_RANGE: m1 |= range tb tofs (tofs + sizeof ce ty) ** MP).
    { eapply sep_imp.
      - exact MPRED.
      - exact TGT_LOC_PERM.
      - apply massert_imp_refl. }
    assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + sizeof ce ty) ** MP).
    { eapply sep_preserved. exact MPRED_RANGE.
      - intros H1. eapply storebytes_range_unchanged; eauto.
      - intros HMP. eapply (m_invar MP).
        + exact HMP.
        + eapply Mem.storebytes_unchanged_on; eauto.
          intros i IN. intro HF.
          destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
          destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
          apply (DISJ tb i).
          * unfold range in TGTRANGE_FP.
            apply (TGTRANGE_FP tb i). simpl. split; auto.
            rewrite <- LEN_EQ. exact IN.
          * exact HF. }
    rewrite (massert_eqv_prop_l MP (alignof ce ty | tofs) AL) in MPRED_RANGE2.
    rewrite <- sep_assoc in MPRED_RANGE2.
    exact MPRED_RANGE2.
  - inv WTFP.
    assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce ty).
    { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
      apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }
    assert (MPRED_HAS: m1_src |= hasvalue chunk sb sofs v).
    { rewrite EQV in MPRED_SRC. exact MPRED_SRC. }
    exploit load_rule. exact MPRED_HAS. intros (vload & LOAD1 & HVEQ).
    exploit Mem.load_loadbytes; eauto. intros (bytes' & LB' & VEQBYTES).
    rewrite (sizeof_by_value ce ty chunk MODE) in LB'.
    rewrite LOAD in LB'. inv LB'.
    assert (ALIGN: (align_chunk chunk | tofs)).
    { simpl in AL. exact AL. }
    assert (MPRED_RANGE: m1 |= range tb tofs (tofs + size_chunk chunk) ** MP).
    { eapply sep_imp.
      - exact MPRED.
      - rewrite (sizeof_by_value ce ty chunk MODE). exact TGT_LOC_PERM.
      - apply massert_imp_refl. }
    assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + size_chunk chunk) ** MP).
    { eapply sep_preserved. exact MPRED_RANGE.
      - intros H1. eapply storebytes_range_unchanged; eauto.
      - intros HMP. eapply (m_invar MP).
        + exact HMP.
        + eapply Mem.storebytes_unchanged_on; eauto.
          intros i IN. intro HF.
          destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
          destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
          unfold range in TGTRANGE_FP.
          apply (DISJ tb i).
          * apply (TGTRANGE_FP tb i). simpl. split; auto.
            rewrite <- LEN_EQ. exact IN.
          * exact HF. }
    assert (LOAD2: Mem.load chunk m2 tb tofs = Some (decode_val chunk bytes')).
    { eapply Mem.loadbytes_load.
      - rewrite (sizeof_by_value ce ty chunk MODE). rewrite <- LEN_EQ.
        eapply Mem.loadbytes_storebytes_same; eauto.
      - exact ALIGN. }
    exists (hasvalue chunk tb tofs (decode_val chunk bytes')).
    split.
    econstructor. reflexivity.
    eapply range_hasvalue.
    exact MPRED_RANGE2.
    exact LOAD2.
  - inv WTFP.
    assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce (Tbox ty0)).
    { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
      apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }
    assert (MPRED_HAS: m1_src |= hasvalue Mptr sb sofs (Vptr b1 Ptrofs.zero) ** box_pred ce fp1 b1 nextmp).
    { rewrite EQV in MPRED_SRC. exact MPRED_SRC. }
    assert (MPRED_PTR: m1_src |= hasvalue Mptr sb sofs (Vptr b1 Ptrofs.zero)).
    { eapply massert_imp_proj1. exact MPRED_HAS. }
    assert (MPRED_BOX: m1_src |= box_pred ce fp1 b1 nextmp).
    { eapply massert_imp_proj2. exact MPRED_HAS. }
    exploit load_rule. exact MPRED_PTR. intros (vload & LOAD1 & HVEQ).
    exploit Mem.load_loadbytes; eauto. intros (bytes'' & LB'' & VEQBYTES).
    rewrite (sizeof_by_value ce (Tbox ty0) Mptr (eq_refl)) in LB''.
    rewrite LOAD in LB''. inv LB''.
    assert (ALIGN: (align_chunk Mptr | tofs)).
    { simpl in AL. exact AL. }
    assert (MPRED_RANGE: m1 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
    { eapply sep_imp.
      - exact MPRED.
      - rewrite (sizeof_by_value ce (Tbox ty0) Mptr (eq_refl)). exact TGT_LOC_PERM.
      - apply massert_imp_refl. }
    assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
    { eapply sep_preserved. exact MPRED_RANGE.
      - intros H1. eapply storebytes_range_unchanged; eauto.
      - intros HMP. eapply (m_invar MP).
        + exact HMP.
        + eapply Mem.storebytes_unchanged_on; eauto.
          intros i IN. intro HF.
          destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
          destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
          unfold range in TGTRANGE_FP.
          apply (DISJ tb i).
          * apply (TGTRANGE_FP tb i). simpl. split; auto.
            unfold sizeof in LEN_EQ. rewrite <- LEN_EQ. exact IN.
          * exact HF. }
    assert (LOAD2: Mem.load Mptr m2 tb tofs = Some (decode_val Mptr bytes'')).
    { eapply Mem.loadbytes_load.
      - rewrite (sizeof_by_value ce (Tbox ty0) Mptr (eq_refl)). rewrite <- LEN_EQ.
        eapply Mem.loadbytes_storebytes_same; eauto.
      - exact ALIGN. }
    assert (VEQ: Vptr b1 Ptrofs.zero = decode_val Mptr bytes'').
    { exact VEQBYTES. }
    assert (MPRED_BOX2: m2 |= box_pred ce fp1 b1 nextmp).
    { admit. }
    exists (hasvalue Mptr tb tofs (Vptr b1 Ptrofs.zero) ** box_pred ce fp1 b1 nextmp).
    split.
    eapply (sem_wt_box ce tb tofs fp1 b1 nextmp (hasvalue Mptr tb tofs (Vptr b1 Ptrofs.zero) ** box_pred ce fp1 b1 nextmp)).
    admit.
    admit.
    (* exact WTLOC. *)
    (* reflexivity. *)
    admit.

  - (* fp_struct *)
    inv WTFP.
    assert (SIZEEQ: sizeof ce (Tstruct orgs id) = sizeof_comp ce id).
    { unfold sizeof, sizeof_comp. rewrite CO. reflexivity. }
    rewrite SIZEEQ in LOAD. rewrite SIZEEQ in TGT_LOC_PERM.
    simpl in AL.
    set (SSTR := sizeof_struct_comp ce id).
    assert (SZPOS: 0 <= SSTR).
    { unfold SSTR, sizeof_struct_comp. rewrite CO. rewrite STRUCT. change (0 <= sizeof_composite ce Struct (co_members co)). apply sizeof_composite_pos. }
    assert (SZLE: SSTR <= sizeof_comp ce id).
    { unfold SSTR, sizeof_struct_comp, sizeof_comp. rewrite CO. rewrite STRUCT.
      destruct (CONS id co CO) as [_ _ SZC _].
      rewrite STRUCT in SZC. rewrite SZC. unfold sizeof_composite. apply align_le. apply co_alignof_pos. }
    assert (SORTED: fields_sorted ce fpl).
    { eapply fp_match_field_fields_sorted_strong; eauto. }
    assert (WF_SSTR: Forall (fp_field_in_range ce SSTR (fields_fp_well_formed ce)) fpl).
    { unfold SSTR. eapply wt_struct_fields_in_range; eauto. }
    assert (WF_SSTR_ALIGNED: Forall (fp_field_in_range_aligned ce SSTR (alignof_comp ce id) (fields_fp_well_formed ce)) fpl).
    { unfold SSTR. eapply wt_struct_fields_in_range_aligned; eauto. }
    assert (WTFPS: Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) fpl).
    { apply Forall_forall. intros x IN. destruct x as [fid [[base fofs] ffp]]. simpl.
      eapply fp_match_field_In_wt; eauto. }
    assert (ABS_ALIGN: Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + fofs))) fpl).
    { eapply struct_fields_abs_align; eauto. }
    assert (MPRED_SRC_MASS: m1_src |= mass).
    { rewrite EQV in MPRED_SRC.
      apply (proj1 (massert_imp_proj1 mass (range sb (sofs + sizeof_struct_comp ce id) (sofs + sizeof_comp ce id) ** spure (alignof_comp ce id | sofs)))). exact MPRED_SRC. }
    assert (LOAD_EQ: Mem.loadbytes m1_src sb sofs (SSTR + (sizeof_comp ce id - SSTR)) = Some bytes).
    { replace (SSTR + (sizeof_comp ce id - SSTR)) with (sizeof_comp ce id) by lia. exact LOAD. }
    exploit (Mem.loadbytes_split m1_src sb sofs SSTR (sizeof_comp ce id - SSTR) bytes LOAD_EQ); [lia | lia |].
    intros (bytesF & bytesT & LOAD_F & LOAD_T & B_EQ).
    assert (LEN_F: Z.of_nat (length bytesF) = SSTR).
    { pose proof (Mem.loadbytes_length m1_src sb sofs SSTR bytesF LOAD_F) as LEN. rewrite LEN. apply Z2Nat.id. exact SZPOS. }
    assert (LEN_T: Z.of_nat (length bytesT) = sizeof_comp ce id - SSTR).
    { pose proof (Mem.loadbytes_length m1_src sb (sofs + SSTR) (sizeof_comp ce id - SSTR) bytesT LOAD_T) as LEN. rewrite LEN. apply Z2Nat.id. lia. }
    exploit (Mem.storebytes_split m1 tb tofs bytesF bytesT m2).
    { rewrite <- B_EQ. exact STORE. }
    intros (m1' & STORE_F & STORE_T).
    rewrite LEN_F in STORE_T.
    assert (MPRED_RANGE0: m1 |= range tb tofs (tofs + sizeof_comp ce id) ** MP).
    { eapply sep_imp; [exact MPRED | exact TGT_LOC_PERM | apply massert_imp_refl]. }
    assert (MPRED_RANGE1: m1 |= range tb tofs (tofs + SSTR) ** range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** MP).
    { eapply range_split; [lia | exact MPRED_RANGE0]. }
    assert (IMP_SP: massert_imp (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** MP)
                                (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sepconj_morph_1; [apply massert_imp_refl |].
      apply (proj1 (massert_eqv_prop_l MP (alignof_comp ce id | tofs) AL)). }
    assert (MPRED_AL: m1 |= range tb tofs (tofs + SSTR) ** (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sep_imp; [exact MPRED_RANGE1 | apply massert_imp_refl | exact IMP_SP]. }
    assert (IH_FIELDS: forall fid0 base0 fofs0 ffp0, In (fid0, ((base0, fofs0), ffp0)) fpl ->
        forall tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0,
        sem_wt_loc ce ffp0 sb0 sofs0 mp10 ->
        massert_imp mp20 (range tb0 tofs0 (tofs0 + sizeof_footprint ce ffp0)) ->
        (alignof_footprint ce ffp0 | tofs0) ->
        m1_src0 |= mp10 ->
        m10 |= mp20 ** MP0 ->
        Mem.loadbytes m1_src0 sb0 sofs0 (sizeof_footprint ce ffp0) = Some bytes0 ->
        Mem.storebytes m10 tb0 tofs0 bytes0 = Some m20 ->
        wt_footprint ce te0 ty0 ffp0 ->
        exists mass3, sem_wt_loc ce ffp0 tb0 tofs0 mass3 /\ m20 |= mass3 ** MP0).
    { intros fid0 base0 fofs0 ffp0 IN0 tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0 WTLOC0 RANGE0 AL0 MPRED_SRC0 MPRED0 LOAD0 STORE0 WTFP0.
      pose proof (wt_footprint_size_eq ce ty0 ffp0 te0 WTFP0) as SIZEEQ0.
      rewrite <- SIZEEQ0 in RANGE0. rewrite <- SIZEEQ0 in LOAD0.
      eapply (IHfields fid0 base0 fofs0 ffp0 IN0 tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0); eauto. }
    assert (FIELDS: exists mass3F, (fields_loc_sep tb tofs (sem_wt_loc ce) fpl mass3F /\
                m1' |= mass3F ** (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP))).
    { eapply (storebytes_fields_loc_sep ce fpl tb tofs sb sofs mass (range tb tofs (tofs + SSTR)) (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP) m1_src m1 m1' bytesF te SSTR); eauto. }
    destruct FIELDS as [mass3F [FSEP MPRED_FIELDS]].
    (* assert (FSEP_BOUNDED: forall b0 ofs0, m_footprint mass3F b0 ofs0 -> (b0 = tb /\ tofs <= ofs0 < tofs + SSTR) \/ b0 <> tb). *)
    assert (FSEP_BOUNDED: forall b0 ofs0, m_footprint mass3F b0 ofs0 -> ~ (b0 = tb /\ (tofs + SSTR) <= ofs0 <  (tofs + sizeof_comp ce id))).
    { intros. intro. eapply MPRED_FIELDS. eauto. simpl. left. auto. }

(* eapply (fields_loc_sep_footprint_bounded ce fpl tb tofs mass3F SSTR (alignof_comp ce id)); eauto. *)
(*       intros fid0 base0 fofs0 ffp0 IN0. split. *)
(*       - destruct (fp_match_field_In_wt ce co (wt_footprint ce te) fpl (co_members co) fid0 base0 fofs0 ffp0 MATCH IN0) as [fty0 WTFP0]. *)
(*         pose proof (wt_footprint_size_eq ce fty0 ffp0 te WTFP0) as SIZEEQ0. *)
(*         rewrite <- SIZEEQ0. apply Z.ge_le. apply sizeof_pos. *)
(*       - intros b0 ofs0 m' WTLOC0 FOOT0. *)
(*         destruct (fp_match_field_In_wt ce co (wt_footprint ce te) fpl (co_members co) fid0 base0 fofs0 ffp0 MATCH IN0) as [fty0 WTFP0]. *)
(*         assert (FWF0: fp_field_in_range_aligned ce SSTR (alignof_comp ce id) (fields_fp_well_formed ce) (fid0, ((base0, fofs0), ffp0))). *)
(*         { apply (proj1 (Forall_forall (fp_field_in_range_aligned ce SSTR (alignof_comp ce id) (fields_fp_well_formed ce)) fpl)); [exact WF_SSTR_ALIGNED | exact IN0]. } *)
(*         inv FWF0. *)
(*         exact (sem_wt_loc_footprint_bounded ce te fty0 ffp0 CONS NOREP WTFP0 R5 tb (tofs + fofs0) m' WTLOC0 b0 ofs0 FOOT0). } *)
    assert (MPRED_FIELDS_M2: m2 |= mass3F ** (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sep_preserved. exact MPRED_FIELDS.
      - intros HF. apply (m_invar mass3F) with (m := m1'); [exact HF |].
        eapply Mem.storebytes_unchanged_on; eauto.
        intros i IN. intro HCONTR.
        eapply FSEP_BOUNDED. eauto. split; auto. lia.
        (* destruct (FSEP_BOUNDED tb i HCONTR) as [BND | NEQ]. *)
        (* + destruct BND as [EQ2 LO HI]. lia. *)
        (* + contradiction. *)
      - intros HQ. eapply sep_preserved; [exact HQ | |].
        + intros H1. eapply storebytes_range_unchanged; eauto.
        + intros HMP0. eapply (m_invar (spure (alignof_comp ce id | tofs) ** MP)) with (m := m1'). exact HMP0.
          eapply Mem.storebytes_unchanged_on; eauto.
          intros i IN. intro HF.
          destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
          destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
          destruct HF as [HFS | HFMP].
          * unfold spure in HFS. simpl in HFS. contradiction.
          * apply (DISJ tb i).
            -- apply (TGTRANGE_FP tb i). simpl. split; [reflexivity |]. rewrite LEN_T in IN. lia.
            -- exact HFMP. }
    exists (mass3F ** range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)).
    split.
    + eapply (sem_wt_struct ce tb tofs fpl id mass3F (mass3F ** range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)) (range tb (tofs + SSTR) (tofs + sizeof_comp ce id))).
      exact FSEP.
      unfold SSTR. reflexivity.
      reflexivity.
    + rewrite <- (sep_assoc (range tb (tofs + SSTR) (tofs + sizeof_comp ce id)) (spure (alignof_comp ce id | tofs)) MP) in MPRED_FIELDS_M2.
      rewrite <- (sep_assoc mass3F (range tb (tofs + SSTR) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)) MP) in MPRED_FIELDS_M2.
      exact MPRED_FIELDS_M2.
  - (* fp_enum *)
    inv WTFP.
    assert (SIZEEQ: sizeof ce (Tvariant orgs id) = sizeof_comp ce id).
    { unfold sizeof, sizeof_comp. rewrite CO. reflexivity. }
    rewrite SIZEEQ in LOAD. rewrite SIZEEQ in TGT_LOC_PERM.
    simpl in AL.
    pose (tag_fp := fp_scalar Mint32 (Vint (Int.repr tagz))).
    pose (fpl_enum := (fid, ((0, 0), tag_fp)) :: (fid, ((size_chunk Mint32, fofs), fp1)) :: nil).
    pose (SZ := fofs + sizeof_footprint ce fp1).
    assert (SIZEEQF: sizeof ce fty = sizeof_footprint ce fp1) by (eapply wt_footprint_size_eq; eauto).
    assert (FPOS: 0 <= sizeof_footprint ce fp1).
    { rewrite <- SIZEEQF. apply Z.ge_le. apply sizeof_pos. }
    destruct (place_field_type_res co fid orgs fty FTY) as (fty' & FTY' & TEQ).
    pose proof (variant_field_offset_in_range ce (co_members co) fid fofs fty' FOFS FTY') as RANGEV.
    pose proof (variant_field_offset_aligned ce fid (co_members co) fofs fty' FOFS FTY') as ALIGNV.
    pose proof (type_eq_sizeof_eq fty fty' ce TEQ) as SIZEEQTY.
    pose proof (type_eq_alignof_eq ce fty fty' TEQ) as ALIGNEQTY.
    assert (LE4: 4 <= fofs) by (exact (proj1 RANGEV)).
    assert (SZPOS: 0 <= SZ) by (unfold SZ; lia).
    assert (SZLE: SZ <= sizeof_comp ce id).
    { unfold SZ. rewrite <- SIZEEQF. rewrite SIZEEQTY.
      destruct RANGEV as [_ B].
      destruct (CONS id co CO) as [_ _ SZC _].
      unfold sizeof_comp. rewrite CO. rewrite SZC. rewrite ENUM. simpl.
      apply Z.le_trans with (sizeof_variant ce (co_members co)); [exact B |].
      apply align_le. apply co_alignof_pos. }
    assert (SORTED: fields_sorted ce fpl_enum).
    { unfold fields_sorted, fpl_enum, tag_fp.
      apply fields_after_cons; [reflexivity | lia | simpl; lia |].
      apply fields_after_cons; [simpl; reflexivity | simpl; exact LE4 | exact FPOS | apply fields_after_nil]. }
    assert (WF_ENUM: Forall (fp_field_in_range ce SZ (fields_fp_well_formed ce)) fpl_enum).
    { unfold fpl_enum, tag_fp.
      constructor.
      - apply fp_field_in_range_intro; [lia | lia | | apply fp_scalar_wf].
        unfold SZ. simpl. lia.
      - constructor.
        + apply fp_field_in_range_intro; [simpl; exact LE4 | lia | | apply (wt_footprint_fields_well_formed ce te fty fp1 CONS NOREP WT)].
          unfold SZ. reflexivity.
        + constructor. }
    assert (WTFPS_ENUM: Forall (fun '(fid, ((base, fofs), ffp)) => exists ty, wt_footprint ce te ty ffp) fpl_enum).
    { unfold fpl_enum, tag_fp. simpl. constructor.
      - exists type_int32s. eapply wt_fp_scalar; reflexivity.
      - constructor.
        + exists fty. exact WT.
        + constructor. }
    assert (ABS_ALIGN_ENUM: Forall (fun '(fid, ((base, fofs), ffp)) => (alignof_footprint ce ffp | (tofs + fofs))) fpl_enum).
    { unfold fpl_enum, tag_fp. simpl. constructor.
      - rewrite Z.add_0_r. simpl.
        destruct (CONS id co CO) as [_ ALIGNC _ _].
        pose proof (tag_align_divide_composite co ce) as TAGDIV.
        eapply Z.divide_trans; [| exact AL].
        eapply Z.divide_trans; [exact TAGDIV |].
        rewrite <- ENUM. rewrite <- ALIGNC. unfold alignof_comp. rewrite CO. apply Z.divide_refl.
      - constructor.
        + pose proof (wt_footprint_align_divides ce fty fp1 te WT) as ALIGNDIVF.
          pose proof (field_alignof_divide_composite fty' fid co ce FTY') as ALIGNDIV2.
          destruct (CONS id co CO) as [_ ALIGNC _ _].
          assert (ALIGN_ALOF: (alignof_footprint ce fp1 | alignof_comp ce id)).
          { eapply Z.divide_trans; [exact ALIGNDIVF |].
            rewrite ALIGNEQTY. eapply Z.divide_trans; [exact ALIGNDIV2 |].
            rewrite <- ALIGNC. unfold alignof_comp. rewrite CO. apply Z.divide_refl. }
          assert (ALIGN_TOFS: (alignof_footprint ce fp1 | tofs)).
          { eapply Z.divide_trans; [exact ALIGN_ALOF | exact AL]. }
          assert (ALIGN_FOFS: (alignof_footprint ce fp1 | fofs)).
          { apply Z.divide_trans with (alignof ce fty').
            - rewrite <- ALIGNEQTY. exact ALIGNDIVF.
            - exact ALIGNV. }
          eapply Z.divide_add_r; [exact ALIGN_TOFS | exact ALIGN_FOFS].
        + constructor. }
    (* source fields_loc_sep *)
    assert (MPRED_SRC_TAG: m1_src |= (hasvalue Mint32 sb sofs (Vint (Int.repr tagz)))).
    { rewrite EQV in MPRED_SRC.
      apply (proj1 (massert_imp_proj1 (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** range sb (sofs + fofs + sizeof_footprint ce fp1) (sofs + sizeof_comp ce id) ** spure (alignof_comp ce id | sofs)))). exact MPRED_SRC. }
    assert (BOUNDS: 0 <= sofs /\ sofs <= Ptrofs.modulus).
    { pose proof (contains_no_overflow (fun v => v = Vint (Int.repr tagz)) m1_src Mint32 sb sofs) as H.
      unfold hasvalue in MPRED_SRC_TAG.
      assert (OFS: 0 <= sofs <= Ptrofs.max_unsigned).
      { apply H. exact MPRED_SRC_TAG. }
      split; [lia |].
      apply Z.le_trans with Ptrofs.max_unsigned; [lia |].
      unfold Ptrofs.max_unsigned, Ptrofs.modulus. lia. }
    assert (FSRC_TAIL: fields_loc_sep sb sofs (sem_wt_loc ce) [(fid, ((size_chunk Mint32, fofs), fp1))] (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)).
    { apply (fields_loc_sep_cons sb sofs (sem_wt_loc ce) fid (size_chunk Mint32) fofs fp1 nil mass2 STrue (range sb (sofs + size_chunk Mint32) (sofs + fofs)) (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)).
      - econstructor. reflexivity.
      - exact FWT.
      - reflexivity.
      - reflexivity. }
    assert (FSRC: fields_loc_sep sb sofs (sem_wt_loc ce) fpl_enum (range sb sofs sofs ** (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue))).
    { apply (fields_loc_sep_cons sb sofs (sem_wt_loc ce) fid 0 0 tag_fp [(fid, ((size_chunk Mint32, fofs), fp1))] (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue) (range sb sofs sofs) (range sb sofs sofs ** (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue))).
      - exact FSRC_TAIL.
      - apply sem_wt_scalar. rewrite Z.add_0_r. reflexivity.
      - simpl. f_equal; lia.
      - reflexivity. }
    assert (MPRED_SRC_CORE: m1_src |= (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2).
    { rewrite EQV in MPRED_SRC.
      rewrite <- (sep_assoc (range sb (sofs + size_chunk Mint32) (sofs + fofs)) mass2 (range sb (sofs + fofs + sizeof_footprint ce fp1) (sofs + sizeof_comp ce id) ** spure (alignof_comp ce id | sofs))) in MPRED_SRC.
      rewrite <- (sep_assoc (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2) (range sb (sofs + fofs + sizeof_footprint ce fp1) (sofs + sizeof_comp ce id) ** spure (alignof_comp ce id | sofs))) in MPRED_SRC.
      apply (proj1 (massert_imp_proj1 ((hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2) (range sb (sofs + fofs + sizeof_footprint ce fp1) (sofs + sizeof_comp ce id) ** spure (alignof_comp ce id | sofs)))) in MPRED_SRC.
      exact MPRED_SRC. }
    assert (MPRED_SRC_STrue: m1_src |= (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)).
    { assert (IMP_STrue: massert_imp (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2)
                                     (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)).
      { eapply sepconj_morph_1; [apply massert_imp_refl | apply (proj1 (massert_eqv_pure_r mass2))]. }
      eapply sep_imp; [exact MPRED_SRC_CORE | apply massert_imp_refl | exact IMP_STrue]. }
    assert (MPRED_SRC_MASS_SRC: m1_src |= range sb sofs sofs ** (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)).
    { rewrite (range_empty_sep_l ((hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)) sb sofs (proj1 BOUNDS) (proj2 BOUNDS)).
      exact MPRED_SRC_STrue. }
    (* split source loadbytes and target storebytes *)
    assert (LOAD_EQ: Mem.loadbytes m1_src sb sofs (SZ + (sizeof_comp ce id - SZ)) = Some bytes).
    { replace (SZ + (sizeof_comp ce id - SZ)) with (sizeof_comp ce id) by lia. exact LOAD. }
    exploit (Mem.loadbytes_split m1_src sb sofs SZ (sizeof_comp ce id - SZ) bytes LOAD_EQ); [lia | lia |].
    intros (bytesF & bytesT & LOAD_F & LOAD_T & B_EQ).
    assert (LEN_F: Z.of_nat (length bytesF) = SZ).
    { pose proof (Mem.loadbytes_length m1_src sb sofs SZ bytesF LOAD_F) as LEN. rewrite LEN. apply Z2Nat.id. exact SZPOS. }
    assert (LEN_T: Z.of_nat (length bytesT) = sizeof_comp ce id - SZ).
    { pose proof (Mem.loadbytes_length m1_src sb (sofs + SZ) (sizeof_comp ce id - SZ) bytesT LOAD_T) as LEN. rewrite LEN. apply Z2Nat.id. lia. }
    exploit (Mem.storebytes_split m1 tb tofs bytesF bytesT m2).
    { rewrite <- B_EQ. exact STORE. }
    intros (m1' & STORE_F & STORE_T).
    rewrite LEN_F in STORE_T.
    assert (MPRED_RANGE0: m1 |= range tb tofs (tofs + sizeof_comp ce id) ** MP).
    { eapply sep_imp; [exact MPRED | exact TGT_LOC_PERM | apply massert_imp_refl]. }
    assert (MPRED_RANGE1: m1 |= range tb tofs (tofs + SZ) ** range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** MP).
    { eapply range_split; [lia | exact MPRED_RANGE0]. }
    assert (IMP_SP: massert_imp (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** MP)
                                (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sepconj_morph_1; [apply massert_imp_refl |].
      apply (proj1 (massert_eqv_prop_l MP (alignof_comp ce id | tofs) AL)). }
    assert (MPRED_AL: m1 |= range tb tofs (tofs + SZ) ** (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sep_imp; [exact MPRED_RANGE1 | apply massert_imp_refl | exact IMP_SP]. }
    assert (IH_ENUM: forall fid0 base0 fofs0 ffp0, In (fid0, ((base0, fofs0), ffp0)) fpl_enum ->
        forall tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0,
        sem_wt_loc ce ffp0 sb0 sofs0 mp10 ->
        massert_imp mp20 (range tb0 tofs0 (tofs0 + sizeof_footprint ce ffp0)) ->
        (alignof_footprint ce ffp0 | tofs0) ->
        m1_src0 |= mp10 ->
        m10 |= mp20 ** MP0 ->
        Mem.loadbytes m1_src0 sb0 sofs0 (sizeof_footprint ce ffp0) = Some bytes0 ->
        Mem.storebytes m10 tb0 tofs0 bytes0 = Some m20 ->
        wt_footprint ce te0 ty0 ffp0 ->
        exists mass3, sem_wt_loc ce ffp0 tb0 tofs0 mass3 /\ m20 |= mass3 ** MP0).
    { intros fid0 base0 fofs0 ffp0 IN0. simpl in IN0. destruct IN0 as [EQtag | [EQvariant | Hfalse]].
      - inv EQtag. intros tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0 WTLOC0 RANGE0 AL0 MPRED_SRC0 MPRED0 LOAD0 STORE0 WTFP0.
        eapply storebytes_scalar_sem_wt_loc; eauto.
      - inv EQvariant. intros tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0 WTLOC0 RANGE0 AL0 MPRED_SRC0 MPRED0 LOAD0 STORE0 WTFP0.
        pose proof (wt_footprint_size_eq ce ty0 ffp0 te0 WTFP0) as SIZEEQ0.
        rewrite <- SIZEEQ0 in RANGE0. rewrite <- SIZEEQ0 in LOAD0.
        eapply (IHenum tb0 tofs0 sb0 sofs0 mp10 mp20 MP0 m1_src0 m10 m20 bytes0 ty0 te0); eauto.
      - destruct Hfalse. }
    assert (FIELDS: exists mass3F, (fields_loc_sep tb tofs (sem_wt_loc ce) fpl_enum mass3F /\
                m1' |= mass3F ** (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP))).
    { eapply (storebytes_fields_loc_sep ce fpl_enum tb tofs sb sofs (range sb sofs sofs ** (hasvalue Mint32 sb sofs (Vint (Int.repr tagz))) ** (range sb (sofs + size_chunk Mint32) (sofs + fofs) ** mass2 ** STrue)) (range tb tofs (tofs + SZ)) (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP) m1_src m1 m1' bytesF te SZ); eauto. }
    destruct FIELDS as [mass3F [FSEP MPRED_FIELDS]].
    (* store the tail padding *)
    assert (WF_ENUM_ALIGNED: Forall (fp_field_in_range_aligned ce SZ (alignof_comp ce id) (fields_fp_well_formed ce)) fpl_enum).
    { unfold fpl_enum, tag_fp.
      constructor.
      apply fp_field_in_range_aligned_intro; [lia | lia | lia | | | apply fp_scalar_wf].
      unfold SZ. simpl. lia.
      apply Z.divide_0_r.
      constructor.
      apply fp_field_in_range_aligned_intro; [simpl; lia | simpl; exact LE4 | lia | | | apply (wt_footprint_fields_well_formed ce te fty fp1 CONS NOREP WT)].
      unfold SZ. reflexivity.
      pose proof (wt_footprint_align_divides ce fty fp1 te WT) as ALIGNDIVF.
      apply Z.divide_trans with (alignof ce fty').
      rewrite <- ALIGNEQTY. exact ALIGNDIVF.
      exact ALIGNV.
      constructor. }
    assert (FSEP_BOUNDED: forall b0 ofs0, m_footprint mass3F b0 ofs0 -> ~ (b0 = tb /\ (tofs + SZ) <= ofs0 <  (tofs + sizeof_comp ce id))).
    { intros. intro. eapply MPRED_FIELDS. eauto. simpl. left. auto. }

    (* { eapply (fields_loc_sep_footprint_bounded ce fpl_enum tb tofs mass3F SZ (alignof_comp ce id)); eauto. *)
    (*   intros fid0 base0 fofs0 ffp0 IN0. simpl in IN0. destruct IN0 as [EQtag | [EQvariant | Hfalse]]. *)
    (*   - inv EQtag. split. *)
    (*     + simpl. lia. *)
    (*     + intros b0 ofs0 m' WTLOC0 FOOT0. *)
    (*       assert (WTFPtag: wt_footprint ce te type_int32s tag_fp). *)
    (*       { unfold tag_fp. eapply wt_fp_scalar; reflexivity. } *)
    (*       assert (WFtag: fields_fp_well_formed ce tag_fp). *)
    (*       { unfold tag_fp. apply (fp_scalar_wf ce Mint32 (Vint (Int.repr tagz))). } *)
    (*       exact (sem_wt_loc_footprint_bounded ce te type_int32s tag_fp CONS NOREP WTFPtag WFtag tb (tofs + 0) m' WTLOC0 b0 ofs0 FOOT0). *)
    (*   - inv EQvariant. split. *)
    (*     + exact FPOS. *)
    (*     + intros b0 ofs0 m' WTLOC0 FOOT0. *)
    (*       assert (WF1: fields_fp_well_formed ce ffp0) by (apply (wt_footprint_fields_well_formed ce te fty ffp0 CONS NOREP WT)). *)
    (*       exact (sem_wt_loc_footprint_bounded ce te fty ffp0 CONS NOREP WT WF1 tb (tofs + fofs0) m' WTLOC0 b0 ofs0 FOOT0). *)
    (*   - destruct Hfalse. } *)
    assert (MPRED_FIELDS_M2: m2 |= mass3F ** (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs) ** MP)).
    { eapply sep_preserved. exact MPRED_FIELDS.
      - intros HF. apply (m_invar mass3F) with (m := m1'); [exact HF |].
        eapply Mem.storebytes_unchanged_on; eauto.
        intros i IN. intro HCONTR.
        eapply FSEP_BOUNDED. eauto. lia.
        (* destruct (FSEP_BOUNDED tb i HCONTR) as [BND | NEQ]. *)
        (* + destruct BND as [EQ2 LO HI]. lia. *)
        (* + contradiction. *)
      - intros HQ. eapply sep_preserved; [exact HQ | |].
        + intros H1. eapply storebytes_range_unchanged; eauto.
        + intros HMP0. eapply (m_invar (spure (alignof_comp ce id | tofs) ** MP)) with (m := m1'). exact HMP0.
          eapply Mem.storebytes_unchanged_on; eauto.
          intros i IN. intro HF.
          destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
          destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
          destruct HF as [HFS | HFMP].
          * unfold spure in HFS. simpl in HFS. contradiction.
          * apply (DISJ tb i).
            -- apply (TGTRANGE_FP tb i). simpl. split; [reflexivity |]. rewrite LEN_T in IN. lia.
            -- exact HFMP. }
    (* invert the target fields_loc_sep *)
    unfold fpl_enum, tag_fp in FSEP.
    inv FSEP.
    inv IND.
    exists (mass3F ** range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)).
    split.
    + eapply (sem_wt_enum ce fp1 tb tofs tagz fid fofs id (hasvalue Mint32 tb tofs (Vint (Int.repr tagz))) mass3 (mass3F ** range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)) (range tb (tofs + size_chunk Mint32) (tofs + fofs)) (range tb (tofs + SZ) (tofs + sizeof_comp ce id))).
      * reflexivity.
      * exact FWT1.
      * reflexivity.
      * unfold SZ. f_equal; lia.
      * assert (BOUNDS_T: 0 <= tofs /\ tofs <= Ptrofs.modulus).
        { destruct MPRED_RANGE0 as [RANGE_M _]. unfold range in RANGE_M. simpl in RANGE_M.
          destruct RANGE_M as [LO [HI _]]. split; [exact LO | lia]. }
        assert (EQV_tag: massert_eqv mass1 (hasvalue Mint32 tb tofs (Vint (Int.repr tagz)))).
        { apply (sem_wt_loc_unique ce (fp_scalar Mint32 (Vint (Int.repr tagz))) mass1 (hasvalue Mint32 tb tofs (Vint (Int.repr tagz))) tb tofs).
          - rewrite Z.add_0_r in FWT0. exact FWT0.
          - apply sem_wt_scalar. reflexivity. }
        assert (EQV_nil: massert_eqv mass4 STrue).
        { inversion IND0; subst. assumption. }
        rewrite EQV0, EQV1, EQV_tag, EQV_nil.
        simpl. rewrite Z.add_0_r.
        setoid_rewrite (range_empty_sep_l (hasvalue Mint32 tb tofs (Vint (Int.repr tagz)) ** range tb (tofs + 4) (tofs + fofs) ** mass3 ** STrue) tb tofs (proj1 BOUNDS_T) (proj2 BOUNDS_T)).
        setoid_rewrite <- (massert_eqv_pure_r mass3).
        rewrite !sep_assoc. reflexivity.
    + rewrite <- (sep_assoc (range tb (tofs + SZ) (tofs + sizeof_comp ce id)) (spure (alignof_comp ce id | tofs)) MP) in MPRED_FIELDS_M2.
      rewrite <- (sep_assoc mass3F (range tb (tofs + SZ) (tofs + sizeof_comp ce id) ** spure (alignof_comp ce id | tofs)) MP) in MPRED_FIELDS_M2.
      exact MPRED_FIELDS_M2.
  - inv WTFP.
    { assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
      assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce (Treference org mut ty0)).
      { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
        apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }
      assert (MPRED_HAS: m1_src |= hasvalue Mptr sb sofs (Vptr b2 (Ptrofs.repr ofs2))).
      { rewrite EQV in MPRED_SRC. exact MPRED_SRC. }
      exploit load_rule. exact MPRED_HAS. intros (vload & LOAD1 & HVEQ).
      exploit Mem.load_loadbytes; eauto. intros (bytes'' & LB'' & VEQBYTES).
      rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE) in LB''.
      rewrite LOAD in LB''. inv LB''.
      assert (ALIGN: (align_chunk Mptr | tofs)).
      { simpl in AL. exact AL. }
      assert (MPRED_RANGE: m1 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
      { eapply sep_imp.
        - exact MPRED.
        - rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). exact TGT_LOC_PERM.
        - apply massert_imp_refl. }
      assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
      { eapply sep_preserved. exact MPRED_RANGE.
        - intros H1. eapply storebytes_range_unchanged; eauto.
        - intros HMP. eapply (m_invar MP).
          + exact HMP.
          + eapply Mem.storebytes_unchanged_on; eauto.
            intros i IN. intro HF.
            destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
            destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
            unfold range in TGTRANGE_FP.
            apply (DISJ tb i).
            * apply (TGTRANGE_FP tb i). simpl. split; auto.
              unfold sizeof in LEN_EQ. rewrite <- LEN_EQ. exact IN.
            * exact HF. }
      assert (LOAD2: Mem.load Mptr m2 tb tofs = Some (decode_val Mptr bytes'')).
      { eapply Mem.loadbytes_load.
        - rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). rewrite <- LEN_EQ.
          eapply Mem.loadbytes_storebytes_same; eauto.
        - exact ALIGN. }
      assert (VEQ: Vptr b2 (Ptrofs.repr ofs2) = decode_val Mptr bytes'').
      { exact VEQBYTES. }
      exists (hasvalue Mptr tb tofs (Vptr b2 (Ptrofs.repr ofs2))).
      split.
      econstructor. reflexivity.
      eapply range_hasvalue.
      exact MPRED_RANGE2.
      rewrite <- VEQ in LOAD2. exact LOAD2. }
    { assert (MODE: access_mode (Treference org mut ty0) = Ctypes.By_value Mptr) by reflexivity.
      assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce (Treference org mut ty0)).
      { exploit Mem.loadbytes_length; eauto. intros LEN. rewrite LEN.
        apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }
      assert (MPRED_HAS: m1_src |= hasvalue Mptr sb sofs (Vptr b2 (Ptrofs.repr ofs2))).
      { rewrite EQV in MPRED_SRC. exact MPRED_SRC. }
      exploit load_rule. exact MPRED_HAS. intros (vload & LOAD1 & HVEQ).
      exploit Mem.load_loadbytes; eauto. intros (bytes'' & LB'' & VEQBYTES).
      rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE) in LB''.
      rewrite LOAD in LB''. inv LB''.
      assert (ALIGN: (align_chunk Mptr | tofs)).
      { simpl in AL. exact AL. }
      assert (MPRED_RANGE: m1 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
      { eapply sep_imp.
        - exact MPRED.
        - rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). exact TGT_LOC_PERM.
        - apply massert_imp_refl. }
      assert (MPRED_RANGE2: m2 |= range tb tofs (tofs + size_chunk Mptr) ** MP).
      { eapply sep_preserved. exact MPRED_RANGE.
        - intros H1. eapply storebytes_range_unchanged; eauto.
        - intros HMP. eapply (m_invar MP).
          + exact HMP.
          + eapply Mem.storebytes_unchanged_on; eauto.
            intros i IN. intro HF.
            destruct MPRED as (MP2PRED & MPPRED0 & DISJ).
            destruct TGT_LOC_PERM as (_ & TGTRANGE_FP).
            unfold range in TGTRANGE_FP.
            apply (DISJ tb i).
            * apply (TGTRANGE_FP tb i). simpl. split; auto.
              unfold sizeof in LEN_EQ. rewrite <- LEN_EQ. exact IN.
            * exact HF. }
      assert (LOAD2: Mem.load Mptr m2 tb tofs = Some (decode_val Mptr bytes'')).
      { eapply Mem.loadbytes_load.
        - rewrite (sizeof_by_value ce (Treference org mut ty0) Mptr MODE). rewrite <- LEN_EQ.
          eapply Mem.loadbytes_storebytes_same; eauto.
        - exact ALIGN. }
      assert (VEQ: Vptr b2 (Ptrofs.repr ofs2) = decode_val Mptr bytes'').
      { exact VEQBYTES. }
      exists (hasvalue Mptr tb tofs (Vptr b2 (Ptrofs.repr ofs2))).
      split.
      econstructor. reflexivity.
      eapply range_hasvalue.
      exact MPRED_RANGE2.
      rewrite <- VEQ in LOAD2. exact LOAD2. }
Admitted.



Lemma storebytes_sem_wt_loc ce: forall sfp tb tofs sb sofs mp1 mp2 MP m1_src m1 m2 bytes ty te
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (SRC_LOC: sem_wt_loc ce sfp sb sofs mp1)
    (TGT_LOC_PERM: massert_imp mp2 (range tb tofs (tofs + sizeof ce ty)))
    (AL: (alignof ce ty | tofs))
    (MPRED_SRC: m1_src |= mp1)
    (MPRED: m1 |= mp2 ** MP)
    (LOAD: Mem.loadbytes m1_src sb sofs (sizeof ce ty) = Some bytes)
    (STORE: Mem.storebytes m1 tb tofs bytes = Some m2)
    (WTFP: wt_footprint ce te ty sfp),
  exists mass3, sem_wt_loc ce sfp tb tofs mass3 /\ m2 |= mass3 ** MP.
Proof.
  intros.
  assert (AL_FP: (alignof_footprint ce sfp | tofs)).
  { eapply Z.divide_trans; [eapply wt_footprint_align_divides; eauto | exact AL]. }
  eapply storebytes_sem_wt_loc_fp; eauto.
Qed.



Lemma storebytes_coherent_var: forall phl m1 ce mass1 mp1 sfp sb sofs fp1 tfp b1 ofs1 tb tofs MP ty te
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (AL: (alignof ce ty | tofs))
    (SRC_LOC: sem_wt_loc ce sfp sb sofs mp1)
    (TGT_LOC: sem_wt_loc ce fp1 b1 ofs1 mass1)
    (MPIMP: massert_imp (mass1 ** MP) mp1)
    (MPRED: m1 |= mass1 ** MP)
    (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = OK (tb, tofs, tfp))
    (WTFP1: wt_footprint ce te ty sfp)
    (WTFP2: wt_footprint ce te ty tfp)
    (RANGE_SRC: 0 <= sofs /\ sofs + sizeof ce ty <= Ptrofs.max_unsigned)
    (RANGE_TGT: 0 <= tofs /\ tofs + sizeof ce ty <= Ptrofs.max_unsigned),
    exists bytes m2 fp2 mass3,
      Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes
      /\ Mem.storebytes m1 tb tofs bytes = Some m2
      /\ set_footprint phl sfp fp1 = OK fp2
      /\ sem_wt_loc ce fp2 b1 ofs1 mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros.
  assert (SIZEEQ1: sizeof_footprint ce sfp = sizeof ce ty).
  { symmetry. eapply (wt_footprint_size_eq ce ty sfp te). exact WTFP1. }
  assert (SIZEEQ2: sizeof_footprint ce tfp = sizeof ce ty).
  { symmetry. eapply (wt_footprint_size_eq ce ty tfp te). exact WTFP2. }
  assert (SIZEEQ: sizeof_footprint ce sfp = sizeof_footprint ce tfp).
  { rewrite SIZEEQ1, SIZEEQ2. reflexivity. }

  exploit (get_owner_loc_footprint_sem_wt_split ce phl b1 ofs1 tb tofs fp1 tfp mass1); eauto.
  intros (rest & tgt_mass & fp1' & SET_EMP & REST_LOC & TGT_LOC2 & SPLIT & RE_SET).

  exploit (sem_wt_loc_range_perm ce sfp mp1 sb sofs ty te); eauto.
  intros SRC_RANGE.
  exploit (sem_wt_loc_range_perm ce tfp tgt_mass tb tofs ty te); eauto.
  intros TGT_RANGE.

  rewrite SPLIT in MPRED.
  rewrite SPLIT in MPIMP.
  rewrite !sep_assoc in MPRED.
  rewrite !sep_assoc in MPIMP.

  assert (MPRED_SRC: m1 |= mp1).
  { eapply MPIMP. exact MPRED. }

  assert (MPRED_RANGE_SRC: m1 |= range sb sofs (sofs + sizeof ce ty)).
  { eapply SRC_RANGE. exact MPRED_SRC. }

  assert (LOAD: exists bytes, Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes).
  { rewrite SIZEEQ1.
    eapply Mem.range_perm_loadbytes.
    red. intros i IN.
    destruct MPRED_RANGE_SRC as (LO & HI & PERM).
    apply PERM. simpl. repeat split; auto; lia. }
  destruct LOAD as (bytes & LOAD).
  exploit Mem.loadbytes_length; eauto. intros LEN.

  assert (LEN_EQ: Z.of_nat (length bytes) = sizeof ce ty).
  { rewrite LEN. rewrite SIZEEQ1. apply Z2Nat.id. apply Z.ge_le. apply sizeof_pos. }

  assert (MPRED_TGT: m1 |= tgt_mass).
  { apply (sep_proj1 MP tgt_mass m1).
    apply (sep_proj2 rest (tgt_mass ** MP) m1).
    exact MPRED. }

  assert (MPRED_RANGE_TGT: m1 |= range tb tofs (tofs + sizeof ce ty)).
  { eapply TGT_RANGE. exact MPRED_TGT. }

  assert (STORE: exists m2, Mem.storebytes m1 tb tofs bytes = Some m2).
  { edestruct (Mem.range_perm_storebytes m1 tb tofs bytes) as (m2 & STORE0).
    - rewrite LEN_EQ.
      red. intros i IN.
      destruct MPRED_RANGE_TGT as (LO & HI & PERM).
      apply PERM. simpl. repeat split; auto; lia.
    - exists m2. exact STORE0. }
  destruct STORE as (m2 & STORE).

  assert (EQ_MPRED: massert_eqv (rest ** tgt_mass ** MP) (tgt_mass ** rest ** MP)).
  { eapply sep_swap. }
  rewrite EQ_MPRED in MPRED.
  rewrite EQ_MPRED in MPIMP.

  assert (LOAD_TY: Mem.loadbytes m1 sb sofs (sizeof ce ty) = Some bytes).
  { rewrite <- SIZEEQ1. exact LOAD. }

  exploit (storebytes_sem_wt_loc ce sfp tb tofs sb sofs mp1 tgt_mass (rest ** MP) m1 m1 m2 bytes ty te); eauto.
  intros (mass3 & B1 & B2).

  exploit (RE_SET sfp mass3); eauto. intros (mp' & fp2 & SET2 & C1 & C2).

  exists bytes, m2, fp2, mp'.
  split. exact LOAD.
  split. exact STORE.
  split. exact SET2.
  split. exact C1.
  rewrite C2.
  assert (EQ_FINAL: massert_eqv (mass3 ** rest ** MP) ((rest ** mass3) ** MP)).
  { rewrite (sep_swap mass3 rest MP). symmetry. eapply sep_assoc. }
  rewrite <- EQ_FINAL. exact B2.
Qed.


(* [storebytes_coherent_fpm]: storing bytes from [sfp] into the owner
   location [(id, phl)] of [fpm] succeeds and updates [fpm] with [sfp] while
   preserving [coherent_fpm]. The proof splits [coherent_fpm] around the target
   variable, reframes the memory assertion, applies [storebytes_coherent_var],
   and reassembles the updated footprint map. *)

(* The split lemma uses [fp_emp sz al] to retain the target layout while
   removing its location predicate.  In particular, a surrounding box keeps
   owning its allocation metadata. *)
Lemma storebytes_coherent_fpm: forall phl m1 ce fpm mass1 mp1 sfp tfp sb sofs tb tofs id MP ty
    (CONS: composite_env_consistent ce)
    (NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)))
    (AL: (alignof ce ty | tofs))
    (RANGE_SRC: 0 <= sofs /\ sofs + sizeof ce ty <= Ptrofs.max_unsigned)
    (RANGE_TGT: 0 <= tofs /\ tofs + sizeof ce ty <= Ptrofs.max_unsigned)
    (SRC_LOC: sem_wt_loc ce sfp sb sofs mp1)
    (COH: coherent_fpm ce fpm mass1)
    (MPIMP: massert_imp (mass1 ** MP) mp1)
    (MPRED: m1 |= mass1 ** MP)
    (GFP: get_owner_loc_footprint_map (id, phl) fpm = OK (tb, tofs, tfp))
    (WTFP1: wt_footprint ce (fpm_to_tenv fpm) ty sfp)
    (WTFP2: wt_footprint ce (fpm_to_tenv fpm) ty tfp),
    exists bytes m2 fpm1 mass3,
      Mem.loadbytes m1 sb sofs (sizeof_footprint ce sfp) = Some bytes
      /\ Mem.storebytes m1 tb tofs bytes = Some m2
      /\ set_footprint_map (id, phl) sfp fpm = OK fpm1
      /\ coherent_fpm ce fpm1 mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros.
  unfold get_owner_loc_footprint_map in GFP.
  destruct (fpm ! id) as [(((b1, ofs1), ty1), fp1) | ] eqn:B; try discriminate.
  inv COH.
  exploit PTree.elements_remove. exact B. intros (l1 & l2 & ELEMS_OLD & ELEMS_REM_OLD).
  rewrite ELEMS_OLD in ALLSEP.
  apply Forall_sep_app in ALLSEP as (mp_l & mp_rest & SEP_L & SEP_MID & EQV_L_REST).
  inversion SEP_MID as [| x0 l0 mhead mtail mwhole HEAD TAIL EQV_MID]; subst.
  inv HEAD; inv ELTEQ.
  assert (EQV_MASS1: massert_eqv mass1 (mp_l ** mhead ** mtail)).
  { etransitivity; [exact EQV_L_REST |].
    apply sepconj_morph_2; [reflexivity |]. symmetry. exact EQV_MID. }
  assert (EQV_FRAME: massert_eqv ((mp_l ** mhead ** mtail) ** MP) (mhead ** (mp_l ** mtail ** MP))).
  { rewrite (sep_assoc mp_l (mhead ** mtail) MP).
    rewrite (sep_assoc mhead mtail MP).
    apply sep_swap. }
  assert (MPIMP_VAR: massert_imp (mhead ** (mp_l ** mtail ** MP)) mp1).
  { rewrite EQV_MASS1 in MPIMP. rewrite EQV_FRAME in MPIMP. exact MPIMP. }
  assert (MPRED_VAR: m1 |= mhead ** (mp_l ** mtail ** MP)).
  { rewrite EQV_MASS1 in MPRED. rewrite EQV_FRAME in MPRED. exact MPRED. }
  exploit (storebytes_coherent_var phl m1 ce mhead mp1 sfp sb sofs fp tfp b ofs tb tofs (mp_l ** mtail ** MP) ty (fpm_to_tenv fpm)); eauto.
  intros (bytes & m2 & fp2 & mass3 & LOAD & STORE & SET_FOOT & WTLOC_FP2 & MPRED_M2).
  remember (PTree.set id0 (b, ofs, ty0, fp2) fpm) as fpm1 eqn:FPM1.
  assert (SET_MAP: set_footprint_map (id0, phl) sfp fpm = OK fpm1).
  { unfold set_footprint_map. simpl. rewrite B. rewrite SET_FOOT. simpl. rewrite <- FPM1. reflexivity. }
  assert (FPM1_GET: fpm1 ! id0 = Some (b, ofs, ty0, fp2)).
  { rewrite FPM1. apply PTree.gss. }
  exploit PTree.elements_remove. exact FPM1_GET. intros (l1' & l2' & ELEMS_NEW & ELEMS_REM_NEW).
  assert (REM_ELEMS_EQ: PTree.elements (PTree.remove id0 fpm1) = PTree.elements (PTree.remove id0 fpm)).
  { rewrite FPM1. symmetry. apply PTree_remove_elements_eq. }
  assert (L_EQ: l1' ++ l2' = l1 ++ l2).
  { rewrite <- ELEMS_REM_NEW. rewrite REM_ELEMS_EQ. exact ELEMS_REM_OLD. }
  assert (SEP_OLD: Forall_sep (coherent_var ce) (l1 ++ l2) (mp_l ** mtail)).
  { eapply Forall_sep_app. exists mp_l, mtail.
    split; [exact SEP_L |].
    split; [exact TAIL |].
    apply massert_eqv_refl. }
  assert (SEP_NEW_TAIL: Forall_sep (coherent_var ce) (l1' ++ l2') (mp_l ** mtail)).
  { rewrite L_EQ. exact SEP_OLD. }
  apply Forall_sep_app in SEP_NEW_TAIL as (mp_l' & mp_r' & SEP_L' & SEP_R' & EQV_LR').
  assert (COH_NEW_HEAD: coherent_var ce (id0, (b, ofs, ty0, fp2)) mass3).
  { econstructor; [reflexivity | exact WTLOC_FP2]. }
  assert (SEP_NEW_MID: Forall_sep (coherent_var ce) ((id0, (b, ofs, ty0, fp2)) :: l2') (mass3 ** mp_r')).
  { econstructor; [exact COH_NEW_HEAD | exact SEP_R' | apply massert_eqv_refl]. }
  assert (EQV_NEW_LIST: massert_eqv (mass3 ** mp_l ** mtail) (mp_l' ** (mass3 ** mp_r'))).
  { etransitivity; [apply sepconj_morph_2; [reflexivity | exact EQV_LR'] |].
    apply sep_swap. }
  assert (SEP_NEW_LIST: Forall_sep (coherent_var ce) (l1' ++ (id0, (b, ofs, ty0, fp2)) :: l2') (mass3 ** mp_l ** mtail)).
  { eapply Forall_sep_app. exists mp_l', (mass3 ** mp_r').
    split; [exact SEP_L' |].
    split; [exact SEP_NEW_MID |].
    exact EQV_NEW_LIST. }
  assert (COH_FPM1: coherent_fpm ce fpm1 (mass3 ** mp_l ** mtail)).
  { apply coherent_fpm_intro. rewrite ELEMS_NEW. exact SEP_NEW_LIST. }
  exists bytes, m2, fpm1, (mass3 ** mp_l ** mtail).
  split; [exact LOAD |].
  split; [exact STORE |].
  split; [exact SET_MAP |].
  split; [exact COH_FPM1 |].
  rewrite (sep_assoc mass3 (mp_l ** mtail) MP).
  rewrite (sep_assoc mp_l mtail MP).
  exact MPRED_M2.
Qed.


(* ** General and historical lemmas *)

(* Lemma assign_loc_coherent_fpm: forall phl m ce fpm mass1 mass2 v vfp pfp chunk b ofs id MP ty *)
(*     (COH: coherent_fpm ce fpm mass1) *)
(*     (* (WTVAL: sem_wt_val ce vfp v mass2) *) *)
(*     (** This premises should be provided by the properties of *)
(*     eval_expr *) *)
(*     (MODE: match access_mode ty with *)
(*            | Ctypes.By_value chunk =>  *)
(*            | Ctypes.By_copy => *)
(*                (* ensure by type checking *) *)
               
(*     (MPRED: m |= mass1 ** mass2 ** MP) *)
(*     (* id may denote an external owner? We reduce all store for *)
(*     reference into store for their referred owner *) *)
(*     (GFP: get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, pfp)) *)
(*     (* The following properties should be derived from wt_footprint *) *)
(*     (AL: (alignof ce ty | ofs)) *)
(*     (* (MAT1: fp_match_chunk pfp chunk) *) *)
(*     (* (MAT2: fp_match_chunk vfp chunk),     *) *)
(*     (WTFP1: wt_footprint ce (fpm_to_tenv fpm) ty pfp) *)
(*     (WTFP2: wt_footprint ce (fpm_to_tenv fpm) ty vfp) *)
(*     (* (BYVAL: access_mode ty = Ctypes.By_value chunk) *) *)
(*     (SHALLOW: shallow_init pfp = true) *)
(*     (FPWF: fields_fp_well_formed ce pfp) *)
(*     (RANGE: 0 <= ofs /\ ofs + sizeof ce ty <= Ptrofs.max_unsigned), *)
(*     exists m1 fpm1 mass3, *)
(*       assign_loc ce ty m b (Ptrofs.repr ofs) v m1 *)
(*       /\ set_footprint_map (id, phl) vfp fpm = OK fpm1 *)
(*       /\ coherent_fpm ce fpm1 mass3 *)
(*       /\ m1 |= mass3 ** MP. *)
(* Proof. *)
