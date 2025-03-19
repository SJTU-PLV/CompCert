Require Import Coqlib.
Require Export LanguageInterface.
Require Export Smallstep.
Require Import CallconvAlgebra Invariant.
Require Import SmallstepLinkingSafe.

Local Open Scope inv_scope.

(* Refinement of invariants *)

(* [I2] is refined by [I1], meaning that any lts is safe under [I2] is
also safe under [I1] *)
Definition invref {li} (I1 I2: invariant li) :=
  forall w1 se q,
    symtbl_inv I1 w1 se ->
    query_inv I1 w1 q ->
    exists w2,
      symtbl_inv I2 w2 se
      /\ query_inv I2 w2 q
      /\ forall r,
        reply_inv I2 w2 r ->
        reply_inv I1 w1 r.

Definition inveqv {li} (I1 I2: invariant li) :=
  invref I1 I2 /\ invref I2 I1.

Global Instance inv_ref_preo li:
  PreOrder (@invref li).
Proof.
  split.
  - intros I w1 se q SINV QINV.
    eauto.
  - intros I1 I2 I3 R1 R2 w1 se q SINV QINV.
    edestruct R1 as (w2' & SINV' & QINV' & RINV'); eauto.
    edestruct R2 as (w3' & SINV'' & QINV'' & RINV''); eauto 10.
Qed.

Global Instance inveqv_equiv li:
  Equivalence (@inveqv li).
Proof.
  split.
  - intros I. split; reflexivity.
  - intros I1 I2. unfold inveqv. tauto.
  - intros I1 I2 I3 [R1 R1'] [R2 R2'].
    split; etransitivity; eauto.
Qed.

Global Instance inv_ref_po li:
  PartialOrder (@inveqv li) (@invref li).
Proof.
  firstorder.
Qed.

Global Instance open_safety_inv_ref:
  Monotonic
    (@module_type_safe)
    (forallr - @ liA, forallr - @ liB, invref ++>
     invref --> 
     forallr - @ L, forallr - @ PS,
     impl
    ).
Proof.
  intros liA liB IA1 IA2 RA IB1 IB2 RB L PS [SAFE].
  red in RB. econstructor.
  inv SAFE.
  set (ms se wB2 s :=
         exists wB1, type_safe_invariant se wB1 s
                /\ symtbl_inv IB1 wB1 se
                /\ forall r, reply_inv IB1 wB1 r ->
                       reply_inv IB2 wB2 r).  
  eapply Module_type_safe_components with (type_safe_invariant := ms).
  intros se wB2 SINV2 VSE.
  econstructor.
  - intros s t s' (wB1 & INV & SINV1 & RINV) STEP.
    exists wB1. repeat apply conj; auto.
    eapply internal_step_preserves; eauto.
  - intros s (wB1 & INV & SINV1 & RINV).
    eapply internal_state_progress; eauto.
  - intros q VQ QINV2.
    edestruct RB as (wB1 & SINV1 & QINV1 & RINV); eauto.
    edestruct @initial_preserves_progress as (s & INIT & INIT1); eauto.
    exists s. split; auto.
    intros s' INIT'.
    exists wB1. repeat apply conj; auto.
  - intros s q (wB1 & INV & SINV1 & RINV) ATEXT.
    edestruct @external_preserves_progress as (wA1 & SINV1' & QINV1 & RINV1); eauto.
    edestruct RA as (wA2 & SINV2' & QINV2' & RINV'); eauto.
    exists wA2. repeat apply conj; auto.
    intros r RINV2. specialize (RINV' r RINV2).
    edestruct RINV1 as (s' & AFEXT & AFEXT'); eauto.
    exists s'. split; auto.
    intros. exists wB1.
    repeat apply conj; auto.
  - intros s r (wB1 & SINV1 & QINV1 & RINV) FINAL.
    eapply RINV. eapply final_state_preserves; eauto.
Qed.

(** FIXME *)
Lemma test_rewrite_inv_ref_fail {liA liB} : forall (IA: invariant liA) (IB1 IB2: invariant liB) L PS,
    invref IB2 IB1 ->
    module_type_safe IA IB1 L PS ->
    module_type_safe IA IB2 L PS.
Proof.
  intros.
  (* why we cannot rewrite H? *)
  (* rewrite H. *)
  eapply open_safety_inv_ref. reflexivity. eauto. auto.
Qed.


Global Instance inv_compose_ref li:
  Proper (invref ++> invref ++> invref) (@inv_compose li).
Proof.
  intros I1 I1' R1 I2 I2' R2 (w1 & w2) se q (SINV1 & SINV2) (QINV1 & QINV2).
  edestruct R1 as (w1' & SINV1' & QINV1' & RINV1'); eauto.
  edestruct R2 as (w2' & SINV2' & QINV2' & RINV2'); eauto.
  exists (w1', w2'). repeat apply conj; eauto.
  intros. inv H. econstructor; eauto.
Qed.

(** Refinement of the calling conventions implies refinement of the
invariants *)

Global Instance cc_inv_ref li1 li2:
  Proper (invref ++> ccref ++> invref) (@invcc li1 li2).
Proof.
  intros I I' RI cc cc' RCC (w & wcc) se2 q2 (se1 & SINV1 & MSENV) (q1 & QINV1 & MQ).
  edestruct RI as (w' & SINV1' & QINV1' & RINV1'); eauto.
  edestruct RCC as (wcc' & MSENV' & MQ' & MR'); eauto.
  exists (w', wcc'). repeat apply conj.
  econstructor; eauto.
  econstructor; eauto.
  intros r (r'' & RINV'' & MR''). econstructor; eauto.
Qed.

Lemma inv_compose_assoc {li} I1 I2 I3:
  inveqv
    (@inv_compose li (@inv_compose li I1 I2) I3)
    (@inv_compose li I1 (@inv_compose li I2 I3)).
Proof.
  split.
  - red. intros ((w1 & w2) & w3). intros.
    inv H. inv H0. inv H. inv H1.
    exists (w1, (w2, w3)). repeat apply conj; eauto.
    intros. inv H1. inv H7. repeat econstructor; eauto.
  - red. intros (w1 & (w2 & w3)). intros.
    inv H. inv H0. inv H3. inv H2.
    exists (w1, w2, w3). repeat apply conj; eauto.
    intros. inv H2. inv H6. repeat econstructor; eauto.
Qed.

Lemma invcc_compose_assoc {li1 li2 li3} I cc1 cc2:
  inveqv
    (@invcc li2 li3 (@invcc li1 li2 I cc1) cc2)
    (@invcc li1 li3 I (@cc_compose li1 li2 li3 cc1 cc2)).
Proof.
  split.
  - red. intros ((w & wcc1) & wcc2) se3 q3 (se2 & (se1 & SINV1 & MSENV1) &MSENV2) (q2 & (q1 & QINV1 & MQ1) & MQ2).
    exists (w, (se2, wcc1, wcc2)).
    repeat apply conj.
    + econstructor. split; eauto.
      econstructor; eauto.
    + econstructor. split; eauto.
      econstructor; eauto.
    + intros. inv H. inv H0. inv H1. inv H0.
      repeat econstructor; eauto.
  - red. intros (w & ((se2 & wcc1) & wcc2)) se3 q3 SINV QINV.
    inv SINV. destruct H. inv H0.
    inv QINV. destruct H0. inv H3. destruct H4.
    exists ((w, wcc1), wcc2). repeat apply conj.
    1-2: repeat econstructor; eauto.
    intros. inv H5. destruct H6. inv H5. destruct H7.
    repeat econstructor; eauto.
Qed.


(* (I@@I1)@!cc ⊑ (I@!cc)@@I2 *)
Definition invcc_commute1 {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) :=
  forall w2 wcc q1 q2 se1 se2,
    match_query cc wcc q1 q2 ->
    match_senv cc wcc se1 se2 ->
    symtbl_inv I2 w2 se2 ->
    query_inv I2 w2 q2 ->
    exists w1, symtbl_inv I1 w1 se1
          /\ query_inv I1 w1 q1
          /\ forall r1 r2, match_reply cc wcc r1 r2 ->
                     reply_inv I1 w1 r1 ->
                     reply_inv I2 w2 r2.

(* (I@!cc)@@I2 ⊑ (I@@I1)@!cc *)
Definition invcc_commute2 {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) :=
  forall w1 wcc q1 q2 se1 se2,
    match_query cc wcc q1 q2 ->
    match_senv cc wcc se1 se2 ->
    symtbl_inv I1 w1 se1 ->
    query_inv I1 w1 q1 ->
    exists w2, symtbl_inv I2 w2 se2
          /\ query_inv I2 w2 q2
          /\ forall r1 r2, match_reply cc wcc r1 r2 ->
                     reply_inv I2 w2 r2 ->
                     reply_inv I1 w1 r1.

Lemma inv_commute_ref1 {li1 li2} I I1 I2 (cc: callconv li1 li2):
  invcc_commute1 cc I1 I2 ->
  invref ((I @! cc) @@ I2) ((I @@ I1) @! cc).
Proof.
  intros COM.
  red. intros ((w & wcc) & w2) se2 q2. intros.
  inv H. inv H1. inv H. 
  inv H0. inv H. destruct H0. 
  edestruct COM as (w1 & SINV1 & QINV1 & RINV1); eauto.
  exists ((w, w1), wcc). repeat apply conj.
  - repeat econstructor; eauto.
  - repeat econstructor; eauto.
  - intros. inv H5. destruct H6. inv H5.
    repeat econstructor; eauto.
Qed.

Lemma inv_commute_ref2 {li1 li2} I I1 I2 (cc: callconv li1 li2):
  invcc_commute2 cc I1 I2 ->
  invref ((I @@ I1) @! cc) ((I @! cc) @@ I2).
Proof. 
  intros COM.
  red. intros ((w & w1) & wcc) se1 q1. intros.
  inv H. destruct H1. inv H. 
  inv H0. destruct H. inv H. 
  edestruct COM as (w2 & SINV2 & QINV2 & RINV2); eauto.
  exists ((w, wcc), w2). split.
  repeat econstructor; eauto.
  split.
  repeat econstructor; eauto.
  intros. inv H. inv H6. destruct H. 
  repeat econstructor; eauto.
Qed.

(* cc_id satisfies invcc_commute1/2 *)

Lemma invcc_commute_id1 {li} (I: invariant li):
  invcc_commute1 cc_id I I.
Proof.
  red. intros w wcc q1 q2 se1 se2 MQ MSENV SINV2 QINV2.
  inv MSENV. inv MQ.
  exists w. repeat apply conj; eauto.
  intros. inv H. eauto.
Qed.

Lemma invcc_commute_id2 {li} (I: invariant li):
  invcc_commute2 cc_id I I.
Proof.
  red. intros w wcc q1 q2 se1 se2 MQ MSENV SINV2 QINV2.
  inv MSENV. inv MQ.
  exists w. repeat apply conj; eauto.
  intros. inv H. eauto.
Qed.

(** Commute property of invcc and ccinv *)

Lemma cc_inv_cc_equiv {li} (cc: callconv li li) I:
  inveqv (cc !@ I @! cc) I.
Proof.
  split.
  - red. intros (wcc1, (w, wcc2)) se q1 S Q.
    inv S. destruct H. inv H. destruct H1.
    inv Q. destruct H2. inv H2. destruct H4.
Abort.

(* Arbitary cc is difficult *)
Lemma id_inv_id_equiv {li} (I: invariant li) :
  inveqv (1 !@ I @! 1) I.
Proof.
  split.
  - red. intros (wcc1, (w, wcc2)) se q1 S Q.
    inv S. destruct H. inv H. destruct H1.
    inv Q. destruct H2. inv H2. destruct H4.
    inv H0. inv H1. inv H3. inv H4.
    exists w. repeat apply conj; auto.
    intros. eexists. split.
    econstructor. split. eauto. econstructor.
    econstructor.
  - red. intros w se q1 S Q.
    exists (tt, (w, tt)). repeat apply conj.
    repeat econstructor; eauto.
    repeat econstructor; eauto.
    intros. inv H. destruct H0. inv H. destruct H1. inv H1. inv H0.
    auto.
Qed.

    
