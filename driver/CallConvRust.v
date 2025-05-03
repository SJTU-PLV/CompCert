Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import ValueAnalysis.
Require Import CallConv.
Require Import Asm.
Require Import Rusttypes Rustlightown.

(** This file defines Rust specific calling conventions (e.g., ro_rs)
and provides the proof of their properties. *)

(* Definition of ro and wt for rust interface  *)

Inductive sound_rust_query ge m: rust_query -> Prop :=
  sound_rust_query_intro vf sg vargs:
    sound_memory_ro ge m ->
    sound_rust_query ge m (rsq vf sg vargs m).

Inductive sound_rust_reply m: rust_reply -> Prop :=
  sound_rust_reply_intro res tm:
    ro_acc m tm ->
    sound_rust_reply m (rsr res tm).

Definition ro_rs : invariant li_rs :=
  {|
    symtbl_inv '(row ge m) := eq ge;
    query_inv '(row ge m) := sound_rust_query ge m;
    reply_inv '(row ge m) := sound_rust_reply m;
  |}.

(* we just copy wt_c. *)
Definition wt_rs : invariant li_rs :=
  {|
    symtbl_inv :=
      fun '(se, sg) => eq se;
    query_inv :=
      fun '(se, sg) q =>
        sg = rsq_sg q /\ Val.has_type_list (rsq_args q) (map typ_of_type (rs_sig_args sg));
    reply_inv :=
      fun '(se, sg) r =>
        Val.has_type (rsr_retval r) (proj_rettype (rettype_of_type (rs_sig_res sg)));
  |}.

(* Compilation (R) in C side can be implemented in Rust side *)
Instance commut_rust_c R:
  Commutes cc_rust_c (cc_rs R) (cc_c R).
Proof.
  intros [[_ w] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i.
  exists (se2, wR, tt). repeat apply conj.
  - econstructor; auto. simpl; auto.
  - econstructor. split.
    econstructor; eauto.
    econstructor.
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2.
    econstructor. split.
    econstructor.
    econstructor; eauto. split; eauto.
    econstructor; auto.
Qed.

(* Compilation (ro) in C side can be implemented in Rust side. *)
Instance commut_rust_c_ro:
  Commutes cc_rust_c ro_rs ro.
Proof.
  intros [[_ w] (se' & m)] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv H. inv Hse. inv H. inv Hq1i.
  exists (se2, row se2 m, tt). repeat apply conj.
  - econstructor; simpl; auto.
    econstructor. auto.
  - econstructor. split.
    econstructor. econstructor; auto.
    econstructor.
  - intros r1 r2 (r1' & (Hr1 & Hr2)). inv Hr1. inv Hr2.
    inv H. econstructor. split.
    econstructor.
    econstructor. constructor. auto.
Qed.


(** Rust-level typing constraints *)

Inductive lessdef_rs_mq: rust_query -> rust_query -> Prop :=
  lessdef_rs_mq_intro vf sg args_ args m:
    Val.lessdef_list args_ args ->
    lessdef_rs_mq (rsq vf sg args_ m) (rsq vf sg args m).

Inductive lessdef_rs_mr: rust_reply -> rust_reply -> Prop :=
  lessdef_rs_mr_intro res_ res m:
    Val.lessdef res_ res ->
    lessdef_rs_mr (rsr res_ m) (rsr res m).

Program Definition lessdef_rs : callconv li_rs li_rs :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := lessdef_rs_mq;
    match_reply _ := lessdef_rs_mr;
  |}.
Next Obligation.
  split; auto.
Defined.

(* Intuition: wt_rs does not really utilize the rust type to do
compilation. It uses typ_of_type to transform to rust types to AST
type, so the compilation also can be done in C-side. Oppositely, the
C-side compilation based on wt_c can also be done in Rust side if we
can construct the corresponding rust types (it should work because
rust types have more information than AST type). *)
Lemma commut_rust_c_wt_lessdef:
  cceqv ((wt_rs @ lessdef_rs) @ cc_rust_c) (cc_rust_c @ (wt_c @ lessdef_c)).
Proof.
  split.
  - red. intros ((se' & ((se1'' & (se1''' & sg)) & ?)) & ?).
    intros se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    inv H0. inv Hse. inv Hqi2. destruct Hq1i. destruct H0. inv H1. inv H. inv H1.
    inv H0. inv H. simpl in H1.
    (* construct C signature from Rust *)
    exists (se2, tt, (se2, (se2, (signature_of_rust_signature sg0)), tt)).
    repeat apply conj.
    + econstructor. simpl. auto.
      do 4 econstructor. 
    + econstructor. split.
      econstructor.
      econstructor. split.
      * econstructor. econstructor. simpl. auto.
        simpl. auto.
      * econstructor. auto.
    + intros r1 r2. intros Hr. inv Hr. destruct H. inv H. inv H0.
      destruct H. inv H0. inv H. simpl in H3.
      econstructor. split.
      * econstructor. split.
        econstructor. eauto.
        econstructor. eauto.
      * econstructor.
  - red. intros ((se' & ?) & ((se1'' & (se1''' & sg)) & ?)).
    intros se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    inv Hq1i. inv Hse. inv H. inv H1. inv H0.
    inv Hqi2. destruct H. inv H0. inv H. inv H2.
    cbn [cq_args cq_sg] in *.
    exists (se2,(se2, (se2, sg0), tt), tt).
    repeat apply conj.
    + do 4  econstructor.
    + econstructor. split.
      econstructor. split.
      econstructor. econstructor; eauto.
      econstructor. eauto.
      econstructor.
    + intros r1 r2. intros Hr. inv Hr. destruct H. inv H. inv H2.
      destruct H3. inv H2. inv H. simpl in H2.
      econstructor. split.
      * econstructor.
      * econstructor. split.
        econstructor; eauto.
        econstructor. auto.
Qed.


(* copy from lessdef_c_cklr in CallConv *)
Lemma lessdef_rs_cklr R:
  cceqv (lessdef_rs @ cc_rs R) (cc_rs R).
Proof.
  split.
  - intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hqi2. inv Hq1i.
    eexists wR. cbn. repeat apply conj; auto.
    + constructor; auto. clear - H0 H5.
      eapply val_lessdef_inject_list_compose; eauto.
    + intros r1 r2 Hr. exists r1; split; auto.
      destruct r1; constructor; auto.
  - intros wR se1 se2 q1 q2 Hse Hq.
    exists (se1, tt, wR). repeat apply conj; cbn; eauto.
    + exists q1. split; auto. destruct q1. constructor; auto.
      clear. induction rsq_args; constructor; auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2).
      exists wR'. split; auto. destruct Hri2; inv Hr1i; constructor; auto.
      eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

(* copy from wt_R_refinement in CallConv *)
Theorem wt_rs_R_refinement R:
  ccref (cc_rs R @ (wt_rs @ lessdef_rs)) ((wt_rs @ lessdef_rs) @ cc_rs R).
Proof.
  rewrite cc_compose_assoc. rewrite lessdef_rs_cklr.
  intros [[se wR][[se' [se'' sg]] ?]].
  intros se1 se2 q1 q2 [Hse1 [Hse2 Hse3]] [q2' [Hq1 [q2'' [Hq2 Hq3]]]].
  inv Hse2. inv Hse3. cbn in H. cbn in Hq1. subst se''.
  inv Hq1. inv Hq2. inv Hq3. cbn in H3. destruct H3 as [? TYPE]. subst.
  exists (se1,(se1,sg0),wR). repeat apply conj.
  - constructor; cbn; eauto. constructor; eauto.
  - cbn in H0. cbn in H.
    exists (rsq vf1 sg0 vargs1 m1). split.
    econstructor; eauto. split.
    econstructor; eauto.
    eapply val_has_type_list_inject; eauto.
    econstructor; eauto.
    eapply val_inject_lessdef_list_compose; eauto.
  - intros r1 r2 [r1' [Hr1 Hr2]].
    inv Hr1. cbn in H3.
    destruct Hr2 as [w [Hw Hr2]].
    inv Hr2.
    set (res' := Val.ensure_type vres2 (proj_sig_res (signature_of_rust_signature sg0)) ).
    exists (rsr res' m2'). split. exists w. split. eauto.
    econstructor; eauto.
    unfold res'.
    apply has_type_inject; eauto.
    exists (rsr res' m2'). split.
    constructor; eauto. cbn. unfold res'. apply Val.ensure_has_type.
    constructor; eauto. unfold res'.
    destruct vres2, (proj_sig_res (signature_of_rust_signature sg0)); auto. 
Qed.

(* copy from commut_wt_c in CallConv *)
Instance commut_wt_rs (R : cklr):
  Commutes (wt_rs @ lessdef_rs) (cc_rs R) (cc_rs R).
Proof.
 red. rewrite cc_compose_assoc. rewrite lessdef_rs_cklr.
  intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H4. cbn [rsq_sg rsq_args] in *.
  eexists (se2, wR, (se2, (se2, sg), tt)). repeat apply conj; cbn.
  + repeat constructor; cbn; auto.
  + edestruct has_type_inject_list as (vl2 & Hvl2 & Hvl & Hvl'); eauto.
    exists (rsq vf2 sg vl2 m2). split.
    * constructor; eauto.
    * eexists. split; constructor; cbn; eauto.
  + intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. cbn in *.
    eexists; split.
    * constructor. cbn. eapply val_has_type_inject; eauto.
    * exists wR'. split; auto. constructor; eauto.
      eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

(* just copy trans_injp_ro_outgoing *)
Lemma trans_injp_rors_outgoing:
  ccref ((ro_rs @ (cc_rs injp)) @ (ro_rs @ (cc_rs injp))) (ro_rs @ (cc_rs injp)).
Proof.
  red.
  intros w se1' se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2' [[se1 wi1] w12]] [[se2 wi2] w23]].
  destruct MSTBL13 as [[Hsi1 MSTBL12] [Hsi2 MSTBL23]].
  destruct MMEM13 as [m2 [[q1' [Hmi1 MMEM12]] [q2' [Hmi2 MMEM23]]]].
  inv Hsi1. inv Hsi2. inv Hmi1. inv Hmi2. rename q1' into q1. rename q2' into q2.
  inv MMEM12. inv H5. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H13. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H12, MSTBL12, H10, MSTBL23,H3, H4. destruct wi1. inv H. inv H1.
  destruct wi2. inv H0. inv H2.
  exists (se1, (row se1 m1), (injpw (compose_meminj j12 j23)
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl.
  repeat apply conj.
  - constructor. eauto.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - exists (rsq vf1 sg vargs1 m1). split. constructor; eauto. constructor; eauto.
    constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
    eapply CKLRAlgebra.val_inject_list_compose.
    econstructor; eauto.
  - intros r1 r3 [r2 [Hi2 [w13' [INCR13' Hr13]]]].
    inv Hr13. inv H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2' into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & INCRn1 & INCRn2 & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME & ADDBLOCK).
    subst. cbn in *.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' m2'_sup INJ12 ).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    set (w1' := injpw j12' m1' m2' INJ12').
    set (w2' := injpw j23' m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2').
    eapply UNCHANGE21; eauto.
    exists (rsr vres2 m2'). split.
    + 
      exists (rsr vres1 m1'). split. cbn. auto.
      exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. red. unfold compose_meminj.
      rewrite H1. reflexivity.
      constructor; eauto. constructor; eauto.
    + exists (rsr vres2 m2'). split. cbn. econstructor. constructor.
      constructor. eapply ROUNC2; eauto.
      inversion UNC21. eauto.
      eapply MAXPERM2; eauto.
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply UNCHANGE22; eauto. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Qed.

(* just copy trans_injp_inv_incoming *)
Lemma trans_rs_injp_inv_incoming (I: invariant li_rs) :
  ccref (I @ cc_rs injp) ((I @ cc_rs injp) @ (I @ cc_rs injp)).
Proof.
  red. intros [[se wi] w] se1 se2 q1' q2 [Hse1 Hse2] [q1 [Hq1 Hq2]].
  inv Hse1. inv Hq1. inv Hse2. inv Hq2. inv H6. rename m0 into m1.
  rename m3 into m2. cbn in H4, H5.
  exists (se, (se,wi, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm))),
      (se,wi, (injpw f m1 m2 Hm))). repeat apply conj.
  - constructor. constructor. red. cbn. constructor. auto.
    constructor; eauto. eapply match_stbls_dom; eauto.
    constructor. constructor. auto.
    constructor; eauto.
  - eexists (rsq vf1 sg vargs1 m1). split. eexists. split. constructor. eauto.
    econstructor; cbn; eauto.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    eexists. split. constructor. eauto. constructor; eauto. constructor.
  - intros r1' r3 [r2' [[r1 [Hi1 Hr1]] [r2 [Hi2 Hr2]]]].
    inv Hi1. inv Hi2.
    exists r1. split. red. cbn. constructor. auto.
    clear H6 H8 H0 H.
    destruct Hr1 as [w12' [Hw12' Hr12']]. destruct Hr2 as [w23' [Hw23' Hr23']].
    destruct w12' as [f12' m1' m2' Hm12']. destruct w23' as [f23' m2'' m3' Hm23'].
    inv Hw12'. inv Hw23'. cbn in *.
    inv Hr12'. inv Hr23'. cbn in *. inv H0. inv H27.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'1 into m3'.
    eexists (injpw (compose_meminj f12' f23') m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. red. unfold meminj_dom. rewrite H0. reflexivity.
      * red. intros. unfold compose_meminj.
        erewrite H17. erewrite H25; eauto.
        2: unfold meminj_dom; rewrite H0; reflexivity.
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H18; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H26; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
Qed.


(* Intuition: the compilation in Rust side (left) can be implementd in
C side (right) because the compilation does not utilize the rust types
(which resides in the signatue of the query), so this refinement
should be correct *)
Lemma injp_rs__rc_injp:
  ccref (cc_rs injp @ cc_rust_c) (cc_rust_c @ injp).
Proof.
  red. intros ((se & w1) & w2) se1 se2 q1 q2 (Hse1 & Hse2) (q2' & (Hq1 & Hq2)).
  inv Hse2. inv Hq2. inv Hq1.
  exists (se1, tt, w1). repeat apply conj.
  - econstructor. simpl. auto.
    auto.
  - econstructor. split. econstructor.
    econstructor; auto.
  - intros r1 r2 (r1' & (Hr1 & Hr2)).
    inv Hr1. destruct Hr2 as (w1' & acc & Hr2). inv Hr2.
    econstructor. split.
    + econstructor. split. eauto.
      econstructor; eauto.
    + econstructor.
Qed.

  
(* ro_rs is defined by copying ro in C side, so it should not utilize
any properties of Rust types to perform optimizations. It can be moved
to (or implemented in) C-side. *)
Lemma ro_rs__rc_ro:
  ccref (ro_rs @ cc_rust_c) (cc_rust_c @ ro).
Proof.
  red. intros ((se & (se' & m)) & w2) se1 se2 q1 q2 (Hse1 & Hse2) (q2' & (Hq1 & Hq2)).
  inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H0. inv H.
  exists (se2, tt, row se2 m0). repeat apply conj.
  - econstructor; simpl; auto.
    econstructor. auto.
  - econstructor. split.
    econstructor.
    econstructor; eauto. econstructor. auto.
  - intros r1 r2 (r1' & (Hr1 & Hr2)). inv Hr1. inv Hr2.
    inv H. econstructor. split.
    econstructor. econstructor. auto.
    econstructor.
Qed.

(** Self simulation of Rustlightown under ro_rs *)


Lemma ro_acc_assign_loc : forall m m' ce t b ofs v,
    assign_loc ce t m b ofs v m' ->
    ro_acc m m'.
Proof.
  intros. inv H.
  - unfold Mem.storev in H1. eapply ro_acc_store; eauto.
  - eapply ro_acc_storebytes; eauto.
Qed.

Lemma ro_acc_bind : forall m m' ge e params args,
    bind_parameters ge e m params args m' -> ro_acc m m'.
Proof.
  intros. induction H. eapply ro_acc_refl.
  eapply ro_acc_trans. eapply ro_acc_assign_loc; eauto.
  eauto.
Qed.

Lemma ro_acc_allocs : forall m m' ge pa e1 e2,
    alloc_variables ge e1 m pa e2 m' -> ro_acc m m'.
Proof.
  intros. induction H. eapply ro_acc_refl.
  eapply ro_acc_trans. eapply ro_acc_alloc; eauto. auto.
Qed.

Lemma ro_acc_fe : forall m m' ge f args e,
    function_entry ge f args m e m' ->
    ro_acc m m'.
Proof.
  intros. inv H.
  eapply ro_acc_trans.
  eapply ro_acc_allocs; eauto.
  eapply ro_acc_bind; eauto.
Qed.

Lemma ro_acc_free_sem: forall ge args v m1 m2 t,
    extcall_free_sem ge args m1 t v m2 ->
    ro_acc m1 m2.
Proof.
  intros. inv H.
  - eapply ro_acc_free. eauto.
  - eapply ro_acc_refl.
Qed.

Lemma ro_acc_drop_box_rec: forall tyl ge b ofs m1 m2,
    drop_box_rec ge b ofs m1 tyl m2 ->
    ro_acc m1 m2.
Proof.
  induction tyl; intros.
  inv H. eapply ro_acc_refl.
  inv H. eapply ro_acc_trans.
  inv H5. eapply ro_acc_free. eauto.
  eauto.
Qed.

(* Rustlightown ro sound_state *)
Inductive sound_state se0 m0 : state -> Prop :=
| ro_inv_state f s k e own m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (State f s k e own m)
| ro_inv_callstate v args c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Callstate v args c m)
| ro_inv_returnstate v c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Returnstate v c m)
| ro_inv_dropinsert f st dk k e own m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Dropinsert f st dk k e own m)
| ro_inv_dropplace f st drops k e own m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Dropplace f st drops k e own m)
| ro_inv_dropstate id v st membs k m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Dropstate id v st membs k m)
.

Definition ro_inv '(row se m) := sound_state se m.

Lemma rustlight_ro_preserves prog:
  preserves (Rustlightown.semantics prog) ro_rs ro_rs ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros.
    Ltac Solve_ro_pre :=
      match goal with
      | [H: assign_loc _ _ _ _ _ _ _ |- _] => apply ro_acc_assign_loc in H
      | [H: external_call _ _ _ _ _ _ _ |- _] => apply ro_acc_external in H
      | [H: Mem.free_list _ _ = Some _ |- _] => apply ro_acc_free_list in H
      | [H: function_entry _ _ _ _ _ _ |- _ ] => apply ro_acc_fe in H
      | [H: Mem.storev _ _ _ _ = Some _ |- _ ] => apply ro_acc_store in H
      | [H: Mem.store _ _ _ _ _ = Some _ |- _ ] => apply ro_acc_store in H
      | [H: Mem.alloc _ _ _ = _ |- _ ] => apply ro_acc_alloc in H
      | [H: extcall_free_sem _ _ _ _ _ _ |- _ ] => apply ro_acc_free_sem in H
      | [H: drop_box_rec _ _ _ _ _ _ |- _ ] => apply ro_acc_drop_box_rec in H
      | _ => idtac
      end.  
    inv H0; inv H; try inv SDROP; repeat Solve_ro_pre; econstructor; eauto using ro_acc_sound, ro_acc_trans.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor.
    eapply ro_acc_sound; eauto.
    eapply ro_acc_trans; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Lemma rustlight_ro_selfsim:
  forall p: (Rustlight.program),
    let sem := Rustlightown.semantics p in
    forward_simulation ro_rs ro_rs sem sem.
Proof.
  intros. eapply preserves_fsim. eapply rustlight_ro_preserves.
Qed.

(** Self simulation of RustIRown under ro_rs. It is used to construct
the calling convention from RustIR to Asm. *)
Require Import RustIRown.

(* Rustlightown ro sound_state *)
Inductive sound_state_rustir se0 m0 : state -> Prop :=
| ro_inv_state_ir f s k e own m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state_rustir se0 m0 (State f s k e own m)
| ro_inv_callstate_ir v args c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state_rustir se0 m0 (Callstate v args c m)
| ro_inv_returnstate_ir v c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state_rustir se0 m0 (Returnstate v c m)
| ro_inv_dropplace_ir f st drops k e own m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state_rustir se0 m0 (Dropplace f st drops k e own m)
| ro_inv_dropstate_ir id v st membs k m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state_rustir se0 m0 (Dropstate id v st membs k m)
.

Lemma ro_acc_drop_box_rec_ir: forall tyl ge b ofs m1 m2,
    RustIR.drop_box_rec ge b ofs m1 tyl m2 ->
    ro_acc m1 m2.
Proof.
  induction tyl; intros.
  inv H. eapply ro_acc_refl.
  inv H. eapply ro_acc_trans.
  inv H5. eapply ro_acc_free. eauto.
  eauto.
Qed.

Lemma ro_acc_fe_ir : forall m m' ge f args e,
    RustIR.function_entry ge f args m e m' ->
    ro_acc m m'.
Proof.
  intros. inv H.
  eapply ro_acc_trans.
  eapply ro_acc_allocs; eauto.
  eapply ro_acc_bind; eauto.
Qed.


Definition ro_inv_ir '(row se m) := sound_state_rustir se m.

Lemma rustir_ro_preserves prog:
  preserves (RustIRown.semantics prog) ro_rs ro_rs ro_inv_ir.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros.
    Ltac Solve_ro_pre_ir :=
      match goal with
      | [H: assign_loc _ _ _ _ _ _ _ |- _] => apply ro_acc_assign_loc in H
      | [H: external_call _ _ _ _ _ _ _ |- _] => apply ro_acc_external in H
      | [H: Mem.free_list _ _ = Some _ |- _] => apply ro_acc_free_list in H
      | [H: RustIR.function_entry _ _ _ _ _ _ |- _ ] => apply ro_acc_fe_ir in H
      | [H: Mem.storev _ _ _ _ = Some _ |- _ ] => apply ro_acc_store in H
      | [H: Mem.store _ _ _ _ _ = Some _ |- _ ] => apply ro_acc_store in H
      | [H: Mem.alloc _ _ _ = _ |- _ ] => apply ro_acc_alloc in H
      | [H: extcall_free_sem _ _ _ _ _ _ |- _ ] => apply ro_acc_free_sem in H
      | [H: RustIR.drop_box_rec _ _ _ _ _ _ |- _ ] => apply ro_acc_drop_box_rec_ir in H
      | _ => idtac
      end.  
    inv H0; inv H; try inv SDROP; repeat Solve_ro_pre_ir; econstructor; eauto using ro_acc_sound, ro_acc_trans.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor.
    eapply ro_acc_sound; eauto.
    eapply ro_acc_trans; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

Lemma rustir_ro_selfsim:
  forall p: (RustIR.program),
    let sem := RustIRown.semantics p in
    forward_simulation ro_rs ro_rs sem sem.
Proof.
  intros. eapply preserves_fsim. eapply rustir_ro_preserves.
Qed.
