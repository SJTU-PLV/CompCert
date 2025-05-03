Require Import Axioms.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Export CKLR.

(** Algebraic structures on CKLRs *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the CKLR [R] is refined by the
  CKLR [R'], meaning that any [R']-simulation is also a [R]-simulation. *)

Definition subcklr (Q R: cklr) :=
  forall wq se1 se2 m1 m2,
    match_stbls Q wq se1 se2 ->
    match_mem Q wq m1 m2 ->
    exists wr,
      match_stbls R wr se1 se2 /\
      match_mem R wr m1 m2 /\
      inject_incr (mi Q wq) (mi R wr) /\
      forall wr' m1' m2',
        match_mem R wr' m1' m2' ->
        wr ~> wr' ->
        exists wq',
          match_mem Q wq' m1' m2' /\
          wq ~> wq' /\
          inject_incr (mi R wr') (mi Q wq').

Definition eqcklr R1 R2 :=
  subcklr R1 R2 /\ subcklr R2 R1.

Global Instance subcklr_preo:
  PreOrder subcklr.
Proof.
  split.
  - intros R w q1 q2 Hq.
    exists w; intuition eauto.
  - intros R1 R2 R3 H12 H23 w1 sea seb ma mb Hse1 Hm1.
    destruct (H12 w1 sea seb ma mb Hse1 Hm1) as (w2 & Hse2 & Hm2 & Hincr12 & H21); clear H12.
    destruct (H23 w2 sea seb ma mb Hse2 Hm2) as (w3 & Hse3 & Hm3 & Hincr23 & H32); clear H23.
    exists w3. repeat apply conj; eauto using inject_incr_trans.
    intros w3' ma' mb' Hm3' Hw3'.
    destruct (H32 w3' ma' mb' Hm3' Hw3') as (w2' & Hm2' & Hw2' & Hincr32).
    destruct (H21 w2' ma' mb' Hm2' Hw2') as (w1' & Hm1' & Hw1' & Hincr21).
    exists w1'; intuition eauto using inject_incr_trans.
Qed.

Global Instance eqcklr_equiv:
  Equivalence eqcklr.
Proof.
  split.
  - intros R.
    split; reflexivity.
  - intros R1 R2. unfold eqcklr.
    tauto.
  - intros R1 R2 R3 [H12 H21] [H23 H32].
    split; etransitivity; eauto.
Qed.

Global Instance subcklr_po:
  PartialOrder eqcklr subcklr.
Proof.
  unfold eqcklr. red. generalize subcklr.
  firstorder.
Qed.


(** * Composition *)

(** ** Preliminaries *)

Lemma option_le_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (option_le (rel_compose R1 R2))
    (rel_compose (option_le R1) (option_le R2)).
Proof.
  split.
  - intros _ _ [x z (y & Hxy & Hyz) | z];
    eexists; split; constructor; eauto.
  - intros x z (y & Hxy & Hyz).
    destruct Hxy; [inversion Hyz; clear Hyz; subst | ];
    constructor; eexists; split; eauto.
Qed.

Lemma list_rel_compose {A B C} (R1: rel A B) (R2: rel B C):
  eqrel
    (list_rel (rel_compose R1 R2))
    (rel_compose (list_rel R1) (list_rel R2)).
Proof.
  split.
  - induction 1.
    + exists nil; split; constructor.
    + destruct H as (z & ? & ?).
      destruct IHlist_rel as (z0 & ? & ?).
      exists (z::z0); split; constructor; eauto.
  - intros la lc (lb & H1 & H2).
    revert lc H2.
    induction H1; intros lc H2; inv H2.
    + constructor.
    + constructor; eauto.
Qed.

Global Instance compose_meminj_incr:
  Monotonic compose_meminj (inject_incr ++> inject_incr ++> inject_incr).
Proof.
  intros f1 f2 Hf g1 g2 Hg b xb xdelta.
  unfold compose_meminj.
  destruct (f1 b) as [[b' delta] | ] eqn:Hb'; try discriminate.
  erewrite Hf by eauto.
  destruct (g1 b') as [[b'' delta'] | ] eqn:Hb''; try discriminate.
  erewrite Hg by eauto.
  tauto.
Qed.

Lemma val_inject_compose f g:
  eqrel
    (Val.inject (compose_meminj f g))
    (rel_compose (Val.inject f) (Val.inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try (eexists; split; constructor).
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    exists (Vptr bi (Ptrofs.add ofs1 (Ptrofs.repr di))).
    split; econstructor; eauto.
    rewrite add_repr, Ptrofs.add_assoc.
    reflexivity.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; econstructor.
    unfold compose_meminj.
    + rewrite H, H3.
      reflexivity.
    + rewrite add_repr, Ptrofs.add_assoc.
      reflexivity.
Qed.

Lemma memval_inject_compose f g:
  eqrel
    (memval_inject (compose_meminj f g))
    (rel_compose (memval_inject f) (memval_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv; try solve [eexists; split; constructor].
    apply val_inject_compose in H.
    destruct H as (vi & Hv1i & Hvi2).
    eexists; split; constructor; eauto.
  - intros v1 v3 Hv.
    destruct Hv as (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23; constructor.
    apply val_inject_compose.
    eexists; split; eauto.
Qed.

Lemma ptr_inject_compose f g:
  eqrel
    (ptr_inject (compose_meminj f g))
    (rel_compose (ptr_inject f) (ptr_inject g)).
Proof.
  split.
  - intros v1 v3 Hv.
    destruct Hv.
    unfold compose_meminj in H.
    destruct (f b1) as [[bi di] | ] eqn:Hi; try discriminate.
    destruct (g bi) as [[bj dj] | ] eqn:Hj; try discriminate.
    inv H.
    rewrite Z.add_assoc.
    exists (bi, ofs1 + di); split; econstructor; eauto.
  - intros v1 v3 (v2 & Hv12 & Hv23).
    destruct Hv12; inv Hv23.
    rewrite <- Z.add_assoc.
    constructor.
    unfold compose_meminj.
    rewrite H, H3.
    reflexivity.
Qed.

Lemma ptrbits_inject_compose f g:
  eqrel
    (ptrbits_inject (compose_meminj f g))
    (rel_compose (ptrbits_inject f) (ptrbits_inject g)).
Proof.
  split.
  - destruct 1.
    unfold compose_meminj in H.
    destruct (f b1) as [[bI delta1I] | ] eqn:H1I; [ | discriminate].
    exists (bI, Ptrofs.add ofs1 (Ptrofs.repr delta1I)); split; eauto.
    destruct (g bI) as [[xb2 deltaI2] | ] eqn:HI2; [ | discriminate].
    inv H.
    rewrite add_repr.
    rewrite <- Ptrofs.add_assoc.
    constructor; eauto.
  - intros p1 p3 (p2 & H12 & H23).
    destruct H12 as [b1 ofs1 b2 delta12].
    inv H23.
    rewrite Ptrofs.add_assoc.
    rewrite <- add_repr.
    constructor.
    unfold compose_meminj. rewrite H, H3.
    reflexivity.
Qed.

Lemma rptr_inject_compose f g:
  subrel
    (rptr_inject (compose_meminj f g))
    (rel_compose (rptr_inject f) (rptr_inject g)).
Proof.
  unfold rptr_inject.
  intros p1 p3 Hp.
  rewrite ptr_inject_compose in Hp.
  rewrite ptrbits_inject_compose in Hp.
  destruct Hp as [(p2 & H12 & H23) | [q1 q3 (q2 & H12 & H23)]].
  - exists p2; split; rauto.
  - exists (ptrbits_unsigned q2); split; rauto.
Qed.

Lemma ptrrange_inject_compose f g:
  eqrel
    (ptrrange_inject (compose_meminj f g))
    (rel_compose (ptrrange_inject f) (ptrrange_inject g)).
Proof.
  split.
  - destruct 1.
    apply ptr_inject_compose in H.
    destruct H as ([bi ofsi] & H1 & H2).
    exists (bi, ofsi, ofsi + sz).
    split; constructor; eauto.
  - intros r1 r3 (r2 & H12 & H23).
    destruct H12; inv H23.
    assert (sz0 = sz) by lia; subst.
    constructor.
    apply ptr_inject_compose.
    eexists; split; eauto.
Qed.

Lemma block_inject_compose f g:
  eqrel
    (block_inject (compose_meminj f g))
    (rel_compose (block_inject f) (block_inject g)).
Proof.
  split.
  - intros b1 b3 [d13 H13].
    unfold compose_meminj in H13.
    destruct (f b1) as [[b2 d12] | ] eqn:H12; [ | discriminate].
    destruct (g b2) as [[xb3 d23] | ] eqn:H23; [ | discriminate].
    inv H13.
    exists b2; eexists; eauto.
  - intros b1 b3 (b2 & [d2 H12] & [d3 H23]).
    exists (d2 + d3).
    unfold compose_meminj.
    rewrite H12, H23.
    reflexivity.
Qed.

Lemma block_inject_sameofs_compose f g:
  subrel
    (rel_compose (block_inject_sameofs f) (block_inject_sameofs g))
    (block_inject_sameofs (compose_meminj f g)).
Proof.
  intros b1 b3 (b2 & H12 & H23).
  red in H12, H23 |- *.
  unfold compose_meminj. rewrite H12, H23.
  reflexivity.
Qed.

Lemma flat_inj_idemp thr:
  compose_meminj (Mem.flat_inj thr) (Mem.flat_inj thr) = Mem.flat_inj thr.
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj, Mem.flat_inj.
  destruct Mem.sup_dec eqn:Hb; eauto.
  rewrite Hb.
  reflexivity.
Qed.

(** ** Definition *)

Program Definition cklr_compose (R1 R2: cklr): cklr :=
  {|
    world := world R1 * world R2;
    wacc := wacc R1 * wacc R2;
    mi w := compose_meminj (mi R1 (fst w)) (mi R2 (snd w));
    match_stbls w := rel_compose (match_stbls R1 (fst w)) (match_stbls R2 (snd w));
    match_mem w := rel_compose (match_mem R1 (fst w)) (match_mem R2 (snd w));
  |}.

Next Obligation.
  rauto.
Qed.

(** mi_acc_separated *)
Next Obligation.
  rename w1 into w2'.
  rename w0 into w1'.
  rename w into w1.
  intros b1 b2 delta Hw Hw'.

  destruct H as (m & Hm1 & Hm2).
  destruct H0 as [HR1 HR2].
  cbn in *.

  specialize (mi_acc_separated R1 _ _ _ _ Hm1 HR1) as sep1.
  specialize (mi_acc_separated R2 _ _ _ _ Hm2 HR2) as sep2.
  unfold inject_separated in sep1, sep2.
  unfold compose_meminj in Hw, Hw'.
  destruct (mi R1 w1' b1) as [[b11' delta11'] |] eqn:HR1w1'; [|discriminate].
  destruct (mi R2 w2' b11') as [[b22' delta22'] |] eqn:HR2w2'; [|discriminate].
  injection Hw'. clear Hw'. intros; subst delta b22'.
  destruct (mi R1 w1 b1) as [[b11 delta11] |] eqn:HR1w1.
  - destruct (mi R2 w2 b11) as [[b22 delta22] |] eqn:HR2w2.
    discriminate.
    assert (HR1w1'_alt: mi R1 w1' b1 = Some (b11, delta11)).
    { eapply mi_acc; eauto. }
    rewrite HR1w1' in HR1w1'_alt. inv HR1w1'_alt.
    destruct (sep2 _ _ _ HR2w2 HR2w2') as [Hnvb11 Hnvb2].
    split; [|assumption].
    contradict Hnvb11.
    eapply (cklr_valid_block _ _ _ _ Hm1); eauto.
    eexists. eauto.
  - destruct (sep1 _ _ _ HR1w1 HR1w1') as [Hnvb1 Hnvb11'].
    split. auto.
    destruct (mi R2 w2 b11') as [[b22 delta22] |] eqn:HR2w2.
    + contradict Hnvb11'.
      assert (HR2w2'_alt: mi R2 w2' b11' = Some (b22, delta22)).
      { eapply mi_acc; eauto. }
      rewrite HR2w2' in HR2w2'_alt. inv HR2w2'_alt.
      eapply cklr_valid_block; eauto.
      eexists. eauto.
    + eapply sep2; eauto.
Qed.

Next Obligation.
  intros [w12 w23] [w12' w23'] [H12 H23]. cbn.
  eapply rel_compose_subrel; rauto.
Qed.

Next Obligation.
  cbn. intros se1 se3 (se2 & Hse12 & Hse23).
  apply match_stbls_proj in Hse12.
  apply match_stbls_proj in Hse23.
  eapply Genv.match_stbls_compose; eauto.
Qed.

Next Obligation.
  destruct H as (sei & Hse1i & Hsei2), H0 as (mi & Hm1i & Hmi2). cbn in *.
  eapply (match_stbls_support R2); eauto.
  eapply (match_stbls_support R1); eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) lo hi.
  edestruct (cklr_alloc R1 w12 m1 m2 Hm12 lo hi)
    as (w12' & Hw12' & Hm12' & Hb12).
  edestruct (cklr_alloc R2 w23 m2 m3 Hm23 lo hi)
    as (w23' & Hw23' & Hm23' & Hb23).
  exists (w12', w23'); split; [rauto | ].
  rstep. simpl. split.
  - eexists; split; rauto.
  - red. apply block_inject_sameofs_compose.
    eexists; split; eauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [[b1 lo1] hi1] [[b3 lo3] hi3] H.
  apply ptrrange_inject_compose in H.
  destruct H as ([[b2 lo2] hi2] & Hr12 & Hr23).
  simpl in *. red.
  destruct (Mem.free m1 _ _ _) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23').
  split; [rauto | ].
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  red. simpl in *. unfold klr_pullw.
  rewrite val_inject_compose.
  apply option_le_compose.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] chunk m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  simpl in *. red. unfold klr_pullw in *.
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  apply val_inject_compose in Hv. destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.store chunk m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 ofs1] [b3 ofs3] Hptr sz.
  apply ptr_inject_compose in Hptr.
  destruct Hptr as ([b2 ofs2] & Hptr12 & Hptr23).
  unfold k1, klr_pullw. simpl in *.
  eapply option_le_subrel. (* XXX coqrel *)
  {
    apply list_subrel.
    apply memval_inject_compose.
  }
  rewrite list_rel_compose.
  apply option_le_compose.
  eexists; split; rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 (m2 & Hm12 & Hm23) [b1 o1] [b3 o3] Hptr v1 v3 Hv.
  unfold k1, klr_pullw in *. simpl in *.
  apply rptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  rewrite memval_inject_compose in Hv. apply list_rel_compose in Hv.
  destruct Hv as (v2 & Hv12 & Hv23).
  destruct (Mem.storebytes m1 b1 o1 v1) as [m1'|] eqn:H1; [|constructor].
  transport H1.
  transport H.
  rewrite H1. constructor.
  exists (w12', w23'); split; [rauto | ].
  eexists; split; try rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm [b1 o1] [b3 o3] Hptr pk pe.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply ptr_inject_compose in Hptr. destruct Hptr as ([b2 o2] & Hp12 & Hp23).
  etransitivity; rauto.
Qed.

Next Obligation.
  intros [w12 w23] m1 m3 Hm b1 b3 Hb.
  unfold k, klr_pullw in *. simpl in *.
  destruct Hm as (m2 & Hm12 & Hm23).
  apply block_inject_compose in Hb. destruct Hb as (b2 & Hb12 & Hb23).
  etransitivity; rauto.
Qed.

Next Obligation. (* no overlap *)
  intros a1 a2 da b1 b2 db oa ob Hab1 Ha Hb Hoa Hob. simpl in *.
  destruct H as (mx & Hm1x & Hmx2).
  unfold compose_meminj in *.
  destruct (mi R1 w a1) as [[ax da1x] | ] eqn:Ha1x; [ | discriminate].
  destruct (mi R2 w0 ax) as [[ay dax2] | ] eqn:Hax2; [ | discriminate].
  inv Ha.
  destruct (mi R1 w b1) as [[bx db1x] | ] eqn:Hb1x; [ | discriminate].
  destruct (mi R2 w0 bx) as [[bz dbz2] | ] eqn:Hbx2; [ | discriminate].
  inv Hb.
  assert (Mem.perm mx ax (oa + da1x) Max Nonempty).
  { revert Hoa. repeat rstep. left. constructor; eauto. }
  assert (Mem.perm mx bx (ob + db1x) Max Nonempty).
  { revert Hob. repeat rstep. left. constructor; eauto. }
  edestruct (cklr_no_overlap R1 w m1 mx); eauto.
  - edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
    rewrite !Z.add_assoc.
    eauto.
  - destruct (eq_block ax bx); eauto.
    + right. assert (dax2 = dbz2) by congruence. extlia.
    + edestruct (cklr_no_overlap R2 w0 mx m2); eauto.
      rewrite !Z.add_assoc.
      eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H1. simpl in H1.
  destruct (mi R1 w b1) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H1.
  simpl in *.
  assert (d1I >= 0 /\ 0 <= ofs1 + d1I <= Ptrofs.max_unsigned) as [? ?].
  { eapply (cklr_representable R1); eauto. }
  assert (dI2 >= 0 /\ 0 <= (ofs1 + d1I) + dI2 <= Ptrofs.max_unsigned).
  { eapply (cklr_representable R2); eauto.
    revert H0. repeat rstep.
    - left.
      constructor; eauto.
    - left.
      replace (ofs1 + d1I -1) with (ofs1 - 1 + d1I) by extlia.
      constructor; eauto. }
  extlia.
Qed.

Next Obligation. (* aligned_area_inject *)
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in H5. simpl in H5.
  destruct (mi R1 w b) as [[bI d1I] | ] eqn:H1I; [ | discriminate].
  destruct (mi R2 w0 bI) as [[xb2 dI2] | ] eqn:HI2; [ | discriminate].
  inv H5.
  simpl in *.
  rewrite Z.add_assoc.
  eapply (cklr_aligned_area_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b (x - d1I) Cur Nonempty). { eapply H3. extlia. }
    revert H. repeat rstep. left.
    replace x with (x - d1I + d1I) at 2 by extlia.
    constructor; eauto.
  - eapply (cklr_aligned_area_inject R1); eauto.
Qed.

Next Obligation. (* disjoint_or_equal_inject *)
  simpl in *.
  destruct H as (mI & Hm1I & HmI2).
  unfold compose_meminj in *.
  destruct (mi R1 w b1) as [[b1I d1] | ] eqn:Hb1I; [ | discriminate].
  destruct (mi R2 w0 b1I) as [[xb1' d1'] | ] eqn:Hb1'; [ | discriminate].
  inv H0.
  destruct (mi R1 w b2) as [[b2I d2] | ] eqn:Hb2I; [ | discriminate].
  destruct (mi R2 w0 b2I) as [[xb2' d2'] | ] eqn:Hb2'; [ | discriminate].
  inv H1.
  rewrite !Z.add_assoc.
  eapply (cklr_disjoint_or_equal_inject R2); eauto.
  - intros x Hx.
    assert (Mem.perm m b1 (x - d1) Max Nonempty). { eapply H2. extlia. }
    revert H. repeat rstep. left.
    replace x with (x - d1 + d1) at 2 by extlia.
    constructor; eauto.
  - intros x Hx.
    assert (Mem.perm m b2 (x - d2) Max Nonempty). { eapply H3. extlia. }
    revert H. repeat rstep. left.
    replace x with (x - d2 + d2) at 2 by extlia.
    constructor; eauto.
  - eapply (cklr_disjoint_or_equal_inject R1); eauto.
Qed.

Next Obligation. (* perm inv *)
  simpl in *.
  destruct H as (mi & Hm1i & Hmi2).
  apply ptr_inject_compose in H0 as ([bi ofsi] & Hp1i & Hpi2).
  edestruct (cklr_perm_inv R2); eauto.
  - eapply (cklr_perm_inv R1); eauto.
  - right. intros Hm1. apply H. revert Hm1. rauto.
Qed.

Next Obligation. (* sup include *)
  destruct H as (mI & Hm1I & Hm2I).
  destruct H0 as ([w' w0'] & Hw' & mI' & Hm1I' & Hm2I').
  cbn [fst snd] in *. unfold Ple in *.
  inv Hw'; cbn in *.
  etransitivity; eapply cklr_sup_include; eauto; eexists; split; eauto.
Qed.

Declare Scope cklr_scope.
Bind Scope cklr_scope with cklr.
Delimit Scope cklr_scope with cklr.
Infix "@" := cklr_compose (at level 30, right associativity) : cklr_scope.

(** ** Properties *)

(** Monotonicity *)

Global Instance cklr_compose_subcklr:
  Proper (subcklr ++> subcklr ++> subcklr) (@cklr_compose).
Proof.
  intros R12 R12' H12 R23 R23' H23.
  intros [w12 w23] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23). simpl in *.
  specialize (H12 w12 se1 se2 m1 m2 Hse12 Hm12) as (w12' & Hse12' & Hm12' & Hincr12 & H12).
  specialize (H23 w23 se2 se3 m2 m3 Hse23 Hm23) as (w23' & Hse23' & Hm23' & Hincr23 & H23).
  exists (w12', w23'); simpl.
  repeat apply conj; try rauto.
  - eexists; split; eauto.
  - eexists; split; eauto.
  - intros [v12' v23'] m1' m3' (m2' & Hm'12 & Hm'23) [Hwv12 Hwv23].
    specialize (H12 v12' m1' m2' Hm'12 Hwv12) as (v12 & Hm'12' & Hwv12' & Hi12').
    specialize (H23 v23' m2' m3' Hm'23 Hwv23) as (v23 & Hm'23' & Hwv23' & Hi23').
    simpl in *.
    exists (v12, v23).
    split; [ | split].
    + eexists; split; eauto.
    + rauto.
    + rauto.
Qed.

(** Associativity *)

Require Import Axioms.

Lemma compose_meminj_assoc f g h:
  compose_meminj (compose_meminj f g) h =
  compose_meminj f (compose_meminj g h).
Proof.
  apply functional_extensionality; intros b.
  unfold compose_meminj.
  destruct (f b) as [[b' d] | ]; eauto.
  destruct (g b') as [[b'' d'] | ]; eauto.
  destruct (h b'') as [[b''' d''] | ]; eauto.
  rewrite Z.add_assoc; eauto.
Qed.

Lemma cklr_compose_assoc R1 R2 R3:
  subcklr ((R1 @ R2) @ R3) (R1 @ (R2 @ R3)).
Proof.
  intros [[w1 w2] w3] sea sed ma md (seb & (sec & Hse1 & Hse2) & Hse3) (mb & (mc & Hm1 & Hm2) & Hm3).
  simpl in *.
  exists (w1, (w2, w3)).
  repeat apply conj.
  - repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - rewrite compose_meminj_assoc. apply inject_incr_refl.
  - intros (w1' & w2' & w3') ma' md' (mb' & Hm1' & (mc' & Hm2' & Hm3')).
    intros (Hw1 & Hw2 & Hw3).
    simpl in *.
    exists ((w1', w2'), w3').
    split; [ | split].
    + repeat (econstructor; eauto).
    + rauto.
    + rewrite compose_meminj_assoc. apply inject_incr_refl.
Qed.


(** * Properties of [cc_c] *)

Global Instance cc_c_ref:
  Monotonic (@cc_c) (subcklr ++> ccref).
Proof.
  intros Q R HQR. red in HQR |- *.
  intros w se1 se2 q1 q2 Hse Hq.
  destruct Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm].
  specialize (HQR w se1 se2 m1 m2 Hse Hm) as (wr & HseR & HmR & Hincr & HQR').
  exists wr. simpl in *. repeat apply conj; auto.
  - constructor; eauto.
  - intros r1 r2 (wr' & Hw' & Hr). destruct Hr as [v1 v2 m1' m2' Hvres Hm'].
    specialize (HQR' wr' m1' m2' Hm' Hw') as (w' & HmQ' & HwQ' & Hincr').
    eexists. split; eauto. constructor; eauto.
Qed.

Lemma val_inject_list_compose f g:
  eqrel
    (Val.inject_list (compose_meminj f g))
    (rel_compose (Val.inject_list f) (Val.inject_list g)).
Proof.
  split.
  - intros vs1 vs2 Hvs. induction Hvs.
    + exists nil. split; constructor.
    + apply val_inject_compose in H.
      destruct H as (vi & ? & ?), IHHvs as (vsi & ? & ?).
      eexists; split; constructor; eauto.
  - intros vs1 vs3 (vs2 & Hvs12 & Hvs23). revert vs3 Hvs23.
    induction Hvs12; inversion 1; subst.
    + constructor.
    + constructor; eauto.
      apply val_inject_compose. ercompose; eauto.
Qed.

Lemma match_c_query_compose R12 R23 w12 w23:
  eqrel
    (cc_c_query (R12 @ R23) (w12, w23))
    (rel_compose (cc_c_query R12 w12) (cc_c_query R23 w23)).
Proof.
  split.
  - intros _ _ [vf1 vf3 sg vargs1 vargs3 m1 m3 Hvf Hvargs Hm].
    simpl in *.
    apply val_inject_compose in Hvf. destruct Hvf as (vf2 & Hvf12 & Hv23).
    apply val_inject_list_compose in Hvargs. destruct Hvargs as (vargs2 & ? & ?).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (cq vf2 sg vargs2 m2); split; constructor; simpl; eauto.
    destruct Hvf12; congruence.
  - intros q1 q3 (q2 & Hq12 & Hq23).
    destruct Hq23 as [vf1 vf2 sg vargs2 vargs3 m2 m3 Hvf Hvargs23 Hm23 Hvf1].
    inv Hq12.
    constructor; simpl.
    + apply val_inject_compose. ercompose; eauto.
    + apply val_inject_list_compose. ercompose; eauto.
    + ercompose; eauto.
    + auto.
Qed.

Lemma cc_c_compose R12 R23:
  cceqv (cc_c (R12 @ R23)) (cc_c R12 @ cc_c R23).
Proof.
  split.
  - intros [w12 w23] se1 se3 q1 q3 (se2 & Hse12 & Hse23) Hq.
    apply match_c_query_compose in Hq as (q2 & Hq12 & Hq23).
    exists (se2, w12, w23).
    repeat apply conj; cbn; eauto.
    intros r1 r3 (r2 & (w12' & Hw21' & Hr12) & (w23' & Hw23' & Hr23)).
    exists (w12', w23'). split. constructor; cbn; auto.
    destruct Hr12; inv Hr23.
    constructor; cbn; eauto.
    apply val_inject_compose; eauto.
  - intros [[se2 w12] w23] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    cbn in *. exists (w12, w23). repeat apply conj; eauto.
    + apply match_c_query_compose; eauto.
    + intros r1 r3 ([w12' w23'] & Hw' & Hr).
      destruct Hr. cbn in *.
      apply val_inject_compose in H.
      destruct Hw' as [? ?], H as (vi & ? & ?), H0 as (mi & ? & ?).
      exists (cr vi mi).
      split; eexists; constructor; eauto; constructor; eauto.
Qed.
