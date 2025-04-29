Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.


(** * Memory Injection with protection *)

(** ** Worlds *)

Inductive injp_world :=
  injpw (f: meminj) (m1 m2: mem) (Hm: Mem.inject f m1 m2).

Definition injp_max_perm_decrease (m m': mem) :=
  forall b ofs p,
    Mem.valid_block m b ->
    Mem.perm m' b ofs Max p ->
    Mem.perm m b ofs Max p.

Lemma max_perm_decrease_refl :
  forall m, injp_max_perm_decrease m m.
Proof.
  intros. red. eauto.
Qed.

Lemma max_perm_decrease_trans :
  forall m1 m2 m3,
    injp_max_perm_decrease m1 m2 ->
    injp_max_perm_decrease m2 m3 ->
    Mem.sup_include (Mem.support m1) (Mem.support m2) ->
    injp_max_perm_decrease m1 m3.
Proof.
  intros. red in *. intros.
  apply H. auto. apply H0. apply H1. eauto. auto.
Qed.

Hint Resolve max_perm_decrease_refl max_perm_decrease_trans : core.

(** In addition to the criteria in [ec_mem_inject] in Events.v, we introduce 
    [Mem.ro_unchanged] and [injp_max_perm_decrease] which correspond to 
    [ec_readonly] and [ec_max_perm]. *)

Inductive injp_acc: relation injp_world :=
  injp_acc_intro f m1 m2 Hm f' m1' m2' Hm':
    Mem.ro_unchanged m1 m1' -> Mem.ro_unchanged m2 m2' ->
    injp_max_perm_decrease m1 m1' ->
    injp_max_perm_decrease m2 m2' ->
    Mem.unchanged_on (loc_unmapped f) m1 m1' ->
    Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
    inject_incr f f' ->
    inject_separated f f' m1 m2 ->
    injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Definition injp_mi :=
  fun '(injpw f _ _ _) => f.

Inductive injp_match_mem: injp_world -> relation mem :=
  injp_match_mem_intro f m1 m2 Hm:
    injp_match_mem (injpw f m1 m2 Hm) m1 m2.

Inductive injp_match_stbls: injp_world -> relation Genv.symtbl :=
  injp_match_stbls_intro f m1 m2 Hm se1 se2:
    Genv.match_stbls f se1 se2 ->
    Mem.sup_include (Genv.genv_sup se1) (Mem.support m1) ->
    Mem.sup_include (Genv.genv_sup se2) (Mem.support m2) ->
    injp_match_stbls (injpw f m1 m2 Hm) se1 se2.

Hint Constructors injp_match_mem injp_match_stbls : core.

(** ** Properties *)

Definition inject_dom_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b s.

Definition inject_image_in (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) -> Mem.sup_In b' s.

Definition inject_image_eq (f:meminj) (s:sup) :=
  forall b b' o, f b = Some (b', o) <-> Mem.sup_In b' s.


(** Proving the transitivity of the accessibility relation is somewhat
  involved because the different properties need each other. *)

Lemma mem_unchanged_on_trans_implies_valid (P Q: block -> Z -> Prop) m m' m'':
  Mem.unchanged_on P m m' ->
  Mem.unchanged_on Q m' m'' ->
  (forall b ofs, P b ofs -> Mem.valid_block m b -> Q b ofs) ->
  Mem.unchanged_on P m m''.
Proof.
  intros H HPQ H'.
  eapply (Mem.unchanged_on_implies (fun b o => P b o /\ Mem.valid_block m b)).
  - eapply Mem.unchanged_on_trans; eauto.
    + eapply Mem.unchanged_on_implies; eauto.
      tauto.
    + eapply Mem.unchanged_on_implies; eauto.
      firstorder.
  - eauto.
Qed.

Global Instance injp_acc_preo:
  PreOrder injp_acc.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + apply Mem.unchanged_on_refl.
    + apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hr1 Hr2 Hp1 Hp2 H1 H2 Hf Hs].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hr1' Hr2' Hp1' Hp2' H1' H2' Hf' Hs']; subst.
    constructor.
    + red. intros. eapply Hr1; eauto. eapply Hr1'; eauto.
      inversion H1. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + red. intros. eapply Hr2; eauto. eapply Hr2'; eauto.
      inversion H2. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
    + eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped.
      intros b1 _ Hb Hb1.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs; eauto. contradiction.
    + eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach.
      intros b2 ofs2 Hptr2 Hb2 b1 delta Hb' Hperm.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hf in Hb; split; congruence); subst.
        eapply Hptr2; eauto.
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs; eauto.
    + eapply inject_incr_trans; eauto.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hf' in Hb'; split; congruence); subst.
        eapply Hs; eauto.
      * edestruct Hs'; eauto.
        intuition eauto using Mem.valid_block_unchanged_on.
Qed.

Global Instance injp_mi_acc:
  Monotonic (@injp_mi) (injp_acc ++> inject_incr).
Proof.
  unfold injp_mi. rauto.
Qed.

Lemma inject_separated_refl f m1 m2:
  inject_separated f f m1 m2.
Proof.
  red.
  congruence.
Qed.


(** The properties about the preservation of injp accessibility
    by corresponding memory operations on related memories. *)
Lemma injp_acc_alloc: forall f f' m1 m2 b1 b2 lo hi m1' m2' Hm Hm',
    Mem.alloc m1 lo hi = (m1',b1) ->
    Mem.alloc m2 lo hi = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, 0) ->
    (forall b, b<> b1 -> f' b = f b) ->
    injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
Proof.
  intros. constructor.
  - eauto using Mem.ro_unchanged_alloc.
  - eauto using Mem.ro_unchanged_alloc.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - assumption.
  - red. intros b b' delta Hb Hb'.
    assert (b = b1).
    {
      destruct (eq_block b b1); eauto.
      rewrite H3 in Hb'; eauto.
      congruence.
    }
    assert (b' = b2) by congruence.
    subst.
    split; eauto using Mem.fresh_block_alloc.
Qed.

Lemma injp_acc_alloc': forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2' Hm Hm' d,
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, d) ->
    inject_separated f f' m1 m2 ->
    injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
Proof.
  intros. constructor.
  - eauto using Mem.ro_unchanged_alloc.
  - eauto using Mem.ro_unchanged_alloc.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply Mem.alloc_unchanged_on; eauto.
  - assumption.
  - auto. 
Qed.


Lemma injp_acc_local :
  forall f0 wm wtm Htm j1 m1 tm1 Hm1 j2 m2 tm2 Hm2,
    injp_acc (injpw f0 wm wtm Htm) (injpw j1 m1 tm1 Hm1) ->
    Mem.ro_unchanged m1 m2 -> Mem.ro_unchanged tm1 tm2 ->
    injp_max_perm_decrease m1 m2 ->
    injp_max_perm_decrease tm1 tm2 ->
    inject_incr j1 j2 ->
    inject_separated f0 j2 wm wtm ->
    Mem.unchanged_on (fun b ofs => Mem.valid_block wm b /\ loc_unmapped f0 b ofs) m1 m2 ->
    Mem.unchanged_on (fun b ofs => Mem.valid_block wtm b /\ loc_out_of_reach f0 wm b ofs) tm1 tm2 ->
    injp_acc (injpw f0 wm wtm Htm) (injpw j2 m2 tm2 Hm2).
Proof.
  intros.  inv H.
  apply Mem.unchanged_on_support in H18 as SUP.
  apply Mem.unchanged_on_support in H19 as TSUP.
  constructor.
  - red. intros. eapply H14; eauto. eapply H0; eauto.
    eapply SUP; eauto. intros. intro. eapply H9; eauto.
  - red. intros. eapply H15; eauto. eapply H1; eauto.
    eapply TSUP; eauto. intros. intro. eapply H9; eauto.
  - eapply max_perm_decrease_trans; eauto.
  - eapply max_perm_decrease_trans; eauto.
  - inversion H18. inversion H6.
    constructor; eauto.
    intros. etransitivity; eauto.
    eapply unchanged_on_perm0; eauto.
    unfold Mem.valid_block in *. eauto.
    intros. etransitivity. eapply unchanged_on_contents0.
    split; eauto.
    eapply Mem.perm_valid_block; eauto.
    eapply unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    eauto.
  - inversion H19. inversion H7.
    constructor; eauto.
    intros. etransitivity; eauto.
    eapply unchanged_on_perm0; eauto.
    unfold Mem.valid_block in *. eauto.
    intros. etransitivity. eapply unchanged_on_contents0.
    split; eauto.
    eapply Mem.perm_valid_block; eauto.
    eapply unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    eauto.
  - eapply inject_incr_trans; eauto.
  - eauto.
Qed.

Inductive injp_acc_small (w0: injp_world) : relation injp_world :=
    injp_acc_small_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2') j m10 m20 Hm0,
                     w0 = injpw j m10 m20 Hm0 ->
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on (fun b ofs => loc_unmapped f b ofs /\ Mem.valid_block m10 b) m1 m1' ->
                     Mem.unchanged_on (fun b ofs => loc_out_of_reach f m1 b ofs /\ Mem.valid_block m20 b) m2 m2' ->
                     inject_incr f f' ->                     
                     inject_separated f f' m10 m20 ->
                     injp_acc_small w0 (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Lemma injp_acc_small_implies : forall w0 w1 w2,
    injp_acc w0 w1 -> injp_acc_small w0 w1 w2 -> injp_acc w0 w2.
Proof.
  intros. inv H. inv H0.
  apply Mem.unchanged_on_support in H5 as SUP.
  apply Mem.unchanged_on_support in H6 as TSUP.
  apply Mem.unchanged_on_support in H16 as SUP1.
  apply Mem.unchanged_on_support in H17 as TSUP1.
  constructor.
  - red. intros. eapply H1; eauto. eapply H12; eauto.
    eapply SUP; eauto. intros. intro. eapply H9; eauto.
  - red. intros. eapply H2; eauto. eapply H13; eauto.
    eapply TSUP; eauto. intros. intro. eapply H9; eauto.
  - eapply max_perm_decrease_trans; eauto.
  - eapply max_perm_decrease_trans; eauto.
  - inv H11. eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. split; auto. red in H.
    red. destruct (f' b) as [[b' d']|] eqn:Hj.
    apply H8 in Hj as Heq; auto.
    destruct Heq. congruence. auto.
  - inv H11. eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. split; auto. red in H.
    red. intros. destruct (j b0) as [[b' d']|] eqn:Hj.
    apply H7 in Hj as Heq. rewrite H9 in Heq. inv Heq.
    intro. eapply H; eauto. eapply H3; eauto using Mem.valid_block_inject_1.
    intro. eapply H8; eauto.
  - eapply inject_incr_trans; eauto.
  - intros b1 b2 delta Hb Hb''.
    destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
    * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H19 in Hb'; split; congruence); subst.
      eapply H8; eauto.
    * inv H11. eauto. 
Qed.


Lemma injp_acc_free: forall f m1 m2 b1 b2 delta lo1 sz m1' m2' Hm Hm',
    Mem.free m1 b1 lo1 (lo1 + sz) = Some m1' ->
    Mem.free m2 b2 (lo1 + delta) (lo1 + sz + delta) = Some m2' ->
    f b1 = Some (b2, delta) ->
    injp_acc (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. constructor.
  - eauto using Mem.ro_unchanged_free.
  - eauto using Mem.ro_unchanged_free.
  - red. eauto using Mem.perm_free_3.
  - red. eauto using Mem.perm_free_3.
  - eapply Mem.free_unchanged_on; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.free_unchanged_on; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.free_range_perm; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
Qed.


Lemma injp_acc_store : forall f chunk v1 v2 b1 b2 ofs1 delta m1 m2 m1' m2' Hm Hm',
    Mem.store chunk m1 b1 ofs1 v1 = Some m1' ->
    Mem.store chunk m2 b2 (ofs1 + delta) v2 = Some m2' ->
    Val.inject f v1 v2 ->
    f b1 = Some (b2,delta) ->
    injp_acc (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. constructor.
  - eauto using Mem.ro_unchanged_store.
  - eauto using Mem.ro_unchanged_store.
  - red. eauto using Mem.perm_store_2.
  - red. eauto using Mem.perm_store_2.
  - eapply Mem.store_unchanged_on; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.store_unchanged_on; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    edestruct (Mem.store_valid_access_3 chunk m1); eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply H3; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
Qed.

Lemma injp_acc_storev : forall f chunk v1 v2 a1 a2 m1 m2 m1' m2' Hm Hm',
    Mem.storev chunk m1 a1 v1 = Some m1' ->
    Mem.storev chunk m2 a2 v2 = Some m2' ->
    Val.inject f a1 a2 -> Val.inject f v1 v2 ->
    injp_acc (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. unfold Mem.storev in *. destruct a1; try congruence.
  inv H1.
  erewrite Mem.address_inject in H0. 2: apply Hm. 3: eauto.
  eapply injp_acc_store; eauto.
  apply Mem.store_valid_access_3 in H.
  destruct H as [A B].
  apply A. destruct chunk; simpl; lia.
Qed.

(** ** The definition of injp *)

Program Definition injp: cklr :=
  {|
    world := injp_world;
    wacc := injp_acc;
    mi := injp_mi;
    match_mem := injp_match_mem;
    match_stbls := injp_match_stbls;
  |}.

Next Obligation.
  rename m1 into M1. rename m2 into M2.
  inv H0.
  unfold inject_separated in *.
  intros b1 b2 delta Hw Hw'.
  destruct (H8 _ _ _ Hw Hw') as [Hm1 Hm2].
  inv H.
  tauto.
Qed.

Next Obligation. (* ~> vs. match_stbls *)
  intros w w' Hw' se1 se2 Hse.
  destruct Hse as [f m1 m2 se1 se2 Hse Hnb1 Hnb2]. inv Hw'.
  constructor.
  - eapply Genv.match_stbls_incr; eauto.
    intros b1 b2 delta Hb Hb'. specialize (H11 b1 b2 delta Hb Hb').
    unfold Mem.valid_block in H11. split; inv H11; eauto.
  - apply Mem.unchanged_on_support in H7. eauto.
  - apply Mem.unchanged_on_support in H8. eauto.
Qed.

Next Obligation. (* match_stbls vs. Genv.match_stbls *)
  destruct 1; auto.
Qed.

Next Obligation.
  destruct H. inv H0. auto.
Qed.

Next Obligation. (* Mem.alloc *)
  intros _ _ _ [f m1 m2 Hm] lo hi.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:Hm1'.
  edestruct Mem.alloc_parallel_inject
    as (f' & m2' & b2 & Hm2' & Hm' & Hf' & Hb2 & Hff');
    eauto using Z.le_refl.
  rewrite Hm2'.
  exists (injpw f' m1' m2' Hm'); split; repeat rstep; eauto.
  eapply injp_acc_alloc; eauto.
Qed.

Next Obligation. (* Mem.free *)
  intros _ _ _ [f m1 m2 Hm] [[b1 lo1] hi1] [[b2 lo2] hi2] Hr.
  simpl. red.
  destruct (Mem.free m1 b1 lo1 hi1) as [m1'|] eqn:Hm1'; [|rauto].
  inv Hr. inv H0. simpl in H1.
  edestruct Mem.free_parallel_inject as (m2' & Hm2' & Hm'); eauto.
  replace (lo1 + delta + sz) with (lo1 + sz + delta) by extlia.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
  eapply injp_acc_free; eauto.
Qed.

Next Obligation. (* Mem.load *)
  intros _ chunk _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr].
  simpl. red.
  destruct (Mem.load chunk m1 b1 ofs1) as [v1|] eqn:Hv1; [|rauto].
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation. (* Mem.store *)
  intros _ chunk _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr] v1 v2 Hv.
  simpl in *. red.
  destruct (Mem.store chunk m1 b1 ofs1 v1) as [m1'|] eqn:Hm1'; [|rauto].
  edestruct Mem.store_mapped_inject as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. repeat rstep.
  exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
  eapply injp_acc_store; eauto.
Qed.

Next Obligation. (* Mem.loadbytes *)
  intros _ _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hptr] sz.
  simpl. red.
  destruct (Mem.loadbytes m1 b1 ofs1 sz) as [vs1|] eqn:Hvs1; [|rauto].
  edestruct Mem.loadbytes_inject as (vs2 & Hvs2 & Hvs); eauto.
  rewrite Hvs2. rauto.
Qed.

Next Obligation. (* Mem.storebytes *)
  intros _ _ _ [f m1 m2 Hm] [b1 ofs1] [b2 ofs2] Hptr vs1 vs2 Hvs.
  simpl. red.
  destruct (Mem.storebytes m1 _ _ _) as [m1'|] eqn:Hm1'; [|constructor].
  assert (vs1 = nil \/ vs1 <> nil) as [Hvs1|Hvs1].
  { destruct vs1; constructor; congruence. }
  - subst. inv Hvs.
    edestruct (Mem.range_perm_storebytes m2 b2 ofs2 nil) as [m2' Hm2'].
    {
      intros ofs. simpl. extlia.
    }
    rewrite Hm2'.
    constructor.
    assert (Hm': Mem.inject f m1' m2') by eauto using Mem.storebytes_empty_inject.
    exists (injpw f m1' m2' Hm'); split.
    + constructor; eauto.
      * eauto using Mem.ro_unchanged_storebytes.
      * eauto using Mem.ro_unchanged_storebytes.
      * red. eauto using Mem.perm_storebytes_2.
      * red. eauto using Mem.perm_storebytes_2.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. extlia.
      * eapply Mem.storebytes_unchanged_on; eauto.
        simpl. intro. extlia.
      * apply inject_separated_refl.
    + constructor; eauto.
  - assert (ptr_inject f (b1, ofs1) (b2, ofs2)) as Hptr'.
    {
      destruct Hptr as [Hptr|Hptr]; eauto.
      inversion Hptr as [_ _ [xb1 xofs1 xb2 delta Hb]]; clear Hptr; subst.
      unfold ptrbits_unsigned.
      erewrite Mem.address_inject; eauto.
      apply Mem.storebytes_range_perm in Hm1'.
      eapply Hm1'.
      destruct vs1; try congruence.
      simpl. extlia.
    }
    inv Hptr'.
    edestruct Mem.storebytes_mapped_inject as (m2' & Hm2' & Hm'); eauto.
    rauto.
    rewrite Hm2'. constructor.
    exists (injpw f m1' m2' Hm'); split; repeat rstep; eauto.
    constructor.
    + eauto using Mem.ro_unchanged_storebytes.
    + eauto using Mem.ro_unchanged_storebytes.
    + red. eauto using Mem.perm_storebytes_2.
    + red. eauto using Mem.perm_storebytes_2.
    + eapply Mem.storebytes_unchanged_on; eauto.
      unfold loc_unmapped. congruence.
    + eapply Mem.storebytes_unchanged_on; eauto.
      unfold loc_out_of_reach.
      intros ofs Hofs H.
      eelim H; eauto.
      eapply Mem.perm_cur_max.
      eapply Mem.perm_implies; [ | eapply perm_any_N].
      eapply Mem.storebytes_range_perm; eauto.
      red in Hvs. rewrite Hvs.
      extlia.
    + apply inject_incr_refl.
    + apply inject_separated_refl.
Qed.

Next Obligation. (* Mem.perm *)
  intros _ _ _ [f m1 m2 Hm] _ _ [b1 ofs1 b2 delta Hb] p k H.
  eapply Mem.perm_inject; eauto.
Qed.

Next Obligation. (* Mem.valid_block *)
  intros _ _ _ [f m1 m2 Hm] b1 b2 [delta Hb].
  split; intro.
  - eapply Mem.valid_block_inject_2; eauto.
  - eapply Mem.valid_block_inject_1; eauto.
Qed.

Next Obligation. (* Mem.meminj_no_overlap *)
  destruct H as [f m1 m2 Hm].
  eapply Mem.mi_no_overlap; eauto.
Qed.

Next Obligation. (* representable *)
  destruct H as [f m1 m2 Hm].
  rewrite <- (Ptrofs.unsigned_repr ofs1) by extlia.
  eapply Mem.mi_representable; eauto.
  rewrite Ptrofs.unsigned_repr by extlia.
  assumption.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  eapply Mem.aligned_area_inject; eauto.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  eapply Mem.disjoint_or_equal_inject; eauto.
Qed.

Next Obligation.
  destruct H as [f m1 m2 Hm].
  inv H0. cbn in *.
  eapply Mem.perm_inject_inv; eauto.
Qed.

Next Obligation.
  destruct H0 as (w' & Hw' & Hm').
  destruct Hw'. inv H. inv Hm'.
  split; eauto using Mem.unchanged_on_support.
Qed.

(** injp ⋅ injp ⊑ injp, the injp refinement for incoming side. *)
Lemma injp_injp:
  subcklr injp (injp @ injp).
Proof.
  intros w se1 se2 m1 m2 Hse Hm. destruct Hm as [f m1 m2 Hm].
  exists (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm),
          injpw f m1 m2 Hm); simpl.
  repeat apply conj.
  - exists se1. split; eauto.
    inv Hse. econstructor; auto. eapply match_stbls_dom; eauto.
  - exists m1; split; repeat rstep; eauto using inj_mem_intro, mem_inject_dom.
  - rewrite meminj_dom_compose.
    apply inject_incr_refl.
  - intros [w12' w23'] m1' m3' (m2' & H12' & H23') [Hw12' Hw23']. cbn in *.
    destruct H12' as [f12' m1' m2' Hm12'].
    inversion H23' as [f23' xm2' xm3' Hm23']. clear H23'; subst.
    inversion Hw12' as [? ? ? ? ? ? ? ? ? ? ? ? UNMAP1 ? Hf12' SEP12']. clear Hw12'; subst.
    inversion Hw23' as [? ? ? ? ? ? ? ? ? ? ? ? ? ? Hf23' SEP23']. clear Hw23'; subst.
    eexists (injpw (compose_meminj f12' f23') m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; auto.
    + constructor; auto.
      *
        generalize (loc_unmapped_dom f). intros.
        inv UNMAP1. constructor; eauto.
        intros. apply unchanged_on_perm. apply H10. eauto.
        eauto.
        intros. apply unchanged_on_contents. apply H10. eauto.
        eauto.
      * rewrite <- (meminj_dom_compose f). rauto.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct SEP12'; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct SEP23'; eauto.
    + cbn. rstep; auto.
Qed.

(** * The proof of injp ⊑ injp ⋅ injp starts from here *)
(* Injection implies image is in the support *)

Lemma inject_implies_image_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_image_in f (Mem.support m2).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_2 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

(* Injection implies domain is in the support *)
Lemma inject_implies_dom_in: forall f m1 m2,
  Mem.inject f m1 m2 -> inject_dom_in f (Mem.support m1).
Proof.
  intros f m1 m2 INJ.
  red.
  intros b b' o F.
  generalize (Mem.valid_block_inject_1 _ _ _ _ _ _ F INJ).
  intros VLD.
  red in VLD.
  auto.
Qed.

Lemma inject_dom_in_inv: forall f s b,
    inject_dom_in f s -> ~sup_In b s -> f b = None.
Proof.
  intros. destruct (f b) eqn:?. destruct p.
  apply H in Heqo. congruence. auto.
Qed.

(** * Step1: The Construction of meminj j1' j2' *)

(** meminj operations *)
Definition meminj_add (f:meminj) b1 r:=
  fun b => if (eq_block b b1) then Some r else f b.

Lemma meminj_add_new: forall f a b,
    meminj_add f a b a = Some b.
Proof.
  intros. unfold meminj_add. rewrite pred_dec_true; auto.
Qed.

Lemma meminj_add_diff: forall j a b a' ofs,
    a <> b ->
    meminj_add j a (a',ofs ) b = j b.
Proof.
  intros. unfold meminj_add. destruct eq_block; congruence.
Qed.

Lemma meminj_add_incr: forall f a b,
    f a = None -> inject_incr f (meminj_add f a b).
Proof.
  intros. intro. unfold meminj_add. intros.
  destruct eq_block. subst. congruence. eauto.
Qed.

Lemma meminj_add_compose : forall f1 f2 a b c o,
    (forall b0 z, ~ f1 b0 = Some (b,z)) ->
    compose_meminj (meminj_add f1 a (b,0)) (meminj_add f2 b (c,o)) =
    meminj_add (compose_meminj f1 f2) a (c,o).
Proof.
  intros. apply Axioms.extensionality. intro x.
  unfold compose_meminj, meminj_add.
  destruct (eq_block x a). rewrite pred_dec_true; eauto.
  destruct (f1 x) eqn: Hf1; eauto. destruct p.
  destruct (eq_block b0 b); eauto. subst. apply H in Hf1. inv Hf1.
Qed.

(** The constrution of memory injections *)
Fixpoint update_meminj12 (sd1': list block) (j1 j2 j': meminj) (si1: sup) :=
  match sd1' with
    |nil => (j1,j2,si1)
    |hd::tl =>
       match compose_meminj j1 j2 hd, (j' hd) with
       | None , Some (b2,ofs) =>
         let b0 := fresh_block si1 in
         update_meminj12 tl (meminj_add j1 hd (b0,0) )
                         (meminj_add j2 (fresh_block si1) (b2,ofs))
                         j' (sup_incr si1)
       | _,_ => update_meminj12 tl j1 j2 j' si1
       end
  end.

(* results of update_meminj*)
Definition inject_incr_no_overlap' (j j' : meminj) : Prop :=
  forall b1 b2 b1' b2' delta1 delta2,
    b1 <> b2 -> j b1 = None -> j b2 = None ->
    j' b1 = Some (b1', delta1) -> j' b2 = Some (b2',delta2) ->
    b1' <> b2'.

Definition update_add_exists (j12 j12' j': meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) ->
    exists b3 ofs3, j' b1 = Some (b3,ofs3).

Definition update_add_zero (j12 j12' : meminj) : Prop :=
  forall b1 b2 ofs2,
    j12 b1 = None -> j12' b1 = Some (b2 , ofs2) -> ofs2 = 0.

Definition update_add_same (j23 j23' j12': meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    exists b1, j12' b1 = Some (b2,0) /\
    (forall b1' d, j12' b1' = Some (b2,d) -> b1' = b1).

Definition update_add_same2 (j23 j23' : meminj ) : Prop :=
  forall b2 b3 ofs2,
    j23 b2 = None -> j23' b2 = Some (b3,ofs2) ->
    forall b2' ofs2',
      j23' b2' = Some (b3,ofs2') -> b2 = b2'.

(* lemmas using sup_list for update_properties *)

Definition inject_dom_in_bl (f:meminj) (bl: list block) :=
  forall b b' o, f b = Some (b', o) -> In b bl.

Definition inject_incr_disjoint_bl1 (j j':meminj) (bl1: list block) (s2: sup) :=
  forall b b' o, j b = None -> j' b = Some (b',o) ->
            ~ In b bl1 /\ ~ sup_In b' s2.

Lemma inject_dom_in_eqv: forall f s,
    inject_dom_in_bl f (Mem.sup_list s) <-> inject_dom_in f s.
Proof.
  intros. split; intro; red; intros.
  erewrite Mem.sup_list_in; eauto.
  erewrite <- Mem.sup_list_in; eauto.
Qed.

Lemma inject_incr_disjoint_eqv : forall j j' s1 s2,
    inject_incr_disjoint_bl1 j j' (Mem.sup_list s1) s2 <-> inject_incr_disjoint j j' s1 s2.
Proof.
  intros. split; intro; red; intros.
  exploit H. eauto. eauto. intros [A B].
  erewrite <- Mem.sup_list_in in A. auto.
  exploit H. eauto. eauto. intros [A B].
  erewrite Mem.sup_list_in in A. auto.
Qed.
  
Lemma update_properties': forall s1' bl1 j1 j2 s2 s2' j1' j2' j' s3,
    update_meminj12 s1' j1 j2 j' s2 = (j1',j2',s2') ->
    inject_dom_in_bl j1 bl1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint_bl1 (compose_meminj j1 j2) j' bl1 s3 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include s2 s2'
    /\ inject_image_in j1' s2'
    /\ inject_dom_in j2' s2'
    /\ inject_incr_disjoint_bl1 j1 j1' bl1 s2
    /\ inject_incr_disjoint j2 j2' s2 s3
    /\ inject_incr_no_overlap' j1 j1'
    /\ update_add_exists j1 j1' j'
    /\ update_add_zero j1 j1'
    /\ update_add_same j2 j2' j1'.
(*    /\ update_add_same2 j2 j2' . *)
Proof.
  induction s1'.
  - (*base*)
    intros; inv H. repeat apply conj; try congruence; eauto.
  - (*induction*)
    intros until s3. intros UPDATE DOMIN12 IMGIN12 DOMIN23
           INCR13 INCRDISJ13. inv UPDATE.
    destruct (compose_meminj j1 j2 a) eqn: Hja. eauto.
    destruct (j' a) as [[b z]|] eqn:Hj'a; eauto.
    exploit INCRDISJ13; eauto. intros [a_notin_sd1 b_notin_si2].
    (* facts *)
    assert (MIDINCR1: inject_incr j1 (meminj_add j1 a (fresh_block s2,0))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN12 in H. congruence.
    }
    assert (MIDINCR2: inject_incr j2 (meminj_add j2 (fresh_block s2) (b,z))).
    {
      unfold meminj_add. red. intros. destruct eq_block; eauto.
      apply DOMIN23 in H. subst. apply freshness in H. inv H.
    }
    assert (MIDINCR3: inject_incr (meminj_add (compose_meminj j1 j2) a (b,z)) j').
    {
      red. intros b0 b' o INJ. unfold meminj_add in INJ.
      destruct (eq_block b0 a). congruence. eauto.
    }
    exploit IHs1'. eauto.
    (* rebuild preconditions for induction step *)
    + instantiate (1:= (a :: bl1)).
      red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      left. auto. right. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + red. intros b0 b' o. unfold meminj_add. destruct eq_block.
      subst. intro INJ. inv INJ. eapply Mem.sup_incr_in1. intro. apply Mem.sup_incr_in2. eauto.
    + rewrite meminj_add_compose; eauto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    + instantiate (1:= s3). rewrite meminj_add_compose.
      red. intros b0 b' o INJ1 INJ2. unfold meminj_add in INJ1. destruct (eq_block b0 a).
      congruence. exploit INCRDISJ13; eauto. intros [A B]. split.
      intros [H|H]; congruence.
      auto.
      intros. intro. apply IMGIN12 in H. eapply freshness; eauto.
    +
    intros (incr1& incr2 & sinc & imagein1 & domin2 &
            disjoint1 & disjoint2 & no_overlap & add_exists & add_zero & add_same1).
    repeat apply conj; eauto.
    (*incr1*)
    eapply inject_incr_trans; eauto.
    (*incr2*)
    eapply inject_incr_trans; eauto.
    (*disjoint1*)
    {
    red. red in disjoint1. intros b0 b' delta INJ1 INJ2.
    destruct (eq_block b0 a).
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intro INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd. split. auto. apply freshness.
    + exploit disjoint1. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. right. auto. intro. apply B. apply Mem.sup_incr_in2. auto.
    }
    (*disjoint2*)
    {
    red. red in disjoint2. intros b0 b' delta INJ1 INJ2. set (nb := fresh_block s2).
    destruct (eq_block b0 nb).
    + subst. generalize (meminj_add_new j2 nb (b,z)). intro INJadd. apply incr2 in INJadd.
      rewrite INJ2 in INJadd. inv INJadd. split. apply freshness. auto.
    + exploit disjoint2. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
      intros [A B]. split. intro. apply A. apply Mem.sup_incr_in2. auto. intro. apply B. auto.
    }
    (*new_no_overlap*)
    {
    red. red in no_overlap. intros b1 b2 b1' b2' delta1 delta2 Hneq NONE1 NONE2 INJ1 INJ2.
    destruct (eq_block b1 a); destruct (eq_block b2 a).
    + congruence.
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ1 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff; eauto. eauto. intros [A B].
      intro. subst. apply B. apply Mem.sup_incr_in1.
    + subst. generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite INJ2 in INJadd. inv INJadd.
      exploit disjoint1. rewrite meminj_add_diff. apply NONE1. eauto. eauto. intros [A B].
      intro. subst. apply B. apply Mem.sup_incr_in1.
    + eapply no_overlap. apply Hneq. rewrite meminj_add_diff; eauto.
      rewrite meminj_add_diff; eauto. eauto. eauto.
    }
    (* add_exists*)
    {
    red. red in add_exists. intros. destruct (eq_block a b1).
    + subst. eauto.
    + eapply add_exists; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_zero. intros. destruct (eq_block a b1).
      subst. generalize (meminj_add_new j1 b1 (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. rewrite H1 in INJadd. inv INJadd. auto.
      eapply add_zero; eauto. rewrite meminj_add_diff; eauto.
    }
    {
      red. red in add_same1. intros. destruct (eq_block b2 (fresh_block s2)).
      - subst.
      generalize (meminj_add_new j1 a (fresh_block s2,0)). intros INJadd.
      apply incr1 in INJadd. eauto. exists a. split. auto.
      intros.
      destruct (meminj_add j1 a (fresh_block s2, 0) b1') as [[b2' d']|] eqn : Hj1add.
        + destruct (eq_block b1' a). subst. auto.
          apply incr1 in Hj1add as Hj1'.
          rewrite meminj_add_diff in Hj1add; eauto.
          apply IMGIN12 in Hj1add as FRESH.
          rewrite H2 in Hj1'. inv Hj1'.
          exfalso. eapply freshness; eauto.
        + exploit disjoint1; eauto. intros [A B].
          exfalso. apply B. apply Mem.sup_incr_in1.
      - eapply add_same1; eauto. rewrite meminj_add_diff; eauto.
    }
Qed.

(*
Lemma update_properties: forall s1' s1 j1 j2 s2 s2' j1' j2' j' s3,
    update_meminj12 s1' j1 j2 j' s2 = (j1',j2',s2') ->
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    inject_incr j1 j1'
    /\ inject_incr j2 j2'
    /\ Mem.sup_include s2 s2'
    /\ inject_image_in j1' s2'
    /\ inject_dom_in j2' s2'
    /\ inject_incr_disjoint j1 j1' s1 s2
    /\ inject_incr_disjoint j2 j2' s2 s3
    /\ inject_incr_no_overlap' j1 j1'
    /\ update_add_exists j1 j1' j'
    /\ update_add_zero j1 j1'
    /\ update_add_same j2 j2' j1'.
(*    /\ update_add_same2 j2 j2' . *)
Proof.
  intros. exploit update_properties'; eauto.
  (*instantiate (1:= Mem.sup_list s1).
  red. intros. exploit H0; eauto. apply Mem.sup_list_in.
  instantiate (1:= s3).
  red. intros. exploit H4; eauto. intros [A B].
  split. intro. apply A. apply Mem.sup_list_in. auto. auto.
  intros (A & B & C & D & E & F & G & I & J & K & L).
  repeat apply conj; eauto.
  red. intros. exploit F; eauto. intros [X Y].
  split. rewrite Mem.sup_list_in. auto. auto.*)
Qed.
 *)

(** Lemmas to prove j' = compose_meminj j1' j2' *)
Fixpoint update_meminj sd1' j j':=
  match sd1' with
    |nil => j
    |hd::tl => match j hd, j' hd with
              |None, Some (b,ofs) => update_meminj tl (meminj_add j hd (b,ofs)) j'
              |_,_ => update_meminj tl j j'
              end
  end.


Definition meminj_sub (j:meminj) (b:block) :=
  fun b0 => if (eq_block b b0) then None else j b0.

Lemma update_meminj_old: forall s j j' b b' ofs,
  j b = Some (b', ofs) ->
  update_meminj s j j' b = Some (b',ofs).
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja.
    eauto. destruct (j' a) eqn: Hj'a. destruct p.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto.
    eauto.
Qed.

Lemma update_meminj_diff1: forall s j j' a b a' ofs,
    a <> b ->
    update_meminj s j j' b =
    update_meminj s (meminj_add j a (a',ofs)) j' b.
Proof.
  induction s; intros.
  - simpl. unfold meminj_add. destruct (eq_block b a); congruence.
  - simpl.
    destruct (j a) eqn: Hja. eauto.
    + unfold meminj_add at 1. destruct eq_block.
      -- subst. eauto.
      -- rewrite Hja. eauto.
    + unfold meminj_add at 2. destruct eq_block.
      -- subst. destruct (j' a0). destruct p.
         erewrite <- IHs; eauto.
         erewrite <- IHs; eauto.
      -- rewrite Hja. destruct (j' a). destruct p.
         destruct (eq_block a b).
         ++ subst. erewrite update_meminj_old. 2: apply meminj_add_new.
            erewrite update_meminj_old. 2: apply meminj_add_new. auto.
         ++ erewrite <- IHs; eauto.
         erewrite <- IHs with (j := (meminj_add j a0 (a', ofs))); eauto.
         ++ erewrite <- IHs; eauto.
Qed.

Lemma update_meminj_diff: forall s j j' a b,
    a <> b ->
    update_meminj s j (meminj_sub j' a) b =
    update_meminj s j j' b.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) eqn: Hja. eauto.
    destruct (eq_block a0 a).
    + subst. unfold meminj_sub. rewrite pred_dec_true; eauto.
      (* replace (fun b0 : Block.block => if eq_block a b0 then None else j' b0) with (meminj_sub j' a); eauto. *)
      setoid_rewrite IHs. destruct (j' a).
      -- destruct p. erewrite update_meminj_diff1; eauto.
      -- auto.
      -- auto.
    + unfold meminj_sub. rewrite pred_dec_false; eauto.
      destruct (j' a). destruct p. eauto.
      eauto.
Qed.

Lemma inject_dom_in_sub: forall j a s,
    inject_dom_in_bl j (a::s) ->
    inject_dom_in_bl (meminj_sub j a) s.
Proof.
  intros.
  red. red in H. intros. unfold meminj_sub in H0.
  destruct eq_block in H0. congruence. exploit H; eauto.
  intros [A|A]. congruence. auto.
Qed.


Lemma meminj_sub_diff: forall j a b,
    a <> b -> meminj_sub j a b = j b.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma meminj_sub_none : forall j a,
    meminj_sub j a a = None.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma update_meminj_new: forall s j j' b b' ofs,
  j b = None ->
  j' b = Some (b',ofs) ->
  inject_dom_in_bl j' s ->
  update_meminj s j j' b = j' b.
Proof.
  induction s; intros.
  - simpl. apply H1 in H0. inv H0.
  - simpl.
    destruct (j a) as [[a' ofs']|]eqn:Hja.
    + (*here we know a <> b by j a <> j b*)
      generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false; congruence.
      apply inject_dom_in_sub; eauto.
      intro IH.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto. congruence. congruence.
    + destruct (eq_block a b).
      -- subst. rewrite H0. erewrite update_meminj_old. eauto.
         apply meminj_add_new.
      -- generalize (IHs j (meminj_sub j' a) b b' ofs).
      intros. exploit H2. eauto. unfold meminj_sub. rewrite pred_dec_false.
      auto. congruence. apply inject_dom_in_sub; eauto. intro IH.
      destruct (j' a). destruct p. erewrite <- update_meminj_diff1; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
      rewrite update_meminj_diff in IH; eauto.
      rewrite meminj_sub_diff in IH; eauto.
Qed.

Lemma update_meminj_none: forall s j j' b,
  j b = None ->
  j' b = None ->
  update_meminj s j j' b = None.
Proof.
  induction s; intros.
  - simpl. auto.
  - simpl. destruct (j a) as [[a' ofs']|]eqn:Hja.
    eauto. destruct (j' a) as [[a' ofs']|]eqn:Hj'a.
    eapply IHs. unfold meminj_add. destruct eq_block.
    subst. congruence. auto. auto. eauto.
Qed.

Lemma update_meminj_eq: forall sd1' j j',
    inject_dom_in_bl j' sd1' ->
    inject_incr j j' ->
    update_meminj sd1' j j' = j'.
Proof.
  intros. apply Axioms.extensionality.
  intro x.
  destruct (j x) as [[y ofs]|] eqn: Hj.
  - erewrite update_meminj_old; eauto.
    apply H0 in Hj. congruence.
  - destruct (j' x) as [[y ofs]|] eqn: Hj'.
    erewrite update_meminj_new; eauto.
    erewrite update_meminj_none; eauto.
Qed.

Lemma update_compose_meminj : forall sd1' j1 j2 j' si1 si1' j1' j2',
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    inject_image_in j1 si1 ->
    update_meminj sd1' (compose_meminj j1 j2) j' = (compose_meminj j1' j2').
Proof.
  induction sd1'; intros.
  - inv H. simpl. auto.
  - inv H. simpl. destruct (compose_meminj) eqn : Hja.
    + eauto.
    + destruct (j' a) eqn: Hj'a.
      -- destruct p.
         apply IHsd1' in H2.
         rewrite <- H2. f_equal. apply Axioms.extensionality.
         intro x.
         destruct (compose_meminj j1 j2 x) eqn: Hjx.
         ++ destruct (eq_block a x).
            * congruence.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness; eauto.
              ** auto.
         ++ destruct (eq_block a x).
            * subst. rewrite meminj_add_new.
              unfold compose_meminj.
              rewrite meminj_add_new. rewrite meminj_add_new. eauto.
            * rewrite meminj_add_diff; auto. rewrite Hjx.
              unfold compose_meminj.
              rewrite meminj_add_diff; auto.
              unfold compose_meminj in Hjx.
              destruct (j1 x) as [[x' ofs]|] eqn:Hj1x.
              ** rewrite meminj_add_diff. eauto.
                 intro. apply H0 in Hj1x. subst. eapply freshness; eauto.
              ** auto.
         ++ red. intros. red in H0. destruct (eq_block a b0).
            * subst. rewrite meminj_add_new in H. inv H. apply Mem.sup_incr_in1.
            * rewrite meminj_add_diff in H. exploit H0; eauto.
              intro. apply Mem.sup_incr_in2. auto. auto.
      -- eauto.
Qed.

Lemma update_compose: forall j1 j2 j' sd1' si1 si1' j1' j2' sd1 si2,
    update_meminj12 sd1' j1 j2 j' si1 = (j1',j2',si1') ->
    inject_dom_in_bl j' sd1' ->
    inject_dom_in j1 sd1 ->
    inject_image_in j1 si1 ->
    inject_dom_in j2 si1 ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' sd1 si2 ->
    j' = (compose_meminj j1' j2').
Proof.
  intros.
  exploit update_compose_meminj; eauto.
  intro A.
  exploit update_meminj_eq. apply H0.  eauto.
  intro B. congruence.
Qed.

Lemma add_from_to_dom_in : forall s1 s1' j12 j12' j',
    update_add_exists j12 j12' j' ->
    Mem.sup_include s1 s1' ->
    inject_dom_in j12 s1 ->
    inject_incr j12 j12' ->
    inject_dom_in j' s1' ->
    inject_dom_in j12' s1'.
Proof.
  intros. red. intros.
  destruct (j12 b) as [[b'' o']|] eqn: Hj12.
  + erewrite H2 in H4; eauto.
  + exploit H; eauto. intros (b3 & ofs3 & Hj'). eauto.
Qed.

(** Summerize of the memory injection composition. *)
Lemma inject_incr_inv: forall j1 j2 j' s1 s2 s3 s1',
    inject_dom_in j1 s1 ->
    inject_image_in j1 s2 ->
    inject_dom_in j2 s2 ->
    inject_dom_in j' s1' ->
    Mem.sup_include s1 s1' ->
    inject_incr (compose_meminj j1 j2) j' ->
    inject_incr_disjoint (compose_meminj j1 j2) j' s1 s3 ->
    exists j1' j2' s2', j' = compose_meminj j1' j2' /\
               inject_incr j1 j1' /\
               inject_incr j2 j2' /\
               Mem.sup_include s2 s2' /\
               inject_dom_in j1' s1' /\
               inject_image_in j1' s2' /\
               inject_dom_in j2' s2' /\
               inject_incr_disjoint j1 j1' s1 s2 /\
               inject_incr_disjoint j2 j2' s2 s3 /\
               inject_incr_no_overlap' j1 j1' /\
               update_add_zero j1 j1' /\
               update_add_exists j1 j1' j' /\
               update_add_same j2 j2' j1'.
Proof.
  intros.
  destruct (update_meminj12 (Mem.sup_list s1') j1 j2 j' s2) as [[j1' j2'] s2'] eqn: UPDATE.
  exists j1' ,j2' ,s2'.
  apply inject_dom_in_eqv in H as H'.
  apply inject_dom_in_eqv in H2 as H2'.
  apply inject_incr_disjoint_eqv in H5 as H5'.
  exploit update_compose; eauto.
  intro COMPOSE.
  exploit update_properties'; eauto.
  rewrite inject_incr_disjoint_eqv.
  intros (A & B & C & D & E & F & G & I & J & K & L).
  repeat apply conj; eauto. eapply add_from_to_dom_in; eauto.
Qed.


(* no_overlaping from update_meminj12 *)
Lemma update_meminj_no_overlap1 : forall m1' m1 m2 j1 j1',
    injp_max_perm_decrease m1 m1' ->
    inject_incr j1 j1' ->
    Mem.inject j1 m1 m2 ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    inject_incr_no_overlap' j1 j1' ->
    Mem.meminj_no_overlap j1' m1' .
Proof.
  intros m1' m1 m2 j1 j1' MPD INCR INJECT INCRDISJ INCRNOLAP.
  red. intros.
  destruct (j1 b1) as [[b1'' delta1']|] eqn : H0';
  destruct (j1 b2) as [[b2'' delta2']|] eqn : H1'.
  - (* old mappings *)
    erewrite INCR in H0; eauto. inv H0.
    erewrite INCR in H1; eauto. inv H1.
    inversion INJECT. apply inject_implies_dom_in in INJECT as DOMIN.
    eapply mi_no_overlap; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
    apply MPD; eauto. eapply DOMIN; eauto.
  - (* b1 old, b2 new *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H0; eauto. inv H0.
    apply IMGIN in H0'. left. congruence.
  - (* b1 new, b2 old *)
    exploit INCRDISJ; eauto. intros [A B].
    apply inject_implies_image_in in INJECT as IMGIN.
    erewrite INCR in H1; eauto. inv H1.
    apply IMGIN in H1'. left. congruence.
  - (* new mappings *)
    left. eauto.
Qed.



(* properties of memory operations defined in Memory.v *)
Lemma pmap_update_diff: forall (A:Type) b f (map1 map2: NMap.t A) b',
  Mem.pmap_update b f map1 = map2 ->
  b <> b' ->
  NMap.get _ b' map1 = NMap.get _ b' map2.
Proof.
  intros. rewrite <- H. unfold Mem.pmap_update.
  rewrite NMap.gsspec. rewrite pred_dec_false; auto.
Qed.

Definition mem_memval (m:mem) b ofs : memval :=
  Maps.ZMap.get ofs (NMap.get _ b (Mem.mem_contents m)).

Lemma loc_out_of_reach_incr : forall j1 j1' m1 m2 m1' b ofs,
    loc_out_of_reach j1 m1 b ofs ->
    inject_dom_in j1 (Mem.support m1) ->
    inject_incr j1 j1' ->
    injp_max_perm_decrease m1 m1' ->
    sup_In b (Mem.support m2) ->
    inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2) ->
    loc_out_of_reach j1' m1' b ofs.
Proof.
  intros. red. intros.
  destruct (j1 b0) as [[b' delta']|] eqn : Hj1b.
  - erewrite H1 in H5; eauto. inv H5.
    intro. apply H2 in H5.
    apply H in Hj1b. congruence.
    unfold Mem.valid_block. eauto.
  - exploit H4; eauto. intros [A B].
    congruence.
Qed.

(** Lemma C.6 *)
Lemma loc_out_of_reach_trans:
  forall m1 m2 m3 j1 j2 b2 ofs2 b3 delta3 k p,
    Mem.inject j1 m1 m2 ->
    Mem.inject j2 m2 m3 ->
    j2 b2 = Some (b3,delta3) ->
    Mem.perm m2 b2 ofs2 k p ->
    loc_out_of_reach j1 m1 b2 ofs2 ->
    loc_out_of_reach (compose_meminj j1 j2) m1 b3 (ofs2 + delta3).
Proof.
  intros until p. intros INJ12 INJ23 MAP2 PERM2 OUTOFREACH1.
  red.
  red in OUTOFREACH1.
  intros.
  unfold compose_meminj in H.
  destruct (j1 b0) as [[b2' delta']|] eqn: Hj1b; try congruence.
  destruct (j2 b2') as [[b3' delta'']|] eqn: Hj2b; try congruence.
  inv H.
  destruct (Mem.perm_dec m1 b0 (ofs2 + delta3 - (delta' + delta'')) Max Nonempty); auto.
  destruct (eq_block b2 b2'). subst. rewrite MAP2 in Hj2b. inv Hj2b. apply OUTOFREACH1 in Hj1b.
  replace (ofs2 + delta'' - (delta' + delta'')) with (ofs2 - delta') in p0 by lia.
  congruence.
  eapply Mem.perm_inject in Hj1b; eauto.
  inversion INJ23. exploit mi_no_overlap. apply n. eauto. eauto.
  eauto with mem. eauto. intros [A|A]. congruence. extlia.
Qed.

(** Lemma C.5 *)
Lemma memval_compose_1 : forall j1 j2 mv mv3,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j1 mv (Mem.memval_map j1 mv).
Proof.
  intros. destruct mv; simpl; try constructor.
  destruct v; simpl; try repeat constructor.
  destruct (j1 b) as [[b1 d]|] eqn : ?.
  repeat constructor. econstructor; eauto.
  inv H. inv H4. unfold compose_meminj in H1. rewrite Heqo in H1.
  congruence.
Qed.

Lemma memval_compose_2:
  forall mv mv3 j1 j2,
    memval_inject (compose_meminj j1 j2) mv mv3 ->
    memval_inject j2 (Mem.memval_map j1 mv) mv3.
Proof.
  intros; inv H; simpl.
  - constructor.
  - inv H0; try constructor; try constructor.
    unfold compose_meminj in H.
    destruct (j1 b1) as [[b2' delta']|] eqn:Hj1; try constructor.
    destruct (j2 b2') as [[b2'' delta'']|] eqn:Hj2; try constructor.
    inv H.
    econstructor; eauto.
    rewrite add_repr.
    rewrite Ptrofs.add_assoc. auto.
    congruence.
  - constructor.
Qed.

(** * The construction of intermidiate memory state m2' *)
Section CONSTR_PROOF.
  Variable m1 m2 m3 m1' m3': mem.
  Variable j1 j2 j1' j2': meminj.
  Variable s2': sup.
  Hypothesis ROUNC1: Mem.ro_unchanged m1 m1'.
  Hypothesis ROUNC3: Mem.ro_unchanged m3 m3'.
  Hypothesis DOMIN1: inject_dom_in j1 (Mem.support m1).
  Hypothesis DOMIN1': inject_dom_in j1' (Mem.support m1').
  Hypothesis UNCHANGE1: Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1'.
  Hypothesis UNCHANGE3: Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m3 m3'.
  Hypothesis INJ12 : Mem.inject j1 m1 m2.
  Hypothesis INJ23 : Mem.inject j2 m2 m3.
  Hypothesis INJ13': Mem.inject (compose_meminj j1' j2') m1' m3'.
  Hypothesis SUPINCL2 : Mem.sup_include (Mem.support m2) s2'.
  Hypothesis SUPINCL3 : Mem.sup_include (Mem.support m3) (Mem.support m3').
  Hypothesis INCR1 : inject_incr j1 j1'.
  Hypothesis INCR2 : inject_incr j2 j2'.
  Hypothesis INCRDISJ1 :inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2).
  Hypothesis INCRDISJ2 :inject_incr_disjoint j2 j2' (Mem.support m2) (Mem.support m3).
  Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j1 j1'.
  Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'.
  Hypothesis IMGIN1': inject_image_in j1' s2'.
  Hypothesis DOMIN2': inject_dom_in j2' s2'.
  Hypothesis ADDZERO: update_add_zero j1 j1'.
  Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2').
  Hypothesis ADDSAME : update_add_same j2 j2' j1'.

  (** step2 of Definition C.7, defined in common/Memory.v as memory operation *)
  Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.
  (** step3 of Definition C.7, in common/Memory.v *)
  Definition m2' := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.
  
  Lemma INJNOLAP1' : Mem.meminj_no_overlap j1' m1'.
  Proof. eapply update_meminj_no_overlap1; eauto. Qed.

  (** unchanged_on properties about m2' *)

  Lemma pmap_update_diff': forall (A:Type) b f (map: NMap.t A) b',
  b <> b' ->
  NMap.get _ b' (Mem.pmap_update b f map) = NMap.get _ b' map.
  Proof.
    intros. unfold Mem.pmap_update.
    rewrite NMap.gsspec. rewrite pred_dec_false; auto.
  Qed.

  Lemma supext_unchanged_on : forall s m m' P,
    Mem.supext s m = m' ->
    Mem.unchanged_on P m m'.
Proof.
  intros. unfold Mem.supext in H.
  destruct Mem.sup_include_dec in H.
  - constructor; inv H.
    + eauto.
    + intros. reflexivity.
    + intros. reflexivity.
  - subst. eauto with mem.
Qed.

  Lemma unchanged_on_map_block : forall m m' b,
      Mem.map_block m1 m1' j1' b m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    intros. subst.
    unfold Mem.map_block.
    destruct (j1' b) as [[b2 d]|] eqn:j1'b; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl.
    erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
    intros. erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
  Qed.

  Lemma unchanged_on_map_sup' : forall bl m m',
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    induction bl.
    - intros. inv H. simpl. eauto with mem.
    - intros. inv H. simpl.
      eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_map_block; eauto.
      eauto.
  Qed.
  
  Lemma unchanged_on_map_sup : forall s m m',
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    intros. eapply unchanged_on_map_sup'; eauto.
  Qed.

  Lemma unchanged_step2: Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m2 m2'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s2' m2). reflexivity.
    eapply unchanged_on_map_sup; eauto. reflexivity.
  Qed.
                                          
  Lemma unchanged1_step2: Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged2_step2: Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.

    Lemma unchanged_on_copy_block1 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_access_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
          - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
  Qed.

  Lemma unchanged_on_copy'1 : forall s m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block1; eauto.
      eauto.
  Qed.
  
  Lemma unchanged_on_copy'2 : forall s m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block2; eauto.
      eauto.
  Qed.
  
  Lemma unchanged1_step3: Mem.unchanged_on (loc_out_of_reach j1 m1) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'1; eauto.
  Qed.

  Lemma unchanged2_step3: Mem.unchanged_on (loc_unmapped j2) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'2; eauto.
  Qed.

  (** Lemma C.8(1) *)
  Theorem UNCHANGE21 : Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged1_step2.
    eapply unchanged1_step3.
  Qed.

  (** Lemma C.8(2) *)
  Theorem UNCHANGE22 : Mem.unchanged_on (loc_unmapped j2) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged2_step2.
    eapply unchanged2_step3.
  Qed.

  (* Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m3 m1' s2' j1 j2 j1' j2' INJ12 INJ23 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.
   *)

  Lemma m2'1_support : Mem.support m2'1 = s2'.
  Proof. unfold m2'1. erewrite Mem.step2_support; eauto. Qed.
  Lemma m2'_support : Mem.support m2' = s2'.
  Proof. unfold m2'. erewrite Mem.copy_sup_support; eauto. erewrite m2'1_support; eauto. Qed.

  Lemma copy_block_perm1 : forall m b1 o1 b2 o2 k p,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Max Nonempty ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold Mem.perm. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_access_block_result.
      destruct Mem.loc_in_reach_find as [[b1' o1']|]eqn:FIND.
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1. reflexivity.
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia. auto.
      intro. inv H3. eauto.
    - exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.

  Lemma copy_block_perm2 : forall m b2 o2 b2' k p,
      b2 <> b2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. rewrite pmap_update_diff'; eauto. reflexivity.
  Qed.

  Lemma copy_sup_perm': forall bl m b1 o1 b2 o2 k p,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    induction bl; intros.
    - inv H2.
    - simpl. destruct H2.
      + subst a.
        eapply copy_block_perm1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_perm1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_perm2; eauto.
  Qed.

  Lemma copy_sup_perm: forall s m b1 o1 b2 o2 k p,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. apply Mem.sup_list_in in H2 as H2'.
    unfold Mem.copy_sup. eapply copy_sup_perm'; eauto.
  Qed.

  Lemma copy_perm: forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. eapply copy_sup_perm; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_block_content : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
(*      Mem.perm m1 b1 o1 Max Writable ->
*)
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 =
          if (Mem.perm_dec m1 b1 o1 Max Writable) then
            Mem.memval_map j1' (mem_memval m1' b1 o1)
            else mem_memval m b2 o2.
  Proof.
    intros.
    assert (PERM1 : Mem.perm m1 b1 o1 Max Nonempty).
    {
      eapply MAXPERM1; eauto with mem.
      eapply DOMIN1; eauto.
    }
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold mem_memval. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1' o1']|] eqn:FIND.
      + 
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto with mem.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1.
      destruct Mem.perm_dec; try congruence.
      destruct Mem.perm_dec; try congruence.
      +
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia.
      eauto with mem. intro X. inv X.
    - 
      exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.
  
  Lemma copy_block_content1 : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_true; eauto.
  Qed.

  Lemma copy_block_content3 : forall m b2 o2 b2',
      b2 <> b2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold mem_memval. simpl. rewrite pmap_update_diff'; eauto.
  Qed.

  Lemma copy_block_content2 :  forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_false; eauto.
  Qed.

  Lemma copy_sup_content': forall bl m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H3.
    - simpl. destruct H3.
      + subst a.
        eapply copy_block_content1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_content1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_content3; eauto.
  Qed.
  
  Lemma copy_sup_content: forall s m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. apply Mem.sup_list_in in H3 as H3'.
    eapply copy_sup_content'; eauto.
  Qed.
  
  Lemma copy_sup_content_2: forall bl m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        ~ Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m) b2 o2 = mem_memval m b2 o2.
  Proof.
    induction bl; intros; cbn.
    - reflexivity.
    - destruct (eq_block a b2). subst a.
      erewrite copy_block_content2; eauto.
      erewrite Mem.copy_sup_support'; eauto. 
      erewrite copy_block_content3; eauto.
  Qed.

  Lemma copy_content : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. eapply copy_sup_content; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_content_2 : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable -> ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = mem_memval m2 b2 o2.
  Proof.
    intros. etransitivity.
    unfold m2'. eapply copy_sup_content_2; eauto.
    apply m2'1_support.
    apply Mem.ro_unchanged_memval_bytes in ROUNC1.
    exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
    intros [P1 X].
    generalize unchanged_step2. intro U.
    inv U. eapply unchanged_on_contents.
    eapply Mem.valid_block_inject_2; eauto.
    replace o2 with (o1 + (o2 - o1)) by lia.
    eapply Mem.perm_inject; eauto.
  Qed.

  Lemma copy_content_inject : forall b1 o1 b2 o2,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1' b1 o1 Cur Readable ->
          Mem.perm m1 b1 o1 Max Writable ->
          ~ (j2 b2 = None) ->
          memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite copy_content; eauto.
    apply INCR1 in H as MAP1'.
    destruct (j2 b2) as [[b3 d]|] eqn : MAP2; try congruence.
    apply INCR2 in MAP2 as MAP2'.
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto. unfold compose_meminj.
    rewrite MAP1', MAP2'. reflexivity.
  Qed.

  Lemma copy_perm_1 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m1' b1 o1 k p ->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.

  Lemma copy_perm_2 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p ->
          Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.


  Lemma unchanged_on_copy_block_old : forall a m m',
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 a m = m' ->
      Mem.unchanged_on (fun b o => a <> b) m m'.
  Proof.
    intros. constructor.
    - erewrite <- Mem.copy_block_support; eauto.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
      reflexivity. reflexivity.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
  Qed.

  Lemma unchanged_on_copy_sup_old' : forall bl m m',
      Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m = m' ->
      Mem.unchanged_on (fun b o => ~ In b bl) m m'.
  Proof.
    induction bl; intros.
    - inv H. simpl. eauto with mem.
    - simpl in H. set (m'0 := Mem.copy_sup' m1 m2 m1' j1 j2 j1' INJ12 bl m).
      exploit IHbl. instantiate (1:= m'0). reflexivity. fold m'0 in H.
      intro UNC1. apply unchanged_on_copy_block_old in H as UNC2.
      apply Mem.copy_block_support in H as SUP1.
      constructor.
      + inversion UNC1. eapply Mem.sup_include_trans.  eauto.
        apply Mem.copy_block_support in H. rewrite H. eauto.
      + intros. etransitivity.
        inversion UNC1. eapply unchanged_on_perm.
        intro. apply H0. right. eauto. eauto.
        inversion UNC2. eapply unchanged_on_perm.
        intro. apply H0. left. subst. eauto.
        unfold m'0. unfold Mem.valid_block in *.
        erewrite Mem.copy_sup_support'; eauto.
      + intros. etransitivity.
        inversion UNC2. eapply unchanged_on_contents; eauto.
        intro. apply H0. left. eauto.
        inversion UNC1. eapply unchanged_on_perm0; eauto.
        intro. apply H0. right. auto. eauto with mem.
        inversion UNC1. eapply unchanged_on_contents.
        intro. apply H0. right. auto. eauto.
  Qed.
  
  Lemma unchanged_on_copy_sup_old : forall s m m',
      Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (fun b o => ~ sup_In b s) m m'.
  Proof.
    intros.
    unfold Mem.copy_sup in H.
    apply unchanged_on_copy_sup_old' in H.
    eapply Mem.unchanged_on_implies. apply H.
    intros. red. intro. apply H0. eapply Mem.sup_list_in; eauto.
  Qed.

  (*TODO: to mem*)
  Lemma perm_check_true1:
    forall m b o, Mem.perm m b o Max Nonempty ->
             Mem.perm_check_any  (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_any.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) Max) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.
  
  Lemma perm_check_true2:
    forall m b o, Mem.perm m b o Cur Readable ->
             Mem.perm_check_readable  (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_readable.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get (Maps.ZMap.t Mem.memperm) b (Mem.mem_access m)) Cur) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.

  Lemma subinj_dec : forall j j' b1 b2 d,
      inject_incr j j' -> j' b1 = Some (b2,d) ->
      {j b1 = Some (b2,d)} + {j b1 = None}.
  Proof.
    intros.
    destruct (j b1) as [[b' d']|] eqn:H1.
    left.
    apply H in H1. rewrite H0 in H1. inv H1. reflexivity.
    right. reflexivity.
  Qed.


  
  Lemma map_block_perm_1: forall b1 o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm (Mem.map_block m1 m1' j1' b1 m) b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold Mem.perm. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_access_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true1. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_perm_2: forall b1 b1' o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      b1 <> b1' ->
      Mem.perm (Mem.map_block m1 m1' j1' b1' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. 
    simpl. setoid_rewrite NMap.gso. reflexivity.
    assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
    - exploit INCRDISJ1; eauto.
    - intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_1' : forall bl m m' b2 o2 b1 o1 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      In b1 bl ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H.
      destruct H0.
      + subst a. rewrite <- H.
        eapply map_block_perm_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          eapply map_block_perm_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. apply H6. rewrite <- H.
          symmetry.
          eapply map_block_perm_2; eauto.
          rewrite Mem.map_sup_support'. eauto. 
  Qed.

  Lemma map_sup_rev' : forall bl m m' b2 o2 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        In b1 bl /\
        ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
    induction bl; intros.
    - inv H. simpl in H2. exfalso. apply H1. eauto with mem.
    - simpl in H.
      destruct (Mem.perm_dec (Mem.map_sup' m1 m1' j1' bl m) b2 o2 k p).
      + exploit IHbl; eauto.
        intros (b1 & o1 & A & B & C & D).
        exists b1,o1. repeat apply conj; eauto.
        right. eauto.
      + unfold Mem.map_block in H.
        destruct (j1' a) as [[b d]|] eqn:Hj1'a; try congruence.
        destruct (Mem.sup_dec); try congruence.
        destruct (Mem.sup_dec); try congruence.
        subst. unfold Mem.perm in H2. simpl in H2.
        unfold Mem.perm in n. simpl in n.
        destruct (eq_block b b2).
        -- subst. unfold Mem.pmap_update in H2.
           setoid_rewrite NMap.gss in H2; eauto.
           rewrite Mem.update_mem_access_result in H2.
           destruct Mem.perm_check_any.
           ++
           exists a, (o2 -d). repeat apply conj; eauto.
           left. auto. replace (o2 - (o2 - d)) with d by lia. auto.
           ++
           exfalso. apply n. eauto.
           ++ apply Mem.access_default.
        -- rewrite pmap_update_diff' in H2; eauto.
           unfold Mem.perm in n. exfalso. apply n. eauto.
  Qed.
  
  (*Lemma map_sup_rev : forall s m m' b2 o2 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        sup_In b1 s /\
        ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit map_sup_rev'; eauto.
    (* intros (b1 & o1 & A & B & C & D).
    exists b1, o1. repeat apply conj; eauto. apply Mem.sup_list_in; eauto. *)
  Qed.
   *)    
  Lemma map_sup_1 : forall s m m' b2 o2 b1 o1 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      sup_In b1 s ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    intros. apply Mem.sup_list_in in H0 as H0'. split; intro.
    eapply map_sup_1'; eauto with mem.
    exploit map_sup_rev'; eauto.
    intros (b1' & o1' & A & B & C & D).
    assert (b1 = b1').
    { destruct (eq_block b1 b1'). auto.
      exploit INCRNOLAP'1; eauto.
      inv INJ12; eauto. inv INJ12; eauto.
      intro. inv H6.
    }
    subst. rewrite H4 in C. inv C.
    assert (o1 = o1'). lia. subst. eauto.
  Qed.

  Lemma map_block_memval_1: forall b1 o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      mem_memval (Mem.map_block m1 m1' j1' b1 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_content_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true2. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_memval_2: forall b1 b1' o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      b1 <> b1' ->
      mem_memval (Mem.map_block m1 m1' j1' b1' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; eauto.
    destruct Mem.sup_dec; eauto.
    destruct Mem.sup_dec; eauto.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gso. reflexivity.
       assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
       destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
       ++ exploit INCRDISJ1; eauto.
       ++ intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_2 : forall bl m m' b2 o2 b1 o1,
            Mem.map_sup' m1 m1' j1' bl m = m' ->
            In b1 bl ->
            ~ sup_In b1 (Mem.support m1) ->
            Mem.support m = s2' ->
            j1' b1 = Some (b2, o2 - o1) ->
            Mem.perm m1' b1 o1 Cur Readable ->
            (mem_memval m' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H. generalize INJNOLAP1'. intro INJNOLAP1'.
      destruct H0.
      + subst a. rewrite <- H. apply map_block_memval_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          apply map_block_memval_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * exploit IHbl; eauto.
          intro. rewrite <- H5. rewrite <- H.
          eapply map_block_memval_2; eauto.
          rewrite Mem.map_sup_support'. eauto.
  Qed.
  
  Lemma supext_empty : forall b o k p,
      ~ sup_In b (Mem.support m2) ->
      ~ Mem.perm (Mem.supext s2' m2) b o k p.
  Proof.
    intros. unfold Mem.supext.
    destruct Mem.sup_include_dec.
    unfold Mem.perm. simpl.
    erewrite Mem.nextblock_noaccess. eauto. eauto.
    congruence.
  Qed.
      
                        
  Lemma step2_perm: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (forall k p, Mem.perm m1' b1 o1 k p <-> Mem.perm m2' b2 o2 k p).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    transitivity (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence.
      eauto. eauto. eauto.
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
  Qed.

  Lemma step2_perm2: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    assert (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto.
      intro. unfold m2'1 in H2. apply H3. eauto.
  Qed.

  Lemma step2_content: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      (mem_memval m2' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    exploit unchanged_on_copy_sup_old. instantiate (1:= m2'). reflexivity.
    intro UNC2.
    assert (Mem.perm m2'1 b2 o2 Cur Readable).
    { unfold m2'.
      inversion UNC2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
      eapply step2_perm; eauto. eauto with mem.
    }
    - etransitivity. inversion UNC2.
      setoid_rewrite unchanged_on_contents. reflexivity. eauto.
      eauto.
      unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_2. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))). unfold Mem.map_sup.
      reflexivity. rewrite <- Mem.sup_list_in. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto. eauto.
  Qed.

  Lemma step2_content_inject: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite step2_content; eauto.
    exploit ADDEXISTS; eauto. intros (b3 & o3 & MAP13).
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto.
  Qed.

  Lemma step2_perm1: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p ->
      Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit step2_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.
  
  (** Lemma C.10 *)
  Theorem MAXPERM2 : injp_max_perm_decrease m2 m2'.
  Proof.
    red. intros b2 o2 p VALID PERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|]eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct (j2 b2) as [[b3 d2]|] eqn: Hj2.
      + destruct LOCIN as [MAP1 PERM1_].
        exploit copy_perm_2; eauto. congruence.
        intro PERM1'.
        red in MAXPERM1. exploit MAXPERM1; eauto.
        unfold Mem.valid_block. eauto.
        intro PERM1.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
      + generalize (UNCHANGE22). intro UNC2.
        inversion UNC2. eapply unchanged_on_perm; eauto.
    - generalize (UNCHANGE21). intro UNC1.
      inversion UNC1. eapply unchanged_on_perm; eauto.
      eapply Mem.loc_in_reach_find_none; eauto.
  Qed.

  (** Lemma C.11 *)
  Theorem ROUNC2 : Mem.ro_unchanged m2 m2'.
  Proof.
    apply Mem.ro_unchanged_memval_bytes.
    red. intros b2 o2 VALID PERM2' NOPERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
      destruct (j2 b2) as [[b3 d2]|] eqn: MAP2.
      + 
        exploit copy_perm_2; eauto. congruence. intro PERM1'.
        assert (NOWRIT1: ~ Mem.perm m1 b1 o1 Max Writable).
        intro. apply NOPERM2.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        split. apply Mem.ro_unchanged_memval_bytes in ROUNC1.
        exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
        intros [READ1 ?].
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        symmetry. eapply copy_content_2; eauto. congruence.
      + generalize UNCHANGE22. intro UNC22. split; inv UNC22.
        rewrite unchanged_on_perm; eauto.
        symmetry. eapply unchanged_on_contents; eauto.
        eapply unchanged_on_perm; eauto.
    - eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
      generalize UNCHANGE21. intro UNC21.
      split; inv UNC21. rewrite unchanged_on_perm; eauto.
      symmetry. eapply unchanged_on_contents; eauto.
      eapply unchanged_on_perm; eauto.
  Qed.
    
  (** Lemma C.13 *)
  Theorem INJ12' : Mem.inject j1' m1' m2'.
  Proof.
    constructor.
    - constructor.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- eapply copy_perm_1; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. apply unchanged_on_perm; eauto.
             inversion INJ12. eauto.
             eapply Mem.perm_inject; eauto.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          replace (ofs + 0) with ofs by lia.
          eapply step2_perm1; eauto. replace (ofs - ofs) with 0 by lia.
          eauto. eauto with mem.
      + intros. destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * inversion INJ12. inversion mi_inj.
          eapply mi_align; eauto.
          red. intros. exploit H0; eauto.
          intro. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          exists 0. lia.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1 b1 ofs Max Writable).
             ++ 
               eapply copy_content_inject; eauto.
               replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
             ++ generalize ROUNC2. intro ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC1.
                exploit ROUNC1; eauto.
                eapply Mem.valid_block_inject_1; eauto.
                intros [PERM1 MVAL1]. rewrite <- MVAL1.

                exploit ROUNC2; eauto.
                eapply Mem.valid_block_inject_2. apply e. eauto.
                eapply copy_perm_1; eauto with mem. instantiate (1:= ofs + delta).
                replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
                intro. eapply n. inversion INJ12.
                exploit mi_perm_inv; eauto. intros [|]. auto.
                exfalso. apply H2. eauto with mem.
                intros [PERM2 MVAL2]. rewrite <- MVAL2.
                inversion INJ12. inversion mi_inj.
                eapply memval_inject_incr; eauto.
          -- assert (PERM1 : Mem.perm m1 b1 ofs Cur Readable).
             inversion UNCHANGE1. eapply unchanged_on_perm; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
             assert (PERM2 : Mem.perm m2 b2 (ofs + delta) Cur Readable).
             eapply Mem.perm_inject; eauto.
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. rewrite unchanged_on_contents; eauto.
             inversion INJ12. eauto.
             inversion UNCHANGE1. rewrite unchanged_on_contents0; eauto.
             inversion mi_inj.
             eapply memval_inject_incr; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
        * eapply step2_content_inject; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
    - intros.
      destruct (j1' b) as [[b2 d]|] eqn:?.
      exploit ADDEXISTS; eauto. inversion INJ12.
      eapply mi_freeblocks. inversion UNCHANGE1.
      intro. apply H. apply unchanged_on_support. eauto.
      intros (b3 & ofs3 & MAP).
      inversion INJ13'. exploit mi_freeblocks; eauto.
      intro. congruence. reflexivity.
    - intros. unfold Mem.valid_block. rewrite m2'_support. eauto.
    - eapply update_meminj_no_overlap1; eauto.
    - intros. destruct (j1 b) as [[b2' d']|] eqn: Hj1b.
        * apply INCR1 in Hj1b as H'. rewrite H in H'. inv H'.
          inversion INJ12.
          eapply mi_representable; eauto.
          destruct H0.
          left. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
          right. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst. split. lia.
          generalize (Ptrofs.unsigned_range_2 ofs). lia.
    - intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1' b1 ofs Max Nonempty); eauto.
             left.
             eapply copy_perm_2; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- 
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. apply unchanged_on_perm in H0 as PERM2; eauto.
             2: inversion INJ12; eauto.
             inversion INJ12. exploit mi_perm_inv; eauto.
             intros [A|B].
             left.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
             right. intro. apply B.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
        * left. eapply step2_perm2; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
  Qed.


  Lemma step2_perm2': forall b1 o1 b2 o2 b3 d k p,
      j1' b1 = Some (b2, o2 - o1) ->
      j2 b2 = None -> j2' b2 = Some (b3, d) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit step2_perm2; eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 H); auto.
    exploit INCRDISJ2; eauto. intros [A B].
    inversion INJ12. exploit mi_mappedblocks; eauto.
  Qed.

  (** Lemma C.14 *)
  Theorem INJ23' : Mem.inject j2' m2' m3'.
  Proof.
     assert (DOMIN2: inject_dom_in j2 (Mem.support m2)).
     eapply inject_implies_dom_in; eauto.
     assert (IMGIN2: inject_image_in j2 (Mem.support m3)).
     eapply inject_implies_image_in; eauto.
    constructor.
    - (*mem_inj*)
      constructor.
      + (*perm*)
        intros b2 b3 d2 o2 k p MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            
            exploit copy_perm_2; eauto. congruence.
            intro PERM1'.
            apply INCR1 in MAP1 as MAP1'.
            exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
            unfold compose_meminj. rewrite MAP1', MAP2'.
            reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
            auto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM2 : Mem.perm m2 b2 o2 k p).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. eapply unchanged_on_perm; eauto.
            inversion INJ23. eauto.
            eapply Mem.perm_inject; eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          eapply Mem.perm_inject. 2: apply INJ13'. unfold compose_meminj.
          rewrite MAP1', MAP2'. eauto. eauto.
      + (*align*)
        intros b2 b3 d2 chunk o2 p MAP2' RP2. destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
        * inversion INJ23. inversion mi_inj. eapply mi_align; eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intro. generalize MAXPERM2. intro UNC2.
          eapply UNC2; eauto. unfold Mem.valid_block in *.
          destruct (Mem.sup_dec b2 (Mem.support m2)).
          eauto.  exploit mi_freeblocks; eauto.
        *
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          inversion INJ13'. inv mi_inj.
          exploit mi_align.
          unfold compose_meminj. rewrite MAP1', MAP2'.
          replace (0 + d2) with d2 by lia. reflexivity.
          2: eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intros. eapply step2_perm2'; eauto.
          replace (ofs - ofs) with 0 by lia. eauto.
      + (*memval*)
        intros b2 o2 b3 d2 MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            apply INCR1 in MAP1 as MAP1'.
            destruct (Mem.perm_dec m1 b1 o1 Max Writable).
            ++
              exploit copy_content; eauto. eapply copy_perm_2; eauto. congruence. congruence.
              intro. setoid_rewrite H.
              eapply memval_compose_2; eauto.
              inversion INJ13'. inversion mi_inj.
              exploit mi_memval; eauto. unfold compose_meminj.
              rewrite MAP1'. rewrite MAP2'. reflexivity.
              eapply copy_perm; eauto. congruence. 
              replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
              eauto.
            ++ generalize ROUNC2. intro ROUNC2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC2.
               assert (NOWRIT2: ~ Mem.perm m2 b2 o2 Max Writable).
               intro. apply n. inversion INJ12. exploit mi_perm_inv; eauto.
               instantiate (3:= o1). replace (o1 + (o2 - o1)) with o2 by lia. eauto.
               intros [|]. eauto. congruence.
               exploit ROUNC2; eauto. intros [PERM2 MVAL2]. rewrite <- MVAL2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC3.
               assert (NOWRIT3 : ~ Mem.perm m3 b3 (o2 + d2) Max Writable).
               intro. apply NOWRIT2. inversion INJ23. exploit mi_perm_inv; eauto.
               intros [|]. eauto. exfalso. apply H0. eauto with mem.
               exploit ROUNC3; eauto. eapply Mem.valid_block_inject_2; eauto.
               exploit copy_perm_2; eauto. congruence.
               intro PERM1'.
               exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
               unfold compose_meminj. rewrite MAP1', MAP2'.
               reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
               auto.
               intros [PERM3 MVAL3]. rewrite <- MVAL3.
               inversion INJ23. inversion mi_inj. eapply memval_inject_incr; eauto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM2 : Mem.perm m2 b2 o2 Cur Readable).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (PERM3 : Mem.perm m3 b3 (o2 + d2) Cur Readable).
            eapply Mem.perm_inject; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. erewrite unchanged_on_contents; eauto.
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            erewrite unchanged_on_contents0; eauto.
            eapply memval_inject_incr; eauto.
            inversion INJ23. inversion mi_inj. eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          exploit step2_content; eauto.
          destruct (subinj_dec _ _ _ _ _ INCR1 MAP1'); auto.
          exfalso. apply n. inversion INJ12. exploit mi_mappedblocks; eauto.
          instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro.
          setoid_rewrite H.
          eapply memval_compose_2; eauto.
          inversion INJ13'. inversion mi_inj.
          eapply mi_memval; eauto.
          unfold compose_meminj.
          rewrite MAP1'. rewrite MAP2'. reflexivity.
    - intros. destruct (j2' b) as [[b3 d]|] eqn:?.
      exploit DOMIN2'; eauto.
      unfold Mem.valid_block in H.
      rewrite m2'_support in H. intro. congruence.
      reflexivity.
    - intros. destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. exploit mi_mappedblocks; eauto.
        unfold Mem.valid_block.
        intro. inversion UNCHANGE3. eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_mappedblocks; eauto.
        unfold compose_meminj. rewrite MAP1',H. reflexivity.
    - red. intros b2 b3 d2 b2' b3' d2' o2 o2' NEQ MAP2 MAP2' PERM2 PERM2'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2); destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + inversion INJ23. eapply mi_no_overlap; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit ADDSAME. apply e. all: eauto. intros [b1 [MAP1 SAME1]].
        exploit ADDSAME; eauto. intros [b1' [MAP1' SAME1']].
        inversion INJ13'. red in mi_no_overlap.
        assert (b1 <> b1'). intro. subst. rewrite MAP1 in MAP1'. inv MAP1'. congruence.
        eapply mi_no_overlap. eauto.
        unfold compose_meminj. rewrite MAP1, MAP2. eauto.
        unfold compose_meminj. rewrite MAP1', MAP2'. eauto.
        eapply step2_perm2'. instantiate (1:= o2).
        replace (o2 - o2) with 0 by lia. eauto. eauto. eauto. eauto.
        eapply step2_perm2'. instantiate (1:= o2').
        replace (o2' - o2') with 0 by lia. eauto. eauto. eauto. eauto.
    - intros.
      destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. eapply mi_representable; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        destruct H0.
        left. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
        right. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_representable; eauto.
        unfold compose_meminj. rewrite MAP1',H. eauto.
        destruct H0.
        left. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
        right. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
    - intros b2 o2 b3 d2 k p MAP2' PERM3'.
      generalize INJ12'. intro INJ12'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
        * eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
          destruct LOCIN as [MAP1 PERM1].
          apply INCR1 in MAP1 as MAP1'.
          inversion INJ13'. exploit mi_perm_inv.
          unfold compose_meminj. rewrite MAP1', MAP2'. reflexivity.
          instantiate (3:= o1). replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
          eauto. intros [A | B].
          left. eapply copy_perm; eauto. congruence.
          right. intro. apply B. eapply copy_perm; eauto. congruence.
        * eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
          destruct (Mem.perm_dec m2' b2 o2 Max Nonempty); auto.
          left. generalize UNCHANGE21. intro UNC2.
          assert (PERM2: Mem.perm m2 b2 o2 Max Nonempty).
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
          assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
          eapply loc_out_of_reach_trans; eauto.
          assert (PERM3: Mem.perm m3 b3 (o2 + d2) k p).
          inversion UNCHANGE3. eapply unchanged_on_perm; eauto.
          eapply IMGIN2; eauto.
          inversion INJ23. exploit mi_perm_inv. eauto. apply PERM3.
          intros [A|B]; try congruence.
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
      + exploit INCRDISJ2; eauto. intros [A B].
        exploit ADDSAME; eauto. intros [b1 [MAP1' SAME]].
        inversion INJ13'. exploit mi_perm_inv.
        unfold compose_meminj. rewrite MAP1', MAP2'. replace (0 + d2) with d2 by lia.
        reflexivity. eauto.
        destruct (subinj_dec _ _ _ _ _ INCR1 MAP1').
        inversion INJ12. exploit mi_mappedblocks0; eauto.
        intros [P1 | P1].
        left. eapply step2_perm1; eauto. replace (o2 - o2) with 0 by lia. eauto. eauto with mem.
        right. intro. apply P1. eapply step2_perm2; eauto.
        replace (o2 - o2) with 0 by lia. eauto.
  Qed.
    
End CONSTR_PROOF.

(** main content of Lemma C.16*)
Lemma out_of_reach_trans: forall j12 j23 m1 m2 m3 m3',
    Mem.inject j12 m1 m2 ->
    Mem.unchanged_on (loc_out_of_reach (compose_meminj j12 j23) m1) m3 m3' ->
    Mem.unchanged_on (loc_out_of_reach j23 m2) m3 m3'.
Proof.
  intros.
  inv H0. constructor; auto.
  - intros. eapply unchanged_on_perm; auto.
  red in H. red.
  intros b1 delta23 MAP13.  unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto.
  - intros. eapply unchanged_on_contents.
  red in H. red.
  intros b1 delta23 MAP13. unfold compose_meminj in MAP13.
  destruct (j12 b1) as [[b2 delta2]|] eqn: MAP12; try congruence.
  destruct (j23 b2) as [[b3 delta3]|] eqn: MAP23; try congruence.
  inv MAP13.
  apply H0 in MAP23 as NOPERM2.
  inversion H. inversion mi_inj.
  destruct (Mem.perm_dec m1 b1 (ofs - (delta2 + delta3)) Max Nonempty).
  exploit mi_perm; eauto.
  replace (ofs - (delta2 + delta3) + delta2) with (ofs - delta3).
  intro. congruence. lia. auto. auto.
Qed.

(** injp ⊑ injp ⋅ injp *)
Lemma injp_injp2:
  subcklr (injp @ injp) injp.
Proof.
  red.
  intros w se1 se3 m1 m3 MSTBL13 MMEM13. destruct w as [w12 w23].
  destruct MMEM13 as [m2 [MMEM12 MMEM23]].
  simpl in *.
  inv MMEM12. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  exists (injpw (compose_meminj j12 j23)
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23)).
  simpl.
  repeat apply conj.
  - inv MSTBL13. inv H. inv H0. inv H1.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - constructor.
  - apply inject_incr_refl.
  - intros w13' m1' m3' MMEM13' INCR13'.
    unfold rel_compose.
    clear MSTBL13.
    cbn in INCR13'.
    inv MMEM13'. rename f into j13'. rename Hm3 into INJ13'.
    cbn.
    inversion INCR13' as [? ? ? ? ? ? ? ? ROUNC1 ROUNC3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
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
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' m2'_sup INJ12 ).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    set (w1' := injpw j12' m1' m2' INJ12').
    set (w2' := injpw j23' m2' m3' INJ23').
    exists (w1', w2').
    cbn.
    repeat apply conj; cbn.
    + exists m2'.
      repeat apply conj; constructor; auto.
    + unfold w1'. constructor; auto.
      -- eapply ROUNC2; eauto.
      -- eapply MAXPERM2; eauto.
      -- (** * main content of Lemma A.12 *)
         eapply Mem.unchanged_on_implies; eauto.
         intros. red. red in H. unfold compose_meminj.
         rewrite H. reflexivity.
      -- eapply UNCHANGE21; eauto.
    + unfold w2'. constructor; eauto.
      -- eapply ROUNC2; eauto.
      -- eapply MAXPERM2; eauto.
      -- eapply UNCHANGE22; eauto.
      -- eapply out_of_reach_trans; eauto.
    + apply inject_incr_refl.
Qed.

(** injp ≡ injp ⋅ injp *)
Lemma injp_injp_eq :
  eqcklr (injp @ injp) injp.
Proof.
  split.
  apply injp_injp2.
  apply injp_injp.
Qed.

(** * Other refinement properties about injp *)
(* injp -------------- inj *)
Lemma sub_inj_injp :
  subcklr inj injp.
Proof.
  red. intros [j sup1 sup2] se1 se2 m1 m2 MSTBL MMEM0.
  inversion MMEM0 as [? ? ? MMEM]. subst.
  exists (injpw j m1 m2 MMEM).
  simpl.
  repeat apply conj.
  - inv MSTBL. constructor; eauto.
  - constructor.
  - eauto.
  - intros [j' ? ? MMEM'] m1' m2' A B. inv A. inv B.
    exists (injw j' (Mem.support m1') (Mem.support m2')).
    simpl. repeat apply conj; eauto.
    + constructor; eauto.
      inv H9; eauto. inv H10; eauto.
Qed.

Lemma injp_inj__inj :
  subcklr inj (injp @ inj).
Proof.
  etransitivity. eapply inj_inj.
  apply cklr_compose_subcklr. apply sub_inj_injp.
  reflexivity.
Qed.

(* injp   ------------     injp
                ------     injp ---------- inj *)
Lemma injp_inj :
  subcklr (injp @ inj) injp.
Proof.
  etransitivity.
  apply cklr_compose_subcklr. reflexivity.
  apply sub_inj_injp. apply injp_injp2.
Qed.

(* injp   ------------     injp ---------- inj
                ------     injp ---------- inj *)
Lemma inj_injp :
  subcklr (inj @ injp) injp.
Proof.
  etransitivity.
  apply cklr_compose_subcklr. apply sub_inj_injp.
  reflexivity. apply injp_injp2.
Qed.

Lemma injp__injp_inj_injp:
  subcklr injp (injp @ inj @ injp).
Proof.
  intros [f m1 m4 Hm14] se1 se4 ? ? STBL MEM. inv MEM.
  inv STBL. clear Hm0 Hm1 Hm2 Hm3 Hm4 Hm5. rename m2 into m4. rename m0 into m1.
  generalize (mem_inject_dom f m1 m4 Hm14). intro Hm12.
  exists (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m4 Hm14),
           (injw (meminj_dom f) (Mem.support m1) (Mem.support m1),
            injpw f m1 m4 Hm14)).
  simpl.
  repeat apply conj.
  - exists se1. split. constructor; eauto.
    eapply match_stbls_dom; eauto.
    exists se1. split. constructor; eauto.
    eapply match_stbls_dom; eauto.
    eauto.
  - exists m1; split.
    constructor.
    exists m1; split.
    { constructor; repeat rstep; eauto using mem_inject_dom. }
    constructor; eauto.
  - rewrite !meminj_dom_compose.
    apply inject_incr_refl.
  - intros (w12' & w23' & w34') m1' m4'.
    intros (m2' & Hm12' & m3' & Hm23' & Hm34').
    intros (H12 & H23 & H34). simpl in *.
    destruct Hm12' as [f12 m1' m2' Hm12'].
    inversion Hm23' as [f23 xm2' xm3' Hm23'']; clear Hm23'; subst.
    destruct Hm34' as [f34 m3' m4' Hm34'].
    inv H12.
    inv H23.
    inv H34.
    assert (Hm14' :  Mem.inject (compose_meminj f12 (compose_meminj f23 f34)) m1' m4').
    eapply Mem.inject_compose; eauto.
    eapply Mem.inject_compose; eauto.
    eexists (injpw (compose_meminj f12 (compose_meminj f23 f34)) m1' m4' Hm14').
    repeat apply conj.
    + constructor; eauto.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. apply loc_unmapped_dom; eauto.
      * rewrite <- (meminj_dom_compose f).
        rewrite <- (meminj_dom_compose f) at 2.
        rauto.
      * red. intros b1 b4 d f14 INJ. unfold compose_meminj in INJ.
        destruct (f12 b1) as [[b2 d1]|] eqn: INJ1; try congruence.
        destruct (f23 b2) as [[b3 d2]|] eqn: INJ2; try congruence.
        destruct (f34 b3) as [[b4' d3]|] eqn: INJ3; try congruence. inv INJ.
        exploit H16; eauto. unfold meminj_dom. rewrite f14. auto.
        intros [A B].
        exploit H17; eauto. inversion Hm12. apply mi_freeblocks; eauto.
        intros [C D]. eauto.
        exploit H27. 2: eauto. inversion Hm14. apply mi_freeblocks; eauto.
        intros [E F]. split; eauto.
    + repeat rstep; eauto.
Qed.
