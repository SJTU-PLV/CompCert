Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Memory.
Require Import Smallstep.
Require Import Inject InjectFootprint.
Require Import Callconv ForwardSim.

(** * Test1: compose injp' ⋅ injp' = injp' *)

(*
L1 <=injp'->injp' L2 ->
L2 <=injp'->injp' L3 ->
L1 <= injp'-> injp' L3
*)

Section COMPOSE_FORWARD_SIMULATIONS.

Context (L1: semantics li_c li_c) (L2: semantics li_c li_c) (L3: semantics li_c li_c).

Definition symtbl_dom (se: Genv.symtbl) : meminj :=
  fun b => if Mem.sup_dec b (Genv.genv_sup se) then Some (b,0)
        else None.

Definition source_inj (se: Genv.symtbl) (f : meminj) :=
  fun b => if Mem.sup_dec b (Genv.genv_sup se) then
        Some (b,0) else meminj_dom f b.

Lemma source_inj_meminj_dom_incr : forall se f,
    inject_incr (meminj_dom f) (source_inj se f).
Proof.
  intros. intro. intros.
  unfold source_inj.
  unfold meminj_dom in *.
  destruct (f b); try discriminate. inv H.
  destruct Mem.sup_dec; eauto.
Qed.

Global Instance source_inj_incr se:
  Monotonic (@source_inj se) (inject_incr ++> inject_incr).
Proof.
  intros f g Hfg b b' delta Hb.
  unfold source_inj in *.
  destruct (Mem.sup_dec). eauto.
  eapply meminj_dom_incr; eauto.
Qed.

Lemma source_inj_compose se f:
  compose_meminj (source_inj se f) f = f.
Proof.
  apply Axioms.functional_extensionality; intros b.
  unfold compose_meminj, source_inj, meminj_dom.
  destruct (Mem.sup_dec).
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  destruct (f b) as [[b' ofs] | ] eqn:Hfb; eauto.
  rewrite Hfb.
  replace (0 + ofs) with ofs by extlia.
  reflexivity.
Qed.

Lemma block_inject_dom se f b1 b2:
  block_inject f b1 b2 ->
  block_inject (source_inj se f) b1 b1.
Proof.
  unfold source_inj,meminj_dom.
  intros (delta & Hb).
  exists 0.
  rewrite Hb; eauto.
  destruct Mem.sup_dec; eauto.
Qed.

Lemma val_inject_dom se f v1 v2:
  Val.inject f v1 v2 ->
  Val.inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  - unfold source_inj, meminj_dom.
    rewrite H. destruct Mem.sup_dec; eauto.
  - rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Lemma memval_inject_dom se f v1 v2:
  memval_inject f v1 v2 ->
  memval_inject (source_inj se f) v1 v1.
Proof.
  destruct 1; econstructor.
  eapply val_inject_dom; eauto.
Qed.

Lemma val_inject_list_dom se f vs1 vs2:
  Val.inject_list f vs1 vs2 ->
  Val.inject_list (source_inj se f) vs1 vs1.
Proof.
  induction 1; constructor; eauto using val_inject_dom.
Qed.

Lemma mem_mem_inj_dom se f m1 m2:
  Mem.mem_inj f m1 m2 ->
  Mem.mem_inj (source_inj se f) m1 m1.
Proof.
  intros H.
  split.
  - unfold source_inj, meminj_dom. intros b1 b2 delta ofs k p Hb1 Hp.
    destruct Mem.sup_dec; destruct (f b1); inv Hb1;
    replace (ofs + 0) with ofs by extlia; auto.
  - unfold source_inj, meminj_dom. intros b1 b2 delta chunk ofs p Hb1 Hrp.
    destruct (Mem.sup_dec); destruct (f b1) as [[b1' delta'] | ]; inv Hb1;
    eauto using Z.divide_0_r.
  - unfold source_inj, meminj_dom at 1. intros b1 ofs b2 delta Hb1 Hp.
    destruct (Mem.sup_dec) eqn:Hs; destruct (f b1) as [[b1' delta'] | ] eqn:Hb1'; inv Hb1.
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
    replace (ofs + 0) with ofs by extlia.
    {
      set (mv:= (Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b2 (Mem.mem_contents m1)))).
      destruct mv; constructor.
      destruct v; econstructor.
      rewrite pred_dec_true. 2: eauto.
    }
    rewrite pred_dec_true. 2: eauto.
    Search memval_inject.
    eapply memval_inject_dom. admit.
    replace (ofs + 0) with ofs by extlia.
    eapply memval_inject_dom.
    eapply Mem.mi_memval; eauto.
Qed.

Lemma mem_inject_dom f m1 m2:
  Mem.inject f m1 m2 ->
  Mem.inject (meminj_dom f) m1 m1.
Proof.
  intros H.
  split.
  - eapply mem_mem_inj_dom.
    eapply Mem.mi_inj; eauto.
  - unfold meminj_dom. intros.
    erewrite Mem.mi_freeblocks; eauto.
  - unfold meminj_dom; intros.
    destruct (f b) as [[b'' delta'] | ] eqn:Hb; inv H0.
    eapply Mem.valid_block_inject_1; eauto.
  - red. unfold meminj_dom. intros.
    destruct (f b1); inv H1.
    destruct (f b2); inv H2.
    eauto.
  - unfold meminj_dom. intros.
    destruct (f b); inv H0.
    split; try extlia.
    rewrite Z.add_0_r.
    apply Ptrofs.unsigned_range_2.
  - unfold meminj_dom. intros.
    destruct (f b1); inv H0.
    rewrite Z.add_0_r in H1; eauto.
Qed.

Lemma match_stbls_dom f se1 se2:
  Genv.match_stbls f se1 se2 ->
  Genv.match_stbls (meminj_dom f) se1 se1.
Proof.
  intros Hse. unfold meminj_dom. split; eauto; intros.
  - edestruct Genv.mge_dom as (b2 & Hb2); eauto. rewrite Hb2. eauto.
  - edestruct Genv.mge_dom as (b3 & Hb3); eauto. exists b2. rewrite Hb3. eauto.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
Qed.

Lemma loc_unmapped_dom f b ofs:
  loc_unmapped (meminj_dom f) b ofs <->
  loc_unmapped f b ofs.
Proof.
  unfold meminj_dom, loc_unmapped.
  destruct (f b) as [[b' delta] | ].
  - split; discriminate.
  - reflexivity.
Qed.

Lemma mem_inject_source : forall f m1 m2 se,
    Mem.inject f m1 m2 ->
    Mem.inject (source_inj se f) m1 m1.
Proof.
  intros.
  exploit mem_inject_dom; eauto.
  intro.
  Search Mem.inject.
Definition soucr_world (w: injp_world) (se:Genv.symtbl) :=
  match w with
  |injpw f m1 m2 Hm =>
     injpw (source_inj se f) m1 m1 (mem_inject_dom f m1 m2 Hm)
  end.

Lemma match_stbls_dom' f se1 se2:
  Genv.match_stbls' f se1 se2 ->
  Genv.match_stbls (meminj_dom f) se1 se1.
Proof.
  intros Hse. unfold meminj_dom. split; eauto; intros.
  - inv Hse.
  - inv Hse. admit
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
  - destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb; inv H. reflexivity.
Qed.

Lemma compose_fsim_components':
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L2 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L2 L3 ->
  fsim_components' (cc_c' injp') (cc_c' injp') L1 L3.
Proof.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se3 (w: injp_world) (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se1 (id_world w) (snd i) s1 s2 /\
             match_states' se1 se3 w (fst i) s2 s3).
  apply Forward_simulation' with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { etransitivity; eauto. }
  intros se1 se2 w Hse2 Hcompat. cbn in *.
  assert (Hse1: injp_match_stbls' (id_world w) se1 se1).
  { clear - Hse2.
    inv Hse2. constructor; eauto.
    inv H. constructor; intros; eauto.
    - unfold meminj_dom in H2. destruct (f b1); try discriminate
    
  }
  assert (Hse1: Genv.valid_for (skel L1) se1).
  {}
  Search Genv.skel_le.
  { rewrite <- Hsk. eapply match_senv_valid_for; eauto. }
  constructor.
- (* valid query *)
  intros q1 q3 (q2 & Hq12 & Hq23).
  erewrite fsim_match_valid_query by eauto.
  eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros q1 q3 s1 (q2 & Hq12 & Hq23) Hs1.
  edestruct (@fsim_match_initial_states liA1) as (i & s2 & A & B); eauto.
  edestruct (@fsim_match_initial_states liA2) as (i' & s3 & C & D); eauto.
  exists (i', i); exists s3; split; auto. exists s2; auto.
- (* final states *)
  intros. cbn. destruct H as (s3 & A & B).
  edestruct (@fsim_match_final_states liA1) as (r2 & Hr2 & Hr12); eauto.
  edestruct (@fsim_match_final_states liA2) as (r3 & Hr3 & Hr23); eauto.
- (* external states *)
  intros. destruct H as [s3 [A B]].
  edestruct (@fsim_match_external liA1) as (w12 & q2 & Hq2 & Hq12 & Hw12 & Hk12); eauto.
  edestruct (@fsim_match_external liA2) as (w23 & q3 & Hq3 & Hq23 & Hw23 & Hk23); eauto.
  exists (se2, w12, w23), q3. cbn; repeat apply conj; eauto.
  intros r1 r3 s1' (r2 & Hr12 & Hr23) Hs1'.
  edestruct Hk12 as (i12' & s2' & Hs2' & Hs12'); eauto.
  edestruct Hk23 as (i23' & s3' & Hs3' & Hs23'); eauto.
  exists (i23', i12'), s3'. split; auto. exists s2'; auto.
- (* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  edestruct (@fsim_simulation' liA1) as [(i1' & s3' & C & D) | (i1' & C & D & E)]; eauto.
+ (* L2 makes one or several steps. *)
  edestruct (@simulation_plus liA2) as [(i2' & s2' & P & Q) | (i2' & P & Q & R)]; eauto.
* (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
* (* L3 makes no step *)
  exists (i2', i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto.
+ (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto.
  exists s3; auto.
Qed.

Lemma compose_forward_simulations:
  forward_simulation ccA12 ccB12 L1 L2 ->
  forward_simulation ccA23 ccB23 L2 L3 ->
  forward_simulation (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros [X] [Y]. constructor.
  apply compose_fsim_components; auto.
Qed.

End COMPOSE_FORWARD_SIMULATIONS.
