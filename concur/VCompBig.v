Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.
Require Export Smallstep.

Require Import Relations.
Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.

Require Import CallconvBig CallConvAlgebra.

Require Import RelClasses.


(* Set Asymmetric Patterns. *)
(* Set Implicit Arguments. *)
 Generalizable All Variables. 

Import GS.


Section COMP_FSIM.

  Context `(cc1: callconv lis lin) `(cc2: callconv lin lif)
          (Ls: semantics lis lis) (Ln: semantics lin lin) (Lf: semantics lif lif).
  Context (H1: fsim_components cc1 Ls Ln)
          (H2: fsim_components cc2 Ln Lf).

  Inductive compose_fsim_match_states se1 se3:
    ccworld (cc_compose cc1 cc2) ->
    gworld (cc_compose cc1 cc2) ->
    (fsim_index H2 * fsim_index H1) ->
    state Ls -> state Lf -> Prop :=
  | compose_match_states_intro se2 s1 s2 s3 i1 i2 wb1 wb2 wp1 wp2
    (HS1: fsim_match_states H1 se1 se2 wb1 wp1 i1 s1 s2)
    (HS2: fsim_match_states H2 se2 se3 wb2 wp2 i2 s2 s3):
    compose_fsim_match_states se1 se3 (se2, (wb1, wb2)) (wp1,wp2) (i2, i1) s1 s3.

  Lemma st_fsim_vcomp':
    fsim_components (cc_compose cc1 cc2) Ls Lf.
  Proof.
    set (ff_order := lex_ord (Relation_Operators.clos_trans
                                _ (fsim_order H2)) (fsim_order H1)).
    apply GS.Forward_simulation with ff_order compose_fsim_match_states.
    - rewrite (fsim_skel H1); apply (fsim_skel H2).
    - intros se1 se3 [se2 [wb1 wb2]] [Hse01 Hse02] Hse1.
      pose proof (@fsim_lts _ _ _ _ _ H1 se1 se2 wb1 Hse01 Hse1) as X1.
      assert (Hse2: Genv.valid_for (skel Ln) se2).
      { rewrite <- (fsim_skel H1). eapply match_senv_valid_for; eauto. }
      pose proof (@fsim_lts _ _ _ _ _ H2 se2 se3 wb2 Hse02 Hse2) as X2.
      clear Hse1 Hse2. constructor.
      + intros q1 q3 (q2 & Hq1 & Hq2).
        etransitivity; eauto using fsim_match_valid_query.
      + intros q1 q3 s1 (q2 & Hq12 & Hq23) Hi Hse.
        destruct Hse as (Hse1 & Hse2). cbn in *.
        edestruct (@fsim_match_initial_states lis) as (i & s2 & A & B); eauto.
        edestruct (@fsim_match_initial_states lin) as (i' & s3 & C & D); eauto.
        eexists (i', i), s3. split; eauto.
        econstructor; eauto.
      + intros (wb1' & wb2') (i2, i1) s1 s3 r1 Hs H.
        inv Hs.
        edestruct (@fsim_match_final_states lis) as (r2 & wb1'' & Hr2 & ACCO1 & ACCI1 & A); eauto.
        edestruct (@fsim_match_final_states lin) as (r3 & wb2'' & Hr3 & ACCO2 & ACCI2 & B); eauto.
        exists r3. exists (wb1'', wb2''). repeat split; eauto.
        econstructor; eauto.
      + intros (wb1' & wb2') (i2, i1) s1 s3 q1 Hs H.
        inv Hs.
        edestruct (@fsim_match_external lis)
          as (wa2 & q2 & Hq2 & ACC2 & Hq12 & HSE12 & Hk12); eauto.
        edestruct (@fsim_match_external lin)
          as (wa3 & q3 & Hq3 & ACC3 & Hq23 & HSE23 & Hk23); eauto.
        exists (se2, (wa2,wa3)), q3. repeat split; eauto. 
        * econstructor; eauto.
        * intros r1 r3 s1' (wpi & wpj) Hw (r2 & Hr12 & Hr23) HH. inv Hw. cbn in *.
          edestruct Hk12 as (i2' & s2' & Hs2' & Hm); eauto.
          edestruct Hk23 as (i1' & s3' & Hs3' & Hn); eauto.
          eexists (_, _), _. repeat split; eauto.
          econstructor; eauto.
      + intros s1 t s1' Hstep (wpi & wpj) (i2, i1) s3 Hs.
        inv Hs.
        edestruct (@fsim_simulation' lis) as (i1' & Hx); eauto.
        destruct Hx as [[s2' [A B]] | [A [B C]]].
        * (* L2 makes one or several steps. *)
          edestruct (@simulation_plus lin) as (i2'& Hx); eauto.
          destruct Hx as [[s3' [P Q]] | [P [Q R]]].
          -- (* L3 makes one or several steps *)
            exists (i2', i1'); exists s3'; split.
            left; eauto.
            econstructor; eauto.
          -- (* L3 makes no step *)
            exists (i2', i1'); exists s3; split.
            right; split. subst t; apply star_refl. red. left. auto.
            econstructor; eauto.
        * (* L2 makes no step *)
          exists (i2, i1'); exists s3; split.
          right; split. subst t; apply star_refl. red. right. auto.
          econstructor; eauto.
    - unfold ff_order.
      apply wf_lex_ord. apply Transitive_Closure.wf_clos_trans.
      eapply (fsim_order_wf H2). eapply (fsim_order_wf H1).
  Qed.

End COMP_FSIM.

Lemma st_fsim_vcomp
  `(cc1: callconv lis lin) `(cc2: callconv lin lif)
  (Ls: semantics lis lis) (Ln: semantics lin lin) (Lf: semantics lif lif):
  forward_simulation cc1 Ls Ln ->
  forward_simulation cc2 Ln Lf ->
  forward_simulation (cc_compose cc1 cc2) Ls Lf.
Proof.
  intros [X] [Y]. constructor. eapply st_fsim_vcomp'; eauto.
Qed.


(** ** Composing two backward simulations *)

Section COMPOSE_BACKWARD_SIMULATIONS.

Context {li1 li2 li3} {cc12: callconv li1 li2} {cc23: callconv li2 li3}.
Context {state1 state2 state3: Type}.
Variable L1: lts li1 li1 state1.
Variable L2: lts li2 li2 state2.
Variable L3: lts li3 li3 state3.
Context (se1 se2 se3: Genv.symtbl) (w12: ccworld cc12) (w23: ccworld cc23).
Context index order match_states (S12: bsim_properties cc12 se1 se2 w12 L1 L2 index order match_states).
Context index' order' match_states' (S23: bsim_properties cc23 se2 se3 w23 L2 L3 index' order' match_states').
Hypothesis L3_single_events: single_events L3.

Let bb_index : Type := (index * index')%type.

Definition bb_order : bb_index -> bb_index -> Prop := lex_ord (clos_trans _ order) order'.

Inductive bb_match_states:  gworld (cc_compose cc12 cc23) -> bb_index -> state1 -> state3 -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y wp12 wp23,
      match_states wp12 i1 s1 s2x -> Star L2 s2x E0 s2y -> match_states' wp23 i2 s2y s3 ->
      bb_match_states (wp12, wp23) (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2 wp12 wp23,
  match_states wp12 i1 s1 s2 -> match_states' wp23 i2 s2 s3 ->
  bb_match_states (wp12, wp23) (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2 gw12 gw23, match_states gw12 i1 s1 s2 -> match_states' gw23 i2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states (gw12, gw23) i' s1' s3'.
Proof.
  intros.
  exploit (bsim_simulation' S23); eauto. eapply bsim_safe; eauto.
  intros [ [i2' [s2' [PLUS2 MATCH2]]] | [i2' [ORD2 [EQ MATCH2]]]].
- (* 1 L2 makes one or several transitions *)
  assert (EITHER: t = E0 \/ (length t = 1)%nat).
  { exploit L3_single_events; eauto.
    destruct t; auto. destruct t; auto. simpl. intros. extlia. }
  destruct EITHER.
+ (* 1.1 these are silent transitions *)
  subst t. exploit (bsim_E0_plus S12); eauto.
  intros [ [i1' [s1' [PLUS1 MATCH1]]] | [i1' [ORD1 MATCH1]]].
* (* 1.1.1 L1 makes one or several transitions *)
  exists (i1', i2'); exists s1'; split. auto. eapply bb_match_at; eauto.
* (* 1.1.2 L1 makes no transitions *)
  exists (i1', i2'); exists s1; split.
  right; split. apply star_refl. left; auto.
  eapply bb_match_at; eauto.
+ (* 1.2 non-silent transitions *)
  exploit @star_non_E0_split. apply plus_star; eauto. auto.
  intros [s2x [s2y [P [Q R]]]].
  exploit (bsim_E0_star S12). eexact P. eauto. auto. intros [i1' [s1x [X Y]]].
  exploit (bsim_simulation' S12). eexact Q. eauto. eapply star_safe; eauto.
  intros [[i1'' [s1y [U V]]] | [i1'' [U [V W]]]]; try (subst t; discriminate).
  exists (i1'', i2'); exists s1y; split.
  left. eapply star_plus_trans; eauto. eapply bb_match_later; eauto.
- (* 2. L2 makes no transitions *)
  subst. exists (i1, i2'); exists s1; split.
  right; split. apply star_refl. right; auto.
  eapply bb_match_at; eauto.
Qed.

Lemma bb_simulation:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i s1, bb_match_states i s1 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' i))
    /\ bb_match_states i' s1' s3'.
Proof.
  intros. inv H0.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | PLUS].
- (* 1. match at *)
  subst. eapply bb_simulation_base; eauto.
- (* 2. match later *)
  exploit (bsim_E0_plus S12); eauto.
  intros [[i1' [s1' [A B]]] | [i1' [A B]]].
+ (* 2.1 one or several silent transitions *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto.
    eapply star_safe; eauto. eapply plus_star; eauto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  left. eapply plus_star_trans; eauto.
  destruct C as [P | [P Q]]. apply plus_star; eauto. eauto.
  traceEq.
+ (* 2.2 no silent transition *)
  exploit bb_simulation_base. eauto. auto. eexact B. eauto. auto.
  intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto.
  intuition. right; intuition.
  inv H6. left. eapply t_trans; eauto. left; auto.
Qed.

Lemma compose_bsim_match_cont:
  forall k1 k2 k3,
  bsim_match_cont (rex match_states) k1 k2 ->
  bsim_match_cont (rex match_states') k2 k3 ->
  bsim_match_cont (rex bb_match_states) k1 k3.
Proof.
  intros k1 k2 k3 [Hexist Hmatch] [Hexist' Hmatch'].
  split.
  - intros s1 Hs1. edestruct Hexist as [s2 Hs2]; eauto.
  - intros s1 s3 Hs1 Hs3.
    edestruct Hexist as (s2 & Hs2); eauto.
    edestruct Hmatch' as (s2' & Hs2' & i' & M2); eauto.
    edestruct Hmatch as (s1' & Hs1' & i & M1); eauto.
    exists s1'; intuition auto. exists (i, i'). eapply bb_match_at; eauto.
Qed.

End COMPOSE_BACKWARD_SIMULATIONS.

Lemma compose_backward_simulations:
  forall {liA1 liA2 liA3} {ccA12: callconv liA1 liA2} {ccA23: callconv liA2 liA3},
  forall {liB1 liB2 liB3} {ccB12: callconv liB1 liB2} {ccB23: callconv liB2 liB3},
  forall L1 L2 L3,
    backward_simulation ccA12 ccB12 L1 L2 ->
    backward_simulation ccA23 ccB23 L2 L3 ->
    (forall se3, single_events (L3 se3)) ->
    backward_simulation (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros until L3. intros [H12] [H23] H3.
  set (ms := fun se1 se3 '(se2, w12, w23) =>
               bb_match_states (L2 se2) (bsim_match_states H12 se1 se2 w12)
                                        (bsim_match_states H23 se2 se3 w23)).
  constructor.
  apply Backward_simulation with (bb_order (bsim_order H12) (bsim_order H23)) ms.
  - (* skel *)
    etransitivity; eapply bsim_skel; eauto.
  - (* LTS *)
    intros se1 se3 [[se2 wB12] wB23] [Hse12 Hse23] Hse1. cbn. clear ms.
    assert (Hse2: Genv.valid_for (skel L2) se2).
    { erewrite <- bsim_skel by eauto. eapply match_senv_valid_for; eauto. }
    destruct H12 as [index12 order12 ms12 Hsk12 Hlts12 Hwf12]; cbn.
    destruct H23 as [index23 order23 ms23 Hsk23 Hlts23 Hwf23]; cbn.
    specialize (Hlts12 se1 se2 wB12 Hse12 Hse1).
    specialize (Hlts23 se2 se3 wB23 Hse23 Hse2).
    split.
    + (* valid queries *)
      intros q1 q3 (q2 & Hq12 & Hq23).
      etransitivity; eapply bsim_match_valid_query; eauto.
    + (* initial states *)
      intros q1 q3 (q2 & Hq12 & Hq23).
      eauto using compose_bsim_match_cont, bsim_match_initial_states.
    + (* match final states *)
      intros i s1 s3 r MS SAFE FIN. inv MS.
      edestruct (bsim_match_final_states Hlts23) as (s2' & r2 & A & B & Hr23); eauto.
        eapply star_safe; eauto. eapply bsim_safe; eauto.
      edestruct (bsim_E0_star Hlts12) as (i1' & s1' & C & D).
        eapply star_trans. eexact H0. eexact A. auto. eauto. auto.
      edestruct (bsim_match_final_states Hlts12) as (s1'' & r1 & P & Q & Hr12); eauto.
        eapply star_safe; eauto.
      exists s1'', r1; cbn; split; eauto. eapply star_trans; eauto.
    + (* external states *)
      intros i s1 s3 q3 MS SAFE Hq3. destruct MS.
      edestruct (bsim_match_external Hlts23) as (w23 & s2' & q2 & Hs2' & Hq2 & Hq23 & Hse23' & Hk23); eauto.
        eapply star_safe; eauto. eapply bsim_safe; eauto.
      edestruct (bsim_E0_star Hlts12) as (i' & s1' & Hs1' & Hs12').
        eapply star_trans. eexact H0. eexact Hs2'. auto. eauto. auto.
      edestruct (bsim_match_external Hlts12) as (w12 & s1'' & q1 & Hs1'' & Hq1 & Hq12 & Hse12' & Hk12); eauto.
        eapply star_safe; eauto.
      exists (se2, w12, w23), s1'', q1. cbn. repeat apply conj; eauto using star_trans.
      intros r1 r3 (r2 & Hr12 & Hr23).
      eapply compose_bsim_match_cont; eauto.
    + (* progress *)
      intros i s1 s3 MS SAFE. inv MS.
      eapply (bsim_progress Hlts23). eauto. eapply star_safe; eauto. eapply bsim_safe; eauto.
    + (* simulation *)
      eapply bb_simulation; eauto.
  - (* well founded *)
    unfold bb_order. auto using wf_lex_ord, wf_clos_trans, bsim_order_wf.
Qed.
