Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep CallconvBig.
Require Import Linking.
Require Import Classical.
Require Import HCompBig.

Import GS.

Section BSIM.
  Context {li1 li2} (cc: callconv li1 li2).

  Notation I := bool.
  Context (L1 : I -> Smallstep.semantics li1 li1).
  Context (L2 : I -> Smallstep.semantics li2 li2).
  Context (HL : forall i, bsim_components cc (L1 i) (L2 i)).
  Context (se1 se2: Genv.symtbl) (w : ccworld cc).
  Context (Hse: match_senv cc w se1 se2).
  Context (Hse1: forall i, Genv.valid_for (skel (L1 i)) se1).
  Notation index := {i & bsim_index (HL i)}.

  Inductive match_topframes wk : GS.gworld cc -> index -> bool -> frame L1 -> frame L2 -> Prop :=
    match_topframes_intro gw i s1 s2 idx:
      match_senv cc wk se1 se2 ->
      Genv.valid_for (skel (L1 i)) se1 ->
      bsim_match_states (HL i) se1 se2 wk gw idx s1 s2 ->
      match_topframes wk gw
        (existT _ i idx) i
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_contframes wk wk': bool -> frame L1 -> frame L2 -> Prop :=
    match_contframes_intro i s1 s2:
      match_senv cc wk' se1 se2 ->
      (forall r1 r2 (gw': GS.gworld cc), (get wk) o-> gw' ->  match_reply cc (set wk gw') r1 r2 ->
        bsim_match_cont (rex (bsim_match_states (HL i) se1 se2 wk' gw'))
       (Smallstep.after_external (L1 i se1) s1 r1)
       (Smallstep.after_external (L2 i se2) s2 r2)) ->
      match_contframes wk wk' i
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_states: gworld cc -> index -> list (frame L1) -> list (frame L2) -> Prop :=
    | match_states_cons gw gw' wk idx f1 f2 k1 k2 i j:
      match_topframes wk gw' idx i f1 f2 ->
      gw *-> gw' ->
      match_cont wk j k1 k2 ->
      i <> j ->
      match_states gw idx (f1 :: k1) (f2 :: k2)
  with match_cont: ccworld cc -> bool -> _ -> _ -> Prop :=
    | match_cont_cons wk wk' f1 f2 k1 k2 i j:
        match_contframes wk wk' i f1 f2 ->
        match_cont wk' j k1 k2 ->
        i <> j ->
        match_cont wk i (f1 :: k1) (f2 :: k2)
    | match_cont_nil i:
        match_cont w i nil nil.

  Inductive order: index -> index -> Prop :=
    order_intro i x y: bsim_order (HL i) x y -> order (existT _ i x) (existT _ i y).

  (** semantics bsim_properties *)

  Lemma safe_internal : forall (i:I) s1 k1,
      safe L1 se1 (st L1 i s1 :: k1) -> Smallstep.safe (L1 i se1) s1.
  Proof.
    intros.
    red. intros.
    red in H. exploit H. eapply star_internal; eauto.
    intros [[r A] | [[q B] | [t [s2' C]]]].
    - inv A. subst_dep. left. eauto.
    - inv B. subst_dep. right. left. eauto.
    - inv C. subst_dep. right. right. eauto.
      subst_dep. right. left. eauto.
      subst_dep. left. eauto.
  Qed.

  Hypothesis determinate_L1: forall i, determinate_big (L1 i).
  
  Lemma step_simulation:
    forall gw idx s1 s2 t s2', match_states gw idx s1 s2 -> step L2 se2 s2 t s2' -> safe L1 se1 s1 ->
    exists idx' s1',
      (plus (fun _ => step L1 se1) tt s1 t s1' \/
       star (fun _ => step L1 se1) tt s1 t s1' /\ order idx' idx) /\
      match_states gw idx' s1' s2'.
  Proof.
    intros gw idx s1 s2 t s2' Hs Hs1' Hsafe.
    destruct Hs1'; inv Hs.
    - (* internal step *)
      remember (st L2 i s) as f2.
      inv H2. inv H11. subst_dep.
      (* inv H4; subst_dep. clear idx0. *)
      edestruct @bsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto using bsim_lts.
      eapply safe_internal; eauto.
      eexists (existT _ i idx'), _. split.
      * destruct Hs2'; [left | right]; intuition eauto using star_internal, plus_internal.
        constructor. auto.
      * econstructor; eauto. econstructor; eauto.
    - (* cross-component call *)
      remember (st L2 i s) as f2. inv H5. inv H14. subst_dep.
      edestruct @bsim_match_external as (wx & s1' & qx1 & Hsteps1 & Hqx1 & Haci & Hqx & Hsex & Hrx); eauto using bsim_lts.
      eapply safe_internal; eauto.
      pose proof (determinate_L1 i se1) as DETERMi1.
      exploit Hsafe; eauto. eapply star_internal; eauto. rename q into q2.
      intros [[r1' Final1] | [[q1 Ext1] | [t [s2' Step1]]]].
      + inv Final1. subst_dep. exfalso. eapply @sd_big_final_noext; eauto.
      + inv Ext1. subst_dep. exfalso. exploit @sd_big_at_external_determ. eauto.
        apply Hqx1. apply H13. intro. subst qx1.
        pose proof (bsim_lts (HL j) _ _ Hsex (Hse1 j)).
        erewrite bsim_match_valid_query in H0; eauto. congruence.
      + inv Step1; subst_dep.
        -- exfalso. eapply @sd_big_at_external_nostep; eauto.
        -- exploit @sd_big_at_external_determ. eauto.
           apply Hqx1. apply H12. intro. subst qx1.
           pose proof (bsim_lts (HL j1) _ _ Hsex (Hse1 j1)).
           exploit @bsim_match_initial_states; eauto.
           intros HrexI. inv HrexI.
           assert (j0 = j1).
           { destruct j0; destruct j1; destruct i; congruence. }
           subst j1. assert (j0 = j).
           { destruct j0; destruct j; destruct i; congruence. }
           subst j0.
           exploit bsim_match_cont_match; eauto.
           intros [s1j' [HIj1 [idx' Hmsj]]].
           eexists. eexists. split.
           left. eapply plus_right. eapply star_internal; eauto.
           eapply step_push; eauto. reflexivity.
           econstructor.
           econstructor; eauto. etransitivity; eauto.
           econstructor; eauto. econstructor; eauto. congruence.
        -- exfalso. eapply @sd_big_final_noext; eauto.
    - (* cross-component return *)
      remember (st L2 i s) as f2.
      inv H4. inv H13. subst_dep. clear idx0.
      pose proof (bsim_lts (HL i) _ _ H2 H3).
      apply safe_internal in Hsafe as Hsafei.
      edestruct @bsim_match_final_states as (s2' & r2 & gw'' & Hstar2 & Hr2 & Hace & Haci & Hr); eauto.
      remember (st L2 j sk :: k) as k2.
      inv H9; try congruence. inv H15.
      remember (st L2 j sk) as f2. inv H7. inv H15.
      subst_dep. specialize (H12 _ _ _ Hace Hr).
      inv H12.
      pose proof (determinate_L1 i se1) as DETERMi1.
      exploit Hsafe; eauto. eapply star_internal; eauto.
      intros [[r1' Final1] | [[q1 Ext1] | [t [s2'' Step1]]]].
      + inv Final1.
      + inv Ext1. subst_dep. exfalso. exploit @sd_big_final_noext; eauto.
      + inv Step1; subst_dep.
        -- exfalso. exploit @sd_big_final_nostep; eauto.
        -- exfalso. exploit @sd_big_final_noext; eauto.
        -- exploit @sd_big_final_determ. eauto. apply Hr2. apply H18. intro.
           subst r0.
           assert (j1 = i). {destruct j1; destruct i; destruct j; congruence. }
           subst j1.
           exploit bsim_match_cont_match. eauto. eauto.
           intros (s1j' & HY1j & idxj & Hmsj).
           eexists. eexists. split.
           left. eapply plus_right. eapply star_internal; eauto.
           eapply step_pop; eauto. reflexivity.
           econstructor. 2:{ etransitivity; eauto. } all: eauto.
           econstructor; eauto.
  Qed.
  (* bsim_properties *)

  Hypothesis valid_query_excl:
    forall i j se q,
      Smallstep.valid_query (L1 i se) q = true ->
      Smallstep.valid_query (L1 j se) q = true ->
      i = j.
  
  Lemma match_query_excl : forall q1 q2 i j,
      match_query cc w q1 q2 ->
      Smallstep.valid_query (L1 i se1) q1 = true ->
      Smallstep.valid_query (L2 j se2) q2 = true ->
      i = j.
  Proof.
    intros.  pose proof (bsim_lts (HL j) _ _ Hse (Hse1 j)).
    erewrite bsim_match_valid_query in H1; eauto.
  Qed.
    
  Lemma initial_states_simulation:
    forall q1 q2, match_query cc w q1 q2 ->
                bsim_match_cont (rex (match_states (get w))) (initial_state L1 se1 q1) (initial_state L2 se2 q2).
  Proof.
    intros q1 q2 Hq. constructor.
    - intros _ [i s1' Hq1 Hs1].
      pose proof (bsim_lts (HL i) _ _ Hse (Hse1 i)). inv H.
      exploit bsim_match_initial_states0; eauto. intro.
      inv H. exploit bsim_match_cont_exist; eauto. intros (s2 & Hi2).
      eexists. econstructor; eauto.
    - intros sl1 sl2 [i s1' Hq1 Hs1] [j s2' Hq2 Hs2].
      exploit match_query_excl; eauto. intro. subst j.
      pose proof (bsim_lts (HL i) _ _ Hse (Hse1 i)). inv H.
      exploit bsim_match_initial_states0; eauto. intro.
      inv H. exploit bsim_match_cont_match; eauto. intros (s1'' & Hi1' & Hrex).
      eexists. split. econstructor; eauto. inv Hrex.
      eexists. econstructor; eauto. econstructor; eauto. reflexivity.
      instantiate (1:= negb i).
      constructor. destruct i; simpl; congruence.
  Qed.

  Lemma final_states_simulation:
    forall gw idx s1 s2 r2,
      match_states gw idx s1 s2 ->
      safe L1 se1 s1 ->
      final_state L2 se2 s2 r2 ->
      exists s1' r1 gw', star (fun _ => step L1 se1) tt s1 E0 s1' /\
                  final_state L1 se1 s1' r1 /\ (get w) o-> gw' /\ gw *-> gw' /\ match_reply cc (set w gw') r1 r2.
  Proof.
    clear. intros gw idx s1 s2 r2 Hs Hsafe Hr2. destruct Hr2 as [i s2 r2 Hr2].
    inv Hs. inv H6. remember (st L2 i s2) as f2. inv H1. inv H9. subst_dep.
    pose proof (bsim_lts (HL i) _ _ H H0).
    edestruct @bsim_match_final_states as (s1' & r1 & gw'' & Hstar & Hr1 & Hace & Haci & Hr); eauto.
    eapply safe_internal; eauto.
    eexists. exists r1. exists gw''. split. eapply star_internal; eauto.
    split. constructor; eauto. split; eauto. split; eauto. etransitivity; eauto.
  Qed.
  
  Lemma external_simulation:
    forall gw idx s1 s2 qx2, match_states gw idx s1 s2 -> safe L1 se1 s1 -> at_external L2 se2 s2 qx2 ->
    exists wx s1' qx1, star (fun _ => step L1 se1) tt s1 E0 s1' /\ at_external L1 se1 s1' qx1 /\ gw *-> (get wx) /\ match_query cc wx qx1 qx2 /\ match_senv cc wx se1 se2 /\
    forall rx1 rx2 gw'', (get wx) o-> gw'' -> match_reply cc (set wx gw'') rx1 rx2 -> bsim_match_cont (rex (match_states gw'')) (after_external L1 se1 s1' rx1)
                                             (after_external L2 se2 s2 rx2).
  Proof.
    clear - HL Hse1.
    intros gw idx s1 s2 q2 Hs Hsafe Hq2. destruct Hq2 as [i s2 qx2 k2 Hqx2 Hvld].
    inv Hs. remember (st L2 i s2) as f2. inv H1. inv H10. subst_dep.
    pose proof (bsim_lts (HL i) _ _ H H0) as Hi.
    edestruct @bsim_match_external as (wx & s1' & qx1 & Hstar & Hqx1 & Haci & Hqx & Hsex & Hr); eauto.
    eapply safe_internal; eauto.
    exists wx. eexists. exists qx1. intuition idtac.
    + eapply star_internal; eauto.
    + constructor. eauto.
      intros j0. pose proof (bsim_lts (HL j0) _ _ Hsex (Hse1 j0)).
      erewrite <- bsim_match_valid_query; eauto.
    + etransitivity; eauto.
    + exploit Hr; eauto. intros. inv H5.
      constructor.
      -- intros s1'' Hy1. inv Hy1. subst_dep.
         exploit @bsim_match_cont_exist; eauto.
         intros (s2'' & Hy2). eexists. econstructor; eauto.
      -- intros s1'' s2'' Hy1 Hy2. inv Hy1. inv Hy2. subst_dep.
         exploit @bsim_match_cont_match; eauto.
         intros (s1'''  & Hy1' & Hrex).
         eexists. split. econstructor; eauto. inv Hrex. eexists.
         econstructor; eauto. 2: reflexivity. constructor; eauto.
  Qed.

  Lemma progress_simulation :
    forall gw idx s1 s2, match_states gw idx s1 s2 -> safe L1 se1 s1 ->
                  (exists r, final_state L2 se2 s2 r) \/
                  (exists q, at_external L2 se2 s2 q) \/
                    (exists t s2', step L2 se2 s2 t s2').
  Proof.
    intros. inv H. inv H1. subst_dep.
    assert (SAFE_L1i: Smallstep.safe (L1 i se1) s1).
    eapply safe_internal; eauto.
    pose proof (bsim_lts (HL i) _ _ H (Hse1 i)).
    exploit @bsim_progress; eauto.
    pose proof (determinate_L1 i se1).
    intros [[r Final2i] | [[q Ext2i] | [t [s2' Step2i]]]].
    - (** the top target semantics L2 i enters a final state *)
      exploit @bsim_match_final_states; eauto.
      intros (s1' & r1 & gw'' & Star1 & Final1i & He & Hi & MR).
      (** the top source semantics L1 i also finals by bsim*)
      exploit H0. eapply star_internal; eauto.
      intros [[r1' Final1] | [[q Ext1] | [t [s2' Step1]]]].
      + (** the source semantics finals, i.e. with empty state stack *)
        inv Final1. subst_dep. left. inv H3. econstructor; eauto.
        econstructor; eauto.
      + inv Ext1. subst_dep.
        exfalso.
        exploit @sd_big_final_noext; eauto.
      + inv Step1. subst_dep.
        -- exfalso. exploit @sd_big_final_nostep; eauto.
        -- subst_dep. exfalso. exploit @sd_big_final_noext; eauto.
        -- subst_dep. inv H3.
           assert (j1 = i).
           { destruct j; destruct j1; destruct i; congruence. }
           subst j1.
           assert (j0 = j).
           { destruct j; destruct j0; destruct i; congruence. }
           subst j0.
           right. right.
           exploit @sd_big_final_determ. eauto. apply Final1i. apply H11. intro. subst r0.
           inv H10. subst_dep.
           exploit H12; eauto. intro. inv H3.
           exploit bsim_match_cont_exist; eauto.
           intros [s2' AFTER2j].
           eexists. eexists.
           eapply step_pop; eauto.
    - (** the top target semantics L2 i [at_external]s *)
      exploit @bsim_match_external; eauto. rename q into q2.
      intros (wA & s1' & q1 & HStar & X1i & ACI & MQ & MS & MR).
      exploit H0; eauto. eapply star_internal; eauto.
      intros [[r1' Final1] | [[q Ext1] | [t [s2' Step1]]]].
      + (** the source semantics finals, i.e. with empty state stack *)
        inv Final1. subst_dep. exfalso. eapply @sd_big_final_noext; eauto.
      + inv Ext1. subst_dep. right. left.
        exploit @sd_big_at_external_determ. eauto. apply X1i. apply H12. intro.
        subst q. exists q2. econstructor; eauto.
        intros j0. pose proof (bsim_lts (HL j0) _ _ MS (Hse1 j0)).
        erewrite bsim_match_valid_query; eauto.
      + inv Step1. subst_dep.
        -- exfalso. exploit @sd_big_at_external_nostep; eauto.
        -- subst_dep. right. right.
           exploit @sd_big_at_external_determ. eauto. apply X1i. apply H11.
           intro. subst q.
           pose proof (bsim_lts (HL j0) _ _ MS (Hse1 j0)).
           exploit @bsim_match_initial_states. apply H8. eauto.
           intro Hrexj0. inv Hrexj0. exploit bsim_match_cont_exist; eauto.
           intros [s2' I2j0]. do 2 eexists.
           eapply step_push. eauto. 
           erewrite bsim_match_valid_query; eauto. eauto. eauto.
        -- subst_dep. exfalso. eapply @sd_big_final_noext; eauto.
    - right. right. do 2 eexists. econstructor; eauto.
  Qed.

  Lemma semantics_simulation sk1 sk2:
    bsim_properties cc se1 se2 w
      (semantics L1 sk1 se1)
      (semantics L2 sk2 se2)
      index order match_states.
  Proof.
    split; cbn.
    - intros. unfold valid_query. f_equal.
      + eapply (bsim_lts (HL true)); eauto.
      + eapply (bsim_lts (HL false)); eauto.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using progress_simulation.
    - eauto using step_simulation.
  Qed.
  
End BSIM.

(** * Linking operator *)

Lemma compose_simulation {li1 li2} (cc: callconv li1 li2) L1a L1b L1 L2a L2b L2:
  backward_simulation cc L1a L2a ->
  backward_simulation cc L1b L2b ->
  determinate_big L1a -> determinate_big L1b ->
  (forall q se, ~ ((Smallstep.valid_query (L1a se)) q = true /\ Smallstep.valid_query (L1b se) q = true)) ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  backward_simulation cc L1 L2.
Proof.
  intros [Ha] [Hb] Hd1 Hd2 Hqex H1 H2. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  set (L1 := fun i:bool => if i then L1a else L1b).
  set (L2 := fun i:bool => if i then L2a else L2b).
  assert (HL: forall i, bsim_components cc (L1 i) (L2 i)) by (intros [|]; auto).
  constructor.
  eapply Backward_simulation with (order cc L1 L2 HL) (match_states cc L1 L2 HL).
  - destruct Ha, Hb. cbn. congruence.
  - intros se1 se2 w Hse Hse1.
    eapply semantics_simulation; eauto.
    + pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
      intros [|]; cbn; eapply Genv.valid_for_linkorder; eauto.
      (** preconditions introduced above *)
    + intros. destruct i; eauto.
    + intros. destruct i; destruct j; simpl in *; eauto; exfalso; eapply Hqex; eauto.        
  - clear - HL. intros [i x].
    induction (bsim_order_wf (HL i) x) as [x Hx IHx].
    constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
Qed.
