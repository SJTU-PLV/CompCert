Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep CallconvBig.
Require Import Linking.
Require Import Classical.

Ltac subst_dep :=
  subst;
  lazymatch goal with
    | H: existT ?P ?x _ = existT ?P ?x _ |- _ =>
      apply inj_pair2 in H; subst_dep
    | _ =>
      idtac
  end.

Section LINK.
  Context {li} (L: bool -> semantics li li).
  Let I := bool.

  (** * Definition *)

  Section WITH_SE.
    Context (se: Genv.symtbl).

    Variant frame := st (i: I) (s: Smallstep.state (L i)).
    Notation state := (list frame).

    Inductive step: state -> trace -> state -> Prop :=
      | step_internal i s t s' k :
          Step (L i se) s t s' ->
          step (st i s :: k) t (st i s' :: k)
      | step_push i j s q s' k :
          Smallstep.at_external (L i se) s q ->
          valid_query (L j se) q = true ->
          Smallstep.initial_state (L j se) q s' ->
          step (st i s :: k) E0 (st j s' :: st i s :: k)
      | step_pop i j s sk r s' k :
          Smallstep.final_state (L i se) s r ->
          Smallstep.after_external (L j se) sk r s' ->
          step (st i s :: st j sk :: k) E0 (st j s' :: k).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro i s :
          valid_query (L i se) q = true ->
          Smallstep.initial_state (L i se) q s ->
          initial_state q (st i s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro i s q k:
          Smallstep.at_external (L i se) s q ->
          (forall j, valid_query (L j se) q = false) ->
          at_external (st i s :: k) q.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro i s r s' k:
          Smallstep.after_external (L i se) s r s' ->
          after_external (st i s :: k) r (st i s' :: k).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro i s r :
          Smallstep.final_state (L i se) s r ->
          final_state (st i s :: nil) r.

    Definition valid_query q :=
      valid_query (L true se) q || valid_query (L false se) q.

    (* Definition memory_of_state (s: state) : mem :=
      match s with
      |nil => Mem.empty
      |(st i ss) :: _ => (memory_of_state (L i)) ss
      end. *)
    
  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics: semantics li li :=
    {|
      (* Smallstep.memory_of_state := memory_of_state; *)
      activate se :=
        {|
          Smallstep.step ge := step se;
          Smallstep.valid_query := valid_query se;
          Smallstep.initial_state := initial_state se;
          Smallstep.at_external := at_external se;
          Smallstep.after_external := after_external se;
          Smallstep.final_state := final_state se;
          Smallstep.globalenv := tt;
        |};
      skel := sk;
    |}.

  (** * Properties *)

  Lemma star_internal se i s t s' k:
    Star (L i se) s t s' ->
    star (fun _ => step se) tt (st i s :: k) t (st i s' :: k).
  Proof.
    induction 1; [eapply star_refl | eapply star_step]; eauto.
    constructor; auto.
  Qed.

  Lemma plus_internal se i s t s' k:
    Plus (L i se) s t s' ->
    plus (fun _ => step se) tt (st i s :: k) t (st i s' :: k).
  Proof.
    destruct 1; econstructor; eauto using step_internal, star_internal.
  Qed.

  (** * Receptiveness and determinacy *)

      
  Lemma semantics_receptive:
    (forall i, receptive (L i)) ->
    receptive semantics.
  Proof.
    intros HL se. unfold receptive in HL.
    constructor; cbn.
    - intros s t1 s1 t2 STEP Ht. destruct STEP.
      + edestruct @sr_receptive; eauto. eexists. eapply step_internal; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_push; eauto.
      + inversion Ht; clear Ht; subst. eexists. eapply step_pop; eauto.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sr_traces; eauto.
  Qed.

  Hypothesis valid_query_excl:
    forall i j se q,
      Smallstep.valid_query (L i se) q = true ->
      Smallstep.valid_query (L j se) q = true ->
      i = j.
    
  Lemma semantics_determinate_big :
    (forall i, determinate_big (L i)) ->
    determinate_big semantics.
  Proof.
     intros HL se. unfold determinate_big in HL.
    constructor; cbn.
    - destruct 1; inversion 1; subst. assert (i0 = i) by eauto; subst.
      edestruct (sd_big_initial_determ (HL i se) q s s0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_big_at_external_nostep; eauto.
      + edestruct (sd_big_at_external_determ (HL i se) s q q0); eauto.
        specialize (H0 j). congruence.
      + eapply sd_big_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_big_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_big_after_external_determ (HL i se) s r s' s'0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_big_final_nostep; eauto.
      + eapply sd_big_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_big_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_big_final_determ; eauto.
  Qed.


  Lemma semantics_determinate:
    (forall i, determinate (L i)) ->
    determinate semantics.
  Proof.
    intros HL se. unfold determinate in HL.
    constructor; cbn.
    - destruct 1; inversion 1; subst_dep.
      + edestruct (sd_determ (HL i se) s t s' t2 s'0); intuition eauto; congruence.
      + eelim sd_at_external_nostep; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_at_external_nostep; eauto.
      + destruct (sd_at_external_determ (HL i se) s q q0); eauto.
        assert (j0 = j) by eauto; subst.
        destruct (sd_initial_determ (HL j se) q s' s'0); eauto.
        intuition auto. constructor.
      + eelim sd_final_noext; eauto.
      + eelim sd_final_nostep; eauto.
      + eelim sd_final_noext; eauto.
      + edestruct (sd_final_determ (HL i se) s r r0); eauto.
        edestruct (sd_after_external_determ (HL j se) sk0 r s' s'0); eauto.
        intuition auto. constructor.
    - intros s t s' STEP. destruct STEP; cbn; eauto.
      eapply sd_traces; eauto.
    - destruct 1; inversion 1; subst. assert (i0 = i) by eauto; subst.
      edestruct (sd_initial_determ (HL i se) q s s0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_at_external_nostep; eauto.
      + edestruct (sd_at_external_determ (HL i se) s q q0); eauto.
        specialize (H0 j). congruence.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_at_external_determ; eauto.
    - destruct 1. inversion 1; subst_dep.
      edestruct (sd_after_external_determ (HL i se) s r s' s'0); eauto.
    - destruct 1. inversion 1; subst_dep.
      + eapply sd_final_nostep; eauto.
      + eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_noext; eauto.
    - destruct 1. inversion 1; subst_dep.
      eapply sd_final_determ; eauto.
  Qed.

End LINK.

(** * Compatibility with forward simulations *)

(** ** Simulation relation *)

Section FSIM.
  Context {li1 li2} (cc: GS.callconv li1 li2).

  Notation I := bool.
  Context (L1 : I -> Smallstep.semantics li1 li1).
  Context (L2 : I -> Smallstep.semantics li2 li2).
  Context (HL : forall i, GS.fsim_components cc (L1 i) (L2 i)).
  Context (se1 se2: Genv.symtbl) (w : GS.ccworld cc).
  Context (Hse: GS.match_senv cc w se1 se2).
  Context (Hse1: forall i, Genv.valid_for (skel (L1 i)) se1).
  Notation index := {i & GS.fsim_index (HL i)}.
  
  Inductive match_topframes wk: GS.gworld cc -> index -> frame L1 -> frame L2 -> Prop :=
    match_topframes_intro gw i s1 s2 idx:
      GS.match_senv cc wk se1 se2 ->
      Genv.valid_for (skel (L1 i)) se1 -> 
      GS.fsim_match_states (HL i) se1 se2 wk gw idx s1 s2 -> 
      match_topframes wk gw
        (existT _ i idx)
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_contframes wk wk': frame L1 -> frame L2 -> Prop :=
    match_contframes_intro i s1 s2:
      GS.match_senv cc wk' se1 se2 ->
      (forall r1 r2 s1' gw', (get wk) o-> gw' /\ GS.match_reply cc (set wk gw') r1 r2 ->
       Smallstep.after_external (L1 i se1) s1 r1 s1' ->
       exists idx s2',
         Smallstep.after_external (L2 i se2) s2 r2 s2' /\
         GS.fsim_match_states (HL i) se1 se2 wk' gw' idx s1' s2') ->
      match_contframes wk wk' 
        (st L1 i s1)
        (st L2 i s2).

  Inductive match_states: GS.gworld cc -> index -> list (frame L1) -> list (frame L2) -> Prop :=
    | match_states_cons gw gw' wk idx f1 f2 k1 k2:
      match_topframes wk gw' idx f1 f2 ->
      gw *-> gw' ->
      match_cont wk k1 k2 ->
      match_states gw idx (f1 :: k1) (f2 :: k2)
  with match_cont: GS.ccworld cc -> _ -> _ -> Prop :=
    | match_cont_cons wk wk' f1 f2 k1 k2:
        match_contframes wk wk' f1 f2 ->
        match_cont wk' k1 k2 ->
        match_cont wk (f1 :: k1) (f2 :: k2)
    | match_cont_nil:
        match_cont w nil nil.

  Inductive order: index -> index -> Prop :=
    order_intro i x y: GS.fsim_order (HL i) x y -> order (existT _ i x) (existT _ i y).

  (** ** Simulation properties *)

  Lemma step_simulation:
    forall gw idx s1 s2 t s1', match_states gw idx s1 s2 -> step L1 se1 s1 t s1' ->
    exists idx' s2',
      (plus (fun _ => step L2 se2) tt s2 t s2' \/
       star (fun _ => step L2 se2) tt s2 t s2' /\ order idx' idx) /\
       match_states gw idx' s1' s2'.
  Proof.
    intros gw idx s1 s2 t s1' Hs Hs1'.
    destruct Hs1'; inv Hs.
    - (* internal step *)
      inv H2; subst_dep. clear idx0.
      edestruct @GS.fsim_simulation as (idx' & s2' & Hs2' & Hs'); eauto using GS.fsim_lts.
      eexists (existT _ i idx'), _. split.
      * destruct Hs2'; [left | right]; intuition eauto using star_internal, plus_internal.
        constructor. auto.
      * econstructor; eauto.
        econstructor; eauto. 
    - (* cross-component call *)
      inv H4; subst_dep. clear idx0.
      edestruct @GS.fsim_match_external as (wx & qx2 & Hqx2 & ACC & Hqx & Hsex & Hrx); eauto using GS.fsim_lts.
      pose proof (GS.fsim_lts (HL j) _ _ Hsex (Hse1 j)).
      edestruct @GS.fsim_match_initial_states as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_push; eauto 1.
        erewrite GS.fsim_match_valid_query; eauto.
      + econstructor. 2: instantiate (1:= get wx).
        -- econstructor; eauto.
        -- etransitivity; eauto.
        -- econstructor; eauto.
           econstructor; eauto.
           intros r1 r2 s1' gw'' [ACC1 MR] AF.
           exploit Hrx; eauto.
    - (* cross-component return *)
      inv H3; subst_dep. clear idx0.
      pose proof (GS.fsim_lts (HL i) _ _ H4 H9).
      edestruct @GS.fsim_match_final_states as (r2 & gwf & Hr2 & ACCIF & ACCO & Hr); eauto.
      inv H8. inv H7; subst_dep.
      edestruct H10 as (idx' & s2' & Hs2' & Hs'); eauto.
      eexists (existT _ j idx'), _. split.
      + left. apply plus_one. eapply step_pop; eauto.
      + econstructor. 2: instantiate (1:= gwf).
        repeat (econstructor; eauto). etransitivity; eauto. eauto.
  Qed.

  Lemma initial_states_simulation:
    forall q1 q2 s1, GS.match_query cc w q1 q2 -> initial_state L1 se1 q1 s1 ->
    exists idx s2, initial_state L2 se2 q2 s2 /\ match_states (get w) idx s1 s2.
  Proof.
    intros q1 q2 _ Hq [i s1 Hq1 Hs1].
    pose proof (GS.fsim_lts (HL i) _ _ Hse (Hse1 i)).
    edestruct @GS.fsim_match_initial_states as (idx & s2 & Hs2 & Hs); eauto.
    exists (existT _ i idx), (st L2 i s2 :: nil).
    split; econstructor; eauto.
    + erewrite GS.fsim_match_valid_query; eauto.
    + econstructor; eauto.
    + reflexivity.
    + constructor.
  Qed.

  Lemma final_states_simulation:
    forall wp idx s1 s2 r1, match_states wp idx s1 s2 -> final_state L1 se1 s1 r1 ->
    exists r2 wp', final_state L2 se2 s2 r2 /\ (get w) o-> wp' /\ wp *-> wp' /\ GS.match_reply cc (set w wp') r1 r2.
  Proof.
    clear. intros wp idx s1 s2 r1 Hs Hr1. destruct Hr1 as [i s1 r1 Hr1].
    inv Hs. inv H6. inv H1. subst_dep. clear idx0.
    pose proof (GS.fsim_lts (HL i) _ _ H2 H6).
    edestruct @GS.fsim_match_final_states as (r2 & wp' & Hr2 & ACCIF & ACCI & Hr); eauto.
    exists r2, wp'. intuition auto. constructor; eauto. etransitivity; eauto. 
  Qed.

  Lemma external_simulation:
    forall wp idx s1 s2 qx1, match_states wp idx s1 s2 -> at_external L1 se1 s1 qx1 ->
    exists wx qx2, at_external L2 se2 s2 qx2 /\ wp *-> (get wx) /\ GS.match_query cc wx qx1 qx2 /\ GS.match_senv cc wx se1 se2 /\
    forall rx1 rx2 s1' wp'', (get wx) o-> wp'' -> GS.match_reply cc (set wx wp'') rx1 rx2 -> after_external L1 se1 s1 rx1 s1' ->
    exists idx' s2', after_external L2 se2 s2 rx2 s2' /\ match_states wp'' idx' s1' s2'.
  Proof.
    clear - HL Hse1.
    intros wp idx s1 s2 q1 Hs Hq1. destruct Hq1 as [i s1 qx1 k1 Hqx1 Hvld].
    inv Hs. inv H1. subst_dep. clear idx0.
    pose proof (GS.fsim_lts (HL i) _ _ H2 H7) as Hi.
    edestruct @GS.fsim_match_external as (wx & qx2 & Hqx2 & ACC & Hqx & Hsex & H); eauto.
    exists wx, qx2. intuition idtac.
    + constructor. eauto.
      intros j. pose proof (GS.fsim_lts (HL j) _ _ Hsex (Hse1 j)).
      erewrite GS.fsim_match_valid_query; eauto.
    + etransitivity; eauto.
    + inv H3; subst_dep.
      edestruct H as (idx' & s2' & Hs2' & Hs); eauto.
      eexists (existT _ i idx'), _.
      split; repeat (econstructor; eauto). reflexivity.
  Qed.

  Lemma semantics_simulation sk1 sk2:
    GS.fsim_properties cc  se1 se2 w
      (semantics L1 sk1 se1)
      (semantics L2 sk2 se2)
      index order match_states.
  Proof.
    split; cbn.
    - intros. unfold valid_query. f_equal.
      + eapply (GS.fsim_lts (HL true)); eauto.
      + eapply (GS.fsim_lts (HL false)); eauto.
    - eauto using initial_states_simulation.
    - eauto using final_states_simulation.
    - eauto using external_simulation.
    - eauto using step_simulation.
  Qed.
End FSIM.

(** * Linking operator *)

Local Unset Program Cases.

Definition compose {li} (La Lb: Smallstep.semantics li li) :=
  let L i := match i with true => La | false => Lb end in
  option_map (semantics L) (link (skel La) (skel Lb)).

Lemma compose_simulation {li1 li2} (cc: GS.callconv li1 li2) L1a L1b L1 L2a L2b L2:
  GS.forward_simulation cc L1a L2a ->
  GS.forward_simulation cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  GS.forward_simulation cc L1 L2.
Proof.
  intros [Ha] [Hb] H1 H2. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1a) (skel L1b)) as [sk1|] eqn:Hsk1; try discriminate. inv H1.
  destruct (link (skel L2a) (skel L2b)) as [sk2|] eqn:Hsk2; try discriminate. inv H2.
  set (L1 := fun i:bool => if i then L1a else L1b).
  set (L2 := fun i:bool => if i then L2a else L2b).
  assert (HL: forall i, GS.fsim_components cc (L1 i) (L2 i)) by (intros [|]; auto).
  constructor.
  eapply GS.Forward_simulation with (order cc L1 L2 HL) (match_states cc L1 L2 HL).
  - destruct Ha, Hb. cbn. congruence.
  - intros se1 se2 w Hse Hse1.
    eapply semantics_simulation; eauto.
    pose proof (link_linkorder _ _ _ Hsk1) as [Hsk1a Hsk1b].
    intros [|]; cbn; eapply Genv.valid_for_linkorder; eauto.
  - clear - HL. intros [i x].
    induction (GS.fsim_order_wf (HL i) x) as [x Hx IHx].
    constructor. intros z Hxz. inv Hxz; subst_dep. eauto.
Qed.
