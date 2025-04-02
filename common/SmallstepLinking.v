Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
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
          i <> j ->
          step (st i s :: k) E0 (st j s' :: st i s :: k)
      | step_pop i j s sk r s' k :
          Smallstep.final_state (L i se) s r ->
          Smallstep.after_external (L j se) sk r s' ->
          i <> j ->
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

  End WITH_SE.

  Context (sk: AST.program unit unit).

  Definition semantics: semantics li li :=
    {|
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

   Definition safe se s : Prop :=
    forall s',
    star (fun _ => step se) tt s E0 s' ->
    (exists r, final_state se s' r)
    \/ (exists q, at_external se s' q)
    \/ (exists t, exists s'', step se s' t s'').

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

    
  Lemma semantics_determinate_big :
    (forall i, determinate_big (L i)) ->
    determinate_big semantics.
  Proof.
    intros HL se. unfold determinate_big in HL.
    constructor; cbn.
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

  Hypothesis valid_query_excl:
    forall i j se q,
      Smallstep.valid_query (L i se) q = true ->
      Smallstep.valid_query (L j se) q = true ->
      i = j.

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


(** * Linking operator *)

Local Unset Program Cases.

Definition compose {li} (La Lb: Smallstep.semantics li li) :=
  let L i := match i with true => La | false => Lb end in
  option_map (semantics L) (link (skel La) (skel Lb)).


Lemma compose_determinate_big {li}: forall (L1 L2 L: Smallstep.semantics li li),
    compose L1 L2 = Some L ->
    determinate_big L1 ->
    determinate_big L2 ->
    determinate_big L.
Proof.
  intros. unfold compose in H.
  unfold option_map in H. destr_in H.
  inv H. eapply semantics_determinate_big; eauto.
  intros. destr.
Qed.
