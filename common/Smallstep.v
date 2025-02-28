(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable genv: Type.
Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: genv -> state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (ge: genv) (s: state) : Prop :=
  forall t s', ~(step ge s t s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star (ge: genv): state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star ge s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      star ge s1 t s3.

Lemma star_one:
  forall ge s1 t s2, step ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. traceEq.
Qed.

Lemma star_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.
Qed.

Lemma star_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star ge s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star ge s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto.
Qed.

Lemma star_trans:
  forall ge s1 t1 s2, star ge s1 t1 s2 ->
  forall t2 s3 t, star ge s2 t2 s3 -> t = t1 ** t2 -> star ge s1 t s3.
Proof.
  induction 1; intros.
  rewrite H0. simpl. auto.
  eapply star_step; eauto. traceEq.
Qed.

Lemma star_left:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof star_step.

Lemma star_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  star ge s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

Lemma star_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s, P s s) ->
  (forall s1 s2 s3, step ge s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star ge s1 E0 s2 -> P s1 s2.
Proof.
  intros ge P BASE REC.
  assert (forall s1 t s2, star ge s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
  eauto.
Qed.

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus (ge: genv): state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 ->
      plus ge s1 t s3.

Lemma plus_one:
  forall ge s1 t s2,
  step ge s1 t s2 -> plus ge s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. traceEq.
Qed.

Lemma plus_two:
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.
Qed.

Lemma plus_three:
  forall ge s1 t1 s2 t2 s3 t3 s4 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 -> step ge s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus ge s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto.
Qed.

Lemma plus_four:
  forall ge s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step ge s1 t1 s2 -> step ge s2 t2 s3 ->
  step ge s3 t3 s4 -> step ge s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus ge s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto.
Qed.

Lemma plus_star:
  forall ge s1 t s2, plus ge s1 t s2 -> star ge s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto.
Qed.

Lemma plus_right:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  rewrite Eapp_assoc. eapply plus_left; eauto.
  eapply star_right; eauto.
Qed.

Lemma plus_left':
  forall ge s1 t1 s2 t2 s3 t,
  step ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> step ge s2 t2 s3 -> t = t1 ** t2 ->
  plus ge s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> star ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  econstructor; eauto. eapply star_trans; eauto.
  traceEq.
Qed.

Lemma star_plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  star ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  rewrite Eapp_assoc.
  econstructor. eauto. eapply star_trans. eauto.
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall ge s1 t1 s2 t2 s3 t,
  plus ge s1 t1 s2 -> plus ge s2 t2 s3 -> t = t1 ** t2 -> plus ge s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall ge s1 t s2,
  plus ge s1 t s2 ->
  step ge s1 t s2 \/ exists s', exists t1, exists t2, step ge s1 t1 s' /\ plus ge s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall ge s1 t s2,
  star ge s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus ge s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall ge (P: state -> trace -> state -> Prop),
  (forall s1 t s2, step ge s1 t s2 -> P s1 t s2) ->
  (forall s1 t1 s2 t2 s3 t,
   step ge s1 t1 s2 -> plus ge s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
   P s1 t s3) ->
  forall s1 t s2, plus ge s1 t s2 -> P s1 t s2.
Proof.
  intros ge P BASE IND.
  assert (forall s1 t s2, star ge s1 t s2 ->
         forall s0 t0, step ge s0 t0 s1 ->
         P s0 (t0 ** t) s2).
  induction 1; intros.
  rewrite E0_right. apply BASE; auto.
  eapply IND. eauto. econstructor; eauto. subst t. eapply IHstar; eauto. auto.

  intros. inv H0. eauto.
Qed.

Lemma plus_E0_ind:
  forall ge (P: state -> state -> Prop),
  (forall s1 s2 s3, step ge s1 E0 s2 -> star ge s2 E0 s3 -> P s1 s3) ->
  forall s1 s2, plus ge s1 E0 s2 -> P s1 s2.
Proof.
  intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
Qed.

(** Counted sequences of transitions *)

Inductive starN (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s E0 s
  | starN_step: forall n s t t1 s' t2 s'',
      step ge s t1 s' -> starN ge n s' t2 s'' -> t = t1 ** t2 ->
      starN ge (S n) s t s''.

Remark starN_star:
  forall ge n s t s', starN ge n s t s' -> star ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN:
  forall ge s t s', star ge s t s' -> exists n, starN ge n s t s'.
Proof.
  induction 1.
  exists O; constructor.
  destruct IHstar as [n P]. exists (S n); econstructor; eauto.
Qed.

(** Infinitely many transitions *)

CoInductive forever (ge: genv): state -> traceinf -> Prop :=
  | forever_intro: forall s1 t s2 T,
      step ge s1 t s2 -> forever ge s2 T ->
      forever ge s1 (t *** T).

Lemma star_forever:
  forall ge s1 t s2, star ge s1 t s2 ->
  forall T, forever ge s2 T ->
  forever ge s1 (t *** T).
Proof.
  induction 1; intros. simpl. auto.
  subst t. rewrite Eappinf_assoc.
  econstructor; eauto.
Qed.

(** An alternate, equivalent definition of [forever] that is useful
    for coinductive reasoning. *)

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> traceinf -> Prop :=
  | forever_N_star: forall s1 t s2 a1 a2 T1 T2,
      star ge s1 t s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1
  | forever_N_plus: forall s1 t s2 a1 a2 T1 T2,
      plus ge s1 t s2 ->
      forever_N ge a2 s2 T2 ->
      T1 = t *** T2 ->
      forever_N ge a1 s1 T1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv:
  forall ge a s T,
  forever_N ge a s T ->
  exists t, exists s', exists a', exists T',
  step ge s t s' /\ forever_N ge a' s' T' /\ T = t *** T'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  change (E0 *** T2) with T2. apply H with a2. auto. auto.
  (* at least one transition *)
  exists t1; exists s0; exists x; exists (t2 *** T2).
  split. auto. split. eapply forever_N_star; eauto.
  apply Eappinf_assoc.
  (* plus case *)
  inv H1.
  exists t1; exists s0; exists a2; exists (t2 *** T2).
  split. auto.
  split. inv H3. auto.
  eapply forever_N_plus. econstructor; eauto. eauto. auto.
  apply Eappinf_assoc.
Qed.

Lemma forever_N_forever:
  forall ge a s T, forever_N ge a s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_N_inv H) as [t [s' [a' [T' [P [Q R]]]]]].
  rewrite R. apply forever_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Yet another alternative definition of [forever]. *)

CoInductive forever_plus (ge: genv) : state -> traceinf -> Prop :=
  | forever_plus_intro: forall s1 t s2 T1 T2,
      plus ge s1 t s2 ->
      forever_plus ge s2 T2 ->
      T1 = t *** T2 ->
      forever_plus ge s1 T1.

Lemma forever_plus_inv:
  forall ge s T,
  forever_plus ge s T ->
  exists s', exists t, exists T',
  step ge s t s' /\ forever_plus ge s' T' /\ T = t *** T'.
Proof.
  intros. inv H. inv H0. exists s0; exists t1; exists (t2 *** T2).
  split. auto.
  split. exploit star_inv; eauto. intros [[P Q] | R].
    subst. simpl. auto. econstructor; eauto.
  traceEq.
Qed.

Lemma forever_plus_forever:
  forall ge s T, forever_plus ge s T -> forever ge s T.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_plus_inv H) as [s' [t [T' [P [Q R]]]]].
  subst. econstructor; eauto.
Qed.

(** Infinitely many silent transitions *)

CoInductive forever_silent (ge: genv): state -> Prop :=
  | forever_silent_intro: forall s1 s2,
      step ge s1 E0 s2 -> forever_silent ge s2 ->
      forever_silent ge s1.

(** An alternate definition. *)

CoInductive forever_silent_N (ge: genv) : A -> state -> Prop :=
  | forever_silent_N_star: forall s1 s2 a1 a2,
      star ge s1 E0 s2 ->
      order a2 a1 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1
  | forever_silent_N_plus: forall s1 s2 a1 a2,
      plus ge s1 E0 s2 ->
      forever_silent_N ge a2 s2 ->
      forever_silent_N ge a1 s1.

Lemma forever_silent_N_inv:
  forall ge a s,
  forever_silent_N ge a s ->
  exists s', exists a',
  step ge s E0 s' /\ forever_silent_N ge a' s'.
Proof.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2. auto. auto.
  (* at least one transition *)
  exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists x.
  split. auto. eapply forever_silent_N_star; eauto.
  (* plus case *)
  inv H1. exploit Eapp_E0_inv; eauto. intros [P Q]. subst.
  exists s0; exists a2.
  split. auto. inv H3. auto.
  eapply forever_silent_N_plus. econstructor; eauto. eauto.
Qed.

Lemma forever_silent_N_forever:
  forall ge a s, forever_silent_N ge a s -> forever_silent ge s.
Proof.
  cofix COINDHYP; intros.
  destruct (forever_silent_N_inv H) as [s' [a' [P Q]]].
  apply forever_silent_intro with s'. auto.
  apply COINDHYP with a'; auto.
Qed.

(** Infinitely many non-silent transitions *)

CoInductive forever_reactive (ge: genv): state -> traceinf -> Prop :=
  | forever_reactive_intro: forall s1 s2 t T,
      star ge s1 t s2 -> t <> E0 -> forever_reactive ge s2 T ->
      forever_reactive ge s1 (t *** T).

Lemma star_forever_reactive:
  forall ge s1 t s2 T,
  star ge s1 t s2 -> forever_reactive ge s2 T ->
  forever_reactive ge s1 (t *** T).
Proof.
  intros. inv H0. rewrite <- Eappinf_assoc. econstructor.
  eapply star_trans; eauto.
  red; intro. exploit Eapp_E0_inv; eauto. intros [P Q]. contradiction.
  auto.
Qed.

(** [eventually n s P]: all transition sequences of length [n] starting from [s]
    are silent and lead to a state satisfying [P].  However, some transitions can
    get stuck on non-final states. *)

Variable query reply : Type.
Variable at_external: state -> query -> Prop.
Variable final_state: state -> reply -> Prop.

Inductive eventually (ge: genv): nat -> state -> (state -> Prop) -> Prop :=
  | eventually_now: forall s (P: state -> Prop),
      P s ->
      eventually ge O s P
  | eventually_later: forall n s (P: state -> Prop),
      (forall r, ~ final_state s r) ->
      (forall q, ~ at_external s q) -> (* external call is considered not silent *)
      (forall t s', step ge s t s' -> t = E0 /\ eventually ge n s' P) ->
      eventually ge (S n) s P.

Lemma eventually_one: forall ge s (P: state -> Prop),
  (forall r, ~ final_state s r) -> (forall q, ~ at_external s q) ->
  (forall t s', step ge s t s' -> t = E0 /\ P s') ->
  eventually ge 1%nat s P.
Proof.
  intros. apply eventually_later; auto. intros.
  apply H1 in H2. intuition auto using eventually.
Qed.

Lemma eventually_trans: forall ge n1 s1 P1 n2 P2,
  eventually ge n1 s1 P1 -> 
  (forall s2, P1 s2 -> eventually ge n2 s2 P2) ->
  eventually ge (n1 + n2)%nat s1 P2.
Proof.
  intros. revert n1 s1 H. induction n1; intros s1 EV; inv EV; simpl.
- apply H0; assumption.
- apply eventually_later; auto. intros t s' ST. destruct (H3 t s' ST) as [U V]. auto.
Qed.

Corollary eventually_implies: forall ge n s (P1 P2: state -> Prop),
  eventually ge n s P1 ->
  (forall s, P1 s -> P2 s) ->
  eventually ge n s P2.
Proof.
  intros. replace n with (n + 0)%nat by lia. eapply eventually_trans; eauto using eventually_now.
Qed.

Lemma eventually_and_invariant: forall ge (Inv: state -> Prop) n s P,
  (forall s t s', step ge s t s' -> Inv s -> Inv s') ->
  eventually ge n s P -> Inv s ->
  eventually ge n s (fun s' => P s' /\ Inv s').
Proof.
  intros. revert n s H0 H1. induction n; intros s EV IV; inv EV.
- apply eventually_now. auto.
- apply eventually_later; auto. intros. edestruct H3; eauto. 
Qed.

End CLOSURES.

(** * Transition semantics *)

(** The general form of a transition semantics. *)

Record lts liA liB state: Type := {
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  valid_query: query liB -> bool;
  initial_state: query liB -> state -> Prop;
  at_external: state -> query liA -> Prop;
  after_external: state -> reply liA -> state -> Prop;
  final_state: state -> reply liB -> Prop;
  globalenv: genvtype;
}.

Record semantics liA liB := {
  skel: AST.program unit unit;
  state: Type;
  (* get_mem : state -> mem;
  set_mem : state -> mem -> state; *)
  activate :> Genv.symtbl -> lts liA liB state;
}.

(** Handy notations. *)

Notation Semantics_gen (* memory_of_state *) step initial_state at_ext after_ext final_state globalenv p :=
  {|
    skel := AST.erase_program p;
    (* memory_of_state := memory_of_state; *)
    activate se :=
      let ge := globalenv se p in
      {|
        step := step;
        valid_query q := Genv.is_internal ge (entry q);
        initial_state := initial_state ge;
        at_external := at_ext ge;
        after_external := after_ext ge;
        final_state := final_state ge;
        globalenv := ge;
      |};
  |}.

Notation Semantics (* memory_of_state *) step initial_state at_ext after_ext final_state p :=
  (Semantics_gen (* memory_of_state *) step initial_state at_ext (fun _ => after_ext) (fun _ => final_state) (@Genv.globalenv _ _) p).

Declare Scope smallstep_scope.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Eventually' L " := (eventually (step L) (at_external L) (final_state L) (globalenv L)) (at level 1) : smallstep_scope.
Open Scope smallstep_scope.

(** * Forward simulations between two transition semantics. *)

Section FSIM.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

(** The general form of a forward simulation. *)

Record fsim_properties (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop) : Prop := {
    fsim_match_valid_query:
      forall q1 q2, match_query ccB wB q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    fsim_match_initial_states:
      forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
      exists i, exists s2, initial_state L2 q2 s2 /\ match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r1, match_states i s1 s2 -> final_state L1 s1 r1 ->
      exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2;
    fsim_match_external:
      forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
      exists w q2, at_external L2 s2 q2 /\ match_query ccA w q1 q2 /\ match_senv ccA w se1 se2 /\
      forall r1 r2 s1', match_reply ccA w r1 r2 -> after_external L1 s1 r1 s1' ->
      exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2';
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments fsim_properties : clear implicits.

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 index order match_states, fsim_properties L1 L2 index order match_states ->
  forall i s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  intros. exploit @fsim_simulation; eauto.
  intros [i' [s2' [A B]]]. intuition.
  left; exists i'; exists s2'; auto.
  inv H3.
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto.
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.

Variable match_states: state1 -> state2 -> Prop.

Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis match_initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists s2, initial_state L2 q2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r1, match_states s1 s2 -> final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.

Hypothesis match_external:
  forall s1 s2 q1, match_states s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states s1' s2'.

Let ms idx s1 s2 := idx = s1 /\ match_states s1 s2.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: state1 -> state1 -> Prop.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf:
  fsim_properties L1 L2 state1 order ms.
Proof.
  subst ms;
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H. edestruct match_external as (w & q2 & H2 & Hq & Hw & Hr); eauto.
  exists w, q2. intuition auto. edestruct Hr as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition auto.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take
  a stuttering step. *)

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star_wf.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step:
  fsim_properties L1 L2 state1 (ltof _ (fun _ => O)) ms.
Proof.
  apply forward_simulation_plus.
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt:
  fsim_properties L1 L2 state1 (ltof _ measure) ms.
Proof.
  apply forward_simulation_star.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.


(** ** Forward simulation with the "eventually" modality *)

(** A forward simulation diagram where the first semantics can take some extra steps
    before reaching a state that restores the simulation relation. *)

Section FORWARD_SIMU_EVENTUALLY.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.
Variable index: Type.
Variable order: index -> index -> Prop.
Variable match_states: index -> state1 -> state2 -> Prop.

Hypothesis order_wf: well_founded order.
Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists i, exists s2, initial_state L2 q2 s2 /\ match_states i s1 s2.
Hypothesis final_states:
  forall i s1 s2 r1,
    match_states i s1 s2 -> final_state L1 s1 r1 ->
    exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.
Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists n i' s2',
     (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
     /\ Eventually L1 n s1' (fun s1'' => match_states i' s1'' s2').
Hypothesis match_external:
  forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
               exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2'.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)

Let ms := fun i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => match_states (fst i) s1'' s2).
Let index' :=  (index * nat)%type.
Let order' := lex_ord order Nat.lt. 
Lemma forward_simulation_eventually: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor.
- auto.
- intros. exploit initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; split; auto using eventually_now.
  constructor. simpl. eauto.
- intros [i n] s1 s2 r EV FS; simpl in *. inv EV.
  + eapply final_states; eauto.
  + eelim H; eauto.
- intros [i n] s1 s2 q1 EV AT. simpl in *. inv EV.
  + exploit match_external; eauto. intros (wA & q2 & AT' & MQ & MS & AFTER).
    exists wA, q2. intuition eauto. exploit AFTER; eauto.
    intros (i' & s2' & A & B).
    exists (i', O), s2'. split. eauto. constructor. simpl. eauto.
  + eelim H0; eauto.
- intros s1 t s1' ST [i n] s2 EV; simpl in *. inv EV.
  + exploit simulation; eauto. intros (n' & i' & s2' & A & B).
    exists (i', n'), s2'; split; auto.
    destruct A as [P | [P Q]]; auto using lex_ord_left.
    right. split. eauto. constructor. eauto.
  + apply H1 in ST. destruct ST as (A & B). subst t.
    exists (i, n0), s2; split.
    right; split. apply star_refl. 
    apply lex_ord_right. simpl in H2. lia.
    exact B.
Qed.
    
End FORWARD_SIMU_EVENTUALLY.

(** Two simplified diagrams. *)

Section FORWARD_SIMU_EVENTUALLY_SIMPL.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.
Variable match_states: state1 -> state2 -> Prop.

(*Hypothesis public_preserved:
  forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id. *)
Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
           valid_query L2 q2 = valid_query L1 q1.
Hypothesis initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1  ->
  exists s2, initial_state L2 q2 s2 /\ match_states s1 s2.
Hypothesis final_states:
  forall s1 s2 r1,
    match_states s1 s2 -> final_state L1 s1 r1 ->
    exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.
Hypothesis match_external:
  forall s1 s2 q1, match_states s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states s1' s2'.

(** Simplified "plus" simulation diagram, when L2 always makes at least one transition. *)

Section FORWARD_SIMU_EVENTUALLY_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists n s2',
     Plus L2 s2 t s2'
  /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2').

Let ms' := fun (i:nat) s1 s2 => match_states s1 s2.
Let ms := fun i s1 s2 => Eventually L1 (snd i) s1 (fun s1'' => ms' (fst i) s1'' s2).
Let index' :=  (nat * nat)%type.
Let order' := lex_ord lt Nat.lt. 

Lemma forward_simulation_eventually_plus: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually.
- auto.
- intros. exploit initial_states. eauto. eauto.
  intros (s2 & A & B). exists O, s2; auto.
- intros. eapply final_states; eauto.
- intros. exploit simulation; eauto. intros (n & s2' & A & B).
  exists n, O, s2'; eauto.  
- intros. exploit match_external; eauto.
  intros (wA & q2 & A & B & C & D). exists wA, q2. repeat apply conj.
  eauto. eauto. eauto. intros. exploit D. eauto. eauto.
  intros (s2' & A' & B'). exists O, s2'; auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_PLUS.

(** Simplified "star" simulation diagram, with a decreasing, well-founded order on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR_WF.

Variable order: state1 -> state1 -> Prop.
(* Hypothesis order_wf: well_founded order. *)

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1)) /\ match_states s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2')).

Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states s1'' s2).
Lemma forward_simulation_eventually_star_wf: fsim_properties L1 L2 index' order' ms.
Proof.
  constructor; intros.
- auto.
- exploit initial_states; eauto. intros (s2 & A & B).
  exists (O, s1), s2. split. auto. constructor. auto. auto using eventually_now.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + eapply final_states; eauto.
  + eelim H; eauto.
- destruct i as [n s11]; destruct H as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit match_external; eauto. intros (wA & q2 & A & B & C & D).
    exists wA, q2. intuition eauto. exploit D; eauto.
    intros (s2' & A' & B'). exists (O, s1'). exists s2'. split. eauto.
    unfold ms. split. eauto. constructor. eauto.
  + eelim H1; eauto.
- destruct i as [n s11]; destruct H0 as [P Q]; simpl in *; subst s11.
  inv Q.
  + exploit simulation; eauto. intros [(s2' & A & B) | (n & s2' & A & B)].
    * exists (O, s1'), s2'; split. 
      destruct A as [A | [A1 A2]]. eauto. right. split; auto using lex_ord_right.
      eapply lex_ord_right. eauto. constructor; eauto using eventually_now.
    * exists (n, s1'), s2'; unfold ms; auto.
  + apply H2 in H. destruct H. subst t.
    exists (n0, s1'), s2; split.
    right; split. apply star_refl. apply lex_ord_left; lia.
    unfold ms. auto.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR_WF.

(** Simplified "star" simulation diagram, with a decreasing measure on L1 states. *)

Section FORWARD_SIMU_EVENTUALLY_STAR.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
     (exists s2',
        (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1' < measure s1))%nat
        /\ match_states s1' s2')
  \/ (exists n s2',
        Plus L2 s2 t s2' /\ Eventually L1 n s1' (fun s1'' => match_states s1'' s2')).

Let order := (ltof _ measure).
Let index' := (nat * state1)%type.
Let order' := lex_ord Nat.lt order.
Let ms := fun i s1 s2 => snd i = s1 /\ Eventually L1 (fst i) s1 (fun s1'' => match_states s1'' s2).
Lemma forward_simulation_eventually_star: fsim_properties L1 L2 index' order' ms.
Proof.
  apply forward_simulation_eventually_star_wf.
- exact simulation.
Qed.

End FORWARD_SIMU_EVENTUALLY_STAR.

End FORWARD_SIMU_EVENTUALLY_SIMPL.


(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: fsim_properties L1 L2 index order match_states).

Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.

Lemma simulation_plus:
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ t = E0 /\ match_states i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition.
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star. apply plus_star; eauto. eauto.
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition auto.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.

Lemma simulation_forever_silent:
  well_founded order ->
  forall i s1 s2,
  Forever_silent L1 s1 -> match_states i s1 s2 ->
  Forever_silent L2 s2.
Proof.
  assert (forall i s1 s2,
          Forever_silent L1 s1 -> match_states i s1 s2 ->
          forever_silent_N (step L2) order (globalenv L2) i s2).
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_silent_N_plus; eauto.
    eapply forever_silent_N_star; eauto.
  intros. eapply forever_silent_N_forever; eauto.
Qed.

Lemma simulation_forever_reactive:
  forall i s1 s2 T,
  Forever_reactive L1 s1 T -> match_states i s1 s2 ->
  Forever_reactive L2 s2 T.
Proof.
  cofix COINDHYP; intros.
  inv H.
  edestruct simulation_star as [i' [st2' [A B]]]; eauto.
  econstructor; eauto.
Qed.

End SIMULATION_SEQUENCES.

End FSIM.

Arguments fsim_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record fsim_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_match_states: _;

    fsim_skel:
      skel L1 = skel L2;
    fsim_lts se1 se2 wB:
      @match_senv liB1 liB2 ccB wB se1 se2 ->
      Genv.valid_for (skel L1) se1 ->
      fsim_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
        fsim_index fsim_order (fsim_match_states se1 se2 wB);
    fsim_order_wf:
      well_founded fsim_order;
  }.

Arguments Forward_simulation {_ _ ccA _ _ ccB L1 L2 fsim_index}.

Definition forward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
  inhabited (@fsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

(** ** Tactics for forward simulation proofs *)

(** The forward simulation proofs for each compiler pass have the same
  top-level structure, so we use the following tactics to capture the
  patterns, and have a central place to update things when we tweak
  our model. The idea is to use the tactic [fsim tac] on a goal of the
  form [match_prog p tp -> forward_simulation ccA ccB L1 L2], where
  [tac] constructs the [fsim_components] object and is expected to be
  something like [eapply forward_simulation_plus]. *)

Ltac fsim_match_prog_reduce H :=
  lazymatch type of H with
    | Linking.match_program_gen _ _ _ _ _ => idtac
    | _ /\ _ => destruct H as [H _]; fsim_match_prog_reduce H
    | _ => red in H; fsim_match_prog_reduce H
  end.

Ltac fsim_skel MATCH :=
  fsim_match_prog_reduce MATCH;
  apply Linking.match_program_skel in MATCH; auto; fail.

Ltac fsim_tac tac :=
  intros MATCH; constructor;
  eapply Forward_simulation with (fsim_match_states := fun _ _ _ => _);
  [ try fsim_skel MATCH
  | intros se1 se2 w Hse Hse1; tac
  | try solve [auto using well_founded_ltof]].

Tactic Notation (at level 3) "fsim" tactic3(tac) := fsim_tac tac.

(** ** Identity simulation *)

Definition identity_fsim_components {liA liB} (L: semantics liA liB):
  fsim_components cc_id cc_id L L.
Proof.
  eapply Forward_simulation with _ (fun _ _ _ => _); auto.
  - intros se _ [ ] [ ] _.
    eapply forward_simulation_plus with (match_states := eq);
    cbn; intros; subst; eauto 10 using plus_one.
    exists tt, q1. intuition (subst; eauto).
  - apply well_founded_ltof.
Qed.

Lemma identity_forward_simulation {liA liB} (L: semantics liA liB):
  forward_simulation cc_id cc_id L L.
Proof.
  constructor. apply identity_fsim_components.
Qed.

(** ** Composing two forward simulations *)

Section COMPOSE_FORWARD_SIMULATIONS.

Context {liA1 liA2 liA3} {ccA12: callconv liA1 liA2} {ccA23: callconv liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv liB1 liB2} {ccB23: callconv liB2 liB3}.
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2) (L3: semantics liA3 liB3).

Lemma compose_fsim_components:
  fsim_components ccA12 ccB12 L1 L2 ->
  fsim_components ccA23 ccB23 L2 L3 ->
  fsim_components (ccA12 @ ccA23) (ccB12 @ ccB23) L1 L3.
Proof.
  intros [index order match_states Hsk props order_wf].
  intros [index' order' match_states' Hsk' props' order_wf'].
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).
  set (ff_match_states :=
         fun se1 se3 '(se2, w, w') (i: ff_index) (s1: state L1) (s3: state L3) =>
           exists s2,
             match_states se1 se2 w (snd i) s1 s2 /\
             match_states' se2 se3 w' (fst i) s2 s3).
  apply Forward_simulation with ff_order ff_match_states.
  3: { unfold ff_order. auto using wf_lex_ord, wf_clos_trans. }
  1: { congruence. }
  intros se1 se3 [[se2 w] w'] (Hse12 & Hse23) Hse1. cbn in *.
  assert (Hse2: Genv.valid_for (skel L2) se2).
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

(** * Receptiveness and determinacy *)

Definition single_events {liA liB st} (L: lts liA liB st) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record lts_receptive {liA liB st} (L: lts liA liB st) se: Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces se t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record lts_determinate {liA liB st} (L: lts liA liB st) se: Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces se t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall q s1 s2,
      initial_state L q s1 -> initial_state L q s2 -> s1 = s2;
    sd_at_external_nostep: forall s q,
      at_external L s q -> Nostep L s;
    sd_at_external_determ: forall s q1 q2,
      at_external L s q1 -> at_external L s q2 -> q1 = q2;
    sd_after_external_determ: forall s r s1 s2,
      after_external L s r s1 -> after_external L s r s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_noext: forall s r q,
      final_state L s r -> at_external L s q -> False;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

(** The determinacy of LTS which only cares about behaviors at the interface,
    allowing internal non-determinacy  *)

Record lts_determinate_big {liA liB st} (L: lts liA liB st): Prop :=
  Determinate_big {
    sd_big_initial_determ: forall q s1 s2,
      initial_state L q s1 -> initial_state L q s2 -> s1 = s2;
    sd_big_at_external_nostep: forall s q,
      at_external L s q -> Nostep L s;
    sd_big_at_external_determ: forall s q1 q2,
      at_external L s q1 -> at_external L s q2 -> q1 = q2;
    sd_big_after_external_determ: forall s r s1 s2,
      after_external L s r s1 -> after_external L s r s2 -> s1 = s2;
    sd_big_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_big_final_noext: forall s r q,
      final_state L s r -> at_external L s q -> False;
    sd_big_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
    }.

Section DETERMINACY.

Context {liA liB st} (L: lts liA liB st) (se: Genv.symtbl).
Hypothesis DET: lts_determinate L se.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces se t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma sd_determ_3:
  forall s t s1 s2,
  Step L s t s1 -> Step L s E0 s2 -> t = E0 /\ s1 = s2.
Proof.
  intros. exploit (sd_determ DET). eexact H. eexact H0.
  intros [A B]. inv A. auto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros.
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto.
    destruct t1; simpl in L1; try extlia.
    destruct t0. inv MT. destruct t0; simpl in L2; try extlia.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4.
  auto.
Qed.

End DETERMINACY.

Definition receptive {liA liB} (L: semantics liA liB) :=
  forall se, lts_receptive (L se) se.

Definition determinate {liA liB} (L: semantics liA liB) :=
  forall se, lts_determinate (L se) se.

Definition determinate_big {liA liB} (L: semantics liA liB) :=
  forall se, lts_determinate_big (L se).

(** Extra simulation diagrams for determinate languages. *)

Section FORWARD_SIMU_DETERM.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.

Hypothesis L1det: lts_determinate L1 se1.

Variable index: Type.
Variable order: index -> index -> Prop.
Hypothesis wf_order: well_founded order.

Variable match_states: index -> state1 -> state2 -> Prop.

Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis match_initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists i s2, initial_state L2 q2 s2 /\ match_states i s1 s2.

Hypothesis match_final_states:
  forall i s1 s2 r1, match_states i s1 s2 -> final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.

Hypothesis match_external:
  forall i s1 s2 q1, match_states i s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists i' s2', after_external L2 s2 r2 s2' /\ match_states i' s1' s2'.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists s1'' i' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
   /\ match_states i' s1'' s2'.

Inductive match_states_later: index * nat -> state1 -> state2 -> Prop :=
| msl_now: forall i s1 s2,
    match_states i s1 s2 -> match_states_later (i, O) s1 s2
| msl_later: forall i n s1 s1' s2,
    Step L1 s1 E0 s1' -> match_states_later (i, n) s1' s2 -> match_states_later (i, S n) s1 s2.

Lemma star_match_states_later:
  forall s1 s1', Star L1 s1 E0 s1' ->
  forall i s2, match_states i s1' s2 ->
  exists n, match_states_later (i, n) s1 s2. 
Proof.
  intros s10 s10' STAR0. pattern s10, s10'; eapply star_E0_ind; eauto.
  - intros s1 i s2 M. exists O; constructor; auto.
  - intros s1 s1' s1'' STEP IH i s2 M.
    destruct (IH i s2 M) as (n & MS).
    exists (S n); econstructor; eauto.
Qed.

Lemma forward_simulation_determ:
  fsim_properties ccA ccB se1 se2 wB L1 L2 _ (lex_ord order lt) match_states_later.
Proof.
  constructor.
- auto.
- intros. exploit match_initial_states; eauto. intros (i & s2 & A & B).
  exists (i, O), s2; auto using msl_now.
- intros. inv H.
  + eapply match_final_states; eauto.
  + eelim (sd_final_nostep L1det); eauto.
- intros i s1 s2 q1 Hs Hq1. destruct Hs.
  + edestruct match_external as (wA & q2 & Hq2 & Hq & Hse & Hr); eauto.
    exists wA, q2. intuition auto.
    edestruct Hr as (i' & s2' & Hs2' & Hs'); eauto.
    exists (i', O), s2'. split; auto. constructor; auto.
  + eelim sd_at_external_nostep; eauto.
- intros s1 t s1' A; destruct 1.
  + exploit simulation; eauto. intros (s1'' & i' & s2' & B & C & D).
    exploit star_match_states_later; eauto. intros (n & E).
    exists (i', n), s2'; split; auto.
    destruct C as [P | [P Q]]; auto using lex_ord_left.
  + exploit @sd_determ_3. eauto. eexact A. eauto. intros [P Q]; subst t s1'0.
    exists (i, n), s2; split; auto.
    right; split. apply star_refl. apply lex_ord_right. lia.
Qed.

End FORWARD_SIMU_DETERM.

(** A few useful special cases. *)

Section FORWARD_SIMU_DETERM_DIAGRAMS.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.

Hypothesis L1det: lts_determinate L1 se1.

Variable match_states: state1 -> state2 -> Prop.

Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis match_initial_states:
  forall q1 q2 s1, match_query ccB wB q1 q2 -> initial_state L1 q1 s1 ->
  exists s2, initial_state L2 q2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r1, match_states s1 s2 -> final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_reply ccB wB r1 r2.

Hypothesis match_external:
  forall s1 s2 q1, match_states s1 s2 -> at_external L1 s1 q1 ->
  exists wA q2, at_external L2 s2 q2 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2 s1', match_reply ccA wA r1 r2 -> after_external L1 s1 r1 s1' ->
  exists s2', after_external L2 s2 r2 s2' /\ match_states s1' s2'.

Section SIMU_DETERM_STAR.

Variable measure: state1 -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2',
      Star L1 s1' E0 s1''
   /\ (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ measure s1'' < measure s1))%nat
   /\ match_states s1'' s2'.

Lemma forward_simulation_determ_star:
  fsim_properties ccA ccB se1 se2 wB L1 L2 _
    (lex_ord (ltof _ measure) lt)
    (match_states_later L1 (fun i s1 s2 => i = s1 /\ match_states s1 s2)).
Proof.
  apply forward_simulation_determ.
- assumption.
- auto.
- intros. exploit match_initial_states; eauto. intros (s2 & A & B). 
  exists s1, s2; auto.
- intros. destruct H. eapply match_final_states; eauto.
- intros. destruct H. subst.
  edestruct match_external as (wA & q2 & Hq2 & Hq & Hse & Hr); eauto.
  exists wA, q2. intuition auto.
  edestruct Hr as (s2' & Hs2' & Hs'); eauto.
- intros. destruct H0; subst i. 
  exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s1'', s2'. auto.
Qed.

End SIMU_DETERM_STAR.

Section SIMU_DETERM_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Plus L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_plus:
  fsim_properties ccA ccB se1 se2 wB L1 L2 _
    (lex_ord (ltof _ (fun _ => O)) lt)
    (match_states_later L1 (fun i s1 s2 => i = s1 /\ match_states s1 s2)).
Proof.
  apply forward_simulation_determ_star.
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto.
Qed.

End SIMU_DETERM_PLUS.

Section SIMU_DETERM_ONE.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s1'' s2', Star L1 s1' E0 s1'' /\ Step L2 s2 t s2' /\ match_states s1'' s2'.

Lemma forward_simulation_determ_one:
  fsim_properties ccA ccB se1 se2 wB L1 L2 _
    (lex_ord (ltof _ (fun _ => O)) lt)
    (match_states_later L1 (fun i s1 s2 => i = s1 /\ match_states s1 s2)).
Proof.
  apply forward_simulation_determ_plus.
  intros. exploit simulation; eauto. intros (s1'' & s2' & A & B & C).
  exists s1'', s2'; auto using plus_one.
Qed.

End SIMU_DETERM_ONE.

End FORWARD_SIMU_DETERM_DIAGRAMS.

(** * Backward simulations between two transition semantics. *)

Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists q, at_external L s' q)
  \/ (exists t, exists s'', Step L s' t s'').

Lemma star_safe:
  forall {liA liB st} (L: lts liA liB st) s s',
  Star L s E0 s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. apply H0. eapply star_trans; eauto.
Qed.

(** When matching the sets of states specified by [initial_state] or
  [after_external], we need to ensure that:
  1. the target program can only go wrong if the source program did;
  2. if the source program does not go wrong, then any state of the
  target program has a corresponding state of the source program. *)

Record bsim_match_cont {A B} (R: A -> B -> Prop) (S1 S2: _ -> Prop) :=
  {
    bsim_match_cont_exist:
      forall s1, S1 s1 -> exists s2, S2 s2;
    bsim_match_cont_match:
      forall s1 s2, S1 s1 -> S2 s2 -> exists s1', S1 s1' /\ R s1' s2;
  }.

Definition rex {I A B} (R: I -> A -> B -> Prop) (a: A) (b: B): Prop :=
  exists i, R i a b.

Section BSIM.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

(** The general form of a backward simulation. *)

Record bsim_properties (L1 L2: lts _ _ _) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state1 -> state2 -> Prop) : Prop := {
    bsim_match_valid_query:
      forall q1 q2, match_query ccB wB q1 q2 ->
      valid_query L2 q2 = valid_query L1 q1;
    bsim_match_initial_states:
      forall q1 q2, match_query ccB wB q1 q2 ->
      bsim_match_cont (rex match_states) (initial_state L1 q1) (initial_state L2 q2);
    bsim_match_final_states:
      forall i s1 s2 r2,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r2 ->
      exists s1' r1, Star L1 s1 E0 s1' /\ final_state L1 s1' r1 /\ match_reply ccB wB r1 r2;
    bsim_match_external:
      forall i s1 s2 q2, match_states i s1 s2 -> safe L1 s1 -> at_external L2 s2 q2 ->
      exists wA s1' q1, Star L1 s1 E0 s1' /\ at_external L1 s1' q1 /\
      match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
      forall r1 r2, match_reply ccA wA r1 r2 ->
      bsim_match_cont (rex match_states) (after_external L1 s1' r1) (after_external L2 s2 r2);
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists q, at_external L2 s2 q) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
  }.

Arguments bsim_properties: clear implicits.

(** An alternate form of the simulation diagram *)

Lemma bsim_simulation':
  forall L1 L2 index order match_states, bsim_properties L1 L2 index order match_states ->
  forall i s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states i s1 s2 -> safe L1 s1 ->
  (exists i', exists s1', Plus L1 s1 t s1' /\ match_states i' s1' s2')
  \/ (exists i', order i' i /\ t = E0 /\ match_states i' s1 s2').
Proof.
  intros. exploit bsim_simulation; eauto.
  intros [i' [s1' [A B]]]. intuition.
  left; exists i'; exists s1'; auto.
  inv H4.
  right; exists i'; auto.
  left; exists i'; exists s1'; split; auto. econstructor; eauto.
Qed.

(** ** Backward simulation diagrams. *)

(** Various simulation diagrams that imply backward simulation. *)

Section BACKWARD_SIMU_DIAGRAMS.

Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.

Variable match_states: state1 -> state2 -> Prop.

Hypothesis match_valid_query:
  forall q1 q2, match_query ccB wB q1 q2 ->
  valid_query L2 q2 = valid_query L1 q1.

Hypothesis match_initial_states:
  forall q1 q2, match_query ccB wB q1 q2 ->
  bsim_match_cont match_states (initial_state L1 q1) (initial_state L2 q2).

Hypothesis match_final_states:
  forall s1 s2 r2, match_states s1 s2 -> final_state L2 s2 r2 ->
  exists r1, final_state L1 s1 r1 /\ match_reply ccB wB r1 r2.

Hypothesis match_external:
  forall s1 s2 q2, match_states s1 s2 -> at_external L2 s2 q2 ->
  exists wA q1, at_external L1 s1 q1 /\ match_query ccA wA q1 q2 /\ match_senv ccA wA se1 se2 /\
  forall r1 r2, match_reply ccA wA r1 r2 ->
  bsim_match_cont match_states (after_external L1 s1 r1) (after_external L2 s2 r2).

Hypothesis progress:
  forall s1 s2,
  match_states s1 s2 -> safe L1 s1 ->
  (exists r, final_state L2 s2 r) \/
  (exists q, at_external L2 s2 q) \/
  (exists t, exists s2', Step L2 s2 t s2').

Section BACKWARD_SIMULATION_PLUS.

Hypothesis simulation:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall s1, match_states s1 s2 -> safe L1 s1 ->
  exists s1', Plus L1 s1 t s1' /\ match_states s1' s2'.

Lemma bsim_match_cont_unit (k1 k2: _ -> Prop):
  bsim_match_cont match_states k1 k2 ->
  bsim_match_cont (rex (fun (_ : unit) s1 s2 => match_states s1 s2)) k1 k2.
Proof.
  clear. intros [Hex Hmatch].
  split; eauto. intros.
  edestruct Hmatch as (s1' & ? & ?); eauto.
  exists s1'; split; auto.
  exists tt; auto.
Qed.

Lemma backward_simulation_plus:
  bsim_properties L1 L2 unit (fun _ _ => False) (fun _ => match_states).
Proof.
  constructor; auto.
- intros. apply bsim_match_cont_unit; eauto.
- intros. edestruct match_final_states as (r1 & Hr1 & Hr); eauto.
  exists s1, r1; split. apply star_refl. eauto.
- intros. edestruct match_external as (w & q1 & Hq1 & Hq & Hse & Hk); eauto.
  eauto 10 using bsim_match_cont_unit, star_refl.
- intros. exploit simulation; eauto. intros [s1' [A B]].
  exists tt; exists s1'; auto.
Qed.

End BACKWARD_SIMULATION_PLUS.

End BACKWARD_SIMU_DIAGRAMS.

(** ** Backward simulation of transition sequences *)

Section BACKWARD_SIMULATION_SEQUENCES.

Context L1 L2 index order match_states (S: bsim_properties L1 L2 index order match_states).

Lemma bsim_E0_star:
  forall s2 s2', Star L2 s2 E0 s2' ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 E0 s1' /\ match_states i' s1' s2'.
Proof.
  intros s20 s20' STAR0. pattern s20, s20'. eapply star_E0_ind; eauto.
- (* base case *)
  intros. exists i; exists s1; split; auto. apply star_refl.
- (* inductive case *)
  intros. exploit bsim_simulation; eauto. intros [i' [s1' [A B]]].
  assert (Star L1 s0 E0 s1'). intuition. apply plus_star; auto.
  exploit H0. eauto. eapply star_safe; eauto. intros [i'' [s1'' [C D]]].
  exists i''; exists s1''; split; auto. eapply star_trans; eauto.
Qed.

Lemma bsim_safe:
  forall i s1 s2,
  match_states i s1 s2 -> safe L1 s1 -> safe L2 s2.
Proof.
  intros; red; intros.
  exploit bsim_E0_star; eauto. intros [i' [s1' [A B]]].
  eapply bsim_progress; eauto. eapply star_safe; eauto.
Qed.

Lemma bsim_E0_plus:
  forall s2 t s2', Plus L2 s2 t s2' -> t = E0 ->
  forall i s1, match_states i s1 s2 -> safe L1 s1 ->
     (exists i', exists s1', Plus L1 s1 E0 s1' /\ match_states i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ match_states i' s1 s2').
Proof.
  induction 1 using plus_ind2; intros; subst t.
- (* base case *)
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ left; exists i'; exists s1'; auto.
+ right; exists i'; intuition.
- (* inductive case *)
  exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit bsim_simulation'; eauto. intros [[i' [s1' [A B]]] | [i' [A [B C]]]].
+ exploit bsim_E0_star. apply plus_star; eauto. eauto. eapply star_safe; eauto. apply plus_star; auto.
  intros [i'' [s1'' [P Q]]].
  left; exists i''; exists s1''; intuition. eapply plus_star_trans; eauto.
+ exploit IHplus; eauto. intros [P | [i'' [P Q]]].
  left; auto.
  right; exists i''; intuition. eapply t_trans; eauto. apply t_step; auto.
Qed.

Lemma star_non_E0_split:
  forall s2 t s2', Star L2 s2 t s2' -> (length t = 1)%nat ->
  exists s2x, exists s2y, Star L2 s2 E0 s2x /\ Step L2 s2x t s2y /\ Star L2 s2y E0 s2'.
Proof.
  induction 1; intros.
  simpl in H; discriminate.
  subst t.
  assert (EITHER: t1 = E0 \/ t2 = E0).
    unfold Eapp in H2; rewrite app_length in H2.
    destruct t1; auto. destruct t2; auto. simpl in H2; extlia.
  destruct EITHER; subst.
  exploit IHstar; eauto. intros [s2x [s2y [A [B C]]]].
  exists s2x; exists s2y; intuition. eapply star_left; eauto.
  rewrite E0_right. exists s1; exists s2; intuition. apply star_refl.
Qed.

End BACKWARD_SIMULATION_SEQUENCES.

End BSIM.

Arguments bsim_properties {_ _} _ {_ _} _ _ _ _ {_ _} L1 L2 index order match_states.

Record bsim_components {liA1 liA2} (ccA: callconv liA1 liA2) {liB1 liB2} ccB L1 L2 :=
  Backward_simulation {
    bsim_index: Type;
    bsim_order: bsim_index -> bsim_index -> Prop;
    bsim_match_states: _;

    bsim_skel:
      skel L1 = skel L2;
    bsim_lts:
      forall se1 se2 wB,
        @match_senv liB1 liB2 ccB wB se1 se2 ->
        Genv.valid_for (skel L1) se1 ->
        bsim_properties ccA ccB se1 se2 wB (activate L1 se1) (activate L2 se2)
                        bsim_index bsim_order (bsim_match_states se1 se2 wB);
    bsim_order_wf:
      well_founded bsim_order;
    }.

Arguments Backward_simulation {_ _ ccA _ _ ccB L1 L2 bsim_index}.

Definition backward_simulation {liA1 liA2} ccA {liB1 liB2} ccB L1 L2 :=
  inhabited (@bsim_components liA1 liA2 ccA liB1 liB2 ccB L1 L2).

(** ** Composing two backward simulations *)

Section COMPOSE_BACKWARD_SIMULATIONS.

Context {liA1 liA2 liA3} {ccA12: callconv liA1 liA2} {ccA23: callconv liA2 liA3}.
Context {liB1 liB2 liB3} {ccB12: callconv liB1 liB2} {ccB23: callconv liB2 liB3}.
Context {state1 state2 state3: Type}.
Variable L1: lts liA1 liB1 state1.
Variable L2: lts liA2 liB2 state2.
Variable L3: lts liA3 liB3 state3.
Context (se1 se2 se3: Genv.symtbl) (wB12: ccworld ccB12) (wB23: ccworld ccB23).
Context index order match_states (S12: bsim_properties ccA12 ccB12 se1 se2 wB12 L1 L2 index order match_states).
Context index' order' match_states' (S23: bsim_properties ccA23 ccB23 se2 se3 wB23 L2 L3 index' order' match_states').
Hypothesis L3_single_events: single_events L3.

Let bb_index : Type := (index * index')%type.

Definition bb_order : bb_index -> bb_index -> Prop := lex_ord (clos_trans _ order) order'.

Inductive bb_match_states: bb_index -> state1 -> state3 -> Prop :=
  | bb_match_later: forall i1 i2 s1 s3 s2x s2y,
      match_states i1 s1 s2x -> Star L2 s2x E0 s2y -> match_states' i2 s2y s3 ->
      bb_match_states (i1, i2) s1 s3.

Lemma bb_match_at: forall i1 i2 s1 s3 s2,
  match_states i1 s1 s2 -> match_states' i2 s2 s3 ->
  bb_match_states (i1, i2) s1 s3.
Proof.
  intros. econstructor; eauto. apply star_refl.
Qed.

Lemma bb_simulation_base:
  forall s3 t s3', Step L3 s3 t s3' ->
  forall i1 s1 i2 s2, match_states i1 s1 s2 -> match_states' i2 s2 s3 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ bb_order i' (i1, i2)))
    /\ bb_match_states i' s1' s3'.
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

(** ** Converting a forward simulation to a backward simulation *)

Section FORWARD_TO_BACKWARD.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2} (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2).
Context {index order match_states} (FS: fsim_properties ccA ccB se1 se2 wB L1 L2 index order match_states).
Hypothesis order_wf: well_founded order.
Hypothesis Hse: match_senv ccB wB se1 se2.
Hypothesis L1_receptive: lts_receptive L1 se1.
Hypothesis L2_determinate: lts_determinate L2 se2.

(** Exploiting forward simulation *)

Inductive f2b_transitions: state1 -> state2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r1 r2,
      Star L1 s1 E0 s1' ->
      match_reply ccB wB r1 r2 ->
      final_state L1 s1' r1 ->
      final_state L2 s2 r2 ->
      f2b_transitions s1 s2
  | f2b_trans_ext: forall s1 s2 s1' wA q1 q2,
      Star L1 s1 E0 s1' ->
      match_query ccA wA q1 q2 ->
      match_senv ccA wA se1 se2 ->
      at_external L1 s1' q1 ->
      at_external L2 s2 q2 ->
      (forall r1 r2 s1'',
          match_reply ccA wA r1 r2 ->
          after_external L1 s1' r1 s1'' ->
          exists j s2',
            after_external L2 s2 r2 s2' /\
            match_states j s1'' s2') ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' t s1'' s2' i' i'',
      Star L1 s1 E0 s1' ->
      Step L1 s1' t s1'' ->
      Plus L2 s2 t s2' ->
      match_states i' s1' s2 ->
      match_states i'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress:
  forall i s1 s2, match_states i s1 s2 -> safe L1 s1 -> f2b_transitions s1 s2.
Proof.
  intros i0; pattern i0. apply well_founded_ind with (R := order); auto.
  intros i REC s1 s2 MATCH SAFE.
  destruct (SAFE s1) as [[r FINAL] | [[q EXTERN] | [t [s1' STEP1]]]]. apply star_refl.
- (* final state reached *)
  edestruct @fsim_match_final_states as (r2 & Hr & Hfinal); eauto.
  eapply f2b_trans_final; eauto.
  apply star_refl.
- (* external call reached *)
  edestruct @fsim_match_external as (w & q2 & Hq & Hat & Hse' & Hafter); eauto.
  eapply f2b_trans_ext; eauto.
  apply star_refl.
- (* L1 can make one step *)
  exploit (fsim_simulation FS); eauto. intros [i' [s2' [A MATCH']]].
  assert (B: Plus L2 s2 t s2' \/ (s2' = s2 /\ t = E0 /\ order i' i)).
    intuition auto.
    destruct (star_inv H0); intuition auto.
  clear A. destruct B as [PLUS2 | [EQ1 [EQ2 ORDER]]].
+ eapply f2b_trans_step; eauto. apply star_refl.
+ subst. exploit REC; eauto. eapply star_safe; eauto. apply star_one; auto.
  intros TRANS; inv TRANS.
* eapply f2b_trans_final; eauto. eapply star_left; eauto.
* eapply f2b_trans_ext; eauto. eapply star_left; eauto.
* eapply f2b_trans_step; eauto. eapply star_left; eauto.
Qed.

Lemma fsim_simulation_not_E0:
  forall s1 t s1', Step L1 s1 t s1' -> t <> E0 ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Plus L2 s2 t s2' /\ match_states i' s1' s2'.
Proof.
  intros. exploit (fsim_simulation FS); eauto. intros [i' [s2' [A B]]].
  exists i'; exists s2'; split; auto.
  destruct A. auto. destruct H2. exploit star_inv; eauto. intros [[EQ1 EQ2] | P]; auto.
  congruence.
Qed.

(** Exploiting determinacy *)

Remark silent_or_not_silent:
  forall t, t = E0 \/ t <> E0.
Proof.
  intros; unfold E0; destruct t; auto; right; congruence.
Qed.

Remark not_silent_length:
  forall t1 t2, (length (t1 ** t2) <= 1)%nat -> t1 = E0 \/ t2 = E0.
Proof.
  unfold Eapp, E0; intros. rewrite app_length in H.
  destruct t1; destruct t2; auto. simpl in H. extlia.
Qed.

Lemma f2b_determinacy_inv:
  forall s2 t' s2' t'' s2'',
  Step L2 s2 t' s2' -> Step L2 s2 t'' s2'' ->
  (t' = E0 /\ t'' = E0 /\ s2' = s2'')
  \/ (t' <> E0 /\ t'' <> E0 /\ match_traces se1 t' t'').
Proof.
  intros.
  assert (match_traces se2 t' t'').
    eapply sd_determ_1; eauto.
  destruct (silent_or_not_silent t').
  subst. inv H1.
  left; intuition. eapply sd_determ_2; eauto.
  destruct (silent_or_not_silent t'').
  subst. inv H1. elim H2; auto.
  right; intuition.
  eapply match_traces_preserved with (ge1 := se2); auto.
  intro. symmetry. eapply match_senv_public_preserved; eauto.
Qed.

Lemma f2b_determinacy_star:
  forall s s1, Star L2 s E0 s1 ->
  forall t s2 s3,
  Step L2 s1 t s2 -> t <> E0 ->
  Star L2 s t s3 ->
  Star L2 s1 t s3.
Proof.
  intros s0 s01 ST0. pattern s0, s01. eapply star_E0_ind; eauto.
  intros. inv H3. congruence.
  exploit f2b_determinacy_inv. eexact H. eexact H4.
  intros [[EQ1 [EQ2 EQ3]] | [NEQ1 [NEQ2 MT]]].
  subst. simpl in *. eauto.
  congruence.
Qed.

(** Orders *)

Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto.
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)).
    intros n0; pattern n0; apply lt_wf_ind; intros.
    constructor; intros. inv H0. auto. auto.
  red; intros. destruct a; auto.
Qed.

(** Constructing the backward simulation *)

Inductive f2b_match_states: f2b_index -> state1 -> state2 -> Prop :=
  | f2b_match_at: forall i s1 s2,
      match_states i s1 s2 ->
      f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_before: forall s1 t s1' s2b s2 n s2a i,
      Step L1 s1 t s1' ->  t <> E0 ->
      Star L2 s2b E0 s2 ->
      starN (step L2) (globalenv L2) n s2 t s2a ->
      match_states i s1 s2b ->
      f2b_match_states (F2BI_before n) s1 s2
  | f2b_match_after: forall n s2 s2a s1 i,
      starN (step L2) (globalenv L2) (S n) s2 E0 s2a ->
      match_states i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i,
  starN (step L2) (globalenv L2) n s2 E0 s2a ->
  match_states i s1 s2a ->
  f2b_match_states (F2BI_after n) s1 s2.
Proof.
  intros. inv H.
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
Qed.

(** Backward simulation of L2 steps *)

Lemma f2b_simulation_step:
  forall s2 t s2', Step L2 s2 t s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe L1 s1 ->
  exists i', exists s1',
    (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof.
  intros s2 t s2' STEP2 i s1 MATCH SAFE.
  inv MATCH.
- (* 1. At matching states *)
  exploit f2b_progress; eauto. intros TRANS; inv TRANS.
+ (* 1.1  L1 can reach final state and L2 is at final state: impossible! *)
  exploit (sd_final_nostep L2_determinate); eauto. contradiction.
+ (* 1.1b  Same, with external states *)
  exploit (sd_at_external_nostep L2_determinate); eauto. contradiction.
+ (* 1.2  L1 can make 0 or several steps; L2 can make 1 or several matching steps. *)
  inv H2.
  exploit f2b_determinacy_inv. eexact H5. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
* (* 1.2.1  L2 makes a silent transition *)
  destruct (silent_or_not_silent t2).
  (* 1.2.1.1  L1 makes a silent transition too: perform transition now and go to "after" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_after n); exists s1''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.
  (* 1.2.1.2 L1 makes a non-silent transition: keep it for later and go to "before" state *)
  subst. simpl in *. destruct (star_starN H6) as [n STEPS2].
  exists (F2BI_before n); exists s1'; split.
  right; split. auto. constructor.
  econstructor. eauto. auto. apply star_one; eauto. eauto. eauto.
* (* 1.2.2 L2 makes a non-silent transition, and so does L1 *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst t2. rewrite E0_right in H1.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]]. inv P.
  (* Exploit determinacy *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst t0. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H8. auto.
  subst t2. rewrite E0_right in *.
  assert (s4 = s2'). eapply sd_determ_2; eauto. subst s4.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H7) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. eapply plus_right; eauto.
  eapply f2b_match_after'; eauto.

- (* 2. Before *)
  inv H2. congruence.
  exploit f2b_determinacy_inv. eexact H4. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
+ (* 2.1 L2 makes a silent transition: remain in "before" state *)
  subst. simpl in *. exists (F2BI_before n0); exists s1; split.
  right; split. apply star_refl. constructor. lia.
  econstructor; eauto. eapply star_right; eauto.
+ (* 2.2 L2 make a non-silent transition *)
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  congruence.
  subst. rewrite E0_right in *.
  (* Use receptiveness to equate the traces *)
  exploit (sr_receptive L1_receptive); eauto. intros [s1''' STEP1].
  exploit fsim_simulation_not_E0. eexact STEP1. auto. eauto.
  intros [i''' [s2''' [P Q]]].
  (* Exploit determinacy *)
  exploit f2b_determinacy_star. eauto. eexact STEP2. auto. apply plus_star; eauto.
  intro R. inv R. congruence.
  exploit not_silent_length. eapply (sr_traces L1_receptive); eauto. intros [EQ | EQ].
  subst. simpl in *. exploit @sd_determ_1. eauto. eexact STEP2. eexact H2.
  intros. elim NOT2. inv H7; auto.
  subst. rewrite E0_right in *.
  assert (s3 = s2'). eapply sd_determ_2; eauto. subst s3.
  (* Perform transition now and go to "after" state *)
  destruct (star_starN H6) as [n STEPS2]. exists (F2BI_after n); exists s1'''; split.
  left. apply plus_one; auto.
  eapply f2b_match_after'; eauto.

- (* 3. After *)
  inv H. exploit Eapp_E0_inv; eauto. intros [EQ1 EQ2]; subst.
  exploit f2b_determinacy_inv. eexact H2. eexact STEP2.
  intros [[EQ1 [EQ2 EQ3]] | [NOT1 [NOT2 MT]]].
  subst. exists (F2BI_after n); exists s1; split.
  right; split. apply star_refl. constructor; lia.
  eapply f2b_match_after'; eauto.
  congruence.
Qed.

End FORWARD_TO_BACKWARD.

(** The backward simulation *)

Lemma forward_to_backward_simulation:
  forall {liA1 liA2} (ccA: callconv liA1 liA2),
  forall {liB1 liB2} (ccB: callconv liB1 liB2),
  forall L1 L2,
  forward_simulation ccA ccB L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation ccA ccB L1 L2.
Proof.
  intros until L2. intros FS L1_receptive L2_determinate.
  destruct FS as [[index order match_states Hskel FS order_wf]].
  set (ms se1 se2 w := f2b_match_states (L1 se1) (L2 se2) (match_states := match_states se1 se2 w)).
  constructor.
  eapply Backward_simulation with f2b_order ms; auto using wf_f2b_order.
  intros se1 se2 wB Hse Hse1.
  specialize (FS se1 se2 wB Hse Hse1).
  specialize (L1_receptive se1). specialize (L2_determinate se2).
  split.
- (* valid queries *)
  eapply fsim_match_valid_query; eauto.
- split.
  (* initial states exist *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2 [A B]]].
  exists s2; auto.
  (* initial states *)
  intros. exploit (fsim_match_initial_states FS); eauto. intros [i [s2' [A B]]].
  assert (s2 = s2') by (eapply sd_initial_determ; eauto). subst s2'.
  exists s1; split; auto. exists (F2BI_after O). econstructor; eauto.
- (* final states *)
  intros. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS.
  assert (r0 = r2) by eauto using sd_final_determ; subst. eauto using star_refl.
  eelim sd_final_noext; eauto.
  inv H4. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H5. congruence. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
  inv H2. exploit (sd_final_nostep L2_determinate); eauto. contradiction.
- (* external states *)
  intros. inv H.
  + exploit @f2b_progress; eauto.
    intros TRANS; inv TRANS.
    * eelim (sd_final_noext L2_determinate); eauto.
    * assert (q0 = q2) by eauto using sd_at_external_determ; subst.
      exists wA, s1', q1. intuition auto. split.
      intros. edestruct H7 as (j & s2' & Hs2' & Hs'); eauto.
      intros. edestruct H7 as (j & s2' & Hs2' & Hs'); eauto.
      assert (s3 = s2') by eauto using sd_after_external_determ; subst.
      exists s0. intuition auto.
      exists (F2BI_after O). econstructor; eauto.
    * inv H4. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H5. congruence. eelim (sd_at_external_nostep L2_determinate); eauto.
  + inv H2. eelim (sd_at_external_nostep L2_determinate); eauto.
- (* progress *)
  intros. inv H.
  exploit @f2b_progress; eauto. intros TRANS; inv TRANS; eauto.
  inv H3. eauto.
  inv H4. congruence. eauto.
  inv H1. eauto.
- (* simulation *)
  eapply f2b_simulation_step; eauto.
Qed.

(** * Transforming a semantics into a single-event, equivalent semantics *)

Definition well_behaved_traces {liA liB} (L: semantics liA liB) : Prop :=
  forall se s t s', Step (L se) s t s' ->
  match t with nil => True | ev :: t' => output_trace t' end.

Section ATOMIC.

Context {liA liB} (L: semantics liA liB).

Hypothesis Lwb: well_behaved_traces L.

Inductive atomic_step se (ge: genvtype (L se)): (trace * state L) -> trace -> (trace * state L) -> Prop :=
  | atomic_step_silent: forall s s',
      Step (L se) s E0 s' ->
      atomic_step se ge (E0, s) E0 (E0, s')
  | atomic_step_start: forall s ev t s',
      Step (L se) s (ev :: t) s' ->
      atomic_step se ge (E0, s) (ev :: nil) (t, s')
  | atomic_step_continue: forall ev t s,
      output_trace (ev :: t) ->
      atomic_step se ge (ev :: t, s) (ev :: nil) (t, s).

Definition atomic : semantics liA liB :=
{|
  skel := skel L;
  state := trace * state L;
  (* memory_of_state := fun s => (memory_of_state L) (snd s); *)
  activate se := {|
    genvtype := genvtype (L se);
    step := atomic_step se;
    valid_query := valid_query (L se);
    initial_state q s := initial_state (L se) q (snd s) /\ fst s = E0;
    at_external s q := at_external (L se) (snd s) q /\ fst s = E0;
    after_external s r s' := after_external (L se) (snd s) r (snd s') /\ fst s' = E0;
    final_state s r := final_state (L se) (snd s) r /\ fst s = E0;
    globalenv := globalenv (L se);
  |};
|}.

End ATOMIC.

(** A forward simulation from a semantics [L1] to a single-event semantics [L2]
  can be "factored" into a forward simulation from [atomic L1] to [L2]. *)

Section FACTOR_FORWARD_SIMULATION.

Context {liA1 liB1} (L1: semantics liA1 liB1).
Context {liA2 liB2} (L2: semantics liA2 liB2).

Section LTS.
Context {ccA ccB} (FS: fsim_components ccA ccB L1 L2).
Hypothesis L2single: forall se, single_events (L2 se).
Context se1 se2 w (Hse: match_senv ccB w se1 se2) (Hse1: Genv.valid_for (skel L1) se1).
Let sim := fsim_lts FS se2 w Hse Hse1.

Inductive ffs_match: fsim_index FS -> (trace * state L1) -> state L2 -> Prop :=
  | ffs_match_at: forall i s1 s2,
      fsim_match_states FS se1 se2 w i s1 s2 ->
      ffs_match i (E0, s1) s2
  | ffs_match_buffer: forall i ev t s1 s2 s2',
      Star (L2 se2) s2 (ev :: t) s2' -> fsim_match_states FS se1 se2 w i s1 s2' ->
      ffs_match i (ev :: t, s1) s2.

Lemma star_non_E0_split':
  forall se2 s2 t s2', Star (L2 se2) s2 t s2' ->
  match t with
  | nil => True
  | ev :: t' => exists s2x, Plus (L2 se2) s2 (ev :: nil) s2x /\ Star (L2 se2) s2x t' s2'
  end.
Proof.
  induction 1. simpl. auto.
  exploit L2single; eauto. intros LEN.
  destruct t1. simpl in *. subst. destruct t2. auto.
  destruct IHstar as [s2x [A B]]. exists s2x; split; auto.
  eapply plus_left. eauto. apply plus_star; eauto. auto.
  destruct t1. simpl in *. subst t. exists s2; split; auto. apply plus_one; auto.
  simpl in LEN. extlia.
Qed.

Lemma ffs_simulation:
  forall s1 t s1', Step (atomic L1 se1) s1 t s1' ->
  forall i s2, ffs_match i s1 s2 ->
  exists i', exists s2',
     (Plus (L2 se2) s2 t s2' \/ (Star (L2 se2) s2 t s2') /\ fsim_order FS i' i)
  /\ ffs_match i' s1' s2'.
Proof.
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  exists i'; exists s2'; split. auto. constructor; auto.
- (* start step *)
  inv H0.
  exploit (fsim_simulation sim); eauto.
  intros [i' [s2' [A B]]].
  destruct t as [ | ev' t].
+ (* single event *)
  exists i'; exists s2'; split. auto. constructor; auto.
+ (* multiple events *)
  assert (C: Star (L2 se2) s2 (ev :: ev' :: t) s2'). intuition. apply plus_star; auto.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  exists i'; exists s2x; split. auto. econstructor; eauto.
- (* continue step *)
  inv H0.
  exploit star_non_E0_split'. eauto. simpl. intros [s2x [P Q]].
  destruct t.
  exists i; exists s2'; split. left. eapply plus_star_trans; eauto. constructor; auto.
  exists i; exists s2x; split. auto. econstructor; eauto.
Qed.

End LTS.

Theorem factor_forward_simulation {ccA ccB}:
  forward_simulation ccA ccB L1 L2 ->
  (forall se, single_events (L2 se)) ->
  forward_simulation ccA ccB (atomic L1) L2.
Proof.
  intros [FS] L2single. constructor.
  apply Forward_simulation with (fsim_order FS) (ffs_match FS); cbn; try apply FS.
  intros se1 se2 wB Hse Hse1. pose (sim := fsim_lts FS se2 wB Hse Hse1). split; cbn.
- (* valid query *)
  cbn. eapply fsim_match_valid_query; eauto.
- (* initial states *)
  intros. destruct s1 as [t1 s1]. simpl in H0. destruct H0. subst.
  exploit (fsim_match_initial_states sim); eauto. intros [i [s2 [A B]]].
  exists i; exists s2; split; auto. constructor; auto.
- (* final states *)
  intros. destruct s1 as [t1 s1]. simpl in H0; destruct H0; subst. inv H.
  eapply (fsim_match_final_states sim); eauto.
- (* external states *)
  intros i [t1 s1] s2 q1 Hs [Hq1 Ht1]. cbn in *. subst. inv Hs.
  edestruct @fsim_match_external as (wA & q2 & Hq2 & Hq & Hse' & Hk); eauto.
  exists wA, q2. repeat apply conj; auto.
  intros r1 r2 [t s1'] Hr [Hs1' Ht]. cbn in *. subst.
  edestruct Hk as (i' & s2' & Hs2' & Hs'); eauto.
  exists i', s2'. split; auto. constructor; auto.
- (* simulation *)
  eapply ffs_simulation; eauto.
Qed.

End FACTOR_FORWARD_SIMULATION.

(** Likewise, a backward simulation from a single-event semantics [L1] to a semantics [L2]
  can be "factored" as a backward simulation from [L1] to [atomic L2]. *)

Section FACTOR_BACKWARD_SIMULATION.

Context {liA1 liB1} (L1: semantics liA1 liB1).
Context {liA2 liB2} (L2: semantics liA2 liB2).

Section LTS.
Context {ccA ccB} (BS: bsim_components ccA ccB L1 L2).
Hypothesis L1single: forall se, single_events (L1 se).
Hypothesis L2wb: well_behaved_traces L2.
Context se1 se2 w (Hse: match_senv ccB w se1 se2) (Hse1: Genv.valid_for (skel L1) se1).
Let sim := bsim_lts BS se2 w Hse Hse1.

Inductive fbs_match: bsim_index BS -> state L1 -> (trace * state L2) -> Prop :=
  | fbs_match_intro: forall i s1 t s2 s1',
      Star (L1 se1) s1 t s1' -> bsim_match_states BS se1 se2 w i s1' s2 ->
      t = E0 \/ output_trace t ->
      fbs_match i s1 (t, s2).

Lemma fbs_simulation:
  forall s2 t s2', Step (atomic L2 se2) s2 t s2' ->
  forall i s1, fbs_match i s1 s2 -> safe (L1 se1) s1 ->
  exists i', exists s1',
     (Plus (L1 se1) s1 t s1' \/ (Star (L1 se1) s1 t s1' /\ bsim_order BS i' i))
     /\ fbs_match i' s1' s2'.
Proof.
  induction 1; intros.
- (* silent step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  exists i'; exists s1''; split.
  destruct A as [P | [P Q]]. left. eapply star_plus_trans; eauto. right; split; auto. eapply star_trans; eauto.
  econstructor. apply star_refl. auto. auto.
- (* start step *)
  inv H0.
  exploit (bsim_simulation sim); eauto. eapply star_safe; eauto.
  intros [i' [s1'' [A B]]].
  assert (C: Star (L1 se1) s1 (ev :: t) s1'').
    eapply star_trans. eauto. destruct A as [P | [P Q]]. apply plus_star; eauto. eauto. auto.
  exploit @star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i'; exists s1x; split.
  left; auto.
  econstructor; eauto.
  exploit L2wb; eauto.
- (* continue step *)
  inv H0. unfold E0 in H8; destruct H8; try congruence.
  exploit @star_non_E0_split'; eauto. simpl. intros [s1x [P Q]].
  exists i; exists s1x; split. left; auto. econstructor; eauto. simpl in H0; tauto.
Qed.

Lemma fbs_progress:
  forall i s1 s2,
  fbs_match i s1 s2 -> safe (L1 se1) s1 ->
  (exists r, final_state (atomic L2 se2) s2 r) \/
  (exists q, at_external (atomic L2 se2) s2 q) \/
  (exists t, exists s2', Step (atomic L2 se2) s2 t s2').
Proof.
  intros. inv H. destruct t.
- (* 1. no buffered events *)
  exploit (bsim_progress sim); eauto. eapply star_safe; eauto.
  intros [[r A] | [[q A] | [t [s2' A]]]].
+ (* final state *)
  left; exists r; simpl; auto.
+ (* external state *)
  cbn. eauto.
+ (* L2 can step *)
  destruct t.
  right; right; exists E0; exists (nil, s2'). constructor. auto.
  right; right; exists (e :: nil); exists (t, s2'). constructor. auto.
- (* 2. some buffered events *)
  unfold E0 in H3; destruct H3. congruence.
  right; right; exists (e :: nil); exists (t, s3). constructor. auto.
Qed.

End LTS.

Theorem factor_backward_simulation {ccA ccB}:
  backward_simulation ccA ccB L1 L2 ->
  (forall se, single_events (L1 se)) ->
  well_behaved_traces L2 ->
  backward_simulation ccA ccB L1 (atomic L2).
Proof.
  intros [BS] L1single L2wb. constructor.
  apply Backward_simulation with (bsim_order BS) (fbs_match BS); cbn; try apply BS.
  intros se1 se2 wB Hse Hse1. pose (sim := bsim_lts BS se2 wB Hse Hse1).
  split; try apply sim; cbn.
- (* initial states *)
  intros q1 q2 Hq.
  edestruct (bsim_match_initial_states sim) as [He Hm]; eauto. split.
  + intros. exploit He; eauto. intros [s2 A].
    exists (E0, s2). simpl; auto.
  + intros. destruct s2 as [t s2]; simpl in H0; destruct H0; subst.
    exploit Hm; eauto. intros (s1' & A & i & B).
    exists s1'; split. auto. exists i. econstructor. apply star_refl. auto. auto.
- (* final states match *)
  intros. destruct s2 as [t s2]; simpl in H1; destruct H1; subst.
  inv H. exploit (bsim_match_final_states sim); eauto. eapply star_safe; eauto.
  intros (s1'' & r & A & B & ?).
  exists s1'', r; split; auto. eapply star_trans; eauto.
- (* external states *)
  intros i s1 [s2 t2] q2 Hs Hs1 [Hq2 Ht2]. cbn in *; subst. inv Hs.
  edestruct (bsim_match_external sim) as (wA & s1'' & q1 & Hs1'' & Hq1 & Hq & Hse' & Hk);
    eauto using star_safe.
  exists wA, s1'', q1. repeat apply conj; auto.
  + eapply star_trans; eauto.
  + intros r1 r2 Hr. edestruct Hk as [He Hm]; eauto. split.
    * intros. edestruct He; eauto. exists (E0, x); auto.
    * intros ns1 [nt2 ns2] Hns1 [Hns2 Hnt2]. cbn in *; subst.
      edestruct Hm as (? & ? & ? & ?); eauto. eexists; split; eauto. eexists.
      econstructor; eauto using star_refl.
- (* progress *)
  eapply fbs_progress; eauto.
- (* simulation *)
  eapply fbs_simulation; eauto.
Qed.

End FACTOR_BACKWARD_SIMULATION.

(** Receptiveness of [atomic L]. *)

Record strongly_receptive {liA liB} (L: semantics liA liB): Prop :=
  Strongly_receptive {
    ssr_receptive: forall se s ev1 t1 s1 ev2,
      Step (L se) s (ev1 :: t1) s1 ->
      match_traces se (ev1 :: nil) (ev2 :: nil) ->
      exists s2, exists t2, Step (L se) s (ev2 :: t2) s2;
    ssr_well_behaved:
      well_behaved_traces L
  }.

Theorem atomic_receptive {liA liB} (L: semantics liA liB):
  strongly_receptive L -> receptive (atomic L).
Proof.
  intros. constructor; intros.
(* receptive *)
  inv H0.
  (* silent step *)
  inv H1. exists (E0, s'). constructor; auto.
  (* start step *)
  assert (exists ev2, t2 = ev2 :: nil). inv H1; econstructor; eauto.
  destruct H0 as [ev2 EQ]; subst t2.
  exploit @ssr_receptive; eauto. intros [s2 [t2 P]].
  exploit @ssr_well_behaved. eauto. eexact P. simpl; intros Q.
  exists (t2, s2). constructor; auto.
  (* continue step *)
  simpl in H2; destruct H2.
  assert (t2 = ev :: nil). inv H1; simpl in H0; tauto.
  subst t2. exists (t, s0). constructor; auto. simpl; auto.
(* single-event *)
  red. intros. inv H0; simpl; lia.
Qed.

(** * Connections with big-step semantics *)

(** The general form of a big-step semantics *)

Record bigstep_semantics : Type :=
  Bigstep_semantics {
    bigstep_terminates: trace -> int -> Prop;
    bigstep_diverges: traceinf -> Prop
  }.

(** Soundness with respect to a small-step semantics *)

Definition load {liA liB} (L: semantics liA liB): lts liA liB (state L) :=
  L (Genv.symboltbl (skel L)).

Record bigstep_sound (B: bigstep_semantics) (L: semantics li_null li_wp) : Prop :=
  Bigstep_sound {
    bigstep_terminates_sound:
      forall t r,
      bigstep_terminates B t r ->
      exists s1, exists s2, initial_state (load L) tt s1 /\ Star (load L) s1 t s2 /\ final_state (load L) s2 r;
    bigstep_diverges_sound:
      forall T,
      bigstep_diverges B T ->
      exists s1, initial_state (load L) tt s1 /\ forever (step (load L)) (globalenv (load L)) s1 T
}.
