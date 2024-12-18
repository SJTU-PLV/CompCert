Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import Values Maps Memory AST.
Require Import LanguageInterface.
Require Import Integers.
Require Import Smallstep SmallstepClosed.

Set Implicit Arguments.

(** This file defines the "Loading" process which transforms an open semantics
 into a closed semantics alongwith the preservation of open simulations into closed simulations *)

(* Closing open semantics. *)
Import Closed.

Theorem initial_valid_for : forall skel,
    Genv.valid_for skel (Genv.symboltbl skel).
Proof.
  intros. red. intros. rewrite Genv.find_info_symbol in H. destruct H as (b & []).
  exists b, g. split; auto. split; auto.
  destruct g; constructor. constructor.
  destruct v. constructor; constructor.
Qed.

Section CLOSE_SEMANTICS.

Variable liA liB : language_interface.

(** The open semantics *)
Variable s : Smallstep.semantics liA liB.

(** We use the [skel] from open semantics for initial symbol table *)
Definition se := Genv.symboltbl (skel s).

(** Predicate on the initial_query, usually it is for [main] function *)  
Variable query : query liB -> Prop.

(** Predicate between the reply for liB and the return value for [main] funciton *)
Variable reply : int -> reply liB -> Prop.

Definition close_semantics : semantics :=
  let lts := Smallstep.activate s se in
  {|
    state := Smallstep.state s;
    genvtype := Smallstep.genvtype lts;
    step := Smallstep.step lts;
    initial_state := fun state => exists q, query q /\ Smallstep.initial_state lts q state;
    final_state := fun state retval => exists r, reply retval r /\ Smallstep.final_state lts state r;
    globalenv := Smallstep.globalenv lts;
    symbolenv := se;
  |}.

End CLOSE_SEMANTICS.

Section CLOSE_SOUND.
  
Variable liA1 liB1 : language_interface.
Variable query1 : query liB1 -> Prop.
Variable reply1 : int -> reply liB1 -> Prop.
Variable s1 : Smallstep.semantics liA1 liB1.
Let se1 := Genv.symboltbl (skel s1).

Definition lts1 := (Smallstep.activate s1 se1).
Definition L1 := close_semantics s1 query1 reply1.

Variable liA2 liB2 : language_interface.
Variable query2 : query liB2 -> Prop.
Variable reply2 : int -> reply liB2 -> Prop.
Variable s2 : Smallstep.semantics liA2 liB2.
Let se2 := Genv.symboltbl (skel s2).

Definition lts2 := (Smallstep.activate s2 se2).
Definition L2 := close_semantics s2 query2 reply2.

Variable ccA : callconv liA1 liA2.
Variable ccB : callconv liB1 liB2.

Lemma Hvalid : Genv.valid_for (skel s1) se1.
Proof. apply initial_valid_for. Qed.

(** The construction of initial world *)
Variable wB : ccworld ccB.

Hypothesis Hmatch_senv : match_senv ccB wB se1 se2.

Section FORWARD.

Hypothesis Hmatch_query_forward : forall q1,      
    query1 q1 ->
    exists q2, match_query ccB wB q1 q2 /\ query2 q2.
  
Hypothesis Hmatch_reply_forward : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply1 r r1 -> reply2 r r2.

Lemma close_sound_forward :
  Smallstep.forward_simulation ccA ccB s1 s2 -> forward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.forward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (fsim_lts se1 se2 wB Hmatch_senv Hvalid). inv fsim_lts.
  unfold L1, L2, close_semantics.
  do 2 econstructor; simpl; eauto.
  - (* initial *)
    intros s1' [q1 [q1valid INI]]. exploit Hmatch_query_forward; eauto.
    intros [q2 [MATCH_QUERT q2valid]].
    exploit fsim_match_initial_states0; eauto.
    intros (i & s2' & INI' & FM).
    do 2 eexists. split; eauto.
  - (* match final state *)
    intros i s1' s2' r MS (r1 & R1 & FINAL).
    exploit fsim_match_final_states0; eauto. intros (r2 & FINAL' & MATCH_REPLY).
    eexists. split; eauto.
  - eapply match_senv_public_preserved; eauto.
Qed.

End FORWARD.

Section BACKWARD.

Lemma safe_sound_1:
  forall s, safe L1 s -> Smallstep.safe lts1 s.
Proof.
  unfold safe, Smallstep.safe, L1, lts1, close_semantics. simpl. intros.
  specialize (H _ H0) as [(r & r0 & REPLY & FS)|(t & s'' & STEP)]; eauto.
Qed.


Hypothesis closed2 : forall s q, Smallstep.safe lts2 s -> ~ at_external lts2 s q.

Hypothesis reply_sound2: forall s r, Smallstep.final_state lts2 s r -> exists i, reply2 i r.

(** for bsim_initial_states_exists *)
Hypothesis Hmatch_query_backward1 : forall q1,      
    query1 q1 -> exists q2, match_query ccB wB q1 q2 /\ query2 q2.

(** for bsim_match_initial_states  *)
Hypothesis Hmatch_query_backward2 : forall q1 q2,
    query1 q1 -> query2 q2 -> match_query ccB wB q1 q2.

Hypothesis Hmatch_reply_backward : forall r r1 r2,
  match_reply ccB wB r1 r2 ->
  reply2 r r2 -> reply1 r r1.

Lemma close_sound_backward:
  Smallstep.backward_simulation ccA ccB s1 s2 -> backward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.backward_simulation in open_simulation.
  inv open_simulation. inv X.
  specialize (bsim_lts se1 se2 wB Hmatch_senv Hvalid).
  inv bsim_lts.
  unfold L1, L2, close_semantics.
  (* specialize (bsim_match_initial_states0 _ _ Hmatch_query). *)
  (* inv bsim_match_initial_states0. *)
  do 2 econstructor; simpl; simpl; eauto.
  - intros s1' [q1 [q1valid INI1]]. exploit Hmatch_query_backward1; eauto.
    intros [q2 [Hm q2valid]]. exploit bsim_match_initial_states0; eauto.
    intros HH. inv HH. exploit bsim_match_cont_exist; eauto.
    intros [s2' A]. exists s2', q2. split; eauto.
  - intros s1' s2' [q1 [q1valid INI1]] [q2 [q2valid INI2]].
    exploit Hmatch_query_backward2; eauto. intro Hmatch.
    exploit bsim_match_initial_states0; eauto.
    intro HH. inv HH. exploit bsim_match_cont_match; eauto.
    intros (s1'' & A& B). inv B. exists x, s1''.
    split; eauto.
  - (*final states*)
  intros. apply safe_sound_1 in H0. destruct H1 as (r0 & REPLY & FS).
  specialize (bsim_match_final_states0 _ _ _ _ H H0 FS) as (s1' & r1 & STAR & FS' & MS).
  exists s1'. split; eauto.
  - (* progress *)
  intros. apply safe_sound_1 in H0.
  pose proof (progress := bsim_progress0).
  specialize (bsim_progress0 _ _ _ H H0) as [(r & FS)|[|]].
  left. destruct (reply_sound2 _ _ FS) as (ri & REPLY). eauto.
  destruct H1. exfalso. eapply closed2; eauto. eapply open_progress'; eauto.
  auto.
  - (* simulation *)
  intros. apply safe_sound_1 in H1.
  eapply bsim_simulation0; eauto.
  - eapply  match_senv_public_preserved; eauto.
Qed.

End BACKWARD.

End CLOSE_SOUND.