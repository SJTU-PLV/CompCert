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

Variable valid_wB : ccworld ccB -> Prop.

Lemma Hvalid : Genv.valid_for (skel s1) se1.
Proof. apply initial_valid_for. Qed.

(** The construction of initial world *)
(* Variable wB : ccworld ccB.
 
Hypothesis Hmatch_senv : match_senv ccB wB se1 se2. *)

Section FORWARD.

Hypothesis Hmatch_query_forward : forall q1,      
    query1 q1 ->
    exists wB q2, match_query ccB wB q1 q2 /\
               match_senv ccB wB se1 se2 /\
               query2 q2 /\ valid_wB wB.
  
Hypothesis Hmatch_reply_forward : forall r r1 r2 wB,
  match_reply ccB wB r1 r2 -> valid_wB wB ->
  reply1 r r1 -> reply2 r r2.

Lemma close_sound_forward :
  Smallstep.forward_simulation ccA ccB s1 s2 -> forward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.forward_simulation in open_simulation.
  inv open_simulation. inv X.
  (* specialize (fsim_lts se1 se2 wB Hmatch_senv Hvalid). inv fsim_lts. *)
  unfold L1, L2, close_semantics.
  econstructor.
  instantiate (1:= fun i s1 s2 => exists wB,
                       fsim_match_states se1 se2 wB i s1 s2 /\ match_senv ccB wB se1 se2 /\ valid_wB wB).
  econstructor; simpl; eauto.
  - (* initial *)
    intros s1' [q1 [q1valid INI]]. exploit Hmatch_query_forward; eauto.
    intros (wB & q2 & MQ & MS & q2valid & wBvalid).
    specialize (fsim_lts se1 se2 wB MS Hvalid). inv fsim_lts.
    exploit fsim_match_initial_states0; eauto.
    intros (i & s2' & INI' & FM).
    do 2 eexists. split; simpl; eauto.
  - (* match final state *)
    intros i s1' s2' r [wB [Mstate [MS Hw]]] (r1 & R1 & FINAL).
    specialize (fsim_lts se1 se2 wB MS Hvalid). inv fsim_lts.
    exploit fsim_match_final_states0; eauto. intros (r2 & FINAL' & MATCH_REPLY).
    eexists. split; eauto.
  - intros s1' t s1'' STEP i s2' [wB [Mstate [MS Hw]]].
    specialize (fsim_lts se1 se2 wB MS Hvalid). inv fsim_lts.
    exploit fsim_simulation0; eauto. intros (i' & s2'' & STEP' & MS').
    exists i'. eexists. split; eauto.
  - unfold se. rewrite fsim_skel. reflexivity.
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
    query1 q1 -> exists wB q2,
      match_query ccB wB q1 q2
      /\ match_senv ccB wB se1 se2 
      /\ query2 q2 /\ valid_wB wB.

(** for bsim_match_initial_states  *)
Hypothesis Hmatch_query_backward2 : forall q1 q2,
    query1 q1 -> query2 q2 -> exists wB,
        match_query ccB wB q1 q2 /\ match_senv ccB wB se1 se2 /\ valid_wB wB.

(** source determinacy at interface, for getting the return value from [safe] property *)

Hypothesis source_determinate_big: determinate_big s1.

Hypothesis Hmatch_reply_backward : forall rv1 rv2 r1 r2 wB,
  match_reply ccB wB r1 r2 -> valid_wB wB ->
  reply2 rv2 r2 -> reply1 rv1 r1 -> rv2 = rv1.

Lemma star_internal : forall {li1 li2} (lts1: Smallstep.semantics li1 li2) s1 s1' Pq Pr,
    star (Smallstep.step (lts1 (se lts1))) (Smallstep.globalenv (lts1 (se lts1))) s1 E0 s1' ->
    Star (close_semantics lts1 Pq Pr) s1 E0 s1'.
Proof.
  intros. induction H.
  - eapply star_refl.
  - eapply star_step; eauto.
Qed.

Lemma close_sound_backward:
  Smallstep.backward_simulation ccA ccB s1 s2 -> backward_simulation L1 L2.
Proof.
  intro open_simulation.
  unfold Smallstep.backward_simulation in open_simulation.
  inv open_simulation. inv X.
  (* specialize (bsim_lts se1 se2 wB Hmatch_senv Hvalid).
  inv bsim_lts. *)
  unfold L1, L2, close_semantics.
  econstructor.
  instantiate (1:= fun i s1 s2 => exists wB,
                       bsim_match_states se1 se2 wB i s1 s2 /\ match_senv ccB wB se1 se2 /\ valid_wB wB).
  (* specialize (bsim_match_initial_states0 _ _ Hmatch_query). *)
  (* inv bsim_match_initial_states0. *)
  econstructor; simpl; simpl; eauto.
  - intros s1' [q1 [q1valid INI1]]. exploit Hmatch_query_backward1; eauto.
    intros [wB [q2 [Hq [Hs [q2valid Hw]]]]].
    specialize (bsim_lts se1 se2 wB Hs Hvalid).
    inv bsim_lts.
    exploit bsim_match_initial_states0; eauto.
    intros HH. inv HH. exploit bsim_match_cont_exist; eauto.
    intros [s2' A]. exists s2', q2. split; eauto.
  - intros s1' s2' [q1 [q1valid INI1]] [q2 [q2valid INI2]].
    exploit Hmatch_query_backward2; eauto. intros [wB [Hmatch [Hs Hw]]].
    specialize (bsim_lts se1 se2 wB Hs Hvalid).
    inv bsim_lts.
    exploit bsim_match_initial_states0; eauto.
    intro HH. inv HH. exploit bsim_match_cont_match; eauto.
    intros (s1'' & A& B). inv B. exists x, s1''.
    split; eauto.
  - (*final states*)
    intros. apply safe_sound_1 in H0 as Hsafeo.
    destruct H1 as (r0 & REPLY & FS).
    destruct H as [wB [H [Hs Hw]]].
    specialize (bsim_lts se1 se2 wB Hs Hvalid).
    inv bsim_lts.
    specialize (bsim_match_final_states0 _ _ _ _ H Hsafeo FS) as (s1' & r1 & STAR & FS' & MS).
    exists s1'. split. eauto. exploit H0.
    eapply star_internal. eauto. simpl. specialize (source_determinate_big se1) as Hdet. 
    intros [[r2 Hr]|Hs'].
    + destruct Hr as [r1' [Hret1 Hf1]].
      inv Hdet. exploit sd_big_final_determ. apply FS'. apply Hf1. intro. subst r1'.
      exploit Hmatch_reply_backward; eauto. intro. subst r2. eauto.
    + destruct Hs' as [t [s'' Hs1']].
      inv Hdet. exfalso. eapply sd_big_final_nostep; eauto.
  - (* progress *)
    intros. apply safe_sound_1 in H0.
    destruct H as [wB [H [Hs Hw]]].
    specialize (bsim_lts se1 se2 wB Hs Hvalid).
    inv bsim_lts.
    pose proof (progress := bsim_progress0).
    specialize (bsim_progress0 _ _ _ H H0) as [(r & FS)|[|]].
    left. destruct (reply_sound2 _ _ FS) as (ri & REPLY). eauto.
    destruct H1. exfalso. eapply closed2; eauto. eapply open_progress'; eauto.
    auto.
  - (* simulation *)
    intros. apply safe_sound_1 in H1.
    destruct H0 as [wB [H0 [Hs Hw]]].
    specialize (bsim_lts se1 se2 wB Hs Hvalid).
    inv bsim_lts. simpl.
    exploit bsim_simulation0; eauto.
    intros (i' & s1' & A & B).
    exists i', s1'. split; eauto.
  - unfold se. rewrite bsim_skel. reflexivity.
Qed.

End BACKWARD.

End CLOSE_SOUND.
