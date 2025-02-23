Require Import Values.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Smallstep.

(** Simulation proofs sometimes rely on invariants of the source
  and/or target languages, such as type preservation. The
  constructions defined below can be used to decouple these
  preservation and simulation proofs, and to introduce calling
  conventions characterizing the invariant at module boundaries. *)


(** * Invariants *)

(** ** Interface *)

(** First, we need to define a sort of "invariant interface", which
  will describe how a given invariant impacts the queries and replies
  of the language under consideration. *)

Record invariant {li: language_interface} :=
  {
    inv_world : Type;
    symtbl_inv : inv_world -> Genv.symtbl -> Prop;
    query_inv : inv_world -> query li -> Prop;
    reply_inv : inv_world -> reply li -> Prop;
  }.

Arguments invariant : clear implicits.

(** As a core example, here is an invariant for the C language
  interface asserting that the queries and replies are well-typed. *)

Definition wt_c : invariant li_c :=
  {|
    symtbl_inv :=
      fun '(se, sg) => eq se;
    query_inv :=
      fun '(se, sg) q =>
        sg = cq_sg q /\ Val.has_type_list (cq_args q) (sig_args sg);
    reply_inv :=
      fun '(se, sg) r =>
        Val.has_type (cr_retval r) (proj_sig_res sg);
  |}.

(** ** Preservation *)

(** A small step semantics preserves an externally observable
  invariant if the following properties hold. In addition to the
  invariant interfaces for the incoming function call ([IB]) and any
  outgoing external calls ([IA]), we specify a "state invariant" [IS]
  which will be estblished by the initial query and external call
  returns, preserved by internal steps, and ensure the invariant
  interface is respected at external calls and final states. *)

Record lts_preserves {liA liB S} se (L: lts liA liB S) IA IB (IS: _ -> S -> Prop) w :=
  {
    preserves_step s t s':
      IS w s ->
      Step L s t s' ->
      IS w s';
    preserves_initial_state q s:
      query_inv IB w q ->
      initial_state L q s ->
      IS w s;
    preserves_external s q:
      IS w s -> at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
      forall r s', reply_inv IA wA r -> after_external L s r s' -> IS w s';
    preserves_final_state s r:
      IS w s ->
      final_state L s r ->
      reply_inv IB w r;
  }.

Definition preserves {liA liB} (L: semantics liA liB) (IA IB: invariant _) IS :=
  forall w se,
    Genv.valid_for (skel L) se ->
    symtbl_inv IB w se ->
    lts_preserves se (L se) IA IB IS w.

(** ** As calling conventions *)

(** Invariant interfaces are essentially a unary version of calling
  conventions, and can in fact be lifted into actual, binary calling
  conventions asserting that the source and target queries are
  identical, and furthermore satisfy the given invariant. *)

Inductive rel_inv {A} (I: A -> Prop) (x: A): A -> Prop :=
  rel_inv_intro: I x -> rel_inv I x x.

Program Coercion cc_inv {li} (I: invariant li): callconv li li :=
  {|
    ccworld := inv_world I;
    match_senv w := rel_inv (symtbl_inv I w);
    match_query w := rel_inv (query_inv I w);
    match_reply w := rel_inv (reply_inv I w);
  |}.
Solve All Obligations with
  cbn; try split; intros; destruct H; auto.

(** With this, an invariant preservation proof can itself be lifted
  into a self-simulation by the invariant calling conventions. *)

Lemma preserves_fsim {li res} (L: semantics li res) IA IB IS:
  preserves L IA IB IS ->
  forward_simulation (cc_inv IA) (cc_inv IB) L L.
Proof.
  fsim (eapply forward_simulation_step with (match_states := rel_inv (IS w));
        destruct Hse; subst).
  - reflexivity.
  - destruct 1. auto.
  - intros q _ s [Hq] Hs.
    exists s. split; eauto.
    constructor.
    eapply preserves_initial_state; eauto.
  - intros s _ r [Hs] Hr.
    exists r. split; eauto.
    constructor.
    eapply preserves_final_state; eauto.
  - intros s _ q [Hs] Hq.
    edestruct @preserves_external as (wA & Hse & HqA & Hr); eauto.
    exists wA, q. repeat apply conj; cbn; eauto.
    + constructor. auto.
    + constructor. auto.
    + intros r' _ s' [Hr'] Hs'.
      exists s'. split; eauto.
      constructor.
      eapply Hr; eauto.
  - intros s t s' Hstep _ [Hs].
    exists s'. split; eauto.
    constructor.
    eapply preserves_step; eauto.
Qed.

(** * Calling conventions as invariants *)

Definition invcc {liA liB} (IA: invariant liA) (cc: callconv liA liB) : invariant liB :=
  {|
    inv_world := (inv_world IA * ccworld cc);
    symtbl_inv '(wA, wcc) se2 := exists se1, symtbl_inv IA wA se1
                                        /\ match_senv cc wcc se1 se2;
    query_inv '(wA, wcc) q2 := exists q1, query_inv IA wA q1
                                     /\ match_query cc wcc q1 q2; 
    reply_inv '(wA, wcc) r2 := exists r1, reply_inv IA wA r1 /\ match_reply cc wcc r1 r2;
  |}.

Definition ccinv {liA liB} (cc: callconv liA liB) (IB: invariant liB) : invariant liA :=
  {|
    inv_world := (ccworld cc * inv_world IB);
    symtbl_inv '(wcc, wB) se1 := exists se2, symtbl_inv IB wB se2
                                        /\ match_senv cc wcc se1 se2;
    query_inv '(wcc, wB) q1 := exists q2, query_inv IB wB q2
                                     /\ match_query cc wcc q1 q2; 
    reply_inv '(wcc, wB) r1 := exists r2, reply_inv IB wB r2 /\ match_reply cc wcc r1 r2;
  |}.


Definition invcc_in {liA liB} (IA: invariant liA) (cc: callconv liA liB) : invariant liB :=
  {|
    inv_world := (inv_world IA * ccworld cc);
    symtbl_inv '(wA, wcc) se2 := exists se1, symtbl_inv IA wA se1
                                        /\ match_senv cc wcc se1 se2;
    query_inv '(wA, wcc) q2 := exists q1, query_inv IA wA q1
                                     /\ match_query cc wcc q1 q2; 
    reply_inv '(wA, wcc) r2 := exists r1, reply_inv IA wA r1 /\ match_reply cc wcc r1 r2;
  |}.


Definition invcc_out {liA liB} (IA: invariant liA) (cc: callconv liA liB) : invariant liB :=
  {|
    inv_world := inv_world IA;
    symtbl_inv wA se2 := exists se1 wcc, symtbl_inv IA wA se1
                                    /\ match_senv cc wcc se1 se2;
    query_inv wA q2 := forall w q1, match_query cc w q1 q2 ->
                               query_inv IA wA q1;
    (* A requirement for target incoming reply? It is equivalent to a
    requirement for outgoing reply of the linked module *)
    reply_inv _ r2 :=  forall w wA q1 q2, match_query cc w q1 q2 ->
                                     query_inv IA wA q1 ->
                                     exists r1, match_reply cc w r1 r2
                                           /\ reply_inv IA wA r1;
  |}.

(** Compose two invariants *)
Definition inv_compose {li} (I1 I2: invariant li) : invariant li :=
  {|
    inv_world := (inv_world I1 * inv_world I2);
    symtbl_inv '(w1, w2) se := symtbl_inv I1 w1 se /\ symtbl_inv I2 w2 se;
    query_inv '(w1, w2) q := query_inv I1 w1 q /\ query_inv I2 w2 q;
    reply_inv '(w1, w2) r := reply_inv I1 w1 r /\ reply_inv I2 w2 r;
  |}.

Definition inv_sum {li} (I1 I2: invariant li) : invariant li :=
  {|
    inv_world := (inv_world I1 + inv_world I2);
    symtbl_inv w se := match w with
                       | inl w1 => symtbl_inv I1 w1 se
                       | inr w2 => symtbl_inv I2 w2 se
                       end;
    query_inv w q := match w with
                     | inl w1 => query_inv I1 w1 q
                     | inr w2 => query_inv I2 w2 q
                     end;
    reply_inv w r := match w with
                     | inl w1 => reply_inv I1 w1 r
                     | inr w2 => reply_inv I2 w2 r
                     end;
  |}.

Declare Scope inv_scope.
Infix "⊕" := inv_sum (at level 30, right associativity) : inv_scope.
Infix "@@" := inv_compose (at level 30, right associativity) : inv_scope.
Infix "@!" := invcc (at level 30, right associativity) : inv_scope.
Infix "!@" := ccinv (at level 30, right associativity) : inv_scope.


(** * Invariant-based simulation proof methods *)

(** Once we have established that the source or target language
  preserves an invariant of interest, we wish to use that fact to
  help prove the forward simulation for the pass being considered.

  The most basic way to do that is to add an assertion to the
  simulation relation that the states satisfy the invariant. Then,
  we rely on these assertions to prove a simulation step, and use the
  relevant preservation lemmas to establish them again for the
  successor states. This approach is workable and has been used in
  CompCert for typing invariants, but it is somewhat ad-hoc and
  becomes more involved when the interaction with the environment is
  involved in the invariant's preservation.

  Instead, we would like to formulate a weaker simulation diagram,
  where the invariant can be assumed on the current states but does
  not need to be established for the successor states, then show that
  if the language involved [preserves] the invariant (in the sense
  defined above), then this weakened diagram is sufficient to
  establish a forward simulation for the pass.

  The most straightforward way to do this would be to define a
  weakened version of [forward_simulation] along these lines, however
  this comes with its own pitfall: there already exists many lemmas
  one can use to establish a [forward_simulation] using simplified
  diagrams rather than the more complex, general form, and we would
  like to be able to use simplified diagrams for our weakened version
  as well. Under this approach, we would have to duplicate such lemmas
  for the weakened diagram. Instead, the method implemented below
  reuses [forward_simulation] and expresses the weakened diagram as a
  special case, making it possible to reuse all existing techniques to
  prove it.

  Since by definition, [forward_simulation] uses the same simulation
  relation for the current and successor states, we accomplish this by
  acting on the transition systems themselves:

    - for the source language, we can build a strengthened version of
      the transition system which restricts the transitions to states
      which statisfy the invariant;
    - for the target language, we can build a relaxed version of the
      transition system which adds arbitrary transitions from states
      which do not satisfy the invariant.

  Proving a simulation from the strengthened source semantics, and/or
  to the weakened target semantics, is easier because we have
  hypotheses that the states involved satify the invariant. At the
  same time, for an invariant-preserving language, we can easily show
  a simulation from the original to the strengthened version, and from
  the weakened to the original version, and these simulations can be
  composed with that proved by the user to obtain the desired one. *)

(** ** Strengthening the source semantics *)

Section RESTRICT.
  Context {liA liB} (L: semantics liA liB).
  Context (IA: invariant liA) (IB: invariant liB).
  Context (IS: inv_world IB -> state L -> Prop).

  Definition restrict_lts se :=
    {|
      step ge s t s' :=
        step (L se) ge s t s' /\
        exists w,
          symtbl_inv IB w se /\
          IS w s /\
          IS w s';
      valid_query q :=
        valid_query (L se) q;
      initial_state q s :=
        initial_state (L se) q s /\
        exists w,
          symtbl_inv IB w se /\
          query_inv IB w q /\
          IS w s;
      final_state s r :=
        final_state (L se) s r /\
        exists w,
          symtbl_inv IB w se /\
          IS w s /\
          reply_inv IB w r;
      at_external s q :=
        at_external (L se) s q /\
        exists w wA,
          symtbl_inv IB w se /\
          IS w s /\
          query_inv IA wA q;
      after_external s r s' :=
        after_external (L se) s r s' /\
        exists w wA q,
          symtbl_inv IB w se /\
          at_external (L se) s q /\
          IS w s /\
          query_inv IA wA q /\
          reply_inv IA wA r /\
          IS w s';
    globalenv :=
      globalenv (L se);
  |}.

  Definition restrict :=
    {|
      skel := skel L;
      state := state L;
      activate se := restrict_lts se;
    |}.

  Lemma restrict_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) L restrict.
  Proof.
    fsim (apply forward_simulation_step with (match_states := rel_inv (IS w));
          destruct Hse; subst); cbn; auto.
    - destruct 1. reflexivity.
    - intros q _ s [Hq] Hs. exists s.
      assert (IS w s) by (eapply preserves_initial_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros s _ r [Hs] Hr. exists r.
      assert (reply_inv IB w r) by (eapply preserves_final_state; eauto).
      eauto 10 using rel_inv_intro.
    - intros s _ q [Hs] Hx.
      edestruct @preserves_external as (wA & HseA & Hq & Hk); eauto.
      eexists wA, q. intuition eauto 10 using rel_inv_intro.
      destruct H0. exists s1'. intuition eauto 20 using rel_inv_intro.
    - intros s t s' STEP _ [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto 10 using rel_inv_intro.
  Qed.

  Lemma restrict_determinate:
    determinate L ->
    determinate restrict.
  Proof.
    intros HL se. specialize (HL se) as [ ].
    split; unfold nostep, not, single_events in *; cbn; intros;
    repeat (lazymatch goal with H : _ /\ _ |- _ => destruct H as [H _] end);
    eauto.
  Qed.
End RESTRICT.

(** ** Weakening the target semantics *)

Section EXPAND.
  Context {liA liB} (L: semantics liA liB).
  Context (IA: invariant liA) (IB: invariant liB).
  Context (IS: inv_world IB -> state L -> Prop).

  Definition expand_lts se :=
    {|
      valid_query q :=
        valid_query (L se) q;
      step ge s t s' :=
        forall w, symtbl_inv IB w se -> IS w s -> step (L se) ge s t s';
      initial_state q s :=
        forall w, symtbl_inv IB w se -> query_inv IB w q -> initial_state (L se) q s;
      final_state s r :=
        forall w, symtbl_inv IB w se -> IS w s -> final_state (L se) s r;
      at_external s q :=
        forall w, symtbl_inv IB w se -> IS w s -> at_external (L se) s q;
      after_external s r s' :=
        forall w wA q, symtbl_inv IB w se -> IS w s -> at_external (L se) s q ->
        query_inv IA wA q -> reply_inv IA wA r -> after_external (L se) s r s';
      globalenv :=
        globalenv (L se);
    |}.

  Definition expand :=
    {|
      skel := skel L;
      state := state L;
      activate se := expand_lts se;
    |}.

  Lemma expand_fsim:
    preserves L IA IB IS ->
    forward_simulation (cc_inv IA) (cc_inv IB) expand L.
  Proof.
    fsim (apply forward_simulation_step with (match_states := rel_inv (IS w));
          destruct Hse; subst); cbn; auto.
    - destruct 1; reflexivity.
    - intros q _ s [Hq] Hs. exists s.
      assert (IS w s) by (eapply preserves_initial_state; eauto).
      eauto using rel_inv_intro.
    - intros s _ r [Hs] Hr.
      assert (reply_inv IB w r) by (eapply preserves_final_state; eauto).
      eauto using rel_inv_intro.
    - intros s _ q [Hs] Hk. specialize (Hk w H Hs).
      edestruct @preserves_external as (wA & HseA & Hq & Hr); eauto.
      exists wA, q. intuition auto using rel_inv_intro.
      destruct H0. exists s1'. intuition eauto using rel_inv_intro.
    - intros s t s' STEP _ [Hs].
      assert (IS w s') by (eapply preserves_step; eauto).
      exists s'. eauto using rel_inv_intro.
  Qed.
End EXPAND.

(** ** Using invariants to prove simulations *)

Section METHODS.
  Context {liA1 liA2} {ccA: callconv liA1 liA2}.
  Context {liB1 liB2} {ccB: callconv liB1 liB2}.
  Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).

  Lemma source_invariant_fsim IA IB IS:
    preserves L1 IA IB IS ->
    forward_simulation ccA ccB (restrict L1 IA IB IS) L2 ->
    forward_simulation (IA @ ccA) (IB @ ccB) L1 L2.
  Proof.
    intros HL1 HL.
    eapply compose_forward_simulations; eauto.
    apply restrict_fsim; auto.
  Qed.

  Lemma target_invariant_fsim IA IB IS:
    preserves L2 IA IB IS ->
    forward_simulation ccA ccB L1 (expand L2 IA IB IS) ->
    forward_simulation (ccA @ IA) (ccB @ IB) L1 L2.
  Proof.
    intros HL2 HL.
    eapply compose_forward_simulations; eauto.
    apply expand_fsim; auto.
  Qed.
End METHODS.

(** ** Algebraic properties *)

(** *** Commutativity *)

Lemma inv_commute_ref {li} (I J: invariant li):
  ccref (I @ J) (J @ I).
Proof.
  intros [[se2 wi] wj] se1 se3 q1 q3 [Hse12 Hse23] (q2 & Hq12 & Hq23).
  exists (se2, wj, wi). cbn in *.
  destruct Hse12, Hse23, Hq12, Hq23.
  firstorder eauto using rel_inv_intro.
  destruct H3, H4. eauto using rel_inv_intro.
Qed.

Lemma inv_commute {li} (I J: invariant li):
  cceqv (I @ J) (J @ I).
Proof.
  split; auto using inv_commute_ref.
Qed.

Lemma inv_dup {li} (I: invariant li):
  ccref I (I @ I).
Proof.
  intros w se _ q _ [Hse] [Hq].
  exists (se, w, w). cbn.
  intuition eauto 20 using rel_inv_intro.
  destruct H as (_ & [Hr] & [_]).
  eauto 20 using rel_inv_intro.
Qed.
(*
Lemma inv_dup' {li} (I: invariant li):
  cceqv I (I @ I).
Proof.
  split; eauto using inv_dup.
  intros w se1 se2 q1 q2 Hse Hq. destruct w. destruct p. inv Hse. inv Hq. destruct H1.
  inv H1. in H2.
  exists (se.
*)

(** *** Query invariant propagation *)

Class PropagatesQueryInvariant {li} (cc: callconv li li) (I : invariant li) :=
  {
    propagates_query w w2 se1 se2 q1 q2:
      match_senv cc w se1 se2 -> symtbl_inv I w2 se2 ->
      match_query cc w q1 q2 -> query_inv I w2 q2 ->
      exists w1, symtbl_inv I w1 se1 /\ query_inv I w1 q1;
  }.

Lemma inv_prop {li} cc I `{@PropagatesQueryInvariant li cc I} :
  ccref (cc @ I) (I @ cc @ I).
Proof.
  intros [[se2 w] w2] se1 _ q1 _ [Hse [Hse2]] (q2 & Hq & [Hq2]).
  edestruct propagates_query as (w1 & Hse1 & Hq1); eauto.
  exists (se1, w1, (se2, w, w2)).
  cbn; repeat apply conj; eauto 10 using rel_inv_intro.
  intros r1 _ (_ & [Hr1] & r2 & Hr & [Hr2]). eauto using rel_inv_intro.
Qed.

Instance query_prop_ccref:
  Monotonic (@PropagatesQueryInvariant) (forallr -, ccref --> - ==> impl).
Proof.
  intros li cc' cc Hcc I H.
  split.
  - intros.
    edestruct Hcc as (w' & Hse' & Hq' & Hr'); eauto.
    eapply propagates_query; eauto.
Qed.

Class PropagatesReplyInvariant {li} (cc: callconv li li) (I : invariant li) :=
  {
    propagates_reply w1 w w2 se1 se2 q1 q2 r1 r2:
      match_senv cc w se1 se2 -> symtbl_inv I w1 se1 -> symtbl_inv I w2 se2 ->
      match_query cc w q1 q2 -> query_inv I w1 q1 -> query_inv I w2 q2 ->
      match_reply cc w r1 r2 -> reply_inv I w2 r2 -> reply_inv I w1 r1;
  }.

Lemma inv_drop {li} cc I `{@PropagatesReplyInvariant li cc I} :
  ccref (I @ cc @ I) (cc @ I).
Proof.
  intros [[_ w1] [[se2 w] w2]] se1 _ q1 _ [[Hse1] [Hse [Hse2]]]
         (_ & [Hq1] & q2 & Hq & [Hq2]).
  exists (se2, w, w2). cbn; repeat apply conj; eauto using rel_inv_intro.
  intros r1 _ (r2 & Hr & [Hr2]).
  exists r1. split; eauto using rel_inv_intro.
  constructor. eapply propagates_reply; eauto.
Qed.

(** Instances *)

Instance id_query_prop {li} (I: invariant li):
  PropagatesQueryInvariant cc_id I.
Proof.
  split; cbn.
  - intros. subst. eauto.
Qed.

Instance inv_query_prop {li} (I J: invariant li):
  PropagatesQueryInvariant I J.
Proof.
  split; cbn.
  - intros wi wj se _ q _ [Hsei] Hsej [Hqi] Hqj. eauto.
Qed.

Lemma compose_query_prop {li} (cc12 cc23: callconv li li) (I: invariant li):
  PropagatesQueryInvariant cc12 I ->
  PropagatesQueryInvariant cc23 I ->
  PropagatesQueryInvariant (cc12 @ cc23) I.
Proof.
  split.
  - intros [[se2 w12] w23] w3 se1 se3 q1 q3.
    intros [Hse12 Hse23] Hse3 (q2 & Hq12 & Hq23) Hq3.
    edestruct (propagates_query w23) as (w2 & Hse2 & Hq2); eauto.
    edestruct (propagates_query w12) as (w1 & Hse1 & Hq1); eauto.
Qed.

Hint Extern 2 (PropagatesQueryInvariant (_ @ _) _) =>
  class_apply compose_query_prop : typeclass_instances.

Lemma compose_reply_prop {li} (cc12 cc23: callconv li li) (I: invariant li):
  PropagatesReplyInvariant cc12 I ->
  PropagatesReplyInvariant cc23 I ->
  PropagatesQueryInvariant cc23 I ->
  PropagatesReplyInvariant (cc12 @ cc23) I.
Proof.
  split.
  - intros w1 [[se2 w12] w23] w3 se1 se3 q1 q3 r1 r3.
    intros [Hse12 Hse23] Hse1 Hse3 (q2 & Hq12 & Hq23) Hq1 Hq3 (r2 & Hr12 & Hr23) Hr3.
    edestruct (propagates_query w23) as (w2 & Hse2 & Hq2); eauto.
    eapply (propagates_reply w1 w12 w2); eauto.
    eapply (propagates_reply w2 w23 w3); eauto.
Qed.

Hint Extern 2 (PropagatesReplyInvariant (_ @ _) _) =>
  class_apply compose_reply_prop : typeclass_instances.

Lemma join_query_prop {li} (cc1 cc2: callconv li li) (I: invariant li):
  PropagatesQueryInvariant cc1 I ->
  PropagatesQueryInvariant cc2 I ->
  PropagatesQueryInvariant (cc1 + cc2) I.
Proof.
  intros H1 H2. split.
  - intros [w|w]; cbn; apply (propagates_query w).
Qed.

Hint Extern 2 (PropagatesQueryInvariant (_ + _) _) =>
  class_apply join_query_prop : typeclass_instances.

Lemma join_reply_prop {li} (cc1 cc2: callconv li li) (I: invariant li):
  PropagatesReplyInvariant cc1 I ->
  PropagatesReplyInvariant cc2 I ->
  PropagatesReplyInvariant (cc1 + cc2) I.
Proof.
  intros H1 H2. split.
  - intros w1 [w|w]; cbn; apply (propagates_reply w1 w).
Qed.

Hint Extern 2 (PropagatesReplyInvariant (_ + _) _) =>
  class_apply join_reply_prop : typeclass_instances.

Lemma pow_query_prop {li} (cc: callconv li li) (I: invariant li) (n: nat):
  PropagatesQueryInvariant cc I ->
  PropagatesQueryInvariant (cc ^ n) I.
Proof.
  intros H.
  induction n; cbn; typeclasses eauto.
Qed.

Hint Extern 2 (PropagatesQueryInvariant (cc_pow _ _) _) =>
  class_apply pow_query_prop : typeclass_instances.

Lemma star_query_prop {li} (cc: callconv li li) (I: invariant li):
  PropagatesQueryInvariant cc I ->
  PropagatesQueryInvariant (cc^{*}) I.
Proof.
  intros H. split.
  - intros [n w12s]. cbn.
    apply propagates_query.
Qed.

Hint Extern 2 (PropagatesQueryInvariant (cc_star _) _) =>
  class_apply star_query_prop : typeclass_instances.

Lemma pow_reply_prop {li} (cc: callconv li li) (I: invariant li) (n: nat):
  PropagatesReplyInvariant cc_id I ->
  PropagatesQueryInvariant cc I ->
  PropagatesReplyInvariant cc I ->
  PropagatesReplyInvariant (cc ^ n) I.
Proof.
  intros Hid HQ HR.
  induction n; cbn; typeclasses eauto.
Qed.

Hint Extern 3 (PropagatesReplyInvariant (cc_pow _ _) _) =>
  class_apply pow_reply_prop : typeclass_instances.

Lemma star_reply_prop {li} (cc: callconv li li) (I: invariant li):
  PropagatesReplyInvariant cc_id I ->
  PropagatesQueryInvariant cc I ->
  PropagatesReplyInvariant cc I ->
  PropagatesReplyInvariant (cc^{*}) I.
Proof.
  intros H. split.
  - intros w1 [n w12s]. cbn.
    apply propagates_reply.
Qed.

Hint Extern 3 (PropagatesReplyInvariant (cc_star _) _) =>
  class_apply star_reply_prop : typeclass_instances.

Instance wt_c_query_prop R:
  PropagatesQueryInvariant (cc_c R) wt_c.
Proof.
  split.
  - intros w [se sg] se1 se2 q1 q2 Hse Hse2 Hq.
    intros [Hsg Hq2]. subst.
    destruct Hq; cbn in *.
    exists (se1, sg). cbn. intuition auto.
    revert Hq2. generalize (sig_args sg). clear - H0.
    induction H0; auto. cbn. intros [ | t tl]; auto. intuition eauto.
    destruct H, t; cbn in *; tauto.
Qed.

Instance wt_c_reply_prop R:
  PropagatesReplyInvariant (cc_c R) wt_c.
Proof.
  split.
  - intros [se1 sg1] w [se2 sg2] xse1 xse2 q1 q2 r1 r2.
    intros Hse [ ] [ ] Hq [Hsg1 Hargs1] [Hsg2 Hargs2] Hr. subst.
    destruct Hr as (w' & Hw' & Hr).
    destruct Hq; cbn in *. destruct Hr; cbn in *. clear -H3.
    destruct H3; auto. constructor.
Qed.

Global Instance wt_c_id_prop:
  PropagatesReplyInvariant cc_id wt_c.
Proof.
  split.
  - intros [se sg] [ ] [se1 xsg] se2 se3 q q1 r r1. cbn.
    intros. intuition subst. auto.
Qed.

Global Instance wt_c_inv_prop I:
  PropagatesReplyInvariant (cc_inv I) wt_c.
Proof.
  split.
  - intros [se sg] w [se1 xsg] se2 se3 q q1 r r1. cbn.
    intros [Hse] ? ? [Hq] [? Hwt_q] [? _] [Hr]. subst. auto.
Qed.
