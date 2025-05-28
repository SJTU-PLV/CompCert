Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Errors.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Integers.
Require Import Invariant.
Require Import SmallstepLinkingSafe Smallstep.

Import Values Maps Memory AST.

Set Implicit Arguments.

(* Definitions. *)

Record semantics := ClosedSemantics_gen {
  state: Type;
  genvtype: Type;
  step : genvtype -> state -> trace -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> val -> Prop; (* For closed safety, we should make
  the return value to be val instead of int *)
  globalenv: genvtype;
  symbolenv: Genv.symtbl
}.

Declare Scope closed_smallstep_scope.

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Star' L " := (star (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Plus' L " := (plus (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_silent' L " := (forever_silent (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Forever_reactive' L " := (forever_reactive (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Notation " 'Eventually' L " := (eventually (step L) (final_state L) (globalenv L)) (at level 1) : closed_smallstep_scope.
Open Scope closed_smallstep_scope.


(* Closing open semantics. *)

Section CLOSE_SEMANTICS.

Variable liA liB : language_interface.
Variable s : Smallstep.semantics liA liB.
Variable se : Genv.symtbl.
Variable init_q : program unit unit -> option (query liB). (* a function from
program to initial query *)
Variable final_r : reply liB -> val. (* a function from reply to return value *)

Definition close_semantics :=
  let lts := Smallstep.activate s se in
  {|
    state := Smallstep.state s;
    genvtype := Smallstep.genvtype lts;
    step := Smallstep.step lts;
    initial_state :=
      match init_q (skel s) with
      | Some q =>
          Smallstep.initial_state lts q
      | None => fun _ => False
      end;
    final_state := fun state retval =>
                     exists r, Smallstep.final_state lts state r /\ retval = final_r r;
    globalenv := Smallstep.globalenv lts;
    symbolenv := se;
  |}.

End CLOSE_SEMANTICS.

Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

(* Closed safety is defined as reachable safety *)
Definition closed_safety (L: semantics) : Prop :=
  forall s, initial_state L s -> safe L s.

Section CLOSED_SAFE.

Variable liA liB : language_interface.
Variable IB: invariant liB.
Variable s : Smallstep.semantics liA liB.
Variable se : Genv.symtbl.
Variable init_q : program unit unit -> option (query liB). (* a function from
program to initial query *)
Variable final_r : reply liB -> val. (* a function from reply to return value *)

Definition lts := (Smallstep.activate s se).
Definition L := close_semantics s se init_q final_r.

Hypothesis VSE: Genv.valid_for (skel s) se.

(* The query must satisfy the pre-condition if it can be
constructed. Most of the time we just set the query_inv and symtbl_inv
to be True for the main function *)
Hypothesis QINV: forall q, init_q (skel s) = Some q ->
                      valid_query lts q = true
                      /\ (exists w, query_inv IB w q
                              /\ symtbl_inv IB w se).


Theorem closed_open_safety_adequacy:
  module_type_safe inv_bot IB s SIF ->
  closed_safety L.
Proof.
  intros [(inv & SAFE)].
  red. intros inits INIT.
  simpl in INIT.
  destruct (init_q (skel s)) eqn: INIQ; try contradiction.
  exploit QINV; eauto. intros (VQ & (w & HQ & SYM)).
  specialize (SAFE se w SYM VSE).

  exploit @initial_preserves_progress; eauto.
  intros (inits' & INIT' & INIT_SAFE).
  specialize (INIT_SAFE inits INIT).
  red. intros s' STAR.
  exploit @lts_preserves_progress_internal_safe; eauto.
  intros [(r & FINAL)|[(q1 & EXT)|(t1 & s1 & STEP1)]]; eauto.
  - left. simpl.
    exists (final_r r), r. eauto.
  - exploit @lts_preserves_progress_star. eauto.
    simpl in STAR. eauto. auto.
    intros SINV.
    exploit @external_preserves_progress; eauto.
    intros (wA & A1 & A2 & A3). inv A2.
Qed.


End CLOSED_SAFE.

