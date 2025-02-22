(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

(** Simulation convention algebra *)
Require Import LanguageInterface.
Require Import Invariant.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.
Require Import InjectFootprint.
Require Import Extends.
Require Import Clightrel.
Require Import RTLrel.
Require Import Asmrel.
Require Import ValueAnalysis.
Require Import Conventions.
Require Import CallConv.
(* Require Import CA. *)
Require Import CallconvBig VCompBig CallConvAlgebra CallConvLibs Composition.

(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy (*Cexec*).
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproofC.
Require Cshmgenproof.
Require CminorgenproofC.
Require SelectionproofC.
Require RTLgenproofC.
Require TailcallproofC.
Require InliningproofC.
Require Renumberproof.
Require ConstpropproofC.
Require CSEproofC.
Require DeadcodeproofC.

Require AllocproofC.
Require TunnelingproofC.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require StackingproofC.
Require AsmgenproofC.


(** Command-line flags. *)
Require Import Compopts.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a !@@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
  !@@ print (print_RTL 0)
  !@@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
  !@@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
  !@@ print (print_RTL 2)
  !@@ time "Renumbering" Renumber.transf_program
  !@@ print (print_RTL 3)
  !@@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
  !@@ print (print_RTL 4)
  !@@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
  !@@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
  !@@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
  !@@ print (print_RTL 7)
  @@@ time "Register allocation" Allocation.transf_program
  !@@ print print_LTL
  !@@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
  !@@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
  !@@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
  !@@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
  !@@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)


Definition transl_init := Initializers.transl_init.
(* Definition cexec_do_step := Cexec.do_step.
*)

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x !@@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Global Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Definition CompCertO's_passes :=
      mkpass SimplLocalsproofC.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass CminorgenproofC.match_prog
  ::: mkpass SelectionproofC.match_prog
  ::: mkpass RTLgenproofC.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls TailcallproofC.match_prog)
  ::: mkpass InliningproofC.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop ConstpropproofC.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproofC.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy DeadcodeproofC.match_prog)
  ::: mkpass Allocproof.match_prog
  ::: mkpass TunnelingproofC.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass StackingproofC.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes).

(** For CompCertO we are mostly interested in using Clight as a source
  language, however we can still prove a correctness theorem for CompCert C. *)

Definition CompCert's_passes :=
  mkpass SimplExprproof.match_prog ::: CompCertO's_passes.

Definition match_c_prog: Csyntax.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_clight_program_match:
  forall p tp,
  transf_clight_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p1 tp T.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; simpl in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; simpl in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; simpl in T; try discriminate.
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply CminorgenproofC.transf_program_match; auto.
  exists p5; split. apply SelectionproofC.transf_program_match; auto.
  exists p6; split. apply RTLgenproofC.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply TailcallproofC.transf_program_match.
  exists p8; split. apply InliningproofC.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply ConstpropproofC.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproofC.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply DeadcodeproofC.transf_program_match.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply TunnelingproofC.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply StackingproofC.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_c_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  destruct (transf_clight_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  inv T. unfold match_c_prog. cbn -[CompCertO's_passes].
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  apply transf_clight_program_match; auto.
Qed.

(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

(** Preliminaries: this should be in Coqrel. Alternatively, we could
  define it for [ccref] alone. *)

Instance po_subrel {A} (eqv R: relation A) `{!Equivalence eqv} `{!PreOrder R}:
  PartialOrder eqv R ->
  Related eqv R subrel.
Proof.
  firstorder.
Qed.

(*
Instance po_subrel' {A} (eqv R: relation A) `{!Equivalence eqv} `{!PreOrder R}:
  PartialOrder eqv R ->
  Related eqv (flip R) subrel.
Proof.
  firstorder.
Qed.
*)

(** ** Calling conventions *)

Require Import Conventions Asm Mach Lineartyping.
Require Import Injp Ext CAnew.
Require Import InvariantC RTLselfsim.

Infix "@" := GS.cc_compose (at level 30, right associativity).

Lemma compose_identity_pass {li1 li2} cc sem bsem tsem:
  forward_simulation 1 1 sem bsem ->
  GS.forward_simulation cc bsem tsem ->
  @GS.forward_simulation li1 li2 cc sem tsem.
Proof.
  intros. rewrite <- cctrans_id_1.
  eapply st_fsim_vcomp; eauto.
  eapply NEWSIM. auto.
Qed.

Lemma compose_identity_pass' {li1 li2} cc sem bsem tsem:
  GS.forward_simulation cc_id sem bsem ->
  GS.forward_simulation cc bsem tsem ->
  @GS.forward_simulation li1 li2 cc sem tsem.
Proof.
  intros. rewrite <- cctrans_id_1.
  eapply st_fsim_vcomp; eauto.
Qed.

Lemma compose_optional_pass {A li1 li2 cc cc' sem}:
  (forall prog tprog tsem,
      GS.forward_simulation cc (sem prog) (sem tprog) ->
      GS.forward_simulation cc' (sem tprog) tsem ->
      @GS.forward_simulation li1 li2 cc' (sem prog) tsem) ->
  forall flag transf prog tprog tsem,
    @match_if A flag transf prog tprog ->
    (forall p tp, transf p tp -> GS.forward_simulation cc (sem p) (sem tp)) ->
    GS.forward_simulation cc' (sem tprog) tsem ->
    GS.forward_simulation cc' (sem prog) tsem.
Proof.
  intros. unfold match_if in *.
  destruct (flag tt); subst; eauto.
Qed.

(** ** Composition of passes *)

Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  GS.forward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics tp)
  /\ GS.backward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics tp). 
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: GS.forward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics p19)).
  {
    rewrite <- cc_collapse.
  eapply st_fsim_vcomp. apply NEWSIM.
    eapply top_ro_selfsim; eassumption.
  eapply st_fsim_vcomp.
    eapply SimplLocalsproofC.transf_program_correct'; eassumption.
  eapply compose_identity_pass.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply CminorgenproofC.transl_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply SelectionproofC.transf_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply RTLgenproofC.transf_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply RTL_injp_selfsim.
  eapply st_fsim_vcomp.
    unfold match_if in M4. destruct (optim_tailcalls tt).
    eapply TailcallproofC.transf_program_correct; eauto.
    subst. eapply RTL_ext_selfsim.
  eapply st_fsim_vcomp.
    eapply InliningproofC.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply st_fsim_vcomp.
  { unfold match_if in M7. destruct (optim_constprop tt).
    eapply ConstpropproofC.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_identity_pass. 
    unfold match_if in M8. destruct (optim_constprop tt).
    eapply Renumberproof.transf_program_correct; eassumption.
    subst. eapply identity_forward_simulation.
  eapply st_fsim_vcomp.
  { unfold match_if in M9. destruct (optim_CSE tt).
    eapply CSEproofC.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply st_fsim_vcomp.
  { unfold match_if in M10. destruct (optim_redundancy tt).
    eapply DeadcodeproofC.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply st_fsim_vcomp.
    eapply AllocproofC.transf_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply TunnelingproofC.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_identity_pass'.
  intros. eapply NEWSIM.
    eapply Debugvarproof.transf_program_correct; eassumption.
  eapply st_fsim_vcomp.
    eapply StackingproofC.transf_program_correct with (rao := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists. eassumption.
    eapply AsmgenproofC.transf_program_correct; eassumption.
  }
  split. auto.
  apply GS.forward_to_backward_simulation. auto.
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

(*
Theorem c_semantic_preservation:
  forall p tp,
  match_c_prog p tp ->
  backward_simulation cc_compcert cc_compcert (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros p tp (p' & Hp' & Htp). cbn in Hp'.
  rewrite <- (cc_compose_id_left cc_compcert) at 1.
  rewrite <- (cc_compose_id_left cc_compcert) at 2.
  apply compose_backward_simulations with (atomic (Cstrategy.semantics p)).
  - apply factor_backward_simulation.
    + apply Cstrategy.strategy_simulation.
    + apply Csem.semantics_single_events.
    + eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  - apply forward_to_backward_simulation.
    + apply factor_forward_simulation.
      * eapply compose_identity_pass.
        -- apply SimplExprproof.transl_program_correct; eauto.
        -- apply clight_semantic_preservation; eauto.
      * intros. eapply sd_traces. apply Asm.semantics_determinate.
    + apply atomic_receptive.
      apply Cstrategy.semantics_strongly_receptive.
    + apply Asm.semantics_determinate.
  - intros. eapply sd_traces. apply Asm.semantics_determinate.
Qed.
*)
(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

(*
Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation cc_compcert cc_compcert (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.
 *)

(*
(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_clight_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_clight_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply clight_semantic_preservation; auto.
Qed.
*)

(** An example of how the correctness theorem, horizontal composition,
  and assembly linking proofs can be used together. *)

Require Import SmallstepLinking.
Require Import HCompBig.
Require Import AsmLinking.


(** TODO5: prove asmlinking based on [HCompbig] instead of [SmallstepLinking]*)
Lemma asm_linking : forall p1 p2 p,
    link p1 p2 = Some p ->
    GS.forward_simulation cc_id
      (semantics (fun i : bool => Asm.semantics ((fun i0 : bool => if i0 then p1 else p2) i))
         (erase_program p)) (Asm.semantics p).
Proof.
  intros.
  apply NEWSIM. apply AsmLinking.asm_linking. auto.
Qed.
      
Lemma compose_transf_c_program_correct:
  forall p1 p2 spec tp1 tp2 tp,
    compose (Clight.semantics1 p1) (Clight.semantics1 p2) = Some spec ->
    transf_clight_program p1 = OK tp1 ->
    transf_clight_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    GS.forward_simulation cc_compcert spec (Asm.semantics tp).
Proof.
  intros. rewrite <- cctrans_id_2.
  eapply st_fsim_vcomp.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply asm_linking; eauto. }
  eapply compose_simulation; eauto.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  unfold compose. cbn.
  apply link_erase_program in H2. rewrite H2. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.
