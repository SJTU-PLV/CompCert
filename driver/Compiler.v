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
Require Import CA.

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
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.

Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
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
  @@@ time "Unused globals" Unusedglob.transform_program
  !@@ print (print_RTL 8)
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
      mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
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
  destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
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

(** This is the simulation convention for the whole compiler. *)

Definition cc_compcert : callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp @
       cc_asm injp.

(** The C-level simulation convention *)
Definition cc_c_level : callconv li_c li_c := ro @ wt_c @ injp.

Definition cc_compcert_cod : callconv li_c li_asm :=
  ro @ wt_c @ cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm @
       @ cc_asm inj.

Definition cc_compcert_dom : callconv li_c li_asm :=
  ro @ wt_c @  cc_c injp @
       cc_c_locset @ cc_locset_mach @ cc_mach_asm.

Lemma transport_injp_to_asm :
  ccref (ro @ wt_c @ cc_c injp @ cc_c_locset @ cc_locset_mach @ cc_mach_asm @ cc_asm injp @ cc_asm inj)
        cc_compcert_cod.
Proof.
  rewrite (commute_around cc_mach_asm).
  rewrite (commute_around cc_locset_mach).
  rewrite (commute_around cc_c_locset).
  rewrite <- (cc_compose_assoc injp).
  rewrite <- cc_c_compose.
  rewrite injp_injp_eq.
  reflexivity.
Qed.

(** The first expand of cc_compcert for both directions *)
Theorem cc_compcert_merge:
  forall p tp,
  forward_simulation cc_compcert_dom cc_compcert_cod (Clight.semantics1 p) (Asm.semantics tp) ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros.
  unfold cc_compcert, cc_compcert_cod, cc_compcert_dom in *.
  rewrite injp__injp_inj_injp at 2. rewrite !cc_asm_compose.
  rewrite <- transport_injp_to_asm in H.
  rewrite <- !cc_compose_assoc.
  eapply compose_forward_simulations.
  rewrite <- cc_injpca_cainjp at 1.
  rewrite cc_cainjp__injp_ca.
  rewrite <- cc_cllmma_ca at 1.
  rewrite cc_ca_cllmma.
  rewrite cc_compose_assoc at 1.
  rewrite !cc_compose_assoc. eauto.
  eapply semantics_asm_rel.
Qed.

(** Derivation of the simulation conventions after C-level at the incoming side *)
Lemma cc_compcert_expand:
  ccref
    cc_compcert_cod
    (cc_c_level @                                          (* Passes up to Alloc *)
     cc_c inj @                                            (* Unusedglob *)
     (wt_c @ cc_c ext @ cc_c_locset) @                     (* Alloc *)
     cc_locset ext @                                       (* Tunneling *)
     (wt_loc @ cc_locset_mach @ cc_mach inj) @             (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                         (* Asmgen *)
     cc_asm inj).
Proof.
  unfold cc_compcert_cod. unfold cc_c_level.
  rewrite !cc_compose_assoc.
  etransitivity.
  {
    rewrite inj_inj, !cc_asm_compose.
    rewrite inj_inj at 1. rewrite !cc_asm_compose. rewrite cc_compose_assoc.
    rewrite <- lessdef_c_cklr, cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c lessdef_c).
    rewrite (inv_dup wt_c), (cc_compose_assoc wt_c), (cc_compose_assoc wt_c).
    rewrite (commute_around (_@_) (R2:= injp)).
    do 4 rewrite (commute_around _ (R2 := _ inj)).
    reflexivity.
  }
  repeat (rstep; [rauto | ]).
  etransitivity.
  {
    rewrite !cc_compose_assoc.
    rewrite <- ext_inj, !cc_asm_compose.
    rewrite cc_compose_assoc.
    rewrite <- ext_ext at 1. rewrite cc_asm_compose, cc_compose_assoc.
    do 4 rewrite (commute_around cc_mach_asm).
    do 2 rewrite (commute_around cc_locset_mach).
    do 1 rewrite (commute_around cc_c_locset).
    rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
    rewrite <- wt_loc_out_of_thin_air, cc_compose_assoc.
    reflexivity.
  }
  reflexivity.
Qed.

(** Derivation of the simulation conventions after C-level at the outgoing side *)
Lemma cc_compcert_collapse:
  ccref
    (cc_c_level @                                 (* Passes up to Alloc *)
     cc_c inj @                                   (* Unusedglob  *)
     (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
     cc_locset ext @                              (* Tunneling *)
     (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @
    cc_asm inj)                                   (* Asmgen *)
    cc_compcert_dom.
Proof.
  (* commute the cklrs towards source C level *)
  rewrite <- wt_loc_out_of_thin_air.
  rewrite <- (cc_compose_assoc wt_loc) at 1.
  rewrite <- (cc_compose_assoc (wt_loc @ _)) at 1.
  rewrite (cc_compose_assoc wt_loc) at 1.
  rewrite (inv_drop (cc_locset injp) wt_loc), (cc_compose_assoc _ wt_loc).
  rewrite wt_loc_out_of_thin_air, !cc_compose_assoc.
  assert (ccref (cc_mach_asm @ cc_asm inj) (cc_mach inj @ cc_mach_asm)).
  eapply commut_mach_asm.
  rewrite H.
  rewrite !(commute_around cc_locset_mach).
  rewrite !(commute_around cc_c_locset).
  unfold cc_c_level. rewrite !cc_compose_assoc.

  (* compose the wt_c invaraint using its propagatation property *)
  rewrite <- lessdef_c_cklr, cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite (commute_around (wt_c @ lessdef_c)), cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.
  rewrite <- (cc_compose_assoc inj).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (inv_drop _ wt_c), !cc_compose_assoc.
  (* move the wt_c to top level *)
  rewrite <- (lessdef_c_cklr ext) , cc_compose_assoc, <- (cc_compose_assoc wt_c) at 1.
  rewrite <- (cc_compose_assoc inj).
  rewrite !wt_R_refinement. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc injp).
  rewrite wt_R_refinement. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.

  (* manully compose the cklrs into a single injp *)
  rewrite <- (cc_compose_assoc inj), <- cc_c_compose.
  rewrite inj_ext.
  rewrite <- (cc_compose_assoc inj), <- cc_c_compose.
  rewrite inj_ext.
  rewrite <- (cc_compose_assoc ext), <- cc_c_compose.
  rewrite ext_inj.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose.
  rewrite injp_inj.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose.
  rewrite injp_injp_eq.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose.
  rewrite injp_inj.
  reflexivity.
Qed.

(** Derivation of the simulation conventions for C-level at the incoming side *)
Lemma cc_c_level_expand:
  ccref cc_c_level
        ( ro @ cc_c injp @ 
              cc_c inj@
              (wt_c @ cc_c ext) @ cc_c ext @
              cc_c inj @
              cc_c ext @ cc_c inj @ cc_c injp @
              (ro @ injp) @ (ro @ injp) @ (ro @ injp)).
Proof.
  unfold cc_c_level.
  (*p j e e j e j p*)
  etransitivity.
  (*prepare for ro*)
  rewrite <- cc_compose_assoc at 1.
  rewrite inv_commute_ref.
  rewrite cc_compose_assoc.
  rewrite (trans_injp_inv_incoming ro).
  rewrite (trans_injp_inv_incoming ro).
  rewrite ! cc_compose_assoc.
  rewrite <- cc_compose_assoc.
  rewrite inv_commute_ref.
  rewrite cc_compose_assoc.
  reflexivity. rstep. rauto.
  
  (*prepare for other C optimizations *)
  etransitivity.
  rewrite injp__injp_inj_injp, !cc_c_compose at 1.
  rewrite inj_inj, cc_c_compose, cc_compose_assoc.
  rewrite inj_inj, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext, cc_c_compose, cc_compose_assoc at 1.
  rewrite <- inj_ext at 2. rewrite cc_c_compose, cc_compose_assoc.
  rewrite <- (lessdef_c_cklr injp) at 1. rewrite cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- cc_compose_assoc.
  assert (HINJP: ccref ((wt_c @ lessdef_c) @ injp) (injp @ wt_c @ lessdef_c)).
  apply commut_wt_c.
  rewrite HINJP.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc (_@_)).
  assert (HINJ: ccref ((wt_c @ lessdef_c) @ inj) (inj @ wt_c @ lessdef_c)).
  apply commut_wt_c.
  rewrite HINJ.
  rewrite !cc_compose_assoc. rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr. reflexivity.
  rewrite !cc_compose_assoc.
  repeat rstep.
Qed.

(** Derivation of the simulation conventions for C-level at the outgoing side *)
Lemma cc_c_level_collapse:
  ccref (ro @ cc_c injp @ cc_c injp @
              (wt_c @ cc_c ext) @ cc_c ext @
              cc_c inj @
              cc_c ext @
              cc_c injp @
              cc_c injp @
              (ro @ injp) @ (ro @ injp) @ (ro @ injp)
        )
        cc_c_level.
Proof.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  rewrite <- (lessdef_c_cklr ext) at 1. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc injp).
  rewrite wt_R_refinement.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.
  (* unfold cc_c_level. rstep. rauto. *)
  rewrite <- (cc_compose_assoc ext), <- cc_c_compose. rewrite ext_ext.
  rewrite <- (cc_compose_assoc ext), <- cc_c_compose. rewrite ext_inj.
  rewrite <- (cc_compose_assoc inj), <- cc_c_compose. rewrite inj_ext.
  rewrite <- (cc_compose_assoc inj).
  rewrite <- (cc_c_compose inj). rewrite inj_injp.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.
  unfold cc_c_level. rewrite <- !(cc_compose_assoc ro).
  rewrite <- inv_commute_ref at 2. rewrite inv_commute_ref.
  rewrite !cc_compose_assoc. rstep. rauto.
  rewrite <- !(cc_compose_assoc ro).
  assert (ccref (injp @ injp) injp).
  rewrite <- cc_c_compose. rewrite injp_injp_eq. reflexivity.
  rewrite !(trans_injp_ro_outgoing); eauto. reflexivity.
Qed.

(** Unification of the incoming side *)
Lemma cc_expand :
  ccref 
    cc_compcert_cod
    (
      ro @
      cc_c injp @ 
      cc_c inj @
      (wt_c @ cc_c ext) @ cc_c ext @
      cc_c inj @
      cc_c ext @ cc_c inj @ cc_c injp @
      (ro @ injp) @ (ro @ injp) @ (ro @ injp) @
    cc_c inj @                                   (* Unusedglob *)
    (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
    cc_locset ext @                              (* Tunneling *)
    (wt_loc @ cc_locset_mach @ cc_mach inj ) @   (* Stacking *)
    (cc_mach ext @ cc_mach_asm) @
    cc_asm inj
    ).
Proof.
  unfold cc_compcert_cod. rewrite cc_compcert_expand.
  rewrite cc_c_level_expand. rewrite !cc_compose_assoc.
  reflexivity.
Qed.

(** Unification of the outgoing side *)
Lemma cc_collapse :
  ccref
    ( ro @ cc_c injp @ 
      cc_c injp @
      (wt_c @ cc_c ext) @ cc_c ext @
      cc_c inj @
      cc_c ext @ cc_c injp @ cc_c injp @
      (ro @ injp) @ (ro @ injp) @ (ro @ injp) @
      cc_c inj @                                   (* Unusedglob *)
      (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
      cc_locset ext @                              (* Tunneling *)
      (wt_loc @ cc_locset injp @ cc_locset_mach) @ (* Stacking *)
      (cc_mach ext @ cc_mach_asm) @
      cc_asm inj
    )
    cc_compcert_dom.
Proof.
  rewrite <- cc_compcert_collapse.
  rewrite <- cc_c_level_collapse.
  rewrite ! cc_compose_assoc.
  reflexivity.
Qed.

Lemma injp_pass: forall p tp,
    let sem := RTL.semantics p in
    let tsem := RTL.semantics tp in
  forward_simulation (cc_c injp) (cc_c inj) sem tsem ->
  forward_simulation (cc_c injp) (cc_c injp) sem tsem.
Proof.
  intros.
  rewrite injp__injp_inj_injp at 2.
  rewrite <- injp_injp2,  !cc_c_compose at 1.
  rewrite <- injp_injp2,  !cc_c_compose at 1.
  rewrite cc_compose_assoc.
  eapply compose_forward_simulations.
  eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations. eauto.
  eapply RTLrel.semantics_rel.
Qed.

Lemma compose_identity_pass {liA1 liA2 liB1 liB2} ccA ccB sem bsem tsem:
  forward_simulation 1 1 sem bsem ->
  forward_simulation ccA ccB bsem tsem ->
  @forward_simulation liA1 liA2 ccA liB1 liB2 ccB sem tsem.
Proof.
  intros.
  rewrite <- (cc_compose_id_left ccA).
  rewrite <- (cc_compose_id_left ccB).
  eapply compose_forward_simulations; eauto.
Qed.

Lemma compose_optional_pass {A liA1 liA2 liB1 liB2 ccA ccB ccA' ccB' sem}:
  (forall prog tprog tsem,
      forward_simulation ccA ccB (sem prog) (sem tprog) ->
      forward_simulation ccA' ccB' (sem tprog) tsem ->
      @forward_simulation liA1 liA2 ccA' liB1 liB2 ccB' (sem prog) tsem) ->
  forall flag transf prog tprog tsem,
    @match_if A flag transf prog tprog ->
    (forall p tp, transf p tp -> forward_simulation ccA ccB (sem p) (sem tp)) ->
    forward_simulation ccA' ccB' (sem tprog) tsem ->
    forward_simulation ccA' ccB' (sem prog) tsem.
Proof.
  intros. unfold match_if in *.
  destruct (flag tt); subst; eauto.
Qed.

Lemma va_interface_selfsim: forall (prog: RTL.program),
  forward_simulation (ro @ injp) (ro @ injp) (RTL.semantics prog) (RTL.semantics prog).
Proof.
  intros.
  eapply compose_forward_simulations.
  eapply preserves_fsim. eapply ValueAnalysis.RTL_ro_preserves.
  eapply RTLrel.semantics_rel.
Qed.

Lemma deadcode_va_correct : forall (p tp:  RTL.program),
    let sem1 := RTL.semantics p in
    let sem2 := RTL.semantics tp in
    forward_simulation (ro @ injp) (ro @ inj) sem1 sem2 ->
    forward_simulation (ro @ injp) (ro @ injp) sem1 sem2.
Proof.
  intros. rewrite (ro_injp_inj_I_incoming ro) at 2.
  rewrite <- Deadcode_ext_out at 1.
  eapply compose_forward_simulations.
  eapply va_interface_selfsim; eauto.
  eapply compose_forward_simulations. eauto.
  apply RTLrel.semantics_rel.
Qed.
  
(** ** Composition of passes *)

Theorem clight_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp)
  /\ backward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM); clear H
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics p20)).
  {
  eapply cc_compcert_merge; eauto.
  rewrite cc_expand. rewrite <- cc_collapse at 1.
  eapply compose_forward_simulations.
    eapply top_ro_selfsim; eassumption.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct'; eassumption.
  eapply compose_identity_pass.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
    unfold match_if in M4. destruct (optim_tailcalls tt).
    eapply Tailcallproof.transf_program_correct; eauto.
    subst. eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLrel.semantics_rel.
  eapply compose_forward_simulations.
  { unfold match_if in M7. destruct (optim_constprop tt).
    eapply Constpropproof.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_identity_pass. 
    unfold match_if in M8. destruct (optim_constprop tt).
    eapply Renumberproof.transf_program_correct; eassumption.
    subst. eapply identity_forward_simulation.
  eapply compose_forward_simulations.
  { unfold match_if in M9. destruct (optim_CSE tt).
    eapply CSEproof.transf_program_correct; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_forward_simulations.
  { unfold match_if in M10. destruct (optim_redundancy tt).
    eapply deadcode_va_correct.
    eapply Deadcodeproof.transf_program_correct'; eassumption.
    subst. apply va_interface_selfsim. }
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_identity_pass.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_optional_pass; eauto using compose_identity_pass.
    exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    rewrite <- cc_stacking_lm, cc_lm_stacking.
    eapply Stackingproof.transf_program_correct with (rao := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply compose_forward_simulations.
    eapply Asmgenproof.transf_program_correct; eassumption.
  apply semantics_asm_rel.
  }
  split. auto.
  apply forward_to_backward_simulation. auto.
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

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

(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation cc_compcert cc_compcert (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.

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
  { eapply link_list_compose_passes; eauto. }  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply clight_semantic_preservation; auto.
Qed.
*)

(** An example of how the correctness theorem, horizontal composition,
  and assembly linking proofs can be used together. *)

Require Import SmallstepLinking SmallstepLinkingForward.
Require Import AsmLinking.

Lemma compose_transf_clight_program_correct:
  forall p1 p2 spec tp1 tp2 tp,
    compose (Clight.semantics1 p1) (Clight.semantics1 p2) = Some spec ->
    transf_clight_program p1 = OK tp1 ->
    transf_clight_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    forward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_forward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply AsmLinking.asm_linking; eauto. }
  eapply compose_simulation; eauto.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  eapply clight_semantic_preservation; eauto using transf_clight_program_match.
  unfold compose. cbn.
  apply link_erase_program in H2. rewrite H2. cbn. f_equal. f_equal.
  apply Axioms.functional_extensionality. intros [|]; auto.
Qed.

Require Import SmallstepLinkingBack.


Lemma Csem_determinate_big: forall p, determinate_big (Csem.semantics p).
Proof.
  intros p se. constructor.
  - (*initial_nostep*)
    intros. red. intros. intro. inv H. inv H0. inv H. inv H.
    setoid_rewrite H1 in FIND. inv FIND.
    setoid_rewrite H1 in FIND. inv FIND. inv H7.
  - (*ext_determ*)
    intros. inv H. inv H0. setoid_rewrite H1 in H6. inv H6. reflexivity.
  - (*after_determ*)
    intros. inv H. inv H0. reflexivity.
  - (*final_nostep*)
    intros. red. intros. intro. inv H. inv H0. inv H. inv H.
  - (*final_noext*)
    intros. inv H. inv H0.
  - (*final_determ*)
    intros. inv H. inv H0. reflexivity.
Qed.

Lemma Clight_determinate_big: forall p, determinate_big (Clight.semantics1 p).
Proof.
  intros p se. constructor.
  - (*initial_nostep*)
    intros. red. intros. intro. inv H. inv H0.
    setoid_rewrite H1 in FIND. inv FIND.
    setoid_rewrite H1 in FIND. inv FIND. inv H7.
  - (*ext_determ*)
    intros. inv H. inv H0. setoid_rewrite H1 in H6. inv H6. reflexivity.
  - (*after_determ*)
    intros. inv H. inv H0. reflexivity.
  - (*final_nostep*)
    intros. red. intros. intro. inv H. inv H0.
  - (*final_noext*)
    intros. inv H. inv H0.
  - (*final_determ*)
    intros. inv H. inv H0. reflexivity.
Qed.

Lemma match_c_prog_defmap_exists : forall i p tp f,
    match_c_prog p tp ->
    Maps.PTree.get i (prog_defmap (Ctypes.program_of_program p)) = Some (Gfun (Ctypes.Internal f)) ->
    exists tf,
      Maps.PTree.get i (prog_defmap tp) = Some (Gfun (Internal tf)).
Proof.
  intros i p tp f M. unfold match_c_prog, pass_match in M; simpl in M.
  repeat DestructM. subst tp.
  intro Hfp0. rename p1 into p2. rename p0 into p1. rename p into p0.

  inv M0. eapply match_program_defmap in H. setoid_rewrite Hfp0 in H. inv H. inv H3. inv H4.
  rename H2 into Hfp1. symmetry in Hfp1. 
  inv M. eapply match_program_defmap in H. setoid_rewrite Hfp1 in H. inv H. inv H6.
  inv H7. monadInv H6. rename H5 into Hfp2. symmetry in Hfp2.
  eapply match_program_defmap in M1. setoid_rewrite Hfp2 in M1. inv M1. inv H6. inv H8.
  rename H5 into Hfp3. symmetry in Hfp3.
  eapply match_program_defmap in M2. setoid_rewrite Hfp3 in M2. inv M2. inv H8. inv H10.
  monadInv H8. rename H5 into Hfp4. symmetry in Hfp4.
  eapply match_program_defmap in M3. setoid_rewrite Hfp4 in M3. inv M3. inv H8. destruct H11 as [A [B C]].
  inv C. monadInv H8. rename H5 into Hfp5. symmetry in Hfp5.
  eapply match_program_defmap in M4. setoid_rewrite Hfp5 in M4. inv M4. inv H8. inv H12.
  monadInv H8. rename H5 into Hfp6. symmetry in Hfp6.
  assert (Hfp7: exists f7, Maps.PTree.get i (prog_defmap p7) = Some (Gfun (Internal f7))).
  { unfold match_if in M5. destr_in M5.
    2: { subst. eauto. } 
    eapply match_program_defmap in M5. setoid_rewrite Hfp6 in M5. inv M5. inv H8.
    eexists. f_equal. f_equal. reflexivity.
  } destruct Hfp7 as [f7 Hfp7].
  eapply match_program_defmap in M6. setoid_rewrite Hfp7 in M6. inv M6. inv H8. inv H13.
  monadInv H8. rename H5 into Hfp8. symmetry in Hfp8.
  eapply match_program_defmap in M7. setoid_rewrite Hfp8 in M7. inv M7. inv H8. simpl in H5.
  rename H5 into Hfp9. symmetry in Hfp9.
  assert (Hfp10: exists f10, Maps.PTree.get i (prog_defmap p10) = Some (Gfun (Internal f10))).
  { unfold match_if in M8. destr_in M8.
    2: { subst. eauto. } 
    eapply match_program_defmap in M8. setoid_rewrite Hfp9 in M8. inv M8. inv H8.
    simpl. eauto.
  } destruct Hfp10 as [f10 Hfp10].
  assert (Hfp11: exists f11, Maps.PTree.get i (prog_defmap p11) = Some (Gfun (Internal f11))).
  { unfold match_if in M9. destr_in M9.
    2: { subst. eauto. } 
    eapply match_program_defmap in M9. setoid_rewrite Hfp10 in M9. inv M9. inv H8.
    simpl. eauto.
  } destruct Hfp11 as [f11 Hfp11].
  assert (Hfp12: exists f12, Maps.PTree.get i (prog_defmap p12) = Some (Gfun (Internal f12))).
  { unfold match_if in M10. destr_in M10.
    2: { subst. eauto. } 
    eapply match_program_defmap in M10. setoid_rewrite Hfp11 in M10. inv M10. inv H8.
    simpl in H15. monadInv H15.
    simpl. eauto.
  } destruct Hfp12 as [f12 Hfp12].
  assert (Hfp13: exists f13, Maps.PTree.get i (prog_defmap p13) = Some (Gfun (Internal f13))).
  { unfold match_if in M11. destr_in M11.
    2: { subst. eauto. } 
    eapply match_program_defmap in M11. setoid_rewrite Hfp12 in M11. inv M11. inv H8.
    inv H15. monadInv H8.
    simpl. eauto.
  } destruct Hfp13 as [f13 Hfp13].
  assert (Hfp14: exists f14, Maps.PTree.get i (prog_defmap p14) = Some (Gfun (Internal f14))).
  { inv M12. destruct H as [C D]. inv D. specialize (match_prog_def i) as HH.
    destr_in HH. eexists. rewrite HH. eauto. unfold option_map in HH.
    rewrite Hfp13 in HH. simpl in HH. eauto.
  } destruct Hfp14 as [f14 Hfp14].
  eapply match_program_defmap in M13. setoid_rewrite Hfp14 in M13. inv M13. inv H8. inv H15.
  monadInv H8. rename H5 into Hfp15. symmetry in Hfp15.
  eapply match_program_defmap in M14. setoid_rewrite Hfp15 in M14. inv M14. inv H8. simpl in H5.
  rename H5 into Hfp16. symmetry in Hfp16.
  eapply match_program_defmap in M15. setoid_rewrite Hfp16 in M15. inv M15. inv H8. inv H17.
  monadInv H8. rename H5 into Hfp17. symmetry in Hfp17.
  eapply match_program_defmap in M16. setoid_rewrite Hfp17 in M16. inv M16. inv H8. simpl in H5.
  rename H5 into Hfp18. symmetry in Hfp18.
  assert (Hfp19: exists f19, Maps.PTree.get i (prog_defmap p19) = Some (Gfun (Internal f19))).
  { unfold match_if in M17. destr_in M17.
    2: { subst. eauto. } 
    eapply match_program_defmap in M17. setoid_rewrite Hfp18 in M17. inv M17. inv H8.
    inv H19. monadInv H8.
    simpl. eauto.
  } destruct Hfp19 as [f19 Hfp19].
  eapply match_program_defmap in M18. setoid_rewrite Hfp19 in M18. inv M18. inv H8. inv H19.
  monadInv H8. rename H5 into Hfp20. symmetry in Hfp20.
  eapply match_program_defmap in M19. setoid_rewrite Hfp20 in M19. inv M19. inv H8. inv H20.
  monadInv H8. eauto.
Qed.

Lemma compose_transf_c_program_correct:
  forall p1 p2 spec tp1 tp2 tp,
    compose (Csem.semantics p1) (Csem.semantics p2) = Some spec ->
    transf_c_program p1 = OK tp1 ->
    transf_c_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    backward_simulation cc_compcert cc_compcert spec (Asm.semantics tp).
Proof.
  intros.
  rewrite <- (cc_compose_id_right cc_compcert) at 1.
  rewrite <- (cc_compose_id_right cc_compcert) at 2.
  eapply compose_backward_simulations.
  2: { unfold compose in H.
       destruct (@link (AST.program unit unit)) as [skel|] eqn:Hskel; try discriminate.
       cbn in *. inv H.
       eapply forward_to_backward_simulation.
       eapply AsmLinking.asm_linking; eauto.
       eapply SmallstepLinking.semantics_receptive.
       intros. destruct i; eapply Asm.semantics_receptive.
       eapply Asm.semantics_determinate.
  }
  2: { intros. pose proof (Asm.semantics_receptive tp se3). apply H3. }
  pose proof (transf_c_program_correct _ _ H0) as Bsim1.
  pose proof (transf_c_program_correct _ _ H1) as Bsim2.
  eapply compose_simulation. 6: eauto. all: eauto using Csem_determinate_big.
  - intros. intros [A B].
    (* unfold compose in H. unfold option_map in H. destr_in H.
    inv H. *)
    inv A. inv B.
    unfold Genv.is_internal in *. destr_in H4. destr_in H5.
    destruct f; inv H4.
    destruct f0; inv H5.
    unfold Genv.find_funct in *. repeat destr_in Heqo.
    rewrite Genv.find_funct_ptr_iff,Genv.find_def_spec in Heqo0.
    rewrite Genv.find_funct_ptr_iff,Genv.find_def_spec in H4.
    destr_in Heqo0.
    eapply transf_c_program_match in H0.
    eapply transf_c_program_match in H1.
    exploit match_c_prog_defmap_exists. apply H0. apply H4.
    intros [tf0 A].
    exploit match_c_prog_defmap_exists. apply H1. apply Heqo0.
    intros [tf B].
    destruct (link_prog_inv _ _ _ H2) as (_ & X & _).
    exploit X; eauto. intros (_ & _ & [gd Y]).
    inv Y.
  - unfold compose. cbn.
    apply link_erase_program in H2. rewrite H2. cbn.
    f_equal. f_equal. apply Axioms.functional_extensionality. intros [|]; auto.
Qed.
