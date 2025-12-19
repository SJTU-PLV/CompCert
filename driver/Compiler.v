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
Require Import InjpExtInjp.
Require Import Extends.
Require Import Clightrel.
Require Import RTLrel.
Require Import Asmrel.
Require Import ValueAnalysis.
Require Import Conventions.
Require Import CallConv CallConvRust.
Require Import CA RA.

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
(* Require Unusedglob. *)
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
(* Require Unusedglobproof. *)

Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

(** Rust frontend *)
Require Import Rusttypes.
Require Rustsyntax.
Require Rustlight.
Require RustIR.

Require Rustlightgen.
Require RustIRgen.
Require InitAnalysis.
Require ElaborateDrop.
Require MoveChecking.
Require BorrowCheck.
Require ReplaceOrigins.
Require BorrowCheckPolonius.
Require Clightgen.

(** Proof of Rust frontend  *)
Require RustIRgenProof.
Require Clightgenproof.
Require ElaborateDropProof.
(* Require Import MoveCheckingDomain. *)
(* Require MoveCheckingSafe. *)

(** Open safety *)
Require Import SmallstepSafe SmallstepLinkingSafe.
Require Import InvariantAlgebra.

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

Definition apply_partial_id (A B: Type)
                         (x: res A) (f: A -> res B) : res A :=
  match x with
  | Error msg => Error msg
  | OK x1 =>
      match f x1 with
      | Error msg => Error msg
      | OK _ =>
          OK x1
      end
  end.

Notation "a @!@ b" :=
   (apply_partial_id _ _ a b) (at level 50, left associativity).
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
  (* @@@ time "Unused globals" Unusedglob.transform_program *)
  (* !@@ print (print_RTL 8) *)
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

(** * Rust frontend compiler  *)

(* The pass of Rustsyntax to Rustlight is unverified *)
Definition transf_rust_program (p: Rustsyntax.program) : res Asm.program :=
  OK p
  @@@ time "Rustsyntax to Rustlight" Rustlightgen.transl_program
  !@@ time "Rustlight to RustIR" RustIRgen.transl_program
  @@@ time "Elaborate drop in RustIR" ElaborateDrop.transl_program
  (** The move checking and borrow checking are not verified yet *)
  (* @@@ time "Replace origins in RustIR" ReplaceOrigins.transl_program *)
  (* @@@ time "Borrow check" (fun p => match BorrowCheckPolonius.borrow_check_program p with *)
  (*                                | OK _ => OK p *)
  (*                                | Error msg => Error msg *)
  (*                                end) *)
  @@@ time "Generate Clight and insert drop glue" Clightgen.transl_program
  @@@ transf_clight_program.

(* For ownership language, we just consider Rustlight as the source
language and remove the borrow checking passes. This compilation is
verified. *)
Definition transf_rustlight_program (p: Rustlight.program) : res Asm.program :=
  OK p
  !@@ time "Rustlight to RustIR" RustIRgen.transl_program
  @@@ time "Borrow checking" (fun p => match BorrowCheck.borrow_check_program p with
                                 | OK _ => OK p
                                 | Error msg => Error msg
                                 end)
  @@@ time "Elaborate drop in RustIR" ElaborateDrop.transl_program
  @@@ time "Generate Clight and insert drop glue" Clightgen.transl_program
  @@@ transf_clight_program.


Definition transf_rustlight_program_borck (p: Rustlight.program) : res Asm.program :=
  OK p
  !@@ time "Rustlight to RustIR" RustIRgen.transl_program
  (* @@@ time "Move checking" (fun p => match MoveChecking.move_check_program p with *)
  (*                                | OK _ => OK p *)
  (*                                | Error msg => Error msg *)
  (*                                end) *)
  @@@ time "Replace origins in RustIR" ReplaceOrigins.transl_program
  @@@ time "Borrow checking" (fun p => match BorrowCheck.borrow_check_program p with
                                 | OK _ => OK p
                                 | Error msg => Error msg
                                 end)
  @@@ time "Elaborate drop in RustIR" ElaborateDrop.transl_program
  @@@ time "Generate Clight and insert drop glue" Clightgen.transl_program
  @@@ transf_clight_program.


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
  (* ::: mkpass Unusedglobproof.match_prog *)
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** match_prog for the rust compiler *)

Program Definition pass_partial_identity {l: Language} {A} (f: l -> res A): Pass l l :=
  {| pass_match := fun p1 p2 => p1 = p2 /\ (exists x, f p1 = OK x);
     (*pass_match_link := _*) |}.

Definition passes_rustlight_rustir :=
  mkpass RustIRgenProof.match_prog
  ::: pass_nil _.

Definition CompCertO's_passes_rustir :=
    mkpass ElaborateDropProof.match_prog
    ::: mkpass Clightgenproof.match_prog
    ::: CompCertO's_passes.

Definition CompCertO's_passes_rustlight :=
  mkpass (compose_passes passes_rustlight_rustir)
    (** Borrow Checking pass *)
    ::: pass_partial_identity BorrowCheck.borrow_check_program
    ::: CompCertO's_passes_rustir.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Clight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes).

Definition match_prog_rustlight: Rustlight.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes_rustlight).

Definition match_prog_rustir: RustIR.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCertO's_passes_rustir).

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
  (* destruct (Unusedglob.transform_program p13) as [p14|e] eqn:P14; simpl in T; try discriminate. *)
  (* destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate. *)
  destruct (Allocation.transf_program p13) as [p15|e] eqn:P15; simpl in T; try discriminate.
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
  (* exists p14; split. apply Unusedglobproof.transf_program_match; auto. *)
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

(* Rust compilation chain *)

Theorem transf_rustlight_program_match: forall p tp,
    transf_rustlight_program p = OK tp ->
    match_prog_rustlight p tp.
Proof.
  intros p tp T.
  unfold transf_rustlight_program, time in T. simpl in T.
  destruct BorrowCheck.borrow_check_program eqn: MOVECHECK in T; simpl in T; try congruence.
  set (p1 := (RustIRgen.transl_program p)) in *.
  destruct (ElaborateDrop.transl_program p1) as [p2|e] eqn: P2; simpl in T; try discriminate.
  destruct (Clightgen.transl_program p2) as [p3|e] eqn: P3; simpl in T; try discriminate.
  unfold match_prog_rustlight. cbn -[CompCertO's_passes_rustlight].
  exists p1; split. simpl. exists p1. split; auto.
  apply RustIRgenProof.match_transf_program; auto.
  exists p1; split. simpl. split; auto.
  eexists. eauto.
  exists p2; split. apply ElaborateDropProof.match_transf_program; auto.
  exists p3; split. apply Clightgenproof.match_transf_program; auto.
  apply transf_clight_program_match; eauto.
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

(** Simulation Convention of the CompCert Compilation Passes:

    SimplLocals : injp ↠ injp
    Cshmgen: id ↠ id
    Cminorgen: injp ↠ inj
    Selection : (wt_c @ ext) ↠ (wt_c @ ext)
    RTLgen : ext ↠ ext
    Tailcall : ext ↠ ext
    Inlining : injp ↠ inj
    Renumber : id ↠ id
    Constprop : option ((ro @ injp) ↠ (ro @ injp))
    CSE      : option ((ro @ injp) ↠ (ro @ injp))
    Deadcode  : option ((ro @ injp) ↠ (ro @ injp))
    (* End of cc_c_level *)

    Alloc : (wt_c @ ext @ CL) ↠ (wt_c @ ext @ CL)
    Tunneling : (cc_locset ext) ↠ (cc_locset ext)
    Linearize : id ↠ id
    Cleanuplabels : id ↠ id
    Debugvar : id ↠ id
    Stacking : (wt_loc @ cc_stacking_injp) ↠ (wt_loc @ cc_stacking_injp)
    Asmgen : (cc_mach ext @ MA) ↠ (cc_mach ext @ MA)
 *)

(** This is the simulation convention for the whole compiler. *)

(* Definition cc_compcert : callconv li_c li_asm := *)
(*        ro @ wt_c @ *)
(*        cc_c_asm_injp @ *)
(*        cc_asm injp. *)

Definition cc_compcert : callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp @
       cc_asm ext.


(** The C-level simulation convention *)
Definition cc_c_level : callconv li_c li_c := ro @ wt_c @ cc_c injp.

(* Definition cc_compcert_cod : callconv li_c li_asm := *)
(*   ro @ wt_c @ cc_c injp @ *)
(*        cc_c_locset @ cc_locset_mach @ cc_mach_asm @ *)
(*        @ cc_asm inj. *)

(* Definition cc_compcert_dom : callconv li_c li_asm := *)
(*   ro @ wt_c @  cc_c injp @ *)
(*        cc_c_locset @ cc_locset_mach @ cc_mach_asm. *)

Definition cc_compcert_cod : callconv li_c li_asm :=
  ro @ wt_c @ cc_c injp @
       cc_c_locset @ cc_stacking injp @ cc_mach_asm @
       @ cc_asm ext.

Definition cc_compcert_dom : callconv li_c li_asm :=
  ro @ wt_c @ cc_c injp @
       cc_c_locset @ cc_stacking injp @ cc_mach_asm @
       @ cc_asm ext.


(** The first expand of cc_compcert for both directions *)
Theorem cc_compcert_merge:
  forall p tp,
  forward_simulation cc_compcert_dom cc_compcert_cod (Clight.semantics1 p) (Asm.semantics tp) ->
  forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros.
  unfold cc_compcert, cc_compcert_cod, cc_compcert_dom in *.
  rewrite cc_cainjp_expand at 2. rewrite !cc_compose_assoc.
  rewrite <- cc_cainjp_collapse at 1. rewrite !cc_compose_assoc.
  (* split injp from cc_stacking injp *)
  erewrite cc_stacking_injp_injp2 at 2. rewrite !cc_compose_assoc.
  rewrite (commute_around cc_c_locset (R2:= cc_locset injp)).
  rewrite <- cc_stacking_injp2_injp at 1. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc cc_c_locset). rewrite <- cc_injpCL_CLinjp, cc_compose_assoc.    
  auto.
Qed.

(** Derivation of the simulation conventions after C-level at the incoming side *)
Lemma cc_compcert_expand:
  ccref
    cc_compcert_cod
    (cc_c_level @                                          (* Passes up to Alloc *)
     (wt_c @ cc_c ext @ cc_c_locset) @                     (* Alloc *)
     cc_locset ext @                                       (* Tunneling *)
     (wt_loc @ cc_stacking injp) @                         (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                         (* Asmgen *)
     cc_asm ext).
Proof.
  unfold cc_compcert_cod. unfold cc_c_level.
  rewrite !cc_compose_assoc.
  etransitivity.
  {
    (* get ext from stacking injp *)
    rewrite cc_stacking_injp_injp2, !cc_compose_assoc.
    rewrite injp__injp_ext_injp at 2. rewrite !cc_locset_compose, !cc_compose_assoc.
    rewrite <- ext_ext at 1. rewrite !cc_locset_compose, !cc_compose_assoc.
    do 1 rewrite (commute_around cc_c_locset).
    rewrite <- (cc_compose_assoc injp), <- cc_c_compose. rewrite injp_injp_eq.    
    rewrite <- lessdef_c_cklr, cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_c lessdef_c).
    rewrite (inv_dup wt_c), (cc_compose_assoc wt_c), (cc_compose_assoc wt_c).
    rewrite (commute_around (_@_) (R2:= cc_c injp)).
    do 1 rewrite (commute_around cc_c_locset).
    reflexivity.
  }
  repeat (rstep; [rauto | ]).
  etransitivity.
  {
    rewrite !cc_compose_assoc.
    rewrite <- ext_ext at 3. rewrite cc_asm_compose. 
    do 1 rewrite (commute_around cc_mach_asm).
    rewrite <- (cc_compose_assoc lessdef_c), lessdef_c_cklr.
    rewrite <- (cc_compose_assoc (cc_locset injp)).
    rewrite cc_stacking_injp2_injp.
    rewrite cc_stacking_wtstacking, cc_compose_assoc.
    reflexivity.
  }
  reflexivity.
Qed.

(** Derivation of the simulation conventions after C-level at the outgoing side *)
Lemma cc_compcert_collapse:
  ccref
    (cc_c_level @                                 (* Passes up to Alloc *)
     (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
     cc_locset ext @                              (* Tunneling *)
     (wt_loc @ cc_stacking injp) @                (* Stacking *)
     (cc_mach ext @ cc_mach_asm) @                (* Asmgen *)
    cc_asm ext)                                   
    cc_compcert_dom.
Proof.
  (* absorb wt_loc into stacking injp *)
  rewrite cc_wtstacking_stacking.  
  (* commute mach ext to asm ext *)
  rewrite cc_extMA_MAext, !cc_compose_assoc.
  rewrite <- cc_asm_compose, ext_ext.
  (* commute the cklrs towards source C level *)
  unfold cc_c_level. rewrite !cc_compose_assoc.
  
  (* compose the wt_c invaraint using its propagatation property *)
  rewrite <- (cc_compose_assoc (cc_c injp)).
  rewrite <- (cc_compose_assoc wt_c).
  rewrite (inv_drop _ wt_c), !cc_compose_assoc.
  (* move the wt_c to top level *)
  rewrite <- (lessdef_c_cklr ext) , cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  rewrite <- (cc_compose_assoc injp).
  rewrite !wt_R_refinement. rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.

  (* produce a injp from stacking *)
  rewrite cc_stacking_injp_injp2, cc_compose_assoc.
  (* merge injp ext injp *)
  rewrite !(commute_around cc_c_locset).
  rewrite <- (cc_compose_assoc ext). rewrite <- cc_c_compose, ext_ext.
  rewrite <- (cc_compose_assoc ext), <- (cc_compose_assoc injp), <- !cc_c_compose.
  rewrite injp_ext_injp__injp.
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
    (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
    cc_locset ext @                              (* Tunneling *)
    (wt_loc @ cc_stacking injp) @                (* Stacking *)
    (cc_mach ext @ cc_mach_asm) @
    cc_asm ext
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
      (wt_c @ cc_c ext @ cc_c_locset) @            (* Alloc *)
      cc_locset ext @                              (* Tunneling *)
      (wt_loc @ cc_stacking injp) @                (* Stacking *)
      (cc_mach ext @ cc_mach_asm) @
      cc_asm ext
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


(** Simulation convention of the rust compiler *)

Definition cc_rust_compcert: callconv li_rs li_asm :=
  ro_rs @ wt_rs @
  cc_rust_asm_injp @
  cc_asm ext.

Lemma cc_rust_collapse:
  ccref
    (ro_rs @                    (* Self simulation of Rustlight *)
       cc_rs injp @             (* Elaborate drop *)
       (cc_rs injp @ cc_rust_c) @  (* Clightgen: may be changed to injp *)
       cc_compcert)             (* CompCertO *)
    cc_rust_compcert.
Proof.
  unfold cc_compcert, cc_rust_compcert.
  rewrite cc_compose_assoc.
  (* merge top-level injp *)
  rewrite <- (cc_compose_assoc (cc_rs injp)), <- cc_rs_compose. rewrite injp_injp2.
  (* move ro to the top *)
  rewrite cc_cainjp__injp_ca.
  rewrite cc_compose_assoc.
  rewrite <- lessdef_c_cklr, cc_compose_assoc, <- (cc_compose_assoc wt_c).
  rewrite (commute_around (wt_c @ lessdef_c)).
  rewrite !(commute_around cc_rust_c).
  rewrite <- !(cc_compose_assoc ro_rs).
  rewrite <- (cc_compose_assoc (ro_rs @ cc_rs injp)).
  rewrite trans_injp_rors_outgoing.
  rewrite cc_compose_assoc.
  (* move wt_c to the top *)
  rewrite <- (cc_compose_assoc cc_rust_c).
  rewrite <- commut_rust_c_wt_lessdef.
  do 2 rewrite <- (cc_compose_assoc (cc_rs injp)).
  rewrite wt_rs_R_refinement.
  rewrite !cc_compose_assoc, <- (cc_compose_assoc lessdef_rs).
  rewrite lessdef_rs_cklr.
  (* merge injp, cc_rust_c and cc_c_asm_injp *)  
  rewrite <- (cc_compose_assoc cc_rust_c), cc_rcca_ra.
  rewrite <- (cc_compose_assoc (cc_rs injp)), cc_injpra_rainjp.
  reflexivity.
Qed.

    
Lemma cc_rust_expand:
  ccref
    cc_rust_compcert
    (ro_rs @                    (* Self simulation of Rustlight *)
       cc_rs injp @             (* Elaborate drop *)
       (cc_rs injp @ cc_rust_c) @  (* Clightgen: outgoing should be injp *)
       (** may be we should not use cc_compcert because it contains
       some self-simulation invariant which is not belong to the
       compiler *)
       cc_compcert)             (* CompCertO *)
.
Proof.
  unfold cc_rust_compcert, cc_compcert.
  rewrite !cc_compose_assoc.
  (* 1. expand RAinjp *)
  rewrite cc_rainjp_injpra.
  rewrite !cc_compose_assoc.
  rewrite cc_ra_rcca, cc_compose_assoc.
  (* 2. put down an injp *)
  rewrite injp_injp at 1. rewrite cc_rs_compose, cc_compose_assoc.
  (* swap injp⋅rc *)
  rewrite <- (cc_compose_assoc (cc_rs injp) cc_rust_c).
  rewrite injp_rs__rc_injp.
  rewrite cc_compose_assoc.    
  (* 3. put down wt_rs from rust to c *)
  rewrite <- (cc_compose_assoc wt_rs).
  rewrite <- lessdef_rs_cklr at 1.
  rewrite ! cc_compose_assoc, <- (cc_compose_assoc wt_rs).
  rewrite (commute_around (wt_rs @ lessdef_rs)).
  (* 3.1 swap (wt_rs @ lessdef_rs) and cc_rust_c *)
  rewrite <- (cc_compose_assoc (wt_rs @ lessdef_rs)).
  rewrite commut_rust_c_wt_lessdef.
  (* 3.2 absorb lessdef_c into injp *)
  rewrite !cc_compose_assoc. 
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.  
  (* 4. put down (ro⋅injp) from rust to c *)
  rewrite <- (cc_compose_assoc ro_rs).
  rewrite trans_rs_injp_inv_incoming.
  rewrite !cc_compose_assoc.
  (* 4.1 swap injp⋅rc *)
  rewrite <- (cc_compose_assoc (cc_rs injp) cc_rust_c).
  rewrite injp_rs__rc_injp.
  rewrite cc_compose_assoc.    
  (* 4.2 swap ro⋅rc *)
  rewrite <- (cc_compose_assoc ro_rs cc_rust_c).
  rewrite ro_rs__rc_ro.
  rewrite cc_compose_assoc.
  (* 4.3 swap injp and wt_c at c level *)
  rewrite <- (cc_compose_assoc wt_c injp).
  rewrite <- (cc_compose_assoc injp (wt_c @ injp)).
  rewrite wt_R__R_wt.
  (* 4.4 combine two injps in c level *)
  rewrite <- cc_c_compose. rewrite injp_injp2, cc_compose_assoc.
  (* 5. combine injp and ca *)
  rewrite <- (cc_compose_assoc injp). rewrite cc_injpca_cainjp.
  rewrite injp_injp at 1. rewrite cc_rs_compose.
  rewrite cc_compose_assoc.
  reflexivity.
Qed.

Lemma cc_rust_compcert_eqv:
  cceqv cc_rust_compcert (cc_rust_c @ cc_compcert).
Proof.
  unfold cc_rust_compcert, cc_compcert.
  split.
  - rewrite cainjp__injp_ca_equiv.
    rewrite rainjp_injpra_equiv.
    rewrite cc_ra_rcca_equiv.
    (* 1. wt_rs => (wt_rs @ lessdef_rs) *)
    rewrite !cc_compose_assoc.
    rewrite <- (cc_compose_assoc wt_rs).
    rewrite <- lessdef_rs_cklr at 1.
    rewrite ! cc_compose_assoc, <- (cc_compose_assoc wt_rs).
    (* 2. swap injp @ rc *)
    rewrite <- (cc_compose_assoc (cc_rs injp) cc_rust_c).
    rewrite injp_rs__rc_injp.
    rewrite (cc_compose_assoc cc_rust_c).
    (* 3 swap (wt_rs @ lessdef_rs) and cc_rust_c *)
    rewrite <- (cc_compose_assoc (wt_rs @ lessdef_rs)).
    rewrite commut_rust_c_wt_lessdef.
    (* 4 absorb lessdef_c into injp *)
    rewrite !cc_compose_assoc. 
    rewrite <- (cc_compose_assoc lessdef_c).
    rewrite lessdef_c_cklr.  
    (* 5. swap ro_rs @ cc_rust_c *)
    rewrite <- (cc_compose_assoc ro_rs cc_rust_c).
    rewrite ro_rs__rc_ro.
    rewrite cc_compose_assoc.
    reflexivity.
  - rewrite cainjp__injp_ca_equiv.
    rewrite rainjp_injpra_equiv.
    rewrite cc_ra_rcca_equiv.
    rewrite !cc_compose_assoc.
    (* 1. swap rc and ro *)
    rewrite !(commute_around cc_rust_c).
    (* 2. wt_rs => (wt_rs @ lessdef_rs) *)
    rewrite <- (cc_compose_assoc wt_c).
    rewrite <- lessdef_c_cklr at 1.
    rewrite ! cc_compose_assoc, <- (cc_compose_assoc wt_c).
    (* 3 swap cc_rust_c and (wt_rs @ lessdef_rs) *)
    rewrite <- (cc_compose_assoc cc_rust_c (wt_c @ lessdef_c)).
    rewrite <- commut_rust_c_wt_lessdef.
    (* 4. swap rc and injp *)
    rewrite cc_compose_assoc.
    rewrite !(commute_around cc_rust_c).
    (* 5 absorb lessdef_rs into injp *)
    rewrite !cc_compose_assoc. 
    rewrite <- (cc_compose_assoc lessdef_rs).
    rewrite lessdef_rs_cklr.  
    reflexivity.
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
  assert (F: forward_simulation cc_compcert cc_compcert (Clight.semantics1 p) (Asm.semantics p19)).
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

(** Safety preservation of the CompCert compiler (with Clight as the
source language) *)

Local Open Scope inv_scope.

Lemma clight_total_safety_preservation P Q: forall p tp,
  match_prog p tp ->
  module_type_safe P Q (Clight.semantics1 p) SIF ->
  module_type_safe (P @! cc_compcert) (Q @! cc_compcert) (Asm.semantics tp) SIF.
Proof.
  intros.
  eapply module_type_safe_preservation. eauto.
  eapply clight_semantic_preservation. auto.
Qed.

Theorem transf_clight_total_safety_preservation P Q: forall p tp,
  transf_clight_program p = OK tp ->
  module_type_safe P Q (Clight.semantics1 p) SIF ->
  module_type_safe (P @! cc_compcert) (Q @! cc_compcert) (Asm.semantics tp) SIF.
Proof.
  intros. eapply clight_total_safety_preservation; eauto.
  eapply transf_clight_program_match; eauto.
Qed.

(** * Correctness of the Rust compiler *)

Definition cc_rustir_compcert : callconv li_rs li_asm :=
  (** FIXME: we can just prove ro in Rustlight and use some refinement
  technique to get the final safety theorem. But for now, we reporve
  ro in RustIRown and get the theorem easily *)
  ro_rs
  @ (cc_rs injp)
  @ (cc_rs injp @ cc_rust_c)
  @ cc_compcert.

(* The calling covention from rustir to asm is not a direct
refinement *)
Lemma rustir_semantic_preservation:
  forall p tp,
  match_prog_rustir p tp ->
  forward_simulation cc_rustir_compcert cc_rustir_compcert (RustIRown.semantics p) (Asm.semantics tp)
  /\ backward_simulation cc_rustir_compcert cc_rustir_compcert (RustIRown.semantics p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog_rustir, pass_match, CompCertO's_passes_rustir in M. 
  cbn -[CompCertO's_passes] in M.
  repeat DestructM.
  assert (F: forward_simulation cc_rustir_compcert cc_rustir_compcert (RustIRown.semantics p) (Asm.semantics tp)).
  { unfold cc_rustir_compcert.
    eapply compose_forward_simulations.
    eapply rustir_ro_selfsim.
    eapply compose_forward_simulations.
    eapply ElaborateDropProof.transl_program_correct; eauto.
    eapply compose_forward_simulations.
    eapply Clightgenproof.transl_program_correct; eauto.
    eapply clight_semantic_preservation. eauto. }
  split. auto.
  apply forward_to_backward_simulation. auto.  
  apply RustIRown.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.


Theorem rustlight_semantic_preservation:
  forall p tp,
  match_prog_rustlight p tp ->
  forward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp)
  /\ backward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog_rustlight, pass_match, CompCertO's_passes_rustlight in M. 
  cbn -[CompCertO's_passes_rustir] in M.
  repeat DestructM. destruct M. subst.
  assert (F: forward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp)).
  { rewrite cc_rust_expand at 2.
    (* do 2 rewrite <- (cc_compose_assoc _ _ cc_compcert). *)
    rewrite <- cc_rust_collapse at 1.
    (* rewrite <- (cc_compose_assoc (cc_rs injp) _ cc_compcert). *)
    (* rewrite <- (cc_compose_assoc ro_rs _ cc_compcert). *)
    (* eapply compose_forward_simulations. *)
    (* RustIR to Asm semantics preservation *)    
    eapply compose_identity_pass. (* RustIRgen *)
    eapply RustIRgenProof.transl_program_correct; eauto.
    eapply rustir_semantic_preservation. eauto.
    (* Rustlight ro self-sim *)
    (* eapply rustlight_ro_selfsim. *)
  }
  split. auto.
  apply forward_to_backward_simulation. auto.  
  apply Rustlightown.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.


(* If the rust compiler compiles [p] and produces [tp], 
  [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_rustlight_program_correct:
  forall p tp,
  transf_rustlight_program p = OK tp ->
  backward_simulation cc_rust_compcert cc_rust_compcert (Rustlightown.semantics p) (Asm.semantics tp).
Proof.
  intros. apply rustlight_semantic_preservation. apply transf_rustlight_program_match; auto.
Qed.

(** *Correctness of the verifying part of the compiler *)

(* Proof structure

  Rustlight {I} L1 [I]                             {cc1 @@ ((I @@ wt_rs) @@ cc1)} L1 [cc1 @@ ((I @@ wt_rs) @@ cc1)]
      |                                                                            ↑  
 (compile) L1 ⊑_cc1 L2                                                             |
      |                                                                            |
   RustIR   {I @@ cc1} L2 [I @@ cc1]                                               | (by fsim with progress)
      |                                                                            |
 (move checking)                                                                   |
      |                                                                            |
   RustIR   {(I @@ cc1) @@ wt_rs} L2 [(I @@ cc1) @@ wt_rs] ⊑ {(I @@ wt_rs) @@ cc1} L2 [(I @@ wt_rs) @@ cc1]
      |
  (compile) L2 ⊑_cc2 L3
      |           
     Asm    {((I @@ wt_rs) @@ cc1) @@ cc2} L2 [((I @@ wt_rs) @@ cc1) @@ cc2] ⊑ {(I @@ wt_rs) @@ cc} L2 [(I @@ wt_rs) @@ cc]
             where cc ≡ cc1 @ cc2 (i.e., cc ≡ cc_rust_compcert)
 *)

(*

Theorem rustlight_partial_safe_to_total_safe P Q:
  forall p tp,
  match_prog_rustlight p tp ->
  module_type_safe P Q (Rustlightown.semantics p) (Rustlightown.mem_error p) ->
  module_type_safe ((P @@ rs_own) @! cc_rust_compcert) ((Q @@ rs_own) @! cc_rust_compcert) (Asm.semantics tp) SIF
  /\ module_type_safe (P @@ rs_own) (Q @@ rs_own) (Rustlightown.semantics p) SIF.
Proof.
  intros p tp M SAFE. generalize M as M1. intros.
  unfold match_prog_rustlight, pass_match, CompCertO's_passes_rustlight in M.
  cbn -[CompCertO's_passes_rustir] in M.
  repeat DestructM. destruct M; subst.
  destruct H0.
  (* 1. show backward simulation between p and p1 and then show p1 is
  partial safe *)
  assert (BSIM1: backward_simulation_preserve_error cc_id cc_id (Rustlightown.semantics p) (RustIRown.semantics p1) (Rustlightown.mem_error p) (RustIRown.mem_error p1)).
  { eapply forward_to_backward_simulation_partial.
    eapply RustIRgenProof.transl_program_correct1; eauto.
    eapply Rustlightown.semantics_receptive.
    eapply RustIRown.semantics_determinate.
    eapply RustIRown.sound_mem_error. }
  exploit @module_partial_safe_preservation; eauto.
  intros PSAFE.
  (* 2. show p1 is total safe after move checking *)  
  (* exploit MoveCheckingSafe.move_check_module_safe; eauto. *)
  (* intros TSAFE. *)
  (** TODO: when the proof borrow checking is finished, remove this assert *)
  assert (TSAFE: module_type_safe ((P @! 1) @@ rs_own) ((Q @! 1) @@ rs_own) (RustIRown.semantics p1) SIF) by admit.
  (* 3. swap rs_own and cc_id in TSAFE *)
  exploit @open_safety_inv_ref. 3: eapply TSAFE.
  eapply inv_commute_ref1. eapply invcc_commute_id1.
  red. eapply inv_commute_ref2. eapply invcc_commute_id2.
  intros TSAFE1.
  (* 4. show backward simulation between RustIRown and Asm *)  
  exploit @module_type_safe_preservation.
  eapply TSAFE1. eapply rustir_semantic_preservation; eauto.
  intros TSAFE2.
  (** show total safety in Asm and Rustlght  *)
  split.
 - (* 5. invaraint refinement *)
   eapply open_safety_inv_ref.
   3: eapply TSAFE2.
   (* ref1 *)
   etransitivity. erewrite invcc_compose_assoc.
   eapply cc_inv_ref. reflexivity.
   instantiate (1 := cc_rust_compcert).
   erewrite cc_compose_id_left.
   unfold cc_rustir_compcert.
   eapply cc_rust_collapse. reflexivity.
   (* ref2 *)
   red. etransitivity.
   eapply cc_inv_ref. reflexivity.
   eapply cc_rust_expand.
   erewrite invcc_compose_assoc.
   eapply cc_inv_ref. reflexivity.
   erewrite cc_compose_id_left. reflexivity.
 - (* 6 show forward simulation with the progress property between
  rustlight and rustir *)
  assert (FSIM: forward_simulation_progress cc_id cc_id (Rustlightown.semantics p) (RustIRown.semantics p1)).
  { eapply fsim_progress_ubpreserve_implies_progress.
    eapply RustIRgenProof.transl_program_correct1. auto. }
  (* 7. show total safety of Rustlight *)
  exploit @module_type_safe_preservation_fsimg. eapply TSAFE1.
  eauto. intros TSAFE0.
  eapply open_safety_inv_ref. 3: eapply TSAFE0.
  eapply id_inv_id_equiv.  eapply id_inv_id_equiv.  
Admitted.

Theorem transf_rustlight_partial_safe_to_total_safe P Q:
  forall p tp,
  transf_rustlight_program p = OK tp ->
  module_type_safe P Q (Rustlightown.semantics p) (Rustlightown.mem_error p) ->
  module_type_safe ((P @@ rs_own) @! cc_rust_compcert) ((Q @@ rs_own) @! cc_rust_compcert) (Asm.semantics tp) SIF
  /\ module_type_safe (P @@ rs_own) (Q @@ rs_own) (Rustlightown.semantics p) SIF.
Proof.
  intros. eapply rustlight_partial_safe_to_total_safe; auto.
  eapply transf_rustlight_program_match; auto.
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
Require Import AsmLinking.

Lemma compose_transf_c_program_correct:
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
