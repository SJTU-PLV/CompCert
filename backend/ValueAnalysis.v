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

Require Import FunInd.
Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import Compopts AST Linking.
Require Import Values Memory Globalenvs Builtins Events.
Require Import Registers Op RTL.
Require Import ValueDomain ValueAOp Liveness.
Require Import LanguageInterface Invariant.
Require Import InjectFootprint.

(** * The dataflow analysis *)

Definition areg (ae: aenv) (r: reg) : aval := AE.get r ae.

Definition aregs (ae: aenv) (rl: list reg) : list aval := List.map (areg ae) rl.

(** Analysis of function calls.  We treat specially the case where
  neither the arguments nor the global variables point within the
  stack frame of the current function.  In this case, no pointer
  within the stack frame escapes during the call. *)

Definition mafter_public_call : amem := mtop.

Definition mafter_private_call (am_before: amem) : amem :=
  {| am_stack := am_before.(am_stack);
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := plub (ab_summary (am_stack am_before)) Nonstack |}.

Definition analyze_call (am: amem) (aargs: list aval) :=
  if pincl am.(am_nonstack) Nonstack
  && forallb (fun av => vpincl av Nonstack) aargs
  then (Ifptr Nonstack, mafter_private_call am)
  else (Vtop, mafter_public_call).

Definition transfer_call (ae: aenv) (am: amem) (args: list reg) (res: reg) :=
  let (av, am') := analyze_call am (aregs ae args) in
  VA.State (AE.set res av ae) am'.

(** Analysis of builtins. *)

Fixpoint abuiltin_arg (ae: aenv) (am: amem) (rm: romem) (ba: builtin_arg reg) : aval :=
  match ba with
  | BA r => areg ae r
  | BA_int n => I n
  | BA_long n => L n
  | BA_float n => F n
  | BA_single n => FS n
  | BA_loadstack chunk ofs => loadv chunk rm am (Ptr (Stk ofs))
  | BA_addrstack ofs => Ptr (Stk ofs)
  | BA_loadglobal chunk id ofs => loadv chunk rm am (Ptr (Gl id ofs))
  | BA_addrglobal id ofs => Ptr (Gl id ofs)
  | BA_splitlong hi lo => longofwords (abuiltin_arg ae am rm hi) (abuiltin_arg ae am rm lo)
  | BA_addptr ba1 ba2 =>
      let v1 := abuiltin_arg ae am rm ba1 in
      let v2 := abuiltin_arg ae am rm ba2 in
      if Archi.ptr64 then addl v1 v2 else add v1 v2
  end.

Definition set_builtin_res (br: builtin_res reg) (av: aval) (ae: aenv) : aenv :=
  match br with
  | BR r => AE.set r av ae
  | _ => ae
  end.

Definition transfer_builtin_default
              (ae: aenv) (am: amem) (rm: romem)
              (args: list (builtin_arg reg)) (res: builtin_res reg) :=
  let (av, am') := analyze_call am (map (abuiltin_arg ae am rm) args) in
  VA.State (set_builtin_res res av ae) am'.

Definition eval_static_builtin_function
              (ae: aenv) (am: amem) (rm: romem)
              (bf: builtin_function) (args: list (builtin_arg reg)) :=
  match builtin_function_sem bf
                 (map val_of_aval (map (abuiltin_arg ae am rm) args)) with
  | Some v => aval_of_val v
  | None => None
  end.

Definition transfer_builtin
              (ae: aenv) (am: amem) (rm: romem) (ef: external_function)
              (args: list (builtin_arg reg)) (res: builtin_res reg) :=
  match ef, args with
  | EF_vload chunk, addr :: nil =>
      let aaddr := abuiltin_arg ae am rm addr in
      let a :=
        if va_strict tt
        then vlub (loadv chunk rm am aaddr) (vnormalize chunk (Ifptr Glob))
        else vnormalize chunk Vtop in
      VA.State (set_builtin_res res a ae) am
  | EF_vstore chunk, addr :: v :: nil =>
      let aaddr := abuiltin_arg ae am rm addr in
      let av := abuiltin_arg ae am rm v in
      let am' := storev chunk am aaddr av in
      VA.State (set_builtin_res res ntop ae) (mlub am am')
  | EF_memcpy sz al, dst :: src :: nil =>
      let adst := abuiltin_arg ae am rm dst in
      let asrc := abuiltin_arg ae am rm src in
      let p := loadbytes am rm (aptr_of_aval asrc) in
      let am' := storebytes am (aptr_of_aval adst) sz p in
      VA.State (set_builtin_res res ntop ae) am'
  | (EF_annot _ _ _ | EF_debug _ _ _), _ =>
      VA.State (set_builtin_res res ntop ae) am
  | EF_annot_val _ _ _, v :: nil =>
      let av := abuiltin_arg ae am rm v in
      VA.State (set_builtin_res res av ae) am
  | EF_builtin name sg, _ =>
      match lookup_builtin_function name sg with
      | Some bf =>
          match eval_static_builtin_function ae am rm bf args with
          | Some av => VA.State (set_builtin_res res av ae) am
          | None => transfer_builtin_default ae am rm args res
          end
      | None => transfer_builtin_default ae am rm args res
      end
  | _, _ =>
      transfer_builtin_default ae am rm args res
  end.

(** The transfer function for one instruction.  Given the abstract state
  "before" the instruction, computes the abstract state "after". *)

Definition transfer (f: function) (rm: romem) (pc: node) (ae: aenv) (am: amem) : VA.t :=
  match f.(fn_code)!pc with
  | None =>
      VA.Bot
  | Some(Inop s) =>
      VA.State ae am
  | Some(Iop op args res s) =>
      let a := eval_static_operation op (aregs ae args) in
      VA.State (AE.set res a ae) am
  | Some(Iload chunk addr args dst s) =>
      let a := loadv chunk rm am (eval_static_addressing addr (aregs ae args)) in
      VA.State (AE.set dst a ae) am
  | Some(Istore chunk addr args src s) =>
      let am' := storev chunk am (eval_static_addressing addr (aregs ae args)) (areg ae src) in
      VA.State ae am'
  | Some(Icall sig ros args res s) =>
      transfer_call ae am args res
  | Some(Itailcall sig ros args) =>
      VA.Bot
  | Some(Ibuiltin ef args res s) =>
      transfer_builtin ae am rm ef args res
  | Some(Icond cond args s1 s2) =>
      VA.State ae am
  | Some(Ijumptable arg tbl) =>
      VA.State ae am
  | Some(Ireturn arg) =>
      VA.Bot
  end.

(** A wrapper on [transfer] that removes information associated with
  dead registers, so as to reduce the sizes of abstract states. *)

Definition transfer' (f: function) (lastuses: PTree.t (list reg)) (rm: romem)
                     (pc: node) (before: VA.t) : VA.t :=
  match before with
  | VA.Bot => VA.Bot
  | VA.State ae am =>
      match transfer f rm pc ae am with
      | VA.Bot => VA.Bot
      | VA.State ae' am' =>
          let ae'' :=
            match lastuses!pc with
            | None => ae'
            | Some regs => eforget regs ae'
            end in
          VA.State ae'' am'
     end
  end.

(** The forward dataflow analysis. *)

Module DS := Dataflow_Solver(VA)(NodeSetForward).

Definition mfunction_entry :=
  {| am_stack := ablock_init Pbot;
     am_glob := PTree.empty _;
     am_nonstack := Nonstack;
     am_top := Nonstack |}.

Definition analyze (rm: romem) (f: function): PMap.t VA.t :=
  let lu := Liveness.last_uses f in
  let entry := VA.State (einit_regs f.(fn_params)) mfunction_entry in
  match DS.fixpoint f.(fn_code) successors_instr (transfer' f lu rm)
                    f.(fn_entrypoint) entry with
  | None => PMap.init (VA.State AE.top mtop)
  | Some res => res
  end.

(** Constructing the approximation of read-only globals *)

Definition store_init_data (ab: ablock) (p: Z) (id: init_data) : ablock :=
  match id with
  | Init_int8 n => ablock_store Mint8unsigned ab p (I n)
  | Init_int16 n => ablock_store Mint16unsigned ab p (I n)
  | Init_int32 n => ablock_store Mint32 ab p (I n)
  | Init_int64 n => ablock_store Mint64 ab p (L n)
  | Init_float32 n => ablock_store Mfloat32 ab p
                        (if propagate_float_constants tt then FS n else ntop)
  | Init_float64 n => ablock_store Mfloat64 ab p
                        (if propagate_float_constants tt then F n else ntop)
  | Init_addrof symb ofs => ablock_store Mptr ab p (Ptr (Gl symb ofs))
  | Init_space n => ab
  end.

Fixpoint store_init_data_list (ab: ablock) (p: Z) (idl: list init_data)
                              {struct idl}: ablock :=
  match idl with
  | nil => ab
  | id :: idl' => store_init_data_list (store_init_data ab p id) (p + init_data_size id) idl'
  end.

(** When CompCert is used in separate compilation mode, the [gvar_init]
  initializer attached to a readonly global variable may not correspond
  to the actual initial value of this global.  This occurs in two cases:
- an [extern const] variable, which is represented by [gvar_init = nil];
- a [const] variable without an explicit initializer, which is treated
  by the linker as a "common" symbol, and is represented by
  [gvar_init = Init_space sz :: nil].

In both cases, the variable can be defined and initialized in another
compilation unit which is later linked with the current compilation unit. *)

Definition definitive_initializer (init: list init_data) : bool :=
  match init with
  | nil => false
  | Init_space _ :: nil => false
  | _ => true
  end.

Definition alloc_global (rm: romem) (idg: ident * globdef fundef unit): romem :=
  match idg with
  | (id, Gfun f) =>
      PTree.remove id rm
  | (id, Gvar v) =>
      if v.(gvar_readonly) && negb v.(gvar_volatile) && definitive_initializer v.(gvar_init)
      then PTree.set id (store_init_data_list (ablock_init Pbot) 0 v.(gvar_init)) rm
      else PTree.remove id rm
  end.

Definition romem_for (p: program) : romem :=
  List.fold_left alloc_global p.(prog_defs) (PTree.empty _).

(** * Soundness proof *)

(** Properties of the dataflow solution. *)

Lemma analyze_entrypoint:
  forall rm f vl m bc,
  (forall v, In v vl -> vmatch bc v (Ifptr Nonstack)) ->
  mmatch bc m mfunction_entry ->
  exists ae am,
     (analyze rm f)!!(fn_entrypoint f) = VA.State ae am
  /\ ematch bc (init_regs vl (fn_params f)) ae
  /\ mmatch bc m am.
Proof.
  intros.
  unfold analyze.
  set (lu := Liveness.last_uses f).
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry).
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu rm)
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!(fn_entrypoint f) entry) by (eapply DS.fixpoint_entry; eauto).
  destruct (res!!(fn_entrypoint f)) as [ | ae am ]; simpl in A. contradiction.
  destruct A as [A1 A2].
  exists ae, am.
  split. auto.
  split. eapply ematch_ge; eauto. apply ematch_init; auto.
  auto.
- exists AE.top, mtop.
  split. apply PMap.gi.
  split. apply ematch_ge with (einit_regs (fn_params f)).
  apply ematch_init; auto. apply AE.ge_top.
  eapply mmatch_top'; eauto.
Qed.

Lemma analyze_successor:
  forall f n ae am instr s rm ae' am',
  (analyze rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  VA.ge (analyze rm f)!!s (transfer f rm n ae am).
Proof.
  unfold analyze; intros.
  set (lu := Liveness.last_uses f) in *.
  set (entry := VA.State (einit_regs f.(fn_params)) mfunction_entry) in *.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' f lu rm)
                        (fn_entrypoint f) entry) as [res|] eqn:FIX.
- assert (A: VA.ge res!!s (transfer' f lu rm n res#n)).
  { eapply DS.fixpoint_solution; eauto with coqlib.
    intros. unfold transfer'. simpl. auto. }
  rewrite H in A. unfold transfer' in A. rewrite H2 in A. rewrite H2.
  destruct lu!n.
  eapply VA.ge_trans. eauto. split; auto. apply eforget_ge.
  auto.
- rewrite H2. rewrite PMap.gi. split; intros. apply AE.ge_top. eapply mmatch_top'; eauto.
Qed.

Lemma analyze_succ:
  forall e m rm f n ae am instr s ae' am' bc,
  (analyze rm f)!!n = VA.State ae am ->
  f.(fn_code)!n = Some instr ->
  In s (successors_instr instr) ->
  transfer f rm n ae am = VA.State ae' am' ->
  ematch bc e ae' ->
  mmatch bc m am' ->
  exists ae'' am'',
     (analyze rm f)!!s = VA.State ae'' am''
  /\ ematch bc e ae''
  /\ mmatch bc m am''.
Proof.
  intros. exploit analyze_successor; eauto. rewrite H2.
  destruct (analyze rm f)#s as [ | ae'' am'']; simpl; try tauto. intros [A B].
  exists ae'', am''.
  split. auto.
  split. eapply ematch_ge; eauto. eauto.
Qed.

(** ** Analysis of registers and builtin arguments *)

Lemma areg_sound:
  forall bc e ae r, ematch bc e ae -> vmatch bc (e#r) (areg ae r).
Proof.
  intros. apply H.
Qed.

Lemma aregs_sound:
  forall bc e ae rl, ematch bc e ae -> list_forall2 (vmatch bc) (e##rl) (aregs ae rl).
Proof.
  induction rl; simpl; intros. constructor. constructor; [apply areg_sound|]; auto.
Qed.

Global Hint Resolve areg_sound aregs_sound: va.

Lemma abuiltin_arg_sound:
  forall bc ge rs sp m ae rm am,
  ematch bc rs ae ->
  romatch bc m rm ->
  mmatch bc m am ->
  genv_match bc ge ->
  bc sp = BCstack ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  vmatch bc v (abuiltin_arg ae am rm a).
Proof.
  intros until am; intros EM RM MM GM SP.
  induction 1; simpl; eauto with va.
- eapply loadv_sound; eauto. simpl. rewrite Ptrofs.add_zero_l. auto with va.
- simpl. rewrite Ptrofs.add_zero_l. auto with va.
- eapply loadv_sound; eauto. apply symbol_address_sound; auto.
- destruct Archi.ptr64; auto with va.
Qed.

Lemma abuiltin_args_sound:
  forall bc ge rs sp m ae rm am,
  ematch bc rs ae ->
  romatch bc m rm ->
  mmatch bc m am ->
  genv_match bc ge ->
  bc sp = BCstack ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  list_forall2 (vmatch bc) vl (map (abuiltin_arg ae am rm) al).
Proof.
  intros until am; intros EM RM MM GM SP.
  induction 1; simpl.
- constructor.
- constructor; auto. eapply abuiltin_arg_sound; eauto.
Qed.

Lemma set_builtin_res_sound:
  forall bc rs ae v av res,
  ematch bc rs ae ->
  vmatch bc v av ->
  ematch bc (regmap_setres res v rs) (set_builtin_res res av ae).
Proof.
  intros. destruct res; simpl; auto. apply ematch_update; auto.
Qed.

Lemma eval_static_builtin_function_sound:
  forall bc ge rs sp m ae rm am (bf: builtin_function) al vl v va,
  ematch bc rs ae ->
  romatch bc m rm ->
  mmatch bc m am ->
  genv_match bc ge ->
  bc sp = BCstack ->
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  eval_static_builtin_function ae am rm bf al = Some va ->
  builtin_function_sem bf vl = Some v ->
  vmatch bc v va.
Proof.
  unfold eval_static_builtin_function; intros.
  exploit abuiltin_args_sound; eauto.
  set (vla := map (abuiltin_arg ae am rm) al) in *. intros VMA.
  destruct (builtin_function_sem bf (map val_of_aval vla)) as [v0|] eqn:A; try discriminate.
  assert (LD: Val.lessdef v0 v).
  { apply val_inject_lessdef.
    exploit (bs_inject _ (builtin_function_sem bf)).
    apply val_inject_list_lessdef. eapply list_val_of_aval_sound; eauto.
    rewrite A, H6; simpl. auto.
  }
  inv LD. apply aval_of_val_sound; auto. discriminate.
Qed.

(** ** Constructing block classifications *)

Definition bc_nostack (bc: block_classification) : Prop :=
  forall b, bc b <> BCstack.

Section NOSTACK.

Variable bc: block_classification.
Hypothesis NOSTACK: bc_nostack bc.

Lemma pmatch_no_stack: forall b ofs p, pmatch bc b ofs p -> pmatch bc b ofs Nonstack.
Proof.
  intros. inv H; constructor; congruence.
Qed.

Lemma vmatch_no_stack: forall v x, vmatch bc v x -> vmatch bc v (Ifptr Nonstack).
Proof.
  induction 1; constructor; auto; eapply pmatch_no_stack; eauto.
Qed.

Lemma smatch_no_stack: forall m b p, smatch bc m b p -> smatch bc m b Nonstack.
Proof.
  intros. destruct H as [A B]. split; intros.
  eapply vmatch_no_stack; eauto.
  eapply pmatch_no_stack; eauto.
Qed.

Lemma mmatch_no_stack: forall m am astk,
  mmatch bc m am -> mmatch bc m {| am_stack := astk; am_glob := PTree.empty _; am_nonstack := Nonstack; am_top := Nonstack |}.
Proof.
  intros. destruct H. constructor; simpl; intros.
- elim (NOSTACK b); auto.
- rewrite PTree.gempty in H0; discriminate.
- eapply smatch_no_stack; eauto.
- eapply smatch_no_stack; eauto.
- auto.
Qed.

End NOSTACK.

(** ** Construction 1: allocating the stack frame at function entry *)

Ltac splitall := repeat (match goal with |- _ /\ _ => split end).

Theorem allocate_stack:
  forall m sz m' sp bc ge am,
  Mem.alloc m 0 sz = (m', sp) ->
  genv_match bc ge ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ bc' sp = BCstack
  /\ genv_match bc' ge
  /\ (forall rm, romatch bc m rm -> romatch bc' m' rm)
  /\ mmatch bc' m' mfunction_entry
  /\ (forall b, sup_In b (Mem.support m) -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v (Ifptr Nonstack)).
Proof.
  intros until am; intros ALLOC GENV MM NOSTACK.
  exploit Mem.support_alloc; eauto. intros NB.
  exploit Mem.alloc_result; eauto. intros SP.
  assert (SPINVALID: bc sp = BCinvalid).
  { rewrite SP. eapply bc_below_invalid. apply freshness. eapply mmatch_below; eauto. }
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCstack else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (BC'EQ: forall b, bc b <> BCinvalid -> bc' b = bc b).
  { intros; simpl. apply dec_eq_false. congruence. }
  assert (INCR: bc_incr bc bc').
  { red; simpl; intros. apply BC'EQ; auto. }
(* Part 2: invariance properties *)
  assert (SM: forall b p, bc b <> BCinvalid -> smatch bc m b p -> smatch bc' m' b Nonstack).
  {
    intros.
    apply smatch_incr with bc; auto.
    apply smatch_inv with m.
    apply smatch_no_stack with p; auto.
    intros. eapply Mem.loadbytes_alloc_unchanged; eauto. eapply mmatch_below; eauto.
  }
  assert (SMSTACK: smatch bc' m' sp Pbot).
  {
    split; intros.
    exploit Mem.load_alloc_same; eauto. intros EQ. subst v. constructor.
    exploit Mem.loadbytes_alloc_same; eauto with coqlib. congruence.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  assumption.
- (* sp is BCstack *)
  simpl; apply dec_eq_true.
- (* genv match *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* romatch *)
  intros rm RO.
  apply romatch_exten with bc.
  eapply romatch_alloc; eauto. eapply mmatch_below; eauto.
  simpl; intros. destruct (eq_block b sp); intuition.
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. apply SMSTACK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp).
    subst b. apply smatch_ge with Pbot. apply SMSTACK. constructor.
    eapply SM; auto. eapply mmatch_top; eauto.
  + (* below *)
    red; simpl; intros. rewrite NB. destruct (eq_block b sp).
    subst b; rewrite SP. apply Mem.mem_incr_1.
    exploit mmatch_below; eauto. intro. apply Mem.mem_incr_2. auto.
- (* unchanged *)
  simpl; intros. apply dec_eq_false. intro. subst b.
  assert (~ sup_In sp (Mem.support m)). rewrite SP. apply freshness. congruence.
- (* values *)
  intros. apply vmatch_incr with bc; auto. eapply vmatch_no_stack; eauto.
Qed.

(** Construction 2: turn the stack into an "other" block, at public calls or function returns *)

Theorem anonymize_stack:
  forall m sp bc ge am,
  genv_match bc ge ->
  mmatch bc m am ->
  bc sp = BCstack ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCother
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ (forall rm, romatch bc m rm -> romatch bc' m rm)
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV MM SP.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCother else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate.
    eapply bc_stack; eauto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate.
    eapply bc_glob; eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch bc v x -> vmatch bc' v Vtop).
  {
    induction 1; constructor; eauto.

  }
  assert (SM: forall b p, smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H as [S1 S2]. split; intros.
    eapply VM. eapply S1; eauto.
    eapply PM. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence.
  red; intros. elim n. eapply bc_stack; eauto.
- (* bc' sp is BCother *)
  simpl; apply dec_eq_true.
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto.
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); auto.
- (* romatch *)
  intros rm RO.
  apply romatch_exten with bc; auto.
  simpl; intros. destruct (eq_block b sp); intuition.
- (* mmatch top *)
  constructor; simpl; intros.
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_nonstack; eauto.
  + destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_stack; eauto.
    eapply SM. eapply mmatch_top; eauto.
  + red; simpl; intros. destruct (eq_block b sp).
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
Qed.

(** Construction 3: turn the stack into an invalid block, at private calls *)

Theorem hide_stack:
  forall m sp bc ge am,
  genv_match bc ge ->
  mmatch bc m am ->
  bc sp = BCstack ->
  pge Nonstack am.(am_nonstack) ->
  exists bc',
     bc_nostack bc'
  /\ bc' sp = BCinvalid
  /\ (forall b, b <> sp -> bc' b = bc b)
  /\ (forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop)
  /\ genv_match bc' ge
  /\ (forall rm, romatch bc m rm -> romatch bc' m rm)
  /\ mmatch bc' m mtop.
Proof.
  intros until am; intros GENV MM SP NOLEAK.
(* Part 1: constructing bc' *)
  set (f := fun b => if eq_block b sp then BCinvalid else bc b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate.
    eapply bc_stack; eauto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (eq_block b1 sp); try discriminate.
    destruct (eq_block b2 sp); try discriminate.
    eapply bc_glob; eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.

(* Part 2: matching wrt bc' *)
  assert (PM: forall b ofs p, pge Nonstack p -> pmatch bc b ofs p -> pmatch bc' b ofs Ptop).
  {
    intros. assert (pmatch bc b ofs Nonstack) by (eapply pmatch_ge; eauto).
    inv H1. constructor; simpl; destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vge (Ifptr Nonstack) x -> vmatch bc v x -> vmatch bc' v Vtop).
  {
    intros. apply vmatch_ifptr; intros. subst v.
    inv H0; inv H; eapply PM; eauto.
  }
  assert (SM: forall b p, pge Nonstack p -> smatch bc m b p -> smatch bc' m b Ptop).
  {
    intros. destruct H0 as [S1 S2]. split; intros.
    eapply VM with (x := Ifptr p). constructor; auto. eapply S1; eauto.
    eapply PM. eauto. eapply S2; eauto.
  }
(* Conclusions *)
  exists bc'; splitall.
- (* nostack *)
  red; simpl; intros. destruct (eq_block b sp). congruence.
  red; intros. elim n. eapply bc_stack; eauto.
- (* bc' sp is BCinvalid *)
  simpl; apply dec_eq_true.
- (* other blocks *)
  intros; simpl; apply dec_eq_false; auto.
- (* values *)
  auto.
- (* genv *)
  apply genv_match_exten with bc; auto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* romatch *)
  intros rm RO.
  apply romatch_exten with bc; auto.
  simpl; intros. destruct (eq_block b sp); intuition.
- (* mmatch top *)
  constructor; simpl; intros.
  + destruct (eq_block b sp). congruence. elim n. eapply bc_stack; eauto.
  + rewrite PTree.gempty in H0; discriminate.
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto.
  + destruct (eq_block b sp). congruence.
    eapply SM. eauto. eapply mmatch_nonstack; eauto.
    red; intros; elim n. eapply bc_stack; eauto.
  + red; simpl; intros. destruct (eq_block b sp). congruence.
    eapply mmatch_below; eauto.
Qed.

(** Construction 4: restore the stack after a public call *)

Theorem return_from_public_call:
  forall (caller callee: block_classification) bound sp ge e ae v m,
  bc_below caller bound ->
  callee sp = BCother ->
  caller sp = BCstack ->
  (forall b, sup_In b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  Mem.sup_include bound (Mem.support m) ->
  vmatch callee v Vtop ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v Vtop
   /\ ematch bc e ae
   /\ (forall rm, romatch callee m rm -> romatch bc m rm)
   /\ mmatch bc m mafter_public_call
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, sup_In b bound -> bc b = caller b).
Proof.
  intros until m; intros BELOW SP1 SP2 SAME GE1 EM BOUND RESM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto.
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence.
    symmetry; apply SAME; auto.
  }
(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Ptop).
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl. destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v Vtop).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto).
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Ptop).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto.
- (* romem *)
  intros rm RM.
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition.
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    apply ablock_init_sound. destruct (eq_block b sp).
    subst b. eapply SM. eapply mmatch_nonstack; eauto. congruence.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    eapply SM. eapply mmatch_top; eauto.
    destruct (eq_block b sp); congruence.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp).
    subst b. eapply mmatch_below; eauto. congruence.
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten with caller; eauto.
  simpl; intros. destruct (eq_block b sp). intuition congruence.
  split; intros. rewrite SAME in H by eauto with va. auto.
  apply <- (proj1 GE2) in H. apply (proj1 GE1) in H. auto.
  simpl; intros. destruct (eq_block b sp). congruence.
  rewrite <- SAME; eauto with va.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence.
  symmetry. apply SAME; auto.
Qed.

(** Construction 5: restore the stack after a private call *)

Theorem return_from_private_call:
  forall (caller callee: block_classification) bound sp ge e ae v m am,
  bc_below caller bound ->
  callee sp = BCinvalid ->
  caller sp = BCstack ->
  (forall b, sup_In b bound -> b <> sp -> caller b = callee b) ->
  genv_match caller ge ->
  ematch caller e ae ->
  bmatch caller m sp am.(am_stack) ->
  Mem.sup_include bound (Mem.support m) ->
  vmatch callee v Vtop ->
  mmatch callee m mtop ->
  genv_match callee ge ->
  bc_nostack callee ->
  exists bc,
      vmatch bc v (Ifptr Nonstack)
   /\ ematch bc e ae
   /\ (forall rm, romatch callee m rm -> romatch bc m rm)
   /\ mmatch bc m (mafter_private_call am)
   /\ genv_match bc ge
   /\ bc sp = BCstack
   /\ (forall b, sup_In b bound -> bc b = caller b).
Proof.
  intros until am; intros BELOW SP1 SP2 SAME GE1 EM CONTENTS BOUND RESM MM GE2 NOSTACK.
(* Constructing bc *)
  set (f := fun b => if eq_block b sp then BCstack else callee b).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> b = sp).
    { unfold f; intros. destruct (eq_block b sp); auto. eelim NOSTACK; eauto. }
    intros. transitivity sp; auto. symmetry; auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> callee b = BCglob id).
    { unfold f; intros. destruct (eq_block b sp). congruence. auto. }
    intros. eapply (bc_glob callee); eauto.
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  assert (INCR1: bc_incr caller bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence.
    symmetry; apply SAME; auto.
  }
  assert (INCR2: bc_incr callee bc).
  {
    red; simpl; intros. destruct (eq_block b sp). congruence. auto.
  }

(* Invariance properties *)
  assert (PM: forall b ofs p, pmatch callee b ofs p -> pmatch bc b ofs Nonstack).
  {
    intros. assert (pmatch callee b ofs Ptop) by (eapply pmatch_top'; eauto).
    inv H0. constructor; simpl; destruct (eq_block b sp); congruence.
  }
  assert (VM: forall v x, vmatch callee v x -> vmatch bc v (Ifptr Nonstack)).
  {
    intros. assert (vmatch callee v0 Vtop) by (eapply vmatch_top; eauto).
    inv H0; constructor; eauto.
  }
  assert (SM: forall b p, smatch callee m b p -> smatch bc m b Nonstack).
  {
    intros. destruct H; split; intros. eapply VM; eauto. eapply PM; eauto.
  }
  assert (BSTK: bmatch bc m sp (am_stack am)).
  {
    apply bmatch_incr with caller; eauto.
  }
(* Conclusions *)
  exists bc; splitall.
- (* result value *)
  eapply VM; eauto.
- (* environment *)
  eapply ematch_incr; eauto.
- (* romem *)
  intros rm RO.
  apply romatch_exten with callee; auto.
  intros; simpl. destruct (eq_block b sp); intuition.
- (* mmatch *)
  constructor; simpl; intros.
  + (* stack *)
    destruct (eq_block b sp).
    subst b. exact BSTK.
    elim (NOSTACK b); auto.
  + (* globals *)
    rewrite PTree.gempty in H0; discriminate.
  + (* nonstack *)
    destruct (eq_block b sp). congruence. eapply SM; auto. eapply mmatch_nonstack; eauto.
  + (* top *)
    destruct (eq_block b sp).
    subst. apply smatch_ge with (ab_summary (am_stack am)). apply BSTK. apply pge_lub_l.
    apply smatch_ge with Nonstack. eapply SM. eapply mmatch_top; eauto. apply pge_lub_r.
  + (* below *)
    red; simpl; intros. destruct (eq_block b sp).
    subst b. apply BOUND. apply BELOW. congruence. auto.
    eapply mmatch_below; eauto.
- (* genv *)
  eapply genv_match_exten; eauto.
  simpl; intros. destruct (eq_block b sp); intuition congruence.
  simpl; intros. destruct (eq_block b sp); congruence.
- (* sp *)
  simpl. apply dec_eq_true.
- (* unchanged *)
  simpl; intros. destruct (eq_block b sp). congruence.
  symmetry. apply SAME; auto.
Qed.

(** Construction 6: external call *)

Theorem external_call_match:
  forall ef ge vargs m t vres m' bc am,
  external_call ef ge vargs m t vres m' ->
  genv_match bc ge ->
  (forall v, In v vargs -> vmatch bc v Vtop) ->
  mmatch bc m am ->
  bc_nostack bc ->
  exists bc',
     bc_incr bc bc'
  /\ (forall b, sup_In b (Mem.support m) -> bc' b = bc b)
  /\ vmatch bc' vres Vtop
  /\ genv_match bc' ge
  /\ (forall rm, romatch bc m rm -> romatch bc' m' rm)
  /\ mmatch bc' m' mtop
  /\ bc_nostack bc'
  /\ (forall b ofs n, Mem.valid_block m b -> bc b = BCinvalid -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n).
Proof.
  intros until am; intros EC GENV ARGS MM NOSTACK.
  (* Part 1: using ec_mem_inject *)
  exploit (@external_call_mem_inject ef ge ge vargs m t vres m' (inj_of_bc bc) m vargs).
  apply inj_of_bc_preserves_globals; auto.
  exact EC.
  eapply mmatch_inj; eauto. eapply mmatch_below; eauto.
  revert ARGS. generalize vargs.
  induction vargs0; simpl; intros; constructor.
  eapply vmatch_inj; eauto. auto.
  intros (j' & vres' & m'' & EC' & IRES & IMEM & UNCH1 & UNCH2 & IINCR & ISEP).
  assert (JBELOW: forall b, sup_In b (Mem.support m) -> j' b = inj_of_bc bc b).
  {
    intros. destruct (inj_of_bc bc b) as [[b' delta] | ] eqn:EQ.
    eapply IINCR; eauto.
    destruct (j' b) as [[b'' delta'] | ] eqn:EQ'; auto.
    exploit ISEP; eauto. tauto.
  }
  (* Part 2: constructing bc' from j' *)
  set (f := fun b => if Mem.sup_dec b (Mem.support m)
                     then bc b
                     else match j' b with None => BCinvalid | Some _ => BCother end).
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    assert (forall b, f b = BCstack -> bc b = BCstack).
    { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
    intros. apply (bc_stack bc); auto.
  }
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    assert (forall b id, f b = BCglob id -> bc b = BCglob id).
    { unfold f; intros. destruct (Mem.sup_dec b (Mem.support m)); auto. destruct (j' b); discriminate. }
    intros. eapply (bc_glob bc); eauto.
  }
  set (bc' := BC f F_stack F_glob). unfold f in bc'.
  assert (INCR: bc_incr bc bc').
  {
    red; simpl; intros. apply pred_dec_true. eapply mmatch_below; eauto.
  }
  assert (BC'INV: forall b, bc' b <> BCinvalid -> exists b' delta, j' b = Some(b', delta)).
  {
    simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
    exists b, 0. rewrite JBELOW by auto. apply inj_of_bc_valid; auto.
    destruct (j' b) as [[b' delta] | ].
    exists b', delta; auto.
    congruence.
  }

  (* Part 3: injection wrt j' implies matching with top wrt bc' *)
  assert (PMTOP: forall b b' delta ofs, j' b = Some (b', delta) -> pmatch bc' b ofs Ptop).
  {
    intros. constructor. simpl; unfold f.
    destruct (Mem.sup_dec b (Mem.support m)).
    rewrite JBELOW in H by auto. eapply inj_of_bc_inv; eauto.
    rewrite H; congruence.
  }
  assert (VMTOP: forall v v', Val.inject j' v v' -> vmatch bc' v Vtop).
  {
    intros. inv H; constructor. eapply PMTOP; eauto.
  }
  assert (SMTOP: forall b, bc' b <> BCinvalid -> smatch bc' m' b Ptop).
  {
    intros; split; intros.
  - exploit BC'INV; eauto. intros (b' & delta & J').
    exploit Mem.load_inject. eexact IMEM. eauto. eauto. intros (v' & A & B).
    eapply VMTOP; eauto.
  - exploit BC'INV; eauto. intros (b'' & delta & J').
    exploit Mem.loadbytes_inject. eexact IMEM. eauto. eauto. intros (bytes & A & B).
    inv B. inv H3. inv H7. eapply PMTOP; eauto.
  }
  (* Conclusions *)
  exists bc'; splitall.
- (* incr *)
  exact INCR.
- (* unchanged *)
  simpl; intros. apply pred_dec_true; auto.
- (* vmatch res *)
  eapply VMTOP; eauto.
- (* genv match *)
  apply genv_match_exten with bc; auto.
  simpl; intros; split; intros.
  rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
  destruct (Mem.sup_dec b (Mem.support m)). auto. destruct (j' b); congruence.
  simpl; intros. rewrite pred_dec_true by (eapply mmatch_below; eauto with va). auto.
- (* romatch m' *)
  intros rm RO.
  red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
  + 
  exploit RO; eauto. intros (R & P & Q).
  split; auto.
  split. apply bmatch_incr with bc; auto. apply bmatch_ext with m; auto.
  intros. eapply external_call_readonly with (m2 := m'); eauto.
  intros; red; intros; elim (Q ofs).
  eapply external_call_max_perm with (m2 := m'); eauto.
  + destruct (j' b); congruence.
- (* mmatch top *)
  constructor; simpl; intros.
  + apply ablock_init_sound. apply SMTOP. simpl; congruence.
  + rewrite PTree.gempty in H0; discriminate.
  + apply SMTOP; auto.
  + apply SMTOP; auto.
  + red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
    eapply external_call_support; eauto.
    destruct (j' b) as [[bx deltax] | ] eqn:J'.
    eapply Mem.valid_block_inject_1; eauto.
    congruence.
- (* nostack *)
  red; simpl; intros. destruct (Mem.sup_dec b (Mem.support m)).
  apply NOSTACK; auto.
  destruct (j' b); congruence.
- (* unmapped blocks are invariant *)
  intros. eapply Mem.loadbytes_unchanged_on_1; auto.
  apply UNCH1; auto. intros; red. unfold inj_of_bc; rewrite H0; auto.
Qed.


(** romem derived from symtbl *)

Definition romem_consistent (defmap: PTree.t (globdef fundef unit)) (rm: romem) :=
  forall id ab,
  rm!id = Some ab ->
  exists v,
     defmap!id = Some (Gvar v)
  /\ v.(gvar_readonly) = true
  /\ v.(gvar_volatile) = false
  /\ definitive_initializer v.(gvar_init) = true
  /\ ab = store_init_data_list (ablock_init Pbot) 0 v.(gvar_init).

Lemma alloc_global_consistent:
  forall dm rm idg,
  romem_consistent dm rm ->
  romem_consistent (PTree.set (fst idg) (snd idg) dm) (alloc_global rm idg).
Proof.
  intros; red; intros. destruct idg as [id1 [f1 | v1]]; simpl in *.
- rewrite PTree.grspec in H0. destruct (PTree.elt_eq id id1); try discriminate.
  rewrite PTree.gso by auto. apply H; auto.
- destruct (gvar_readonly v1 && negb (gvar_volatile v1) && definitive_initializer (gvar_init v1)) eqn:RO.
+ InvBooleans. rewrite negb_true_iff in H4.
  rewrite PTree.gsspec in *. destruct (peq id id1).
* inv H0. exists v1; auto.
* apply H; auto.
+ rewrite PTree.grspec in H0. destruct (PTree.elt_eq id id1); try discriminate.
  rewrite PTree.gso by auto. apply H; auto.
Qed.

Lemma romem_for_consistent:
  forall cunit, romem_consistent (prog_defmap cunit) (romem_for cunit).
Proof.
  assert (REC: forall l dm rm,
            romem_consistent dm rm ->
            romem_consistent (fold_left (fun m idg => PTree.set (fst idg) (snd idg) m) l dm)
                             (fold_left alloc_global l rm)).
  { induction l; intros; simpl; auto. apply IHl. apply alloc_global_consistent; auto. }
  intros. apply REC.
  red; intros. rewrite PTree.gempty in H; discriminate.
Qed.

Definition check_add_global (se : Genv.symtbl)
  (b:block)(rm : romem) : romem :=
  match Genv.invert_symbol se b with
  | Some id =>
      match NMap.get _ b (Genv.find_info se) with
      | Some (Gvar v) =>
          if v.(gvar_readonly) && negb v.(gvar_volatile) && definitive_initializer v.(gvar_init)
          then PTree.set id (store_init_data_list (ablock_init Pbot) 0 v.(gvar_init)) rm
          else PTree.remove id rm
      | _ => PTree.remove id rm
      end
  | None => rm
  end.
                            
Definition romem_for_symtbl (se : Genv.symtbl) : romem :=
  fold_right (check_add_global se)  (PTree.empty ablock) (Mem.sup_list (Genv.genv_sup se)).

Lemma check_add_global_diff:
  forall a b se id map,
    a <> b ->
    Genv.find_symbol se id = Some b ->
    (check_add_global se a map) ! id = map ! id.
Proof.
  intros. unfold check_add_global.
  destruct Genv.invert_symbol eqn:INV; eauto.
  assert (i <> id).
  {
    apply Genv.invert_find_symbol in INV.
    congruence.
  }
  destruct NMap.get eqn:INFO; eauto.
  destruct g; eauto.
  rewrite PTree.gro; eauto.
  destruct ( gvar_readonly v && negb (gvar_volatile v) && definitive_initializer (gvar_init v)).
  rewrite PTree.gso; eauto.
  rewrite PTree.gro; eauto.
  rewrite PTree.gro; eauto.
Qed.

Lemma romem_for_in : forall l se b (F:Type) (g0: globdef F unit) (v: globvar unit) g id,
      In b l ->
      Genv.find_symbol se id = Some b ->
      Genv.find_info se b = Some g ->
      g0 = Gvar v ->
      linkorder (erase_globdef g0) g -> 
      gvar_readonly v = true ->
      gvar_volatile v = false ->
      definitive_initializer (gvar_init v) = true ->
      (fold_right (check_add_global se) (PTree.empty ablock) l) ! id = Some (store_init_data_list (ablock_init Pbot) 0 (gvar_init v)).
Proof.
  induction l; intros. inv H.
  destruct H.
  - subst. simpl. unfold check_add_global.
    simpl.
    exploit Genv.find_invert_symbol; eauto.
    intro INV. rewrite INV. unfold Genv.find_info in H1.
    setoid_rewrite H1.
    unfold erase_globdef in H3.
    unfold erase_globvar in H3. inv H3.
    inv H2. simpl. rewrite H4. rewrite H5.
    inv H11.
    + 
    rewrite H6. simpl.
    rewrite PTree.gss. reflexivity.
    + rewrite <- H2 in H6. inv H6.
    + rewrite <- H in H6. inv H6.
  - destruct (eq_block a b).
    + subst.
      simpl. unfold check_add_global.
      simpl.
      exploit Genv.find_invert_symbol; eauto.
      intro INV. rewrite INV. unfold Genv.find_info in H1.
      setoid_rewrite H1.
      unfold erase_globdef in H3.
      unfold erase_globvar in H3. inv H3.
      inv H7. simpl. rewrite H4. rewrite H5.
      inv H12.
      -- 
        rewrite H6. simpl.
        rewrite PTree.gss. reflexivity.
      -- rewrite <- H3 in H6. inv H6.
      -- rewrite <- H2 in H6. inv H6.
    +
      exploit IHl; eauto.
      intro. simpl.
      erewrite check_add_global_diff; eauto.
Qed.

Lemma romem_symtbl_prog : forall se prog id ab,
    Genv.valid_for (erase_program prog) se ->
    (romem_for prog) ! id = Some ab ->
    (romem_for_symtbl se) ! id = Some ab.
Proof.
  intros. red in H.
  generalize (romem_for_consistent prog).
  intro CONSIS. exploit CONSIS; eauto.
  intros (v & MAP & RO & VOL & DEF & AB).
  exploit H.
  rewrite erase_program_defmap.
  unfold option_map.
  erewrite MAP. reflexivity.
  intros (b & g & FIND & INFO & LINK).
  subst ab. eapply romem_for_in; eauto.
  apply Mem.sup_list_in.
  eapply Genv.genv_info_range; eauto.
Qed.
  
Theorem romatch_symtbl_prog : forall bc se prog m,
    Genv.valid_for (erase_program prog) se ->
    romatch bc m (romem_for_symtbl se) ->
    romatch bc m (romem_for prog).
Proof.
  intros. red in H. red in H0.
  constructor.
  - exploit H0; eauto.
    eapply romem_symtbl_prog; eauto.
    intros [A B]. eauto.
  - exploit H0; eauto.
    eapply romem_symtbl_prog; eauto.
    intros [A B]. eauto.
Qed.

(** ** Semantic invariant *)

Section SOUNDNESS.

Variable prog: program.
Variable ge: Genv.symtbl.
(* 
Variable m0: mem.
Variable bc0: block_classification.
*)
Hypothesis GEVALID: Genv.valid_for (erase_program prog) ge.

Let rm := romem_for prog.
Let rmge := romem_for_symtbl ge.

(** For the most part, the invariant characterizes the state in terms
  of the specific analysis of [prog] using the [romem] defined
  above. However, the interaction predicates cannot depend on a
  specific compilation unit, and must be strong enough to establish
  the invariant for *any* compilation unit [cu] compatible with the
  symbol table [ge]. To this effect, we use the following property to
  ensure global constants have appropriatea value in the concrete
  memory state. *)

(* Definition romatch_all bc m :=
  forall cu,
    Genv.valid_for (erase_program cu) ge ->
    romatch bc m (romem_for cu). *)

(** State invariant. *)

Inductive sound_stack: block_classification -> list stackframe -> mem -> sup -> Prop :=
  | sound_stack_nil: forall (bc: block_classification) m bound,
(*      (forall b, sup_In b (Mem.support m0) -> bc b = bc0 b) ->
      (forall b ofs n bytes,
          sup_In b (Mem.support m0) -> bc b = BCinvalid -> n >= 0 ->
          Mem.loadbytes m b ofs n = Some bytes ->
          Mem.loadbytes m0 b ofs n = Some bytes) ->
      Mem.sup_include (Mem.support m0) bound ->
*)
      sound_stack bc nil m bound
  | sound_stack_public_call:
      forall (bc: block_classification) res f sps sp pc e stk m bound bc' bound' ae
        (SPS: sp = fresh_block sps)
        (STK: sound_stack bc' stk m sps)
        (INCR: Mem.sup_include bound' bound)
        (SINCR: Mem.sup_include (sup_incr sps) bound')
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCother)
        (SP': bc' sp = BCstack)
        (SAME: forall b, sup_In b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res Vtop ae) mafter_public_call))
        (EM: ematch bc' e ae),
      sound_stack bc (Stackframe res f (Vptr sp Ptrofs.zero) pc e :: stk) m bound
  | sound_stack_private_call:
     forall (bc: block_classification) res f sps sp pc e stk m bound bc' bound' ae am
        (SPS: sp = fresh_block sps)
        (STK: sound_stack bc' stk m sps)
        (SINCR: Mem.sup_include (sup_incr sps) bound')
        (INCR: Mem.sup_include bound' bound)
        (BELOW: bc_below bc' bound')
        (SP: bc sp = BCinvalid)
        (SP': bc' sp = BCstack)
        (SAME: forall b, sup_In b bound' -> b <> sp -> bc b = bc' b)
        (GE: genv_match bc' ge)
        (AN: VA.ge (analyze rm f)!!pc (VA.State (AE.set res (Ifptr Nonstack) ae) (mafter_private_call am)))
        (EM: ematch bc' e ae)
        (CONTENTS: bmatch bc' m sp am.(am_stack)),
      sound_stack bc (Stackframe res f (Vptr sp Ptrofs.zero) pc e :: stk) m bound.

Inductive sound_state: state -> Prop :=
  | sound_regular_state:
      forall s f sps sp pc e m ae am bc
        (SPS: sp = fresh_block sps)
        (SINCR: Mem.sup_include (sup_incr sps) (Mem.support m))
        (STK: sound_stack bc s m sps)
        (AN: (analyze rm f)!!pc = VA.State ae am)
        (EM: ematch bc e ae)
        (RO: romatch bc m rmge)
        (MM: mmatch bc m am)
        (GE: genv_match bc ge)
        (SP: bc sp = BCstack),
      sound_state (State s f (Vptr sp Ptrofs.zero) pc e m)
  | sound_call_state:
      forall s fd args m bc
        (STK: sound_stack bc s m (Mem.support m))
        (VF: vmatch bc fd Vtop)
        (ARGS: forall v, In v args -> vmatch bc v Vtop)
        (RO: romatch bc m rmge)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Callstate s fd args m)
  | sound_return_state:
      forall s v m bc
        (STK: sound_stack bc s m (Mem.support m))
        (RES: vmatch bc v Vtop)
        (RO: romatch bc m rmge)
        (MM: mmatch bc m mtop)
        (GE: genv_match bc ge)
        (NOSTK: bc_nostack bc),
      sound_state (Returnstate s v m).

(** Properties of the [sound_stack] invariant on call stacks. *)

Lemma sound_stack_ext:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n bytes,
       sup_In b bound -> bc b = BCinvalid -> n >= 0 ->
       Mem.loadbytes m' b ofs n = Some bytes ->
       Mem.loadbytes m b ofs n = Some bytes) ->
  sound_stack bc stk m' bound.
Proof.
  induction 1; intros INV.
- (* assert (forall b, sup_In b (Mem.support m0) -> sup_In b bound) by (intros; eauto). *)
  constructor; auto.
- assert (sup_In sp bound') by eauto with va.
  eapply sound_stack_public_call; eauto. apply IHsound_stack; intros.
  apply INV.
  eapply Mem.sup_include_trans. eauto. auto. apply Mem.sup_incr_in2. auto.
  rewrite SAME; auto with ordered_type.
  apply SINCR. apply Mem.sup_incr_in2.  auto.
  intro. subst b. assert(~ sup_In (fresh_block sps) sps) by apply freshness.
  congruence.
  auto. auto.
- assert (sup_In sp bound') by eauto with va.
  eapply sound_stack_private_call; eauto. apply IHsound_stack; intros.
  apply INV.
  eapply Mem.sup_include_trans. apply SINCR. auto. apply Mem.sup_incr_in2. auto.
  rewrite SAME; auto with ordered_type. apply SINCR. apply Mem.sup_incr_in2. auto.
  intro. subst b. assert(~ sup_In (fresh_block sps) sps) by apply freshness. congruence.
  auto. auto.
  apply bmatch_ext with m; auto.
Qed.

Lemma sound_stack_inv:
  forall m' bc stk m bound,
  sound_stack bc stk m bound ->
  (forall b ofs n, sup_In b bound -> bc b = BCinvalid -> n >= 0 -> Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros. rewrite <- H0; auto.
Qed.

Lemma sound_stack_storev:
  forall chunk m addr v m' bc aaddr stk bound,
  Mem.storev chunk m addr v = Some m' ->
  vmatch bc addr aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto.
  destruct addr; simpl in H; try discriminate.
  assert (A: pmatch bc b i Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A.
  intros. eapply Mem.loadbytes_store_other; eauto. left; congruence.
Qed.

Lemma sound_stack_storebytes:
  forall m b ofs bytes m' bc aaddr stk bound,
  Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
  vmatch bc (Vptr b ofs) aaddr ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. apply sound_stack_inv with m; auto.
  assert (A: pmatch bc b ofs Ptop).
  { inv H0; eapply pmatch_top'; eauto. }
  inv A.
  intros. eapply Mem.loadbytes_storebytes_other; eauto. left; congruence.
Qed.

Lemma sound_stack_free:
  forall m b lo hi m' bc stk bound,
  Mem.free m b lo hi = Some m' ->
  sound_stack bc stk m bound ->
  sound_stack bc stk m' bound.
Proof.
  intros. eapply sound_stack_ext; eauto. intros.
  eapply Mem.loadbytes_free_2; eauto.
Qed.

Lemma sound_stack_new_bound:
  forall bc stk m bound bound',
  sound_stack bc stk m bound ->
  Mem.sup_include bound bound' ->
  sound_stack bc stk m bound'.
Proof.
  intros. inv H.
- constructor; eauto.
- eapply sound_stack_public_call with (bound' := bound'0); eauto.
- eapply sound_stack_private_call with (bound' := bound'0); eauto.
Qed.

Lemma sound_stack_exten:
  forall bc stk m bound (bc1: block_classification),
  sound_stack bc stk m bound ->
  (forall b, sup_In b bound -> bc1 b = bc b) ->
  sound_stack bc1 stk m bound.
Proof.
  intros. inv H.
- constructor; eauto.
(*  + intros. rewrite H0 by eauto. auto.
  + intros. eapply H2; auto. rewrite <- H0; auto.
*)
- assert (sup_In (fresh_block sps) bound') by eauto with va.
  eapply sound_stack_public_call; eauto.
  rewrite H0; auto.
  intros. rewrite H0; auto.
- assert (sup_In (fresh_block sps) bound') by eauto with va.
  eapply sound_stack_private_call; eauto.
  rewrite H0; auto.
  intros. rewrite H0; auto.
Qed.

(** For compatibility with CKLRs, we show the soundness of function
  pointers in call states. *)

Lemma find_funct_sound bc vf fd:
  genv_match bc ge ->
  Genv.find_funct (Genv.globalenv ge prog) vf = Some fd ->
  vmatch bc vf (Ifptr Nonstack).
Proof.
  intros GEMATCH Hfd.
  destruct vf; try discriminate. cbn in *.
  destruct Ptrofs.eq_dec; try discriminate. subst.
  apply Genv.find_funct_ptr_iff in Hfd.
  apply Genv.genv_defs_range in Hfd.
  constructor. constructor; apply GEMATCH; auto.
Qed.

(** ** Preservation of the semantic invariant by one step of execution *)

Lemma sound_succ_state:
  forall bc pc ae am instr ae' am'  s f sps sp pc' e' m',
  (analyze rm f)!!pc = VA.State ae am ->
  f.(fn_code)!pc = Some instr ->
  In pc' (successors_instr instr) ->
  transfer f rm pc ae am = VA.State ae' am' ->
  sp = fresh_block sps ->
  Mem.sup_include (sup_incr sps) (Mem.support m') ->
  ematch bc e' ae' ->
  mmatch bc m' am' ->
  romatch bc m' rmge ->
  genv_match bc ge ->
  bc sp = BCstack ->
  sound_stack bc s m' sps ->
  sound_state (State s f (Vptr sp Ptrofs.zero) pc' e' m').
Proof.
  intros. exploit analyze_succ; eauto. intros (ae'' & am'' & AN & EM & MM).
  econstructor; eauto.
Qed.

Theorem sound_step:
  forall st t st', RTL.step (Genv.globalenv ge prog) st t st' -> sound_state st -> sound_state st'.
Proof.
  induction 1; intros SOUND; inv SOUND.

- (* nop *)
  eapply sound_succ_state; eauto. simpl; auto.
  unfold transfer; rewrite H. auto.

- (* op *)
  eapply sound_succ_state; eauto. simpl; auto.
  unfold transfer; rewrite H. eauto.
  apply ematch_update; auto. eapply eval_static_operation_sound; eauto with va.

- (* load *)
  eapply sound_succ_state; eauto. simpl; auto.
  unfold transfer; rewrite H. eauto.
  apply ematch_update; auto. eapply loadv_sound; eauto with va.
  eapply romatch_symtbl_prog; eauto.
  eapply eval_static_addressing_sound; eauto with va.

- (* store *)
  exploit eval_static_addressing_sound; eauto with va. intros VMADDR.
  eapply sound_succ_state; eauto. simpl; auto.
  unfold transfer; rewrite H. eauto.
  erewrite <- Mem.support_storev. eauto. eauto.
  eapply storev_sound; eauto.
  destruct a; simpl in H1; try discriminate. eauto using romatch_store.
  eapply sound_stack_storev; eauto.

- (* call *)
  assert (TR: transfer f rm pc ae am = transfer_call ae am args res).
  { unfold transfer; rewrite H; auto. }
  unfold transfer_call, analyze_call in TR.
  destruct (pincl (am_nonstack am) Nonstack &&
            forallb (fun av => vpincl av Nonstack) (aregs ae args)) eqn:NOLEAK.
+ (* private call *)
  InvBooleans.
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC.
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_private_call with (bound' := Mem.support m) (bc' := bc); eauto.
    eauto.
    eapply mmatch_below; eauto.
    eapply mmatch_stack; eauto.
  * eauto using vmatch_top, find_funct_sound.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v.
    apply D with (areg ae r).
    rewrite forallb_forall in H2. apply vpincl_ge.
    apply H2. apply in_map; auto.
    auto with va.
+ (* public call *)
  exploit analyze_successor; eauto. simpl; eauto. rewrite TR. intros SUCC.
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  * eapply sound_stack_public_call with (bound' := Mem.support m) (bc' := bc); eauto.
    eapply mmatch_below; eauto.
  * eauto using vmatch_top, find_funct_sound.
  * intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v.
    apply D with (areg ae r). auto with va.

- (* tailcall *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_call_state with bc'; auto.
  erewrite Mem.support_free by eauto.
  apply sound_stack_new_bound with sps.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. intro. eapply freshness. rewrite H3 in H1. eauto.
  eapply Mem.sup_include_trans; eauto.
  eauto using vmatch_top, find_funct_sound.
  intros. exploit list_in_map_inv; eauto. intros (r & P & Q). subst v.
  apply D with (areg ae r). auto with va.
  eauto using romatch_free.
  eapply mmatch_free; eauto.

- (* builtin *)
  assert (SPVALID: sup_In (fresh_block sps) (Mem.support m)) by (eapply mmatch_below; eauto with va).
  assert (TR: transfer f rm pc ae am = transfer_builtin ae am rm ef args res).
  { unfold transfer; rewrite H; auto. }
  (* The default case *)
  assert (DEFAULT:
            transfer f rm pc ae am = transfer_builtin_default ae am rm args res ->
            sound_state
               (State s f (Vptr (fresh_block sps) Ptrofs.zero) pc' (regmap_setres res vres rs) m')).
  { unfold transfer_builtin_default, analyze_call; intros TR'.
  set (aargs := map (abuiltin_arg ae am rm) args) in *.
  assert (ARGS: list_forall2 (vmatch bc) vargs aargs).
  { eapply abuiltin_args_sound; eauto.   eapply romatch_symtbl_prog; eauto. }
  destruct (pincl (am_nonstack am) Nonstack &&
            forallb (fun av => vpincl av Nonstack) aargs)
        eqn: NOLEAK.
* (* private builtin call *)
  InvBooleans. rewrite forallb_forall in H3.
  exploit hide_stack; eauto. apply pincl_ge; auto.
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto.
  intros. exploit list_forall2_in_left; eauto. intros (av & U & V).
  eapply D; eauto with va. apply vpincl_ge. apply H3; auto.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_private_call bc bc2).
  eapply mmatch_below; eauto.
  rewrite K. apply B. auto. auto.
  intros. rewrite K; auto. rewrite C; auto.
  eauto. eauto.
  apply bmatch_inv with m. eapply mmatch_stack; eauto.
  intros. apply Q; auto.
  eapply external_call_support; eauto.
  eauto. eauto. eauto. eauto. eauto.
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto.
  eapply Mem.sup_include_trans. eauto. eapply external_call_support. eauto.
  apply set_builtin_res_sound; auto.
  eauto 10.
  apply sound_stack_exten with bc.
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. apply SINCR. apply Mem.sup_incr_in2. auto.
  rewrite C; auto with ordered_type. intro. rewrite H7 in H4.
  eapply freshness. eauto.
  intros. apply AA. apply SINCR. apply Mem.sup_incr_in2. auto.
* (* public builtin call *)
  exploit anonymize_stack; eauto.
  intros (bc1 & A & B & C & D & E & F & G).
  exploit external_call_match; eauto.
  intros. exploit list_forall2_in_left; eauto. intros (av & U & V). eapply D; eauto with va.
  intros (bc2 & J & K & L & M & N & O & P & Q).
  exploit (return_from_public_call bc bc2).
  eapply mmatch_below; eauto.
  rewrite K. apply B. auto. auto.
  intros. rewrite K; auto. rewrite C; auto.
  eauto. eauto.
  eapply external_call_support; eauto.
  eauto. eauto. eauto. eauto. eauto.
  intros (bc3 & U & V & W & X & Y & Z & AA).
  eapply sound_succ_state with (bc := bc3); eauto. simpl; auto.
  eapply Mem.sup_include_trans. eauto. eapply external_call_support. eauto.
  apply set_builtin_res_sound; auto. eauto 10.
  apply sound_stack_exten with bc.
  apply sound_stack_inv with m. auto.
  intros. apply Q. red. apply SINCR. apply Mem.sup_incr_in2. auto.
  rewrite C; auto with ordered_type. intro. rewrite H5 in H2.
  eapply freshness; eauto.
  intros. apply AA. apply SINCR. apply Mem.sup_incr_in2. auto.
  }
  unfold transfer_builtin in TR.
  destruct ef; auto.
+ (* builtin function *)
  destruct (lookup_builtin_function name sg) as [bf|] eqn:LK; auto.
  destruct (eval_static_builtin_function ae am rm bf args) as [av|] eqn:ES; auto.
  simpl in H1. red in H1. rewrite LK in H1. inv H1.
  eapply sound_succ_state; eauto. simpl; auto.
  apply set_builtin_res_sound; auto.
  eapply eval_static_builtin_function_sound with (rm := rm); eauto.
  eapply romatch_symtbl_prog; eauto.
+ (* volatile load *)
  inv H0; auto. inv H3; auto. inv H1.
  eapply romatch_symtbl_prog in GEVALID as RO'; eauto. fold rm in RO'.
  exploit abuiltin_arg_sound; eauto. intros VM1.
  eapply sound_succ_state; eauto. simpl; auto.
  apply set_builtin_res_sound; auto.
  inv H3.
  * (* true volatile access *)
    assert (V: vmatch bc v (Ifptr Glob)).
    { inv H4; simpl in *; constructor. econstructor. eapply GE; eauto. }
    destruct (va_strict tt). apply vmatch_lub_r. apply vnormalize_sound. auto.
    apply vnormalize_sound. eapply vmatch_ge; eauto. constructor. constructor.
  * (* normal memory access *)
    exploit loadv_sound; eauto; simpl; eauto. intros V.
    destruct (va_strict tt).
    apply vmatch_lub_l. auto.
    eapply vnormalize_cast; eauto. eapply vmatch_top; eauto.
+ (* volatile store *)
  inv H0; auto. inv H3; auto. inv H4; auto. inv H1.
  eapply romatch_symtbl_prog in GEVALID as RO'; eauto. fold rm in RO'.
  exploit abuiltin_arg_sound. eauto. eauto. eauto. eauto. eauto. eexact H0. intros VM1.
  exploit abuiltin_arg_sound. eauto. eauto. eauto. eauto. eauto. eexact H2. intros VM2.
  inv H9.
  * (* true volatile access *)
    eapply sound_succ_state; eauto. simpl; auto.
    apply set_builtin_res_sound; auto. constructor.
    apply mmatch_lub_l; auto.
  * (* normal memory access *)
    eapply sound_succ_state; eauto. simpl; auto.
    erewrite Mem.support_store. eauto. eauto.
    apply set_builtin_res_sound; auto. constructor.
    apply mmatch_lub_r. eapply storev_sound; eauto. auto.
    eauto using romatch_store.
    eapply sound_stack_storev; eauto. simpl; eauto.
+ (* memcpy *)
  inv H0; auto. inv H3; auto. inv H4; auto. inv H1.
  eapply romatch_symtbl_prog in GEVALID as RO'; eauto. fold rm in RO'.
  exploit abuiltin_arg_sound. eauto. eauto. eauto. eauto. eauto. eexact H0. intros VM1.
  exploit abuiltin_arg_sound. eauto. eauto. eauto. eauto. eauto. eexact H2. intros VM2.
  eapply sound_succ_state; eauto. simpl; auto.
  erewrite Mem.support_storebytes. eauto. eauto.
  apply set_builtin_res_sound; auto. constructor.
  eapply storebytes_sound; eauto.
  apply match_aptr_of_aval; auto.
  eapply Mem.loadbytes_length; eauto.
  intros. eapply loadbytes_sound; eauto. apply match_aptr_of_aval; auto.
  eauto using romatch_storebytes.
  eapply sound_stack_storebytes; eauto.
+ (* annot *)
  inv H1. eapply sound_succ_state; eauto. simpl; auto. apply set_builtin_res_sound; auto. constructor.
+ (* annot val *)
  inv H0; auto. inv H3; auto. inv H1.
  eapply sound_succ_state; eauto. simpl; auto.
  apply set_builtin_res_sound; auto. eapply abuiltin_arg_sound; eauto.
  eapply romatch_symtbl_prog; eauto.
+ (* debug *)
  inv H1. eapply sound_succ_state; eauto. simpl; auto. apply set_builtin_res_sound; auto. constructor.

- (* cond *)
  eapply sound_succ_state; eauto.
  simpl. destruct b; auto.
  unfold transfer; rewrite H; auto.

- (* jumptable *)
  eapply sound_succ_state; eauto.
  simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto.

- (* return *)
  exploit anonymize_stack; eauto. intros (bc' & A & B & C & D & E & F & G).
  apply sound_return_state with bc'; auto.
  erewrite Mem.support_free by eauto.
  apply sound_stack_new_bound with sps.
  apply sound_stack_exten with bc.
  eapply sound_stack_free; eauto.
  intros. apply C. intro. rewrite H2 in H1. eapply freshness. eauto.
  intro. intro. apply SINCR. apply Mem.sup_incr_in2. auto.
(*  eapply mmatch_below; eauto with va. *)
  destruct or; simpl. eapply D; eauto. constructor.
  eauto using romatch_free.
  eapply mmatch_free; eauto.

- (* internal function *)
  exploit allocate_stack; eauto.
  intros (bc' & A & B & C & D & E & F & G).
  exploit (analyze_entrypoint rm f args m' bc'); eauto.
  intros (ae & am & AN & EM & MM').
  econstructor; eauto.
  eapply Mem.alloc_result. eauto.
  rewrite Mem.support_alloc with m 0 (fn_stacksize f) m' stk.
  eapply Mem.sup_include_refl.
  eauto. auto.
  (* erewrite Mem.alloc_result by eauto. *)
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto.
  intros. eapply Mem.loadbytes_alloc_unchanged; eauto.
  (*intros. apply F. erewrite Mem.alloc_result by eauto. auto. *)

- (* external function *)
  exploit external_call_match; eauto with va.
  intros (bc' & A & B & C & D & E & F & G & K).
  econstructor; eauto.
  apply sound_stack_new_bound with (Mem.support m).
  apply sound_stack_exten with bc; auto.
  apply sound_stack_inv with m; auto.
  eapply external_call_support; eauto.

- (* return *)
  inv STK.
  + (* from public call *)
   exploit return_from_public_call; eauto.
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G).
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   intros. apply G. apply SINCR. apply Mem.sup_incr_in2. auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto.
  + (* from private call *)
   exploit return_from_private_call; eauto.
   intros; rewrite SAME; auto.
   intros (bc1 & A & B & C & D & E & F & G).
   destruct (analyze rm f)#pc as [ |ae' am'] eqn:EQ; simpl in AN; try contradiction. destruct AN as [A1 A2].
   eapply sound_regular_state with (bc := bc1); eauto.
   apply sound_stack_exten with bc'; auto.
   intros. apply G. apply SINCR. apply Mem.sup_incr_in2. auto.
   eapply ematch_ge; eauto. apply ematch_update. auto. auto.
Qed.

End SOUNDNESS.

(** ** Readonly preservation property *)

Record ro_world :=
  row {
      ro_symtbl : Genv.symtbl;
      ro_mem: mem;
    }.

Program Definition bc_of_symtbl (se: Genv.symtbl) :=
  {|
    bc_img b :=
      match Genv.invert_symbol se b with
        | Some id => BCglob id
        | None => BCinvalid
      end
  |}.
Next Obligation.
  destruct Genv.invert_symbol; discriminate.
Qed.
Next Obligation.
  destruct (Genv.invert_symbol se b1) eqn:Hb1; inv H.
  destruct (Genv.invert_symbol se b2) eqn:Hb2; inv H0.
  apply Genv.invert_find_symbol in Hb1.
  apply Genv.invert_find_symbol in Hb2.
  congruence.
Qed.

Lemma bc_of_symtbl_below se thr:
  Mem.sup_include (Genv.genv_sup se) thr ->
  bc_below (bc_of_symtbl se) thr.
Proof.
  intros Hthr b. cbn.
  destruct Genv.invert_symbol eqn:Hb; try congruence. intros _.
  eapply Mem.sup_include_trans; eauto.
  apply Genv.invert_find_symbol in Hb.
  eapply Genv.genv_symb_range; eauto.
Qed.

(** Simplifed version of sound_memory_ro, we need
    1) ro_mem m1 -> sound_memory_ro m1
    2) ro_mem m1 -> ro_acc m1 m2 -> ro_mem m2 *)
(*
Inductive match_init_data_block :list init_data -> mem -> block ->Prop :=
|init_data_block_intro: forall (il : list init_data) m b
   (NOWRIT: forall ofs, ~ Mem.perm m b ofs Max Writable),
  match_init_data_block il m b.
  (*
    1. pge Glob (ab_summary ab) : need requirement here?
    2. bmatch
       2.1 smatch (ab_summary ab)
           2.1.1 load -> vmatch v (Ifptr ab_summay ab)
           2.1.2 loadbytes 1 = Vptr b' ofs' -> pmatch b' ofs' (ab_summary ab)
       2.2 load -> vmatch (ofs---one-to-one)

   *)
Definition readonly_mem se m : Prop :=
  forall b id v,
    Genv.find_symbol se id = Some b ->
    Genv.find_info se b = Some (Gvar v) ->
    gvar_readonly v && negb (gvar_volatile v) && definitive_initializer (gvar_init v) = true ->
    match_init_data_block (gvar_init v) m b.
 *)

Definition sound_memory_ro ge m : Prop :=
  romatch (bc_of_symtbl ge) m (romem_for_symtbl ge)
  /\ Mem.sup_include (Genv.genv_sup ge) (Mem.support m).


Inductive ro_acc : mem -> mem -> Prop :=
| ro_acc_intro m1 m2:
  Mem.ro_unchanged m1 m2 ->
  Mem.sup_include (Mem.support m1) (Mem.support m2) ->
  injp_max_perm_decrease m1 m2 ->
  ro_acc m1 m2.
                  
Lemma ro_acc_refl : forall m, ro_acc m m.
Proof.
  intros. constructor; eauto.
  red. eauto.
Qed.

Lemma ro_acc_trans : forall m1 m2 m3, ro_acc m1 m2 -> ro_acc m2 m3 -> ro_acc m1 m3.
Proof.
  intros. inv H. inv H0. constructor; eauto.
  - red. intros. red in H1. eapply H1; eauto.
    eapply H; eauto. apply H2; eauto.
    intros. intro. eapply H7; eauto.
Qed.

Lemma ro_acc_sound : forall se m1 m2,
    sound_memory_ro se m1 ->
    ro_acc m1 m2 ->
    sound_memory_ro se m2.
Proof.
  intros. inv H0. red. destruct H. red in H.
  red in H1. split; eauto. red. intros.
  exploit H; eauto. intros [A [B C]].
  assert (Mem.valid_block m1 b).
  { clear - H0 H4.
    unfold bc_of_symtbl in H4. cbn in H4.
    destruct Genv.invert_symbol eqn:Hi; inv H4.
    apply Genv.invert_find_symbol in Hi.
    apply Genv.genv_symb_range in Hi. apply H0; eauto.
  }
  split. auto. split.
  - eapply bmatch_ext; eauto.
  - intros. intro. eapply C; eauto.
Qed.

Lemma ro_acc_store : forall m m' chunk b ofs v,
    Mem.store chunk m b ofs v = Some m' ->
    ro_acc m m'.
Proof.
  intros. constructor.
  - eapply Mem.ro_unchanged_store; eauto.
  - erewrite <- Mem.support_store; eauto.
  - red. eauto using Mem.perm_store_2.
Qed.

Lemma ro_acc_alloc : forall m m' lo hi b,
    Mem.alloc m lo hi = (m',b) ->
    ro_acc m m'.
Proof.
  intros. constructor.
  - red. intros.
    erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
  - exploit Mem.alloc_unchanged_on; eauto.
    instantiate (1:= fun _ _ => True). intro.
    inv H0. eauto.
  - red. intros. eapply Mem.perm_alloc_4; eauto.
    apply Mem.fresh_block_alloc in H. intro. congruence.
Qed.

Lemma ro_acc_free : forall m m' b lo hi,
    Mem.free m b lo hi = Some m' ->
    ro_acc m m'.
Proof.
  intros. constructor.
  - red. intros. eapply Mem.loadbytes_free_2; eauto.
  - erewrite <- Mem.support_free; eauto.
  - red. eauto using Mem.perm_free_3; eauto.
Qed.

Lemma ro_acc_external : forall m m' ef ge vargs t vres,
    external_call ef ge vargs m t vres m' ->  
    ro_acc m m'.
Proof.
  intros. constructor.
  - red. intros. eapply external_call_readonly; eauto.
  - eapply external_call_support; eauto.
  - red. intros. eapply external_call_max_perm; eauto.
Qed.

Inductive sound_query ge m: c_query -> Prop :=
  sound_query_intro vf sg vargs:
    sound_memory_ro ge m ->
    sound_query ge m (cq vf sg vargs m).

Inductive sound_reply m: c_reply -> Prop :=
  sound_reply_intro res tm:
    ro_acc m tm ->
    sound_reply m (cr res tm).

Definition ro : invariant li_c :=
  {|
    symtbl_inv '(row ge m) := eq ge;
    query_inv '(row ge m) := sound_query ge m;
    reply_inv '(row ge m) := sound_reply m;
  |}.

(* self-sim for RTL programs using ro *)
Section RO.
  Variable se: Genv.symtbl.
  Variable m0 : mem.

Inductive sound_state_ro : state -> Prop :=
  |sound_regular_state_ro : forall s f sp pc e m,
      sound_memory_ro se m ->
      ro_acc m0 m ->
      sound_state_ro (State s f sp pc e m)
  |sound_call_state_ro: forall s fd args m,
      sound_memory_ro se m ->
      ro_acc m0 m ->
      sound_state_ro (Callstate s fd args m)
  |sound_return_state_ro : forall s v m,
      sound_memory_ro se m ->
      ro_acc m0 m ->
      sound_state_ro (Returnstate s v m).

End RO.

Definition ro_inv '(row se0 m0) := sound_state_ro se0 m0.

Lemma RTL_ro_preserves prog:
  preserves (semantics prog) ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros. inv H0; inv H.
    + constructor; eauto.
    + constructor; eauto.
    + constructor; eauto.
    + unfold Mem.storev in H3.
      destruct a; try congruence.
      exploit ro_acc_store; eauto. intro H.
      constructor; eauto.
      eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + constructor; eauto.
    + exploit ro_acc_free; eauto. intro H.
      constructor; eauto. eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + exploit ro_acc_external; eauto. intro H.
      constructor; eauto.
      eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + constructor; eauto.
    + constructor; eauto.
    + exploit ro_acc_free; eauto. intro H.
      constructor; eauto. eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + exploit ro_acc_alloc; eauto. intro H.
      constructor; eauto. eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + exploit ro_acc_external; eauto. intro H.
      constructor; eauto. eapply ro_acc_sound; eauto.
      eapply ro_acc_trans; eauto.
    + constructor; eauto.
  - intros. inv H0. inv H. constructor; eauto.
    constructor; eauto. red. eauto.
  - intros. inv H0. inv H. simpl.
    exists (row se1 m). split; eauto.
    constructor; eauto. constructor; eauto.
    intros r s' Hr AFTER. inv Hr. inv AFTER.
    constructor.
    eapply ro_acc_sound; eauto.
    eapply ro_acc_trans; eauto.
  - intros. inv H0. inv H. constructor; eauto.
Qed.

(** ** Block classification for an injection *)

Program Definition bc_of_inj (f: meminj) (se: Genv.symtbl) :=
  {|
    bc_img b :=
      if f b then
        match Genv.invert_symbol se b with
        | Some id => BCglob id
        | None => BCother
        end
      else
        BCinvalid
  |}.
Next Obligation.
  destruct (f b1); try discriminate.
  destruct Genv.invert_symbol; discriminate.
Qed.
Next Obligation.
  destruct (f b1); try discriminate.
  destruct (f b2); try discriminate.
  destruct (Genv.invert_symbol se b1) eqn:Hb1; inv H.
  destruct (Genv.invert_symbol se b2) eqn:Hb2; inv H0.
  apply Genv.invert_find_symbol in Hb1.
  apply Genv.invert_find_symbol in Hb2.
  congruence.
Qed.

Lemma bc_of_symtbl_inj f se1 se2:
  Genv.match_stbls f se1 se2 ->
  bc_incr (bc_of_symtbl se1) (bc_of_inj f se1).
Proof.
  intros Hse b Hb. cbn in *.
  destruct Genv.invert_symbol eqn:H; try congruence.
  apply Genv.invert_find_symbol in H.
  edestruct @Genv.find_symbol_match as (tb & Htb & _); eauto.
  rewrite Htb. auto.
Qed.

Lemma bc_of_symtbl_inj_glob f se b id:
  bc_of_inj f se b = BCglob id ->
  bc_of_symtbl se b = BCglob id.
Proof.
  unfold bc_of_inj, bc_of_symtbl; cbn.
  destruct f; try discriminate.
  destruct Genv.invert_symbol; congruence.
Qed.

Lemma bc_of_inj_genv_match f se1 se2:
  Genv.match_stbls f se1 se2 ->
  genv_match (bc_of_inj f se1) se1.
Proof.
  intros Hse. split.
  - intros id b1. split.
    + intros Hb1.
      edestruct @Genv.find_symbol_match as (b2 & Hb12 & Hb2); eauto.
      apply Genv.find_invert_symbol in Hb1. cbn.
      rewrite Hb12, Hb1. auto.
    + cbn.
      destruct (f b1) eqn:Hb; try discriminate.
      destruct Genv.invert_symbol eqn:Hid; try discriminate.
      intro. apply Genv.invert_find_symbol. congruence.
  - intros b1 Hb1. cbn.
    eapply Genv.mge_dom in Hb1 as [b2 Hb]; eauto. rewrite Hb.
    destruct Genv.invert_symbol; split; discriminate.
Qed.

Lemma bc_of_inj_pmatch f se1 b1 ofs1 v2:
  Val.inject f (Vptr b1 ofs1) v2 ->
  pmatch (bc_of_inj f se1) b1 ofs1 Ptop.
Proof.
  inversion 1; subst.
  constructor. cbn.
  rewrite H2.
  destruct Genv.invert_symbol; discriminate.
Qed.

Lemma bc_of_inj_vmatch f se1 v1 v2:
  Val.inject f v1 v2 ->
  vmatch (bc_of_inj f se1) v1 Vtop.
Proof.
  destruct v1; constructor.
  eapply bc_of_inj_pmatch; eauto.
Qed.

Lemma bc_of_inj_args_vmatch f se1 vargs1 vargs2:
  Val.inject_list f vargs1 vargs2 ->
  forall v, In v vargs1 -> vmatch (bc_of_inj f se1) v Vtop.
Proof.
  induction 1 as [ | v1 v2 vargs1 vargs2 Hv IH]; cbn.
  - contradiction.
  - intros v1' [Hv1' | Hv1']; auto. subst v1'.
    eapply bc_of_inj_vmatch; eauto.
Qed.

Lemma bc_of_inj_smatch f se1 m1 m2 b1 b2 delta:
  Mem.inject f m1 m2 ->
  f b1 = Some (b2, delta) ->
  smatch (bc_of_inj f se1) m1 b1 Ptop.
Proof.
  intros Hm Hb.
  split.
  + intros chunk ofs v1 Hv1.
    edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto.
    eapply bc_of_inj_vmatch; eauto.
  + intros ofs1 b1' ofs1' q i H.
    edestruct Mem.loadbytes_inject as (bytes2 & Hbytes2 & Hv'); eauto.
    inv Hv'. inv H4. inv H2.
    eapply bc_of_inj_pmatch; eauto.
Qed.

Lemma bc_of_inj_mmatch f se1 m1 m2:
  Mem.inject f m1 m2 ->
  mmatch (bc_of_inj f se1) m1 mtop.
Proof.
  intros Hm. split.
  - intros b1 Hb1. cbn in *.
    destruct (f b1) as [[b2 delta] | ]; try discriminate.
    destruct Genv.invert_symbol; discriminate.
  - intros id ab b1 Hb1 H. cbn in *.
    rewrite Maps.PTree.gempty in H. discriminate.
  - intros b1 Hb1stk Hb1inv. cbn in *.
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply bc_of_inj_smatch; eauto.
  - intros b1 Hb1. cbn in *.
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply bc_of_inj_smatch; eauto.
  - intros b1 Hb1. cbn in *.    
    destruct (f b1) as [[b2 delta] | ] eqn:Hb; try congruence.
    eapply Mem.valid_block_inject_1; eauto.
Qed.

Lemma bc_of_inj_nostack f se1:
  bc_nostack (bc_of_inj f se1).
Proof.
  intros b. cbn.
  destruct f; try congruence.
  destruct Genv.invert_symbol; congruence.
Qed.

(** * Lemmas for establish sound_state invariant using ro and injp in VA passes *)

(** ** 1st step: Initialize the sound_state at query *)
Lemma sound_memory_ro_sound_state:
  forall j m m' se tse vargs vf vf' vargs' prog,
    Mem.inject j m m' ->
    Val.inject j vf vf' ->
    Val.inject_list j vargs vargs' ->
    Genv.match_stbls j se tse ->
    sound_memory_ro se m ->
    sound_state prog se (Callstate nil vf vargs m).
Proof.
  intros.
  set (bc := bc_of_inj j se).
  econstructor. instantiate (1:= bc).
  constructor; eauto.
  + eapply bc_of_inj_vmatch; eauto.
  + eapply bc_of_inj_args_vmatch; eauto.
  + red in H3. destruct H3 as [H3 H3'].
      eapply romatch_exten; eauto.
      intros. unfold bc, bc_of_inj, bc_of_symtbl.
      simpl. split; intro.
      *
      destruct (j b) as [[b' d']|] eqn:Hf0; try congruence.
      destruct (Genv.invert_symbol se b); try congruence.
      *
      destruct (Genv.invert_symbol se b) eqn:Hinv; try congruence.
      inversion H4. subst id. inversion H2.
      apply Genv.invert_find_symbol in Hinv. exploit mge_dom; eauto.
      eapply Genv.genv_symb_range; eauto.
      intros [b2 Hf0]. rewrite Hf0. reflexivity.
    + eapply bc_of_inj_mmatch; eauto.
    + eapply bc_of_inj_genv_match; eauto.
    + eapply bc_of_inj_nostack; eauto.
Qed.

(** ** 2nd step *)






(** ** Soundness of the initial memory abstraction *)

Require Import Axioms.

Section INITIAL.

Variable prog: program.

Let ge := Genv.globalenv (Genv.symboltbl (erase_program prog)) prog.

Lemma initial_block_classification:
  forall m,
  Genv.init_mem (erase_program prog) = Some m ->
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.support m)
  /\ bc_nostack bc
  /\ (forall b id, bc b = BCglob id -> Genv.find_symbol ge id = Some b)
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid).
Proof.
  intros.
  set (f := fun b =>
              if Mem.sup_dec b (Genv.genv_sup ge) then
                match Genv.invert_symbol ge b with None => BCother | Some id => BCglob id end
              else
                BCinvalid).
  assert (F_glob: forall b1 b2 id, f b1 = BCglob id -> f b2 = BCglob id -> b1 = b2).
  {
    unfold f; intros.
    destruct (Mem.sup_dec b1 (Genv.genv_sup ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1) as [id1|] eqn:I1; inv H0.
    destruct (Mem.sup_dec b2 (Genv.genv_sup ge)); try discriminate.
    destruct (Genv.invert_symbol ge b2) as [id2|] eqn:I2; inv H1.
    exploit Genv.invert_find_symbol. eexact I1.
    exploit Genv.invert_find_symbol. eexact I2.
    congruence.
  }
  assert (F_stack: forall b1 b2, f b1 = BCstack -> f b2 = BCstack -> b1 = b2).
  {
    unfold f; intros.
    destruct (Mem.sup_dec b1 (Genv.genv_sup ge)); try discriminate.
    destruct (Genv.invert_symbol ge b1); discriminate.
  }
  set (bc := BC f F_stack F_glob). unfold f in bc.
  exists bc; splitall.
- split; simpl; intros.
  + split; intros.
    * rewrite pred_dec_true by (eapply Genv.genv_symb_range; eauto).
      erewrite Genv.find_invert_symbol; eauto.
    * apply Genv.invert_find_symbol.
      destruct (Mem.sup_dec b (Genv.genv_sup _)); try discriminate.
      destruct (Genv.invert_symbol _ b); congruence.
  + rewrite ! pred_dec_true by assumption.
    destruct (Genv.invert_symbol); split; congruence.
- red; simpl; intros. destruct (Mem.sup_dec b (Genv.genv_sup _)); try congruence.
  erewrite <- Genv.init_mem_genv_sup by eauto. auto.
- red; simpl; intros.
  destruct (Mem.sup_dec b (Genv.genv_sup _)).
  destruct (Genv.invert_symbol _ b); congruence.
  congruence.
- simpl; intros. destruct (Mem.sup_dec b (Genv.genv_sup _)); try discriminate.
  destruct (Genv.invert_symbol _ b) as [id' | ] eqn:IS; inv H0.
  apply Genv.invert_find_symbol; auto.
- intros; simpl. unfold ge; erewrite Genv.init_mem_genv_sup by eauto.
  rewrite pred_dec_true by assumption.
  destruct (Genv.invert_symbol _ b); congruence.
Qed.

Section INIT.

Variable bc: block_classification.
Hypothesis GMATCH: genv_match bc ge.

Lemma store_init_data_summary:
  forall ab p id,
  pge Glob (ab_summary ab) ->
  pge Glob (ab_summary (store_init_data ab p id)).
Proof.
  intros.
  assert (DFL: forall chunk av,
               vge (Ifptr Glob) av ->
               pge Glob (ab_summary (ablock_store chunk ab p av))).
  {
    intros. simpl. unfold vplub; destruct av; auto.
    inv H0. apply plub_least; auto.
    inv H0. apply plub_least; auto.
  }
  destruct id; auto.
  simpl. destruct (propagate_float_constants tt); auto.
  simpl. destruct (propagate_float_constants tt); auto.
  apply DFL. constructor. constructor.
Qed.

Lemma store_init_data_list_summary:
  forall idl ab p,
  pge Glob (ab_summary ab) ->
  pge Glob (ab_summary (store_init_data_list ab p idl)).
Proof.
  induction idl; simpl; intros. auto. apply IHidl. apply store_init_data_summary; auto.
Qed.

Lemma store_init_data_sound:
  forall m b p id m' ab,
  Genv.store_init_data ge m b p id = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data ab p id).
Proof.
  intros. destruct id; try (eapply ablock_store_sound; eauto; constructor).
- (* float32 *)
  simpl. destruct (propagate_float_constants tt); eapply ablock_store_sound; eauto; constructor.
- (* float64 *)
  simpl. destruct (propagate_float_constants tt); eapply ablock_store_sound; eauto; constructor.
- (* space *)
  simpl in H. inv H. auto.
- (* addrof *)
  simpl in H. destruct (Genv.find_symbol _ i) as [b'|] eqn:FS; try discriminate.
  eapply ablock_store_sound; eauto. constructor. constructor. apply GMATCH; auto.
Qed.

Lemma store_init_data_list_sound:
  forall idl m b p m' ab,
  Genv.store_init_data_list ge m b p idl = Some m' ->
  bmatch bc m b ab ->
  bmatch bc m' b (store_init_data_list ab p idl).
Proof.
  induction idl; simpl; intros.
- inv H; auto.
- destruct (Genv.store_init_data _ m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_sound; eauto.
Qed.

Lemma store_init_data_other:
  forall m b p id m' ab b',
  Genv.store_init_data ge m b p id = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros. eapply bmatch_inv; eauto.
  intros. destruct id; try (eapply Mem.loadbytes_store_other; eauto; fail); simpl in H.
  inv H; auto.
  destruct (Genv.find_symbol _ i); try discriminate.
  eapply Mem.loadbytes_store_other; eauto.
Qed.

Lemma store_init_data_list_other:
  forall b b' ab idl m p m',
  Genv.store_init_data_list ge m b p idl = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  induction idl; simpl; intros.
  inv H; auto.
  destruct (Genv.store_init_data _ m b p a) as [m1|] eqn:SI; try discriminate.
  eapply IHidl; eauto. eapply store_init_data_other; eauto.
Qed.

Lemma store_zeros_same:
  forall p m b pos n m',
  store_zeros m b pos n = Some m' ->
  smatch bc m b p ->
  smatch bc m' b p.
Proof.
  intros until n. functional induction (store_zeros m b pos n); intros.
- inv H. auto.
- eapply IHo; eauto. change p with (vplub (I Int.zero) p).
  eapply smatch_store; eauto. constructor.
- discriminate.
Qed.


Lemma store_zeros_other:
  forall b' ab m b p n m',
  store_zeros m b p n = Some m' ->
  b' <> b ->
  bmatch bc m b' ab ->
  bmatch bc m' b' ab.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
- inv H. auto.
- eapply IHo; eauto. eapply bmatch_inv; eauto.
  intros. eapply Mem.loadbytes_store_other; eauto.
- discriminate.
Qed.

Definition initial_mem_match (bc: block_classification) (m: mem) (g: Genv.symtbl) :=
  forall id b v,
  Genv.find_symbol g id = Some b -> Genv.find_var_info g b = Some v ->
  v.(gvar_volatile) = false -> v.(gvar_readonly) = true ->
  bmatch bc m b (store_init_data_list (ablock_init Pbot) 0 v.(gvar_init)).

Lemma alloc_global_match:
  forall m g idg m',
  Genv.genv_sup g = Mem.support m ->
  initial_mem_match bc m g ->
  Genv.alloc_global ge m idg = Some m' ->
  initial_mem_match bc m' (Genv.add_global g idg).
Proof.
  intros; red; intros. destruct idg as [id1 [fd | gv]]; simpl in *.
- destruct (Mem.alloc m 0 1) as [m1 b1] eqn:ALLOC.
  unfold Genv.find_symbol in H2; simpl in H2.
  unfold Genv.find_var_info, Genv.find_info in H3; simpl in H3.
  rewrite PTree.gsspec in H2. destruct (peq id id1).
  inv H2. setoid_rewrite NMap.gss in H3. discriminate.
  assert (sup_In b (Genv.genv_sup g)) by (eapply Genv.genv_symb_range; eauto).
  setoid_rewrite NMap.gso in H3.
  assert (Mem.valid_block m b) by (red; rewrite <- H; auto).
  assert (b <> b1) by (apply Mem.valid_not_valid_diff with m; eauto with mem).
  apply bmatch_inv with m.
  eapply H0; eauto.
  intros. transitivity (Mem.loadbytes m1 b ofs n0).
  eapply Mem.loadbytes_drop; eauto.
  eapply Mem.loadbytes_alloc_unchanged; eauto.
  intro. rewrite H7 in H6. eapply freshness; eauto.
- set (sz := init_data_list_size (gvar_init gv)) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b1] eqn:ALLOC.
  destruct (store_zeros m1 b1 0 sz) as [m2 | ] eqn:STZ; try discriminate.
  destruct (Genv.store_init_data_list _ m2 b1 0 (gvar_init gv)) as [m3 | ] eqn:SIDL; try discriminate.
  unfold Genv.find_symbol in H2; simpl in H2.
  unfold Genv.find_var_info, Genv.find_info in H3; simpl in H3.
  rewrite PTree.gsspec in H2. destruct (peq id id1).
+ injection H2; clear H2; intro EQ.
  rewrite EQ in H3. setoid_rewrite NMap.gss in H3. injection H3; clear H3; intros EQ'; subst v.
  assert (b = b1).
  { erewrite Mem.alloc_result by eauto.
    rewrite H in EQ. auto. }
  clear EQ. subst b.
  apply bmatch_inv with m3.
  eapply store_init_data_list_sound; eauto.
  apply ablock_init_sound.
  eapply store_zeros_same; eauto.
  split; intros.
  exploit Mem.load_alloc_same; eauto. intros EQ; subst v; constructor.
  exploit Mem.loadbytes_alloc_same; eauto with coqlib. congruence.
  intros. eapply Mem.loadbytes_drop; eauto.
  right; right; right. unfold Genv.perm_globvar. rewrite H4, H5. constructor.
+ assert (sup_In b (Genv.genv_sup g)) by (eapply Genv.genv_symb_range; eauto).
  setoid_rewrite NMap.gso in H3.
  assert (Mem.valid_block m b) by (red; rewrite <- H; auto).
  assert (b <> b1) by (apply Mem.valid_not_valid_diff with m; eauto with mem).
  apply bmatch_inv with m3.
  eapply store_init_data_list_other; eauto.
  eapply store_zeros_other; eauto.
  apply bmatch_inv with m.
  eapply H0; eauto.
  intros. eapply Mem.loadbytes_alloc_unchanged; eauto.
  intros. eapply Mem.loadbytes_drop; eauto.
  intro. rewrite H7 in H6. eapply freshness; eauto.
Qed.

Lemma alloc_globals_match:
  forall gl m g m',
  Genv.genv_sup g = Mem.support m ->
  initial_mem_match bc m g ->
  Genv.alloc_globals ge m gl = Some m' ->
  initial_mem_match bc m' (Genv.add_globals g gl).
Proof.
  induction gl; simpl; intros.
- inv H1; auto.
- destruct (Genv.alloc_global _ m a) as [m1|] eqn:AG; try discriminate.
  eapply IHgl; eauto.
  erewrite Genv.alloc_global_support; eauto. simpl. unfold Mem.nextblock. congruence.
  eapply alloc_global_match; eauto.
Qed.



Lemma romem_for_consistent_2:
  forall cunit, linkorder cunit prog -> romem_consistent (prog_defmap prog) (romem_for cunit).
Proof.
  intros; red; intros.
  exploit (romem_for_consistent cunit); eauto. intros (v & DM & RO & VO & DEFN & AB).
  destruct (prog_defmap_linkorder _ _ _ _ H DM) as (gd & P & Q).
  assert (gd = Gvar v).
  { inv Q. inv H2. simpl in *. f_equal. f_equal.
    destruct info1, info2; auto.
    inv H3; auto; discriminate. }
  subst gd. exists v; auto.
Qed.

End INIT.

Theorem initial_mem_matches:
  forall m,
  Genv.init_mem (erase_program prog) = Some m ->
  exists bc,
     genv_match bc ge
  /\ bc_below bc (Mem.support m)
  /\ bc_nostack bc
  /\ (forall cunit, linkorder cunit prog -> romatch bc m (romem_for cunit))
  /\ (forall b, Mem.valid_block m b -> bc b <> BCinvalid)
  /\ mmatch bc m mtop.
Proof.
  intros.
  exploit initial_block_classification; eauto. intros (bc & GE & BELOW & NOSTACK & INV & VALID).
  exists bc; splitall; auto.
  intros.
  assert (A: initial_mem_match bc m ge).
  {
    apply alloc_globals_match with (m := Mem.empty); auto.
    red. unfold Genv.find_symbol; simpl; intros. rewrite PTree.gempty in H1; discriminate.
  }
  assert (B: romem_consistent (prog_defmap prog) (romem_for cunit)) by (apply romem_for_consistent_2; auto).
  red; intros.
  exploit B; eauto. intros (v & DM & RO & NVOL & DEFN & EQ).
  assert (DM': (prog_defmap (erase_program prog)) ! id = Some (Gvar v)).
  { rewrite erase_program_defmap, DM. cbn. destruct v as [[] ]; auto. }
  rewrite Genv.find_info_symbol in DM'. destruct DM' as (b1 & FS & FD).
  rewrite <- Genv.find_var_info_iff in FD.
  assert (b1 = b). { apply INV in H1. cbn in *; congruence. }
  subst b1.
  split. subst ab. apply store_init_data_list_summary. constructor.
  split. subst ab. eapply A; eauto.
  exploit Genv.init_mem_characterization; eauto.
  intros (P & Q & R).
  intros; red; intros. exploit Q; eauto. intros [U V].
  unfold Genv.perm_globvar in V; rewrite RO, NVOL in V. inv V.
  apply mmatch_inj_top with m.
  replace (inj_of_bc bc) with (Mem.flat_inj (Mem.support m)).
  eapply Genv.initmem_inject; eauto.
  symmetry; apply extensionality; unfold Mem.flat_inj; intros x.
  destruct (Mem.sup_dec x (Mem.support m)).
  apply inj_of_bc_valid; auto.
  unfold inj_of_bc. erewrite bc_below_invalid; eauto.
Qed.

End INITIAL.

Global Hint Resolve areg_sound aregs_sound: va.

(** * Interface with other optimizations *)

Ltac InvSoundState :=
  match goal with
  | H: sound_state ?prog ?ge ?st |- _ => inv H
  end.

Definition avalue (a: VA.t) (r: reg) : aval :=
  match a with
  | VA.Bot => Vbot
  | VA.State ae am => AE.get r ae
  end.

Lemma avalue_sound:
  forall prog ge s f sp pc e m r,
  sound_state prog ge (State s f (Vptr sp Ptrofs.zero) pc e m) ->
  exists bc,
     vmatch bc e#r (avalue (analyze (romem_for prog) f)!!pc r)
  /\ genv_match bc ge
  /\ bc sp = BCstack.
Proof.
  intros. InvSoundState. exists bc; split; auto. rewrite AN. apply EM.
Qed.

Definition aaddr (a: VA.t) (r: reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (AE.get r ae)
  end.

Lemma aaddr_sound:
  forall prog ge s f sp pc e m r b ofs,
  sound_state prog ge (State s f (Vptr sp Ptrofs.zero) pc e m) ->
  e#r = Vptr b ofs ->
  exists bc,
     pmatch bc b ofs (aaddr (analyze (romem_for prog) f)!!pc r)
  /\ genv_match bc ge
  /\ bc sp = BCstack.
Proof.
  intros. InvSoundState. exists bc; split; auto.
  unfold aaddr; rewrite AN. apply match_aptr_of_aval. rewrite <- H0. apply EM.
Qed.

Definition aaddressing (a: VA.t) (addr: addressing) (args: list reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am => aptr_of_aval (eval_static_addressing addr (aregs ae args))
  end.

Lemma aaddressing_sound:
  forall prog ge s f sp pc e m addr args b ofs,
  sound_state prog ge (State s f (Vptr sp Ptrofs.zero) pc e m) ->
  eval_addressing ge (Vptr sp Ptrofs.zero) addr e##args = Some (Vptr b ofs) ->
  exists bc,
     pmatch bc b ofs (aaddressing (analyze (romem_for prog) f)!!pc addr args)
  /\ genv_match bc ge
  /\ bc sp = BCstack.
Proof.
  intros. InvSoundState. exists bc; split; auto.
  unfold aaddressing. rewrite AN. apply match_aptr_of_aval.
  eapply eval_static_addressing_sound; eauto with va.
Qed.

(** This is a less precise version of [abuiltin_arg], where memory
    contents are not taken into account. *)

Definition aaddr_arg (a: VA.t) (ba: builtin_arg reg) : aptr :=
  match a with
  | VA.Bot => Pbot
  | VA.State ae am =>
      match ba with
      | BA r => aptr_of_aval (AE.get r ae)
      | BA_addrstack ofs => Stk ofs
      | BA_addrglobal id ofs => Gl id ofs
      | _ => Ptop
      end
  end.

Lemma aaddr_arg_sound_1:
  forall bc rs ae m rm am ge sp a b ofs,
  ematch bc rs ae ->
  romatch bc m rm ->
  mmatch bc m am ->
  genv_match bc ge ->
  bc sp = BCstack ->
  eval_builtin_arg ge (fun r : positive => rs # r) (Vptr sp Ptrofs.zero) m a (Vptr b ofs) ->
  pmatch bc b ofs (aaddr_arg (VA.State ae am) a).
Proof.
  intros.
  apply pmatch_ge with (aptr_of_aval (abuiltin_arg ae am rm a)).
  simpl. destruct a; try (apply pge_top); simpl; apply pge_refl.
  apply match_aptr_of_aval. eapply abuiltin_arg_sound; eauto.
Qed.

Lemma aaddr_arg_sound:
  forall prog ge s f sp pc e m a b ofs,
  sound_state prog ge (State s f (Vptr sp Ptrofs.zero) pc e m) ->
  eval_builtin_arg ge (fun r => e#r) (Vptr sp Ptrofs.zero) m a (Vptr b ofs) ->
  Genv.valid_for (erase_program prog) ge ->
  exists bc,
     pmatch bc b ofs (aaddr_arg (analyze (romem_for prog) f)!!pc a)
  /\ genv_match bc ge
  /\ bc sp = BCstack.
Proof.
  intros. InvSoundState. rewrite AN. exists bc; split; auto.
  eapply aaddr_arg_sound_1; eauto.
Qed.
