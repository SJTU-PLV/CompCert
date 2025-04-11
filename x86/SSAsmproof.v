Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Asm AsmFacts AsmRegs Asmgen Asmgenproof0.
Require Import LanguageInterface CKLR Extends Inject.
Require Import SSAsm.

Definition program := Asm.program.

Definition transf_program (p: Asm.program) : Asm.program := p.

Definition match_prog (p tp : program) := p = tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. reflexivity.
Qed.

Section PRESERVATION.

Variable prog tprog: Asm.program.
Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Variable w: CKLR.world inj.
Variable se tse: Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse prog.

Hypothesis GE: CKLR.match_stbls inj w se tse.
Hypothesis VALID: Genv.valid_for (erase_program prog) se.

(** this hypothesis can be promised by asmgen *)

Hypothesis prog_unchange_rsp_l: asm_prog_unchange_rsp instr_size (injw_sup_l w) ge.
Hypothesis prog_unchange_rsp_r: asm_prog_unchange_rsp instr_size (injw_sup_r w) tge.

(** Memory Injection Lemmas *)
Record meminj_preserves_globals (j: meminj) : Prop := {
  match_stbls :> Genv.match_stbls j se tse;
  global_inject :> meminj_global j;
}.

Remark defs_inject:
  forall j b b' delta gd,
    meminj_global j ->
    j b = Some (b', delta) ->
    Genv.find_def ge b = Some gd ->
    b = b' /\ delta = 0.
Proof.
  intros. apply Genv.genv_defs_range, Genv.genv_sup_glob in H1 as [id ?]. subst.
  exploit H. eauto. intros [ ]. auto.
Qed.

Remark defs_rev_inject:
  forall j b b' delta gd,
    meminj_preserves_globals j ->
    j b = Some (b', delta) ->
    Genv.find_def tge b' = Some gd ->
    b = b' /\ delta = 0.
Proof.
  intros.
  apply Genv.genv_defs_range in H1. erewrite <- Genv.mge_separated in H1; eauto. 2:apply H.
  apply Genv.genv_sup_glob in H1 as [id ?]. subst.
  exploit global_inject; eauto. intros [ ]. auto.
Qed.

Remark info_inject:
  forall j b b' delta gd,
    meminj_global j ->
    j b = Some (b', delta) ->
    Genv.find_var_info se b = Some gd ->
    b = b' /\ delta = 0.
Proof.
  intros. apply Genv.find_var_info_iff, Genv.genv_info_range, Genv.genv_sup_glob in H1 as [id ?]. subst.
  exploit H. eauto. intros [ ]. auto.
Qed.

Remark info_rev_inject:
  forall j b b' delta gd,
    meminj_preserves_globals j ->
    j b = Some (b', delta) ->
    Genv.find_var_info tse b' = Some gd ->
    b = b' /\ delta = 0.
Proof.
  intros. erewrite Genv.find_var_info_iff in H1.
  unfold Genv.find_info in H1. erewrite <- Genv.mge_info in H1; eauto. 2:apply H.
  apply Genv.genv_info_range, Genv.genv_sup_glob in H1 as [id ?]. subst.
  exploit global_inject; eauto. intros [ ]. auto.
Qed.

Lemma functions_translated (j: meminj):
  meminj_preserves_globals j ->
  forall v tv f,
  Val.inject j v tv -> Genv.find_funct ge v = Some f ->
  Genv.find_funct tge tv = Some f.
Proof.
  intros.
  unfold Genv.find_funct in *. do 2 destr_in H1. subst. inv H0.
  apply Genv.find_funct_ptr_iff in H1.
  eapply defs_inject in H1 as ?; eauto. 2:apply H. destruct H0 as [ ]. subst.
  rewrite Ptrofs.add_zero. destr. rewrite Genv.find_funct_ptr_iff.
  exploit @Genv.globalenvs_match. red. intuition idtac.
    instantiate (1 := prog). instantiate (2 := fun x y => x = y). instantiate (2 := fun x y z => y = z).
    generalize (prog_defs prog). induction l; constructor; auto.
    red. split. auto. destruct (snd a); econstructor; auto. reflexivity.
    destruct v. constructor. auto. apply H. instantiate (1 := tt).
  intros MGE. pose proof Genv.mge_defs MGE _ H4.
  unfold Genv.find_def, ge, tge in *. simpl in *. inv H0. congruence.
  inv H5; congruence.
Qed.

Lemma functions_only_translated (j: meminj):
  meminj_preserves_globals j ->
  forall v tv f (PTR: v <> Vundef),
  Val.inject j v tv -> Genv.find_funct tge tv = Some f ->
  Genv.find_funct ge v = Some f.
Proof.
  intros.
  unfold Genv.find_funct in *. do 2 destr_in H1. subst. inv H0. 2:congruence.
  apply Genv.find_funct_ptr_iff in H1.
  eapply defs_rev_inject in H1 as ?; eauto. destruct H0 as [ ]. subst.
  rewrite Ptrofs.add_zero in H6. subst. destr. rewrite Genv.find_funct_ptr_iff.
  exploit @Genv.globalenvs_match. red. intuition idtac.
    instantiate (1 := prog). instantiate (2 := fun x y => x = y). instantiate (2 := fun x y z => y = z).
    generalize (prog_defs prog). induction l; constructor; auto.
    red. split. auto. destruct (snd a); econstructor; auto. reflexivity.
    destruct v. constructor. auto. apply H. instantiate (1 := tt).
  intros MGE. pose proof Genv.mge_defs MGE _ H5.
  unfold Genv.find_def, ge, tge in *. simpl in *. inv H0. congruence.
  inv H4; congruence.
Qed.

Lemma functions_transl:
  forall j fb tfb f delta,
  meminj_preserves_globals j ->
  Genv.find_funct_ptr ge fb = Some f ->
  j fb = Some (tfb, delta) ->
  Genv.find_funct_ptr tge tfb = Some f.
Proof.
  intros. cut (delta = 0). intros. subst.
  exploit (functions_translated _ H (Vptr fb Ptrofs.zero)); eauto.
  rewrite Genv.find_funct_ptr_iff in H0. eapply defs_inject in H0 as [ ]; eauto. apply H.
Qed.

Lemma functions_only_transl:
  forall j fb tfb f delta,
  meminj_preserves_globals j ->
  Genv.find_funct_ptr tge tfb = Some f ->
  j fb = Some (tfb, delta) ->
  Genv.find_funct_ptr ge fb = Some f.
Proof.
  intros. cut (delta = 0). intros. subst.
  exploit (functions_only_translated _ H (Vptr fb Ptrofs.zero)); eauto. congruence.
  rewrite Genv.find_funct_ptr_iff in H0. eapply defs_rev_inject in H0 as [ ]; eauto.
Qed.

Remark symbol_inject:
  forall j id b,
    meminj_preserves_globals j ->
    Genv.find_symbol se id = Some b ->
    j b = Some (b, 0).
Proof.
  intros.
  apply Genv.genv_symb_range in H0. edestruct Genv.mge_dom as [b2 J]; eauto. apply H.
  apply Genv.genv_sup_glob in H0 as [id' ?]. subst.
  exploit global_inject; eauto. intros [ ]. subst. auto.
Qed.

Lemma globals_symbols_inject:
  forall j, meminj_preserves_globals j ->
  symbols_inject j se tse.
Proof.
  intros j GLOB_INJ.
  repeat split; intros.
  + apply GE.
  + simpl in H0. exploit symbol_inject; eauto. intro INJ. rewrite H in INJ. inv INJ. auto.
  + simpl in H0. exploit symbol_inject; eauto. intro INJ. rewrite H in INJ. inv INJ.
    unfold Genv.find_symbol. erewrite <- Genv.mge_symb; eauto. apply GLOB_INJ.
  + simpl in H0. exploit symbol_inject; eauto. intros. eexists. split. eauto.
    unfold Genv.find_symbol. erewrite <- Genv.mge_symb; eauto. apply GLOB_INJ.
  + simpl. unfold Genv.block_is_volatile.
    erewrite <- Genv.mge_info; eauto. apply GLOB_INJ.
Qed.

Lemma globinj_to_funinj:
  forall (j: meminj),
    meminj_global j ->
    forall b b' f ofs,
      Genv.find_funct_ptr ge b = Some f ->
      j b = Some (b', ofs) ->
      b' = b /\ ofs = 0.
Proof.
  intros j MINJ b b' f ofs FF JB.
  unfold Genv.find_funct_ptr in FF. do 2 destr_in FF. inv FF.
  apply Genv.genv_defs_range, Genv.genv_sup_glob in Heqo as (id & ?). subst b. auto.
Qed.

(** Regset Injection Lemmas *)
Lemma val_inject_set:
  forall j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    v v' (VINJ: Val.inject j v v') r1 r,
    Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
Proof.
  intros.
  destruct (PregEq.eq r1 r); subst; auto.
  rewrite ! Pregmap.gss; auto.
  rewrite ! Pregmap.gso by auto. auto.
Qed.

 Lemma val_inject_undef_regs:
  forall l j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    r,
    Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
Proof.
  induction l; simpl; intros; eauto.
  apply IHl.
  intros; apply val_inject_set; auto.
Qed.

Lemma val_inject_undef_caller_save_regs:
  forall j rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
    r,
    Val.inject j (undef_caller_save_regs rs1 r) (undef_caller_save_regs rs2 r).
Proof.
  intros; eauto.
  unfold undef_caller_save_regs.
  destruct (preg_eq r SP); destruct (in_dec preg_eq r (map preg_of (filter Conventions1.is_callee_save Machregs.all_mregs))); simpl; try (apply RINJ).
  eauto.
Qed.

Lemma val_inject_nextinstr:
  forall j sz rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
    Val.inject j (nextinstr sz rs1 r) (nextinstr sz rs2 r).
Proof.
  unfold nextinstr.
  intros.
  apply val_inject_set; auto.
  apply Val.offset_ptr_inject; auto.
Qed.

Lemma val_inject_nextinstr_nf:
  forall j sz rs1 rs2
    (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
    Val.inject j (nextinstr_nf sz rs1 r) (nextinstr_nf sz rs2 r).
Proof.
  unfold nextinstr_nf.
  intros.
  apply val_inject_nextinstr; auto.
  intros.
  apply val_inject_undef_regs; auto.
Qed.

Lemma val_inject_set_res:
  forall r rs1 rs2 v1 v2 j,
    Val.inject j v1 v2 ->
    (forall r0, Val.inject j (rs1 r0) (rs2 r0)) ->
    forall r0, Val.inject j (set_res r v1 rs1 r0) (set_res r v2 rs2 r0).
Proof.
  induction r; simpl; intros; auto.
  apply val_inject_set; auto.
  eapply IHr2; eauto.
  apply Val.loword_inject. auto.
  intros; eapply IHr1; eauto.
  apply Val.hiword_inject. auto.
Qed.

Lemma val_inject_set_pair:
  forall j p res1 res2 rs1 rs2,
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    Val.inject j res1 res2 ->
    forall r,
      Val.inject j (set_pair p res1 rs1 r) (set_pair p res2 rs2 r).
Proof.
  destruct p; simpl; intros; eauto.
  apply val_inject_set; auto.
  repeat (intros; apply val_inject_set; auto).
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed.

(** Stack Injection Lemmas *)
Record single_stack_perm_ofs (m: mem) : Prop :=
  {
  stack_perm_offset: forall (ofs: Z) (k: perm_kind) (p: permission),
      Mem.perm m stkblock ofs k p -> 0 <= ofs < Ptrofs.max_unsigned;
  stack_offset_perm: forall (ofs: Z) (k: perm_kind) (p: permission),
      0 <= ofs < max_stacksize' -> Mem.perm m stkblock ofs k p;
  }.

Lemma stack_size_aligned :
  forall stk,
    (8 | Memory.stack_size stk).
Proof.
  intros. induction stk.
  - simpl. apply Z.divide_0_r.
  - induction a; simpl.
    + auto.
    + simpl in IHa.
      generalize (Z.add_comm (Memory.size_of_all_frames a0) (Memory.stack_size stk)). intro. rewrite H in IHa.
      exploit Z.divide_add_cancel_r. apply IHstk. apply IHa. intro.
      assert (8 | align (Memory.frame_size a) 8). apply align_divides. lia.
      repeat apply Z.divide_add_r; auto.
Qed.

Definition perm_type :=
  block -> Z -> perm_kind -> permission -> Prop.

Definition current_in_stack' (b:block) (astk:stackadt) : Prop :=
  In b (sp_of_astack astk).

Definition current_in_stack (b:block) (m:mem) : Prop :=
  In b (sp_of_astack (Mem.astack (Mem.support m))).

Definition stack_inject_lowbound j m stklb:=
  forall b delta ofs k p,
    j b = Some (stkblock, delta) ->
    Mem.perm m b ofs k p ->
    stklb <= ofs + delta /\ (current_in_stack b m).

Definition stkcin m : Prop :=
  forall b,
    current_in_stack b m ->
    is_stack b /\ sup_In b (Mem.support m).
Definition stkcin' sup : Prop :=
  forall b,
    current_in_stack' b (Mem.astack sup) ->
    is_stack b /\ sup_In b sup.

Inductive inject_stack (j:meminj) (P:perm_type): stackadt -> stackadt -> Prop :=
  | inject_stack_nil : forall hd t tl hd' t' tl'
      (INIT_STKCIN_L: stkcin' (injw_sup_l w))
      (INIT_STKCIN_R: stkcin' (injw_sup_r w))
      (INIT_PARENT_L: Mem.astack (injw_sup_l w) = nil :: (hd :: t) :: tl)
      (INIT_PARENT_R: Mem.astack (injw_sup_r w) = nil :: (hd' :: t') :: tl')
      (INIT_SIZE: stack_size (Mem.astack (injw_sup_l w)) >= stack_size (Mem.astack (injw_sup_r w)))
      (INIT_INJECT: j (frame_block hd) = Some (stkblock, max_stacksize' - stack_size (Mem.astack (injw_sup_r w))))
      (INIT_INNER:
        forall b,
        current_in_stack' b (Mem.astack (injw_sup_l w)) ->
        (forall o k p, P b o k p -> 0 <= o) /\
        exists ofs,
        j b = Some (stkblock, ofs) /\ ofs >= max_stacksize' - stack_size (Mem.astack (injw_sup_r w))),
      inject_stack j P (Mem.astack (injw_sup_l w)) (Mem.astack (injw_sup_r w))
  | inject_stack_cons : forall b astk astk' size
       (IS_REC: inject_stack j P astk astk')
       (FRESH: ~ sup_In b (injw_sup_l w)),
       j b = Some (stkblock, max_stacksize' - stack_size astk' - frame_size_a (mk_frame b size)) ->
       (forall o k p, 0 <= o < size <-> P b o k p) ->
       inject_stack j P (((mk_frame b size)::nil)::astk) (((mk_frame stkblock size)::nil)::astk').

Remark init_stkcin_l:
  forall j P a a',
    inject_stack j P a a' -> stkcin' (injw_sup_l w).
Proof. induction 1; auto. Qed.

Remark init_stkcin_r:
  forall j P a a',
    inject_stack j P a a' -> stkcin' (injw_sup_l w).
Proof. induction 1; auto. Qed.

Lemma inject_stack_incr:
  forall j j' P (INCR: inject_incr j j')
    l l' (IS: inject_stack j P l l'),
    inject_stack j' P l l'.
Proof.
  induction 2; econstructor; eauto.
  intros. edestruct INIT_INNER as (PERM & ofs & INJ & GE'); eauto.
Qed.


Lemma inject_stack_inv:
  forall j (P P': perm_type)
    l l' (IS: inject_stack j P l l')
    (INCR: forall b o k p, current_in_stack' b l -> (P b o k p <-> P' b o k p)),
    inject_stack j P' l l'.
Proof.
  induction 1; econstructor; eauto.
  - intros. edestruct INIT_INNER as (PERM & EX). eauto. split; auto.
    intros. exploit INCR; eauto. intros RW. rewrite <- RW in H0. eapply PERM; eauto.
  - eapply IHIS; eauto. intros; eapply INCR; eauto. simpl.
    right. simpl in H1. apply H1.
  - intros. etransitivity. 2: eapply INCR; eauto. eauto. simpl.
    left. reflexivity.
Qed.

(** matching state *)
Inductive match_states: meminj -> state -> state -> Prop :=
| match_states_intro:
    forall (j: meminj)
      (rs: regset) (m: mem) (rs': regset) (m': mem) (live: bool)
   (** Memory Injection *)
      (MINJ: Mem.inject j m m')
      (GLOBINJ: meminj_preserves_globals j)
      (ENVSUP: Mem.sup_include (injw_sup_l w) (Mem.support m))
      (ENVSUP': Mem.sup_include (injw_sup_r w) (Mem.support m'))
   (** Regset Injection *)
      (RSPzero: forall b i, rs # RSP = Vptr b i -> i = Ptrofs.zero)
      (RSPblock: forall b i, rs # RSP = Vptr b i -> hd_error (sp_of_astack (Mem.astack (Mem.support m))) = Some b)
      (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
   (** Stack Properties **)
      (STKLIMIT: stack_size (Mem.astack (Mem.support m)) <= max_stacksize)
      (STKNOREPET: list_norepet (sp_of_astack (Mem.astack (Mem.support m))))
      (STKCIN: stkcin m)
      (STKVB: Mem.valid_block m stkblock)
      (STKPERMOFS: forall ofs k p, ~ Mem.perm m stkblock ofs k p)
      (STKVB': Mem.valid_block m' stkblock)
      (STKPERMOFS': single_stack_perm_ofs m')
   (** Stack Injection *)
      (*record the mapping of each active sp*)
      (RSPINJ: inject_stack j (Mem.perm m) (Mem.astack (Mem.support m)) (Mem.astack (Mem.support m')))
      (RSPINJ': rs'#RSP = Vptr stkblock (Ptrofs.repr (max_stacksize' - stack_size (Mem.astack (Mem.support m')))))
          (* (Ptrofs.unsigned stkofs =
           max_stacksize' -
           stack_size (Mem.astack (Mem.support m)))
          /\ (rs'#RSP) = Vptr stkblock stkofs) *)
      (STKINJLWBD: stack_inject_lowbound j m (max_stacksize' - stack_size (Mem.astack (Mem.support m')))),
      match_states j (State rs m live) (State rs' m' live).

(** injection in exec_instr *)
Section VAL_INJ_OPS.

Variable f: meminj.

Inductive opt_val_inject (j:meminj) : option val -> option val -> Prop :=
| opt_val_inject_none v: opt_val_inject j None v
| opt_val_inject_some v1 v2 : Val.inject j v1 v2 ->
                              opt_val_inject j (Some v1) (Some v2).


Remark zero_ext_inject:
  forall v1 v2 n,
    Val.inject f v1 v2 ->
    Val.inject f (Val.zero_ext n v1) (Val.zero_ext n v2).
Proof.
  intros.
  unfold Val.zero_ext. destruct v1, v2; auto; inv H; auto.
Qed.

Remark sign_ext_inject:
  forall v1 v2 n,
    Val.inject f v1 v2 ->
    Val.inject f (Val.sign_ext n v1) (Val.sign_ext n v2).
Proof.
  intros.
  unfold Val.sign_ext. destruct v1, v2; auto; inv H; auto.
Qed.

Remark longofintu_inject:
  forall v1 v2,
    Val.inject f v1 v2 ->
    Val.inject f (Val.longofintu v1) (Val.longofintu v2).
Proof.
  intros.
  unfold Val.longofintu. destruct v1, v2; auto; inv H; auto.
Qed.

Remark longofint_inject:
  forall v1 v2,
    Val.inject f v1 v2 ->
    Val.inject f (Val.longofint v1) (Val.longofint v2).
Proof.
  intros.
  unfold Val.longofint. destruct v1, v2; auto; inv H; auto.
Qed.

Remark singleoffloat_inject:
  forall v1 v2,
    Val.inject f v1 v2 ->
    Val.inject f (Val.singleoffloat v1) (Val.singleoffloat v2).
Proof.
  intros.
  unfold Val.singleoffloat. destruct v1, v2; auto; inv H; auto.
Qed.

Remark floatofsingle_inject:
  forall v1 v2,
    Val.inject f v1 v2 ->
    Val.inject f (Val.floatofsingle v1) (Val.floatofsingle v2).
Proof.
  intros.
  unfold Val.floatofsingle. destruct v1, v2; auto; inv H; auto.
Qed.

Remark maketotal_inject : forall v1 v2 j,
    opt_val_inject j v1 v2 -> Val.inject j (Val.maketotal v1) (Val.maketotal v2).
Proof.
  intros.
  inversion H; simpl; subst; auto.
Qed.

Remark intoffloat_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.intoffloat v1) (Val.intoffloat v2).
Proof.
  intros. unfold Val.intoffloat.
  destruct v1; try (constructor); inv H.
  destruct (Float.to_int f0); simpl; constructor; auto.
Qed.

Remark floatofint_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.floatofint v1) (Val.floatofint v2).
Proof.
  intros. unfold Val.floatofint.
  destruct v1; try (constructor); inv H.
  simpl; constructor; auto.
Qed.

Remark intofsingle_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.intofsingle v1) (Val.intofsingle v2).
Proof.
  intros. unfold Val.intofsingle.
  destruct v1; try (constructor); inv H.
  destruct (Float32.to_int f0); simpl; constructor; auto.
Qed.

Remark singleofint_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.singleofint v1) (Val.singleofint v2).
Proof.
  intros. unfold Val.singleofint.
  destruct v1; try (constructor); inv H.
  simpl; constructor; auto.
Qed.

Remark longoffloat_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.longoffloat v1) (Val.longoffloat v2).
Proof.
  intros. unfold Val.longoffloat.
  destruct v1; try (constructor); inv H.
  destruct (Float.to_long f0); simpl; constructor; auto.
Qed.

Remark floatoflong_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.floatoflong v1) (Val.floatoflong v2).
Proof.
  intros. unfold Val.floatoflong.
  destruct v1; try (constructor); inv H.
  simpl; constructor; auto.
Qed.

Remark longofsingle_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.longofsingle v1) (Val.longofsingle v2).
Proof.
  intros. unfold Val.longofsingle.
  destruct v1; try (constructor); inv H.
  destruct (Float32.to_long f0); simpl; constructor; auto.
Qed.

Remark singleoflong_inject : forall v1 v2,
  Val.inject f v1 v2 -> opt_val_inject f (Val.singleoflong v1) (Val.singleoflong v2).
Proof.
  intros. unfold Val.singleoflong.
  destruct v1; try (constructor); inv H.
  simpl; constructor; auto.
Qed.

Remark neg_inject:
  forall v1 v2,
  Val.inject f v1 v2 ->
  Val.inject f (Val.neg v1) (Val.neg v2).
Proof.
  intros.
  unfold Val.neg. destruct v1, v2; auto; inv H; auto.
Qed.

Remark negl_inject:
  forall v1 v2,
  Val.inject f v1 v2 ->
  Val.inject f (Val.negl v1) (Val.negl v2).
Proof.
  intros.
  unfold Val.negl. destruct v1, v2; auto; inv H; auto.
Qed.

Remark mul_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mul v1 v2) (Val.mul v1' v2').
Proof.
  intros.
  unfold Val.mul. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark mull_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mull v1 v2) (Val.mull v1' v2').
Proof.
  intros.
  unfold Val.mull. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark mulhs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulhs v1 v2) (Val.mulhs v1' v2').
Proof.
  intros.
  unfold Val.mulhs. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark mullhs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mullhs v1 v2) (Val.mullhs v1' v2').
Proof.
  intros.
  unfold Val.mullhs. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark mulhu_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulhu v1 v2) (Val.mulhu v1' v2').
Proof.
  intros.
  unfold Val.mulhu. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark mullhu_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mullhu v1 v2) (Val.mullhu v1' v2').
Proof.
  intros.
  unfold Val.mullhu. destruct v1, v2; auto; inv H; inv H0; auto.
Qed.

Remark shr_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shr v1 v2) (Val.shr v1' v2').
Proof.
  intros.
  unfold Val.shr. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Remark shrl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shrl v1 v2) (Val.shrl v1' v2').
Proof.
  intros.
  unfold Val.shrl. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Remark and_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.and v1 v2) (Val.and v1' v2').
Proof.
  intros.
  unfold Val.and. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark andl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.andl v1 v2) (Val.andl v1' v2').
Proof.
  intros.
  unfold Val.andl. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark or_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.or v1 v2) (Val.or v1' v2').
Proof.
  intros.
  unfold Val.or. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark orl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.orl v1 v2) (Val.orl v1' v2').
Proof.
  intros.
  unfold Val.orl. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark xor_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.xor v1 v2) (Val.xor v1' v2').
Proof.
  intros.
  unfold Val.xor. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark xorl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.xorl v1 v2) (Val.xorl v1' v2').
Proof.
  intros.
  unfold Val.xorl. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark notint_inject:
  forall v1 v2,
  Val.inject f v1 v2 ->
  Val.inject f (Val.notint v1) (Val.notint v2).
Proof.
  intros.
  unfold Val.notint. destruct v1, v2; auto; inv H; auto.
Qed.

Remark notl_inject:
  forall v1 v2,
  Val.inject f v1 v2 ->
  Val.inject f (Val.notl v1) (Val.notl v2).
Proof.
  intros.
  unfold Val.notl. destruct v1, v2; auto; inv H; auto.
Qed.

Remark shl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shl v1 v2) (Val.shl v1' v2').
Proof.
  intros.
  unfold Val.shl. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Remark shll_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shll v1 v2) (Val.shll v1' v2').
Proof.
  intros.
  unfold Val.shll. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Remark shru_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shru v1 v2) (Val.shru v1' v2').
Proof.
  intros.
  unfold Val.shru. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Remark shrlu_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.shrlu v1 v2) (Val.shrlu v1' v2').
Proof.
  intros.
  unfold Val.shrlu. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Remark ror_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.ror v1 v2) (Val.ror v1' v2').
Proof.
  intros.
  unfold Val.ror. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int.iwordsize); auto.
Qed.

Remark rorl_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.rorl v1 v2) (Val.rorl v1' v2').
Proof.
  intros.
  unfold Val.rorl. destruct v1, v2; auto; inv H; inv H0.
  destruct (Int.ltu i0 Int64.iwordsize'); auto.
Qed.

Lemma weak_valid_pointer_nonempty_perm:
  forall m b ofs,
  Mem.weak_valid_pointer m b ofs = true <->
  (Mem.perm m b ofs Cur Nonempty) \/ (Mem.perm m b (ofs-1) Cur Nonempty).
Proof.
  intros. unfold Mem.weak_valid_pointer. unfold Mem.valid_pointer.
  destruct (Mem.perm_dec m b ofs Cur Nonempty); destruct (Mem.perm_dec m b (ofs-1) Cur Nonempty); simpl;
  intuition congruence.
Qed.

Lemma weak_valid_pointer_size_bounds : forall f b1 b2 m1 m2 ofs delta,
  f b1 = Some (b2, delta) ->
  Mem.inject f m1 m2 ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  0 <= delta <= Ptrofs.max_unsigned /\
  0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned.
Proof.
  intros. exploit Mem.mi_representable; eauto.
  rewrite weak_valid_pointer_nonempty_perm in H1.
  destruct H1; eauto with mem. intros.
  generalize (Ptrofs.unsigned_range ofs). lia.
Qed.

Theorem valid_pointer_inject_ofs:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.inject f m1 m2 ->
  Mem.valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.valid_pointer m2 b2  (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. exploit Mem.valid_pointer_inject; eauto. intros.
  intros. unfold Ptrofs.add.
  exploit weak_valid_pointer_size_bounds; eauto.
  erewrite Mem.weak_valid_pointer_spec; eauto.
  intros [A B].
  repeat rewrite Ptrofs.unsigned_repr; eauto.
Qed.

Theorem weak_valid_pointer_inject_ofs:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  Mem.inject f m1 m2 ->
  Mem.weak_valid_pointer m1 b1 (Ptrofs.unsigned ofs) = true ->
  Mem.weak_valid_pointer m2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true.
Proof.
  intros. exploit Mem.weak_valid_pointer_inject; eauto.
  intros. unfold Ptrofs.add.
  exploit weak_valid_pointer_size_bounds; eauto. intros [A B].
  repeat rewrite Ptrofs.unsigned_repr; auto.
Qed.

Remark vtrue_inject :
  Val.inject f Vtrue Vtrue.
Proof.
  intros. unfold Vtrue. auto.
Qed.

Remark vfalse_inject :
  Val.inject f Vfalse Vfalse.
Proof.
  intros. unfold Vfalse. auto.
Qed.

Remark vofbool_inject : forall v,
  Val.inject f (Val.of_bool v) (Val.of_bool v).
Proof.
  destruct v; simpl.
  - apply vtrue_inject.
  - apply vfalse_inject.
Qed.

Definition cmpu_bool_inject := fun j m m' (MINJ: Mem.inject j m m') => Val.cmpu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m') (fun b1 ofs b2 delta FB => valid_pointer_inject_ofs j m m' b1 ofs b2 delta FB MINJ) (fun b1 ofs b2 delta FB => weak_valid_pointer_inject_ofs j m m' b1 ofs b2 delta FB MINJ) (fun b ofs b' delta FB MVP => Mem.weak_valid_pointer_inject_no_overflow j m m' b ofs b' delta MINJ MVP FB) (fun b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 => Mem.different_pointers_inject j m m' b1  ofs1 b2 ofs2 b1' delta1 b2' delta2 MINJ).

Remark cmpu_inject
  : forall (m m' : mem),
    Mem.inject f m m' ->
    forall (c : comparison) (v1 v2 v1' v2' : val),
      Val.inject f v1 v1' ->
      Val.inject f v2 v2' ->
      Val.inject f (Val.cmpu (Mem.valid_pointer m) c v1 v2)
                 (Val.cmpu (Mem.valid_pointer m') c v1' v2').
Proof.
  unfold Val.cmpu. unfold Val.of_optbool.
  intros.
  destr. eapply cmpu_bool_inject in Heqo; eauto.
  rewrite Heqo. unfold Vtrue, Vfalse; destr; auto. auto.
Qed.

Definition cmplu_bool_inject := fun j m m' (MINJ: Mem.inject j m m') => Val.cmplu_bool_inject j (Mem.valid_pointer m) (Mem.valid_pointer m') (fun b1 ofs b2 delta FB => valid_pointer_inject_ofs j m m' b1 ofs b2 delta FB MINJ) (fun b1 ofs b2 delta FB => weak_valid_pointer_inject_ofs j m m' b1 ofs b2 delta FB MINJ) (fun b ofs b' delta FB MVP => Mem.weak_valid_pointer_inject_no_overflow j m m' b ofs b' delta MINJ MVP FB) (fun b1 ofs1 b2 ofs2 b1' delta1 b2' delta2 => Mem.different_pointers_inject j m m' b1  ofs1 b2 ofs2 b1' delta1 b2' delta2 MINJ).

Remark cmplu_inject
  : forall (m m' : mem),
    Mem.inject f m m' ->
    forall (c : comparison) (v1 v2 v1' v2' : val),
      Val.inject f v1 v1' ->
      Val.inject f v2 v2' ->
      opt_val_inject f (Val.cmplu (Mem.valid_pointer m) c v1 v2)
                     (Val.cmplu (Mem.valid_pointer m') c v1' v2').
Proof.
  unfold Val.cmplu. unfold option_map.
  intros.
  destr. eapply cmplu_bool_inject in Heqo; eauto.
  rewrite Heqo. constructor. apply vofbool_inject. constructor.
Qed.

Remark negative_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.negative v) (Val.negative v').
Proof.
  unfold Val.negative. intros.
  destr; auto. inv H. auto.
Qed.

Remark negativel_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.negativel v) (Val.negativel v').
Proof.
  unfold Val.negativel. intros.
  destr; auto. inv H. auto.
Qed.

Remark sub_overflow_inject:
  forall v1 v2 v3 v4,
    Val.inject f v1 v2 ->
    Val.inject f v3 v4 ->
    Val.inject f (Val.sub_overflow v1 v3) (Val.sub_overflow v2 v4).
Proof.
  unfold Val.sub_overflow; intros.
  destr; auto. inv H. destr; auto; inv H0. auto.
Qed.

Remark subl_overflow_inject:
  forall v1 v2 v3 v4,
    Val.inject f v1 v2 ->
    Val.inject f v3 v4 ->
    Val.inject f (Val.subl_overflow v1 v3) (Val.subl_overflow v2 v4).
Proof.
  unfold Val.subl_overflow; intros.
  destr; auto. inv H. destr; auto; inv H0. auto.
Qed.

Remark addf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.addf v1 v2) (Val.addf v1' v2').
Proof.
  intros.
  unfold Val.addf. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark subf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.subf v1 v2) (Val.subf v1' v2').
Proof.
  intros.
  unfold Val.subf. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark mulf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulf v1 v2) (Val.mulf v1' v2').
Proof.
  intros.
  unfold Val.mulf. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark divf_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.divf v1 v2) (Val.divf v1' v2').
Proof.
  intros.
  unfold Val.divf. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark negf_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.negf v) (Val.negf v').
Proof.
  intros.
  unfold Val.negf. destr; auto. inv H. auto.
Qed.

Remark absf_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.absf v) (Val.absf v').
Proof.
  intros.
  unfold Val.absf. destr; auto. inv H. auto.
Qed.

Remark addfs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.addfs v1 v2) (Val.addfs v1' v2').
Proof.
  intros.
  unfold Val.addfs. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark subfs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.subfs v1 v2) (Val.subfs v1' v2').
Proof.
  intros.
  unfold Val.subfs. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark mulfs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.mulfs v1 v2) (Val.mulfs v1' v2').
Proof.
  intros.
  unfold Val.mulfs. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark divfs_inject:
  forall v1 v1' v2 v2',
  Val.inject f v1 v1' ->
  Val.inject f v2 v2' ->
  Val.inject f (Val.divfs v1 v2) (Val.divfs v1' v2').
Proof.
  intros.
  unfold Val.divfs. destruct v1, v2; auto; inv H; inv H0.
  auto.
Qed.

Remark negfs_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.negfs v) (Val.negfs v').
Proof.
  intros.
  unfold Val.negfs. destr; auto. inv H. auto.
Qed.

Remark absfs_inject:
  forall v v',
    Val.inject f v v' ->
    Val.inject f (Val.absfs v) (Val.absfs v').
Proof.
  intros.
  unfold Val.absfs. destr; auto. inv H. auto.
Qed.

End VAL_INJ_OPS.

Lemma symbol_address_inject:
  forall j id ofs,
    meminj_preserves_globals j ->
    Val.inject j (Genv.symbol_address se id ofs) (Genv.symbol_address tse id ofs).
Proof.
  intros j id i0 MPG.
  unfold Genv.symbol_address. destr; auto. eapply symbol_inject in Heqo as INJ; eauto.
  unfold Genv.find_symbol in *. erewrite Genv.mge_symb in Heqo; eauto. 2:apply MPG. erewrite Heqo.
  econstructor; eauto.
  rewrite Ptrofs.add_zero. auto.
Qed.

Lemma eval_addrmode32_inject:
  forall a rs rs' j,
    meminj_preserves_globals j ->
    (forall r, Val.inject j (rs r) (rs' r)) ->
    Val.inject j (eval_addrmode32 ge a rs) (eval_addrmode32 tge a rs').
Proof.
  unfold eval_addrmode32. intros.
  destruct a.
  apply Val.add_inject. destr; auto.
  apply Val.add_inject. repeat destr; eauto using mul_inject.
  repeat destr; eauto using symbol_address_inject.
Qed.

Lemma eval_addrmode64_inject:
  forall a rs rs' j,
    meminj_preserves_globals j ->
    (forall r, Val.inject j (rs r) (rs' r)) ->
    Val.inject j (eval_addrmode64 ge a rs) (eval_addrmode64 tge a rs').
Proof.
  unfold eval_addrmode64. intros.
  destruct a.
  apply Val.addl_inject. destr; auto.
  apply Val.addl_inject. repeat destr; eauto using mull_inject.
  repeat destr; eauto using symbol_address_inject.
Qed.

Lemma eval_addrmode_inject:
  forall a rs rs' j,
    meminj_preserves_globals j ->
    (forall r, Val.inject j (rs r) (rs' r)) ->
    Val.inject j (eval_addrmode ge a rs) (eval_addrmode tge a rs').
Proof.
  unfold eval_addrmode.
  intros.
  destr; eauto using eval_addrmode32_inject, eval_addrmode64_inject.
Qed.

Lemma exec_load_inject:
  forall κ m1 a rs1 rd rs1' m1' rs2 m2 j sz live,
    meminj_preserves_globals j ->
    Mem.inject j m1 m2 ->
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    exec_load ge sz κ m1 a rs1 rd = Next' rs1' m1' live ->
    exists rs2' m2',
      exec_load tge sz κ m2 a rs2 rd = Next' rs2' m2' live /\
      Mem.inject j m1' m2' /\
      forall r, Val.inject j (rs1' r) (rs2' r).
Proof.
  unfold exec_load.
  intros κ m1 a rs1 rd rs1' m1' rs2 m2 j sz live MPG MINJ RINJ EL.
  destr_in EL. inv EL.
  edestruct Mem.loadv_inject as (v2 & LD & VINJ); eauto.
  apply eval_addrmode_inject; auto.
  rewrite LD. do 2 eexists; split; eauto. split; auto.
  intros; apply val_inject_nextinstr_nf.
  intros; apply val_inject_set; auto.
Qed.

Lemma exec_store_inject:
  forall κ m1 a rs1 rd rs1' m1' rs2 m2 j destroyed sz live,
    meminj_preserves_globals j ->
    Mem.inject j m1 m2 ->
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    exec_store ge sz κ m1 a rs1 rd destroyed = Next' rs1' m1' live ->
    exists rs2' m2',
      exec_store tge sz κ m2 a rs2 rd destroyed = Next' rs2' m2' live /\
      Mem.inject j m1' m2' /\
      forall r, Val.inject j (rs1' r) (rs2' r).
Proof.
  unfold exec_store. intros κ m1 a rs1 rd rs1' m1' rs2 m2 j destroyed sz live MPG MINJ RINJ ES.
  destr_in ES. inv ES.
  edestruct Mem.storev_mapped_inject as (m2' & ST & MINJ'); eauto.
  apply eval_addrmode_inject; auto.
  rewrite ST. do 2 eexists; split; eauto. split; auto.
  intros; apply val_inject_nextinstr_nf.
  intros; apply val_inject_undef_regs; auto.
Qed.


Ltac simpl_inject :=
  first [
      apply val_inject_nextinstr
    | apply val_inject_nextinstr_nf
    | apply val_inject_set
    | apply val_inject_undef_regs
    | apply Val.offset_ptr_inject
    | apply Val.loword_inject
    | apply Val.hiword_inject
    | apply Val.add_inject
    | apply Val.sub_inject
    | apply Val.addl_inject
    | apply Val.subl_inject
    | apply eval_addrmode32_inject
    | apply eval_addrmode64_inject
    | apply eval_addrmode_inject
    | apply symbol_address_inject
    | apply zero_ext_inject
    | apply sign_ext_inject
    | apply longofintu_inject
    | apply longofint_inject
    | apply singleoffloat_inject
    | apply floatofsingle_inject
    | apply maketotal_inject
    | apply intoffloat_inject
    | apply floatofint_inject
    | apply intofsingle_inject
    | apply singleofint_inject
    | apply longoffloat_inject
    | apply floatoflong_inject
    | apply longofsingle_inject
    | apply singleoflong_inject
    | apply neg_inject
    | apply negl_inject
    | apply mul_inject
    | apply mull_inject
    | apply mulhs_inject
    | apply mullhs_inject
    | apply mulhu_inject
    | apply mullhu_inject
    | apply shr_inject
    | apply shrl_inject
    | apply and_inject
    | apply andl_inject
    | apply or_inject
    | apply orl_inject
    | apply xor_inject
    | apply xorl_inject
    | apply notint_inject
    | apply notl_inject
    | apply shl_inject
    | apply shll_inject
    | apply shru_inject
    | apply shrlu_inject
    | apply ror_inject
    | apply rorl_inject
    | apply cmpu_inject
    | apply cmplu_inject
    | apply negative_inject
    | apply negativel_inject
    | apply sub_overflow_inject
    | apply subl_overflow_inject
    | apply addf_inject
    | apply subf_inject
    | apply mulf_inject
    | apply divf_inject
    | apply negf_inject
    | apply absf_inject
    | apply addfs_inject
    | apply subfs_inject
    | apply mulfs_inject
    | apply divfs_inject
    | apply negfs_inject
    | apply absfs_inject
    | unfold Vzero; auto
    ].

Lemma eval_testcond_inject:
  forall j rs1 rs2
    (RINJ : forall r : PregEq.t, Val.inject j (rs1 r) (rs2 r)) c b,
    eval_testcond c rs1 = Some b ->
    eval_testcond c rs2 = Some b.
Proof.
  unfold eval_testcond.
  intros.
  generalize (RINJ ZF), (RINJ CF), (RINJ OF), (RINJ SF), (RINJ PF).
  intros A B C D E.
  repeat destr_in H;
    repeat match goal with
           | H: Val.inject _ (Vint _) _ |- _ => inv H
           | |- _ => simpl; auto
           end.
Qed.

Lemma eval_testcond_of_optbool_inject:
  forall j rs1 rs2
    (RINJ : forall r : PregEq.t, Val.inject j (rs1 r) (rs2 r)) c,
    Val.inject j (Val.of_optbool (eval_testcond c rs1)) (Val.of_optbool (eval_testcond c rs2)).
Proof.
  unfold Val.of_optbool. intros.
  destr. erewrite eval_testcond_inject; eauto.
  unfold Vtrue, Vfalse; destr; eauto. auto.
Qed.

Lemma compare_floats_inject:
  forall j rs1 rs2
    (RINJ : forall r : PregEq.t, Val.inject j (rs1 r) (rs2 r)) a b c d
    (INJ1: Val.inject j a c) (INJ2: Val.inject j b d) r,
    Val.inject j (compare_floats a b rs1 r) (compare_floats c d rs2 r).
Proof.
  unfold compare_floats.
  intros.
  inv INJ1; repeat simpl_inject.
  inv INJ2; repeat simpl_inject.
  apply vofbool_inject.
  apply vofbool_inject.
  apply vofbool_inject.
  repeat (destr; repeat simpl_inject).
  repeat (destr; repeat simpl_inject).
Qed.

Lemma compare_floats32_inject:
  forall j rs1 rs2
    (RINJ : forall r : PregEq.t, Val.inject j (rs1 r) (rs2 r)) a b c d
    (INJ1: Val.inject j a c) (INJ2: Val.inject j b d) r,
    Val.inject j (compare_floats32 a b rs1 r) (compare_floats32 c d rs2 r).
Proof.
  unfold compare_floats32.
  intros.
  inv INJ1; repeat simpl_inject.
  inv INJ2; repeat simpl_inject.
  apply vofbool_inject.
  apply vofbool_inject.
  apply vofbool_inject.
  repeat (destr; repeat simpl_inject).
  repeat (destr; repeat simpl_inject).
Qed.

Lemma goto_label_inject:
  forall j rs1 rs2 m1 m2 live
    (MINJ: Mem.inject j m1 m2)
    (GLOBINJ: meminj_preserves_globals j)
    (RINJ : forall r : PregEq.t, Val.inject j (rs1 r) (rs2 r))
    l f rs1' m1',
    Asm.goto_label instr_size ge f l rs1 m1 = Next' rs1' m1' live ->
    exists rs2' m2',
      Asm.goto_label instr_size tge f l rs2 m2 = Next' rs2' m2' live /\
      Mem.inject j m1' m2' /\
      forall r, Val.inject j (rs1' r) (rs2' r).
Proof.
  unfold goto_label. intros. repeat destr_in H.
  generalize (RINJ PC); rewrite Heqv. intro A; inv A.
  exploit globinj_to_funinj; eauto. apply GLOBINJ. intros [ ]. subst.
  erewrite functions_transl; eauto.
  do 2 eexists; split; eauto. split; eauto.
  repeat simpl_inject. econstructor; eauto. rewrite Ptrofs.add_zero. auto.
Qed.

Lemma exec_instr_inject_normal:
  forall j m1 m2 rs1 rs2 f i rs1' m1' live
    (MINJ: Mem.inject j m1 m2)
    (GLOBINJ: meminj_preserves_globals j)
    (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
    (NOTSTKINSTR: stk_unrelated_instr i = true)
    (EI: Asm.exec_instr instr_size (injw_sup_l w) ge f i rs1 m1 = Next' rs1' m1' live),
  exists rs2' m2',
    Asm.exec_instr instr_size (injw_sup_r w) tge f i rs2 m2 = Next' rs2' m2' live
    /\ Mem.inject j m1' m2'
    /\ (forall r, Val.inject j (rs1' # r) (rs2' # r)).
Proof.
  intros.
  destruct i; (simpl in *; repeat destr_in EI;
               try congruence;

               match goal with
               | |- exists _ _, Next' _ _ _ = Next' _ _ _ /\ _ /\ _ =>
                 try (do 2 eexists; split; [now eauto |
                                            split; [
                                              eauto with mem
                                            | repeat
                                                simpl_inject
                                            ]
                                           ]
                     )
               | |- _ => try first [
                             now (eapply exec_load_inject; eauto)
                           | now (eapply exec_store_inject; eauto)
                           ]
               end
              ).
  + generalize (RINJ RDX); rewrite Heqv; inversion 1; subst.
    generalize (RINJ RAX); rewrite Heqv0; inversion 1; subst.
    generalize (RINJ r1); rewrite Heqv1; inversion 1; subst.
    rewrite Heqo.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + generalize (RINJ RDX); rewrite Heqv; inversion 1; subst.
    generalize (RINJ RAX); rewrite Heqv0; inversion 1; subst.
    generalize (RINJ r1); rewrite Heqv1; inversion 1; subst.
    rewrite Heqo.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + generalize (RINJ RDX); rewrite Heqv; inversion 1; subst.
    generalize (RINJ RAX); rewrite Heqv0; inversion 1; subst.
    generalize (RINJ r1); rewrite Heqv1; inversion 1; subst.
    rewrite Heqo.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + generalize (RINJ RDX); rewrite Heqv; inversion 1; subst.
    generalize (RINJ RAX); rewrite Heqv0; inversion 1; subst.
    generalize (RINJ r1); rewrite Heqv1; inversion 1; subst.
    rewrite Heqo.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + erewrite eval_testcond_inject; eauto. simpl. auto.
  + erewrite eval_testcond_inject; eauto. simpl. auto.
  + eapply eval_testcond_of_optbool_inject. auto.
  + eapply compare_floats_inject; auto.
  + eapply compare_floats32_inject; auto.
  + eapply goto_label_inject; eauto.
  + exploit functions_translated. 3:eauto. eauto. apply symbol_address_inject. auto.
    intros FF'. rewrite FF'. do 2 eexists. split; eauto. split. eauto with mem. repeat simpl_inject.
  + generalize (RINJ r). intro.
    exploit functions_translated; eauto. intros FF'. rewrite FF'.
    destruct (rs1 r); simpl in Heqo; inv Heqo. inv H.
    destr_in H1. subst.
    exploit globinj_to_funinj; eauto. apply GLOBINJ. intros [ ]. subst.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
    econstructor; eauto.
  + erewrite eval_testcond_inject; eauto. simpl.
    eapply goto_label_inject; eauto.
  + erewrite eval_testcond_inject; eauto. simpl.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + erewrite eval_testcond_inject; eauto. simpl.
    erewrite eval_testcond_inject; eauto. simpl.
    eapply goto_label_inject; eauto.
  + erewrite eval_testcond_inject; eauto. simpl.
    erewrite eval_testcond_inject; eauto. simpl.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + erewrite eval_testcond_inject; eauto. simpl.
    erewrite eval_testcond_inject; eauto. simpl.
    do 2 eexists; split; eauto. split; eauto. repeat simpl_inject.
  + generalize (RINJ r); rewrite Heqv; intro A; inv A.
    rewrite Heqo.
    eapply goto_label_inject; eauto.
    repeat simpl_inject.
  + generalize (RINJ rd). intro A.
    generalize (RINJ r2). intro B.
    unfold Op.maxf. repeat destr; try congruence; try inv A; try inv B; constructor.
  + generalize (RINJ rd). intro A.
    generalize (RINJ r2). intro B.
    unfold Op.minf. repeat destr; try congruence; try inv A; try inv B; constructor.
Qed.

Lemma inject_stack_size:
  forall j P a a',
    inject_stack j P a a' ->
    stack_size a >= stack_size (Mem.astack (injw_sup_l w)).
Proof.
  intros * RSPINJ. induction RSPINJ. lia.
  simpl. pose proof frame_size_a_pos (mk_frame b size). lia.
Qed.

Lemma inject_stack_size_incr:
  forall j P a a',
    inject_stack j P a a' ->
    stack_size a >= stack_size a'.
Proof. induction 1. auto. simpl. unfold frame_size_a. simpl. lia. Qed.

Lemma max_stacksize_aligned : (8 | max_stacksize).
Proof. unfold max_stacksize. exists 512. lia. Qed.

Lemma max_stacksize_range : 0 <= max_stacksize <= Ptrofs.max_unsigned.
Proof. unfold max_stacksize. vm_compute. split; congruence. Qed.

Lemma max_stacksize'_range : 0 <= max_stacksize' <= Ptrofs.max_unsigned.
Proof. unfold max_stacksize. vm_compute. split; congruence. Qed.

Lemma allocframe_inject:
  forall j stkb m m1 m2 m3 m4 m' live live' rs rs' sz ofs_ra ofs_link isz
    (MS: match_states j (State rs m live) (State rs' m' live))
    (SZPOS: sz>=0)
    (ALLOC: Mem.alloc m 0 sz = (m1, stkb))
    (RECORDFR: Mem.record_frame (Mem.push_stage m1) (Memory.mk_frame stkb sz) = Some m2)
    (RAPOS: 0 <= ofs_ra <= Ptrofs.max_unsigned)
    (STORERA: Mem.store Mptr m2 stkb ofs_ra (rs RA) = Some m3)
    (LINKPOS: 0 <= ofs_link <= Ptrofs.max_unsigned)
    (STORELINK: Mem.store Mptr m3 stkb ofs_link (rs RSP) = Some m4),
    let rs1 := (nextinstr_nf isz (rs # RAX <- (rs RSP)) # RSP <- (Vptr stkb Ptrofs.zero)) in
    let rs1' := (nextinstr_nf isz (rs' # RAX <- (rs' RSP)) # RSP <- (Val.offset_ptr (rs' RSP) (Ptrofs.neg (Ptrofs.repr (align sz 8))))) in
    exists j', inject_incr j j' /\
    exists m1', Mem.record_frame (Mem.push_stage m') (mk_frame stkblock sz) = Some m1' /\
    exists m2', Mem.storev Mptr m1' (Val.offset_ptr (Val.offset_ptr (rs' RSP) (Ptrofs.neg (Ptrofs.repr (align sz 8)))) (Ptrofs.repr ofs_ra)) (rs' RA)= Some m2' /\
    exists m3', Mem.storev Mptr m2' (Val.offset_ptr (Val.offset_ptr (rs' RSP) (Ptrofs.neg (Ptrofs.repr (align sz 8)))) (Ptrofs.repr ofs_link)) (rs' RSP) = Some m3' /\
    match_states j' (State rs1 m4 live') (State rs1' m3' live').
Proof.
  intros.
  inv MS.
  remember (max_stacksize' - stack_size (Mem.astack (Mem.support m'))) as stksize.
  remember (Ptrofs.repr stksize) as stkofs.
  remember (align sz 8) as aligned_sz.
  remember (stksize - aligned_sz) as stksize'.
  (* reuse alloc_inject lemmas in memory *)
  generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ stksize' MINJ ALLOC STKVB').
  (* assert some properties about stack size *)
  assert (ALGIN_SZ_ORDER: sz <= align sz 8). apply align_le. lia.
  remember (Memory.mk_frame stkb sz) as fr.
  assert (FRSZ: sz = Memory.frame_size fr). rewrite Heqfr. simpl. lia.
  assert (OLDSTKSIZE: aligned_sz <= stksize <= Ptrofs.max_unsigned).
  {
    split.
    - rewrite Heqstksize. apply Z.le_add_le_sub_r.
      rewrite Heqaligned_sz. rewrite FRSZ.
      remember (Mem.push_stage m1) as m1'.
      generalize (Mem.record_frame_size1 m1' m2 fr RECORDFR). intros.
      exploit Mem.support_push_stage. symmetry in Heqm1'.
      apply Heqm1'. intros SUPPUSH. rewrite SUPPUSH in H.
      simpl in H. unfold frame_size_a in H.
      exploit Mem.astack_alloc. apply ALLOC. intros ALLOCSTK.
      pose proof inject_stack_size_incr _ _ _ _ RSPINJ as SIZEGE.
      rewrite <- ALLOCSTK in SIZEGE. unfold max_stacksize'.
      unfold Mptr. destr; simpl;
      unfold max_stacksize in H; lia.
    - rewrite Heqstksize. pose proof max_stacksize'_range. pose proof stack_size_pos (Mem.astack (Mem.support m')). lia.
  }
  assert (NEWSTKSIZE: 0 <= stksize' <= Ptrofs.max_unsigned).
  {
    rewrite Heqstksize'. rewrite Heqstksize.
    split. lia.
    lia.
  }
  (* prove for its premise *)
  intro A.
  trim A. lia.
  trim A. intros. right. eapply STKPERMOFS'. eauto.
  trim A.
  {
    intros. eapply STKPERMOFS'.
    split. rewrite Heqstksize'. lia.
    rewrite Heqstksize'. rewrite Heqstksize.
    eapply Z.lt_le_trans with stksize. lia.
    rewrite Heqstksize.
    generalize (Memory.stack_size_pos (Mem.astack (Mem.support m'))).
    intros STKSZPOS.
    lia.
  }
  trim A.
  {
    red. intros. subst.
    eapply Z.divide_trans with 8.
    destruct chunk; try (exists 8; reflexivity);
      try (exists 4; reflexivity);
      try (exists 2; reflexivity);
      try (exists 1; reflexivity).
    apply Z.divide_sub_r.
    generalize (stack_size_aligned (Mem.astack (Mem.support m'))).
    intro ALI1.
    assert (ALI2: (8 | max_stacksize')). unfold max_stacksize'. red. exists 513.
    unfold max_stacksize. unfold Mptr. destr.
    apply Z.divide_sub_r; auto.
    apply align_divides. lia.
  }
  trim A.
  {
    intros b0 delta' ofs k p JB PERM OVERLAP.
    subst. simpl in OVERLAP.
    inv OVERLAP.
    generalize (STKINJLWBD _ _ _ _ _ JB PERM). lia.
  }
  destruct A as (f1 & MINJ1 & INCR & EQ1 & EQ2).
  exists f1. split. auto.
  generalize (Mem.push_stage_inject _ _ _ MINJ1). intros MINJ2.
  edestruct Mem.record_frame_parallel_inject as (m1' & RECORDFR' & MINJ3); eauto.
    rewrite Heqfr in RECORDFR. eauto.
    simpl. congruence.
    apply inject_stack_size_incr in RSPINJ. apply Mem.astack_alloc in ALLOC. simpl. rewrite ALLOC. lia.
    instantiate (1 := stkblock) in RECORDFR'.
  (* store ra *)
  assert (ALIGNED_SZ: 0 <= aligned_sz <= Ptrofs.max_unsigned). lia.
  exploit Mem.store_mapped_inject.
  apply MINJ3. apply STORERA. apply EQ1.
  eapply val_inject_incr; eauto.
  intros (m3' & STORERA' & MINJ1').
  exists m1'. split. auto.
  exists m3'. split. subst.
  rewrite RSPINJ'. simpl.
  remember (Ptrofs.repr (max_stacksize' - stack_size (Mem.astack (Mem.support m')))) as stkofs.
  assert ((Ptrofs.add stkofs (Ptrofs.neg (Ptrofs.repr (align sz 8)))) = Ptrofs.repr (Ptrofs.unsigned stkofs - align sz 8)).
  {
    rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub.
    rewrite (Ptrofs.unsigned_repr _ ALIGNED_SZ). reflexivity.
  }
  rewrite H. remember (Ptrofs.repr ofs_ra) as OFS.
  remember (Ptrofs.unsigned stkofs - align sz 8) as STKSIZE.
  rewrite Ptrofs.add_commut.
  assert (Ptrofs.unsigned (Ptrofs.add OFS (Ptrofs.repr STKSIZE)) =
          Ptrofs.unsigned OFS + STKSIZE) as EQ'.
  {
    rewrite Heqstkofs in HeqSTKSIZE. rewrite Ptrofs.unsigned_repr in HeqSTKSIZE.
    2:{ pose proof max_stacksize'_range. pose proof stack_size_pos. lia. }
    eapply Mem.address_inject; eauto. 2:rewrite HeqSTKSIZE; eauto.
    exploit Mem.store_valid_access_3. exact STORERA.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto.
    destruct VA. eapply H0.
    rewrite HeqOFS. rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); lia.
  }
  rewrite EQ'. rewrite HeqOFS.
  rewrite (Ptrofs.unsigned_repr _ RAPOS). subst. rewrite Ptrofs.unsigned_repr. auto.
  pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
  (* store link *)
  exploit Mem.store_mapped_inject.
  apply MINJ1'. apply STORELINK. apply EQ1.
  eapply val_inject_incr; eauto.
  intros (m4' & STORELINK' & MINJ4).
  exists m4'. split. subst.
  rewrite RSPINJ'. simpl.
  remember (Ptrofs.repr (max_stacksize' - stack_size (Mem.astack (Mem.support m')))) as stkofs.
  assert ((Ptrofs.add stkofs (Ptrofs.neg (Ptrofs.repr (align sz 8)))) = Ptrofs.repr (Ptrofs.unsigned stkofs - align sz 8)).
  {
    rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub.
    rewrite (Ptrofs.unsigned_repr _ ALIGNED_SZ). reflexivity.
  }
  rewrite H. remember (Ptrofs.repr ofs_link) as OFS.
  remember (Ptrofs.unsigned stkofs - align sz 8) as STKSIZE.
  rewrite Ptrofs.add_commut.
  assert (Ptrofs.unsigned (Ptrofs.add OFS (Ptrofs.repr STKSIZE)) =
          Ptrofs.unsigned OFS + STKSIZE) as EQ'.
  {
    rewrite Heqstkofs in HeqSTKSIZE. rewrite Ptrofs.unsigned_repr in HeqSTKSIZE.
    2:{ pose proof max_stacksize'_range. pose proof stack_size_pos. lia. }
    eapply Mem.address_inject; eauto. 2:subst; eauto.
    exploit Mem.store_valid_access_3. exact STORELINK.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto.
    destruct VA. eapply H0.
    rewrite HeqOFS. rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); lia.
  }
  rewrite EQ'. rewrite HeqOFS.
  rewrite (Ptrofs.unsigned_repr _ LINKPOS). rewrite <- RSPINJ'. subst. rewrite Ptrofs.unsigned_repr. auto.
  pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
  (* match state *)
  assert (SUPINCALL: Mem.sup_include (Mem.support m) (Mem.support m4)).
  {
    generalize (Mem.sup_include_alloc _ _ _ _ _ ALLOC).
    remember (Mem.push_stage m1) as m1x. symmetry in Heqm1x.
    generalize (Mem.sup_include_record_frame _ _ _ RECORDFR).
    generalize (Mem.support_store _ _ _ _ _ _ STORERA).
    generalize (Mem.support_store _ _ _ _ _ _ STORELINK).
    intros.
    eapply Mem.sup_include_trans. apply H2.
    rewrite H,H0.
    eapply Mem.sup_include_trans. 2: apply H1.
    inv Heqm1x. auto. simpl. unfold Mem.sup_push_stage.
    intro. destruct b; simpl; auto.
  }

  assert (SUPINCALL': Mem.sup_include (Mem.support m') (Mem.support m4')).
  {
    generalize (Mem.support_push_stage_1 m' _ ltac:(eauto)).
    generalize (Mem.support_record_frame_1 _ _ _ RECORDFR').
    generalize (Mem.support_store _ _ _ _ _ _ STORERA').
    generalize (Mem.support_store _ _ _ _ _ _ STORELINK').
    red. intros. rewrite H, H0, <- H1, <- H2. auto.
  }
  assert (PERMNEQ: forall b k ofs p, b <> stkb -> Mem.perm m b ofs k p <-> Mem.perm m4 b ofs k p).
  {
    intros.
    etransitivity.
    2: split. 2 :eapply Mem.perm_store_1; eauto. 2:eapply Mem.perm_store_2; eauto.
    etransitivity.
    2: split. 2 :eapply Mem.perm_store_1; eauto. 2:eapply Mem.perm_store_2; eauto.
    transitivity (Mem.perm m1 b ofs k p).
    2: erewrite Mem.perm_push_stage; eauto. 2: erewrite Mem.perm_record_frame; eauto.
    split. eapply Mem.perm_alloc_1; eauto.
    intro. exploit Mem.perm_alloc_inv; eauto. rewrite pred_dec_false. auto. auto.
    reflexivity.
  }
  assert (STKOFS': max_stacksize' - align (Z.max 0 sz) 8 - stack_size (Mem.astack (Mem.support m')) = max_stacksize' - stack_size (Mem.astack (Mem.support m4'))).
  {
    generalize (Mem.support_store _ _ _ _ _ _ STORERA').
    intro SUPSTRA.
    generalize (Mem.support_store _ _ _ _ _ _ STORELINK').
    intro SUPSTLINK.
    rewrite SUPSTLINK,SUPSTRA.
    remember (Mem.push_stage m1) as m1x.
    generalize (Mem.astack_record_frame _ _ _ RECORDFR').
    intro SUPRDFR. destruct SUPRDFR as (hd & tl & (H1 & H2)).
    simpl in H1. inversion H1. subst hd. clear H1.
    rewrite <- H3 in H2.
    rewrite H2.
    simpl. unfold frame_size_a. simpl. lia.
  }
  econstructor; eauto.
  (* Memory Injection *)
  - constructor; eauto.
    ++ eapply Genv.match_stbls_incr; eauto. apply GLOBINJ. intros.
       destruct (eq_block b1 stkb).
       subst b1. rewrite EQ1 in H0. inversion H0.
       clear - ALLOC. apply Mem.alloc_result_stack in ALLOC. red in ALLOC. destr_in ALLOC. unfold stkblock.
       split; intros SUP; apply Genv.genv_sup_glob in SUP as [ ]; congruence.
       specialize (EQ2 _ n). congruence.
    ++ red. intros. exploit Mem.alloc_result_stack; eauto. intros STK.
       exploit (EQ2 (Global id)). intro. subst. simpl in STK. auto.
       intros EQ. rewrite EQ in H. inv GLOBINJ. exploit global_inject0; eauto.
  (* Regset Injection *)
  - unfold rs1. intros.
    rewrite nextinstr_nf_rsp in H.
    rewrite Pregmap.gss in H. congruence.
  - unfold rs1, nextinstr_nf, nextinstr, undef_regs.
    repeat rewrite Pregmap.gso by congruence. rewrite Pregmap.gss.
    intros * EQ. inv EQ. clear - ALLOC RECORDFR STORERA STORELINK.
    apply Mem.support_store in STORELINK. apply Mem.support_store in STORERA.
    rewrite STORELINK, STORERA.
    apply Mem.astack_record_frame in RECORDFR as (hd & tl & EQ1 & EQ2). simpl in EQ1. inv EQ1.
    rewrite EQ2. simpl. auto.
  - intros. unfold rs1, rs1'.
    apply val_inject_nextinstr_nf; auto.
    apply val_inject_set; auto.
    apply val_inject_set; auto.
    intros. eapply val_inject_incr; eauto.
    eapply val_inject_incr; eauto.
    rewrite RSPINJ'. econstructor; eauto.
    subst.
    rewrite Ptrofs.add_zero_l.
    rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub.
    rewrite ! Ptrofs.unsigned_repr; auto.
    pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
  (* Stack Injection *)
  - erewrite Mem.support_store. 2: eauto. erewrite Mem.support_store. 2: eauto.
    apply Mem.record_frame_size in RECORDFR. lia.
  - erewrite Mem.support_store. 2: eauto.
    erewrite Mem.support_store. 2: eauto.
    apply Mem.astack_record_frame in RECORDFR as ARE.
    destruct ARE as [hd [tl [X Y]]].
    rewrite Y. simpl in X. inv X.
    erewrite Mem.astack_alloc. 2: eauto.
    simpl. constructor. intro. exploit STKCIN; eauto.
    intros [R S]. apply Mem.fresh_block_alloc in ALLOC. apply ALLOC. auto. auto.
  - unfold stkcin, current_in_stack. erewrite Mem.support_store. 2: eauto.
    erewrite Mem.support_store. 2: eauto.
    apply Mem.astack_record_frame in RECORDFR as ARE.
    destruct ARE as [hd [tl [X Y]]].
    rewrite Y. simpl in X. inv X.
    erewrite Mem.astack_alloc. 2: eauto.
    simpl. intros. destruct H.
    + subst. split.
      eapply Mem.alloc_result_stack; eauto.
      eapply Mem.valid_block_record_frame_1. eauto.
      eapply Mem.valid_block_push_stage_1. eauto.
      eapply Mem.valid_new_block; eauto.
    + exploit STKCIN; eauto. intros [R S].
      split. eauto.
      eapply Mem.valid_block_record_frame_1. eauto.
      eapply Mem.valid_block_push_stage_1. eauto.
      eapply Mem.valid_block_alloc; eauto.
  - unfold Mem.valid_block. apply SUPINCALL. auto.
  - intros. intro. eapply STKPERMOFS. exploit PERMNEQ.
    instantiate (1:= stkblock).
    intro. apply Mem.fresh_block_alloc in ALLOC. congruence.
    intro. apply H0. apply H.
  - unfold Mem.valid_block. apply SUPINCALL'. auto.
  - constructor.
    intros ofs k p PERM.
    apply (Mem.perm_store_2 _ _ _ _ _ _ STORELINK') in PERM.
    apply (Mem.perm_store_2 _ _ _ _ _ _ STORERA') in PERM.
    eapply Mem.perm_record_frame, Mem.perm_push_stage in PERM; eauto.
    apply STKPERMOFS' in PERM. auto.
    intros ofs k p PERM.
    apply (Mem.perm_store_1 _ _ _ _ _ _ STORELINK').
    eapply (Mem.perm_store_1 _ _ _ _ _ _ STORERA').
    erewrite <- Mem.perm_record_frame, <- Mem.perm_push_stage; eauto.
    apply STKPERMOFS'. auto.
  - erewrite Mem.support_store; eauto. erewrite Mem.support_store; eauto.
    apply Mem.astack_record_frame in RECORDFR as ARE.
    destruct ARE as (hd & tl & X & Y).
    simpl in X. inv X. rewrite Y.
    apply Mem.support_store in STORERA'. apply Mem.support_store in STORELINK'.
    apply Mem.astack_record_frame in RECORDFR' as ARE'.
    destruct ARE' as (hd' & tl' & X' & Y').
    simpl in X'. inv X'. rewrite STORELINK', STORERA', Y'.
    econstructor; eauto.
    + 
    eapply inject_stack_incr; eauto.
    erewrite Mem.astack_alloc; eauto.
    eapply inject_stack_inv with (P:= Mem.perm m); eauto.
    intros.
    destruct (eq_block b stkb).
    subst. exfalso. exploit STKCIN. apply H. intros [R S].
    apply Mem.fresh_block_alloc in ALLOC. apply ALLOC. auto.
    eapply PERMNEQ; eauto.
    +
    red. intros SUP. apply ENVSUP in SUP.
    apply Mem.alloc_result in ALLOC. subst. apply freshness in SUP. auto.
    + 
    rewrite EQ1. unfold frame_size_a. rewrite <- FRSZ. auto.
    +
    intros. etransitivity. instantiate (1:= Mem.perm m2 stkb o k p).
    erewrite <- Mem.perm_record_frame; eauto. erewrite <- Mem.perm_push_stage; eauto.
    split. intro. eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto.
    apply perm_F_any.
    eapply Mem.perm_alloc_3; eauto.
    etransitivity. split. eapply Mem.perm_store_1; eauto. eapply Mem.perm_store_2; eauto.
    split. eapply Mem.perm_store_1; eauto. eapply Mem.perm_store_2; eauto.
  - unfold rs1'. rewrite nextinstr_nf_rsp. rewrite Pregmap.gss.
    rewrite RSPINJ'. simpl.
    rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub. subst stksize stkofs aligned_sz.
    rewrite ! Ptrofs.unsigned_repr; auto. rewrite <- STKOFS'. replace (Z.max 0 sz) with sz by lia.
    f_equal. f_equal. lia.
    pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
  - red. intros b0 delta o k p JB PERM.
    apply (Mem.perm_store_2 _ _ _ _ _ _ STORELINK) in PERM.
    apply (Mem.perm_store_2 _ _ _ _ _ _ STORERA) in PERM.
    remember (Mem.push_stage m1) as m1x.
    apply (Mem.perm_record_frame _ _ _ RECORDFR) in PERM.
    symmetry in Heqm1x.
    apply (Mem.perm_push_stage _ _ Heqm1x) in PERM.
    apply (Mem.perm_alloc_inv _ _ _ _ _ ALLOC) in PERM.
    destruct eq_block.
    * subst b0. rewrite EQ1 in JB.
      inversion JB. subst delta. clear JB.
      rewrite <- STKOFS'. subst stksize' stksize aligned_sz.
      replace (Z.max 0 sz) with sz by lia. split. lia.
      unfold current_in_stack.
      erewrite Mem.support_store; eauto. erewrite Mem.support_store; eauto.
      apply Mem.astack_record_frame in RECORDFR. destruct RECORDFR as [hd [tl [X Y]]].
      simpl in X. inv X. rewrite Y. simpl. left. auto.
    * split. rewrite <- STKOFS'.
      transitivity (Ptrofs.unsigned stkofs).
      ** subst stkofs stksize. rewrite Ptrofs.unsigned_repr.
         replace (Z.max 0 sz) with sz by lia. lia.
         pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
      ** rewrite EQ2 in JB; auto.
         unfold stack_inject_lowbound in STKINJLWBD.
         subst stksize stkofs. rewrite Ptrofs.unsigned_repr.
         eapply STKINJLWBD; eauto.
         pose proof max_stacksize'_range. pose proof stack_size_pos. lia.
      ** unfold stack_inject_lowbound in STKINJLWBD.
         subst stksize stkofs.
         exploit STKINJLWBD; eauto. rewrite EQ2 in JB. eauto. auto.
         intros [A B].
         unfold current_in_stack in *.
         erewrite Mem.support_store. 2: eauto. erewrite Mem.support_store. 2: eauto.
         apply Mem.astack_record_frame in RECORDFR. destruct RECORDFR as [hd [tl [X Y]]].
         apply Mem.astack_alloc in ALLOC.
         rewrite <- Heqm1x in X.
         simpl in X. inv X. rewrite <- ALLOC in B.
         rewrite Y. simpl. right. auto.
Qed.

Lemma max_stacksize'_lt_max:
  max_stacksize' < Ptrofs.max_unsigned.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus.
  unfold Ptrofs.wordsize. unfold Wordsize_Ptrofs.wordsize.
  unfold max_stacksize'. unfold max_stacksize. unfold Mptr. destr; simpl; lia.
Qed.

Lemma cis_perm : forall b0 m delta ofs k p j astk astk',
    inject_stack j (Mem.perm m) astk astk' ->
    current_in_stack' b0 astk ->
    j b0 = Some (stkblock, delta) ->
    Mem.perm m b0 ofs k p ->
    delta >= (max_stacksize' - stack_size astk') /\
    0 <= ofs.
Proof.
  induction 1; intros.
  + edestruct INIT_INNER as (PERM & ofs' & INJ & GE'); eauto.
    rewrite H0 in INJ. inv INJ. split. lia. eapply PERM. eauto.
  + assert (ASTK:stack_size (((mk_frame b size)::nil)::astk') = frame_size_a (mk_frame b size) + stack_size astk'). simpl. lia.
    destruct (eq_block b b0).
    ++ subst. rewrite H0 in H3.
       assert (delta = max_stacksize' - stack_size astk' - frame_size_a (mk_frame b0 size)). congruence.
       rewrite H5. split. simpl. unfold frame_size_a. simpl. lia.
       apply H1 in H4. lia.
    ++ exploit IHinject_stack; eauto. destruct H2. simpl in H2. congruence. auto.
       intros [X Y]. split.
       simpl. simpl in ASTK. unfold frame_size_a in *. simpl. simpl in ASTK.
       rewrite ASTK. remember (Z.max 0 size) as sz'. assert (sz' >= 0) by lia.
       assert (align sz' 8 >= 0).
         pose proof align_le sz' 8 ltac:(lia). lia.
       lia. lia.
Qed.

Lemma ra_after_call_inj:
  forall j rs1 m1 rs2 m2 live,
    match_states j (State rs1 m1 live) (State rs2 m2 live) ->
    ra_after_call instr_size ge (rs1 RA) ->
    ra_after_call instr_size tge (rs2 RA).
Proof.
  red. intros j rs1 m1 rs2 m2 live MS (RAU & IAC). inv MS.
  generalize (RINJ RA). intro RAINJ.
  split. inv RAINJ; try congruence.
  intros b o RA2 f0 FFP.
  rewrite RA2 in RAINJ. inv RAINJ; try congruence.
  inversion GLOBINJ.
  apply Genv.find_funct_ptr_iff in FFP as FFP'. eapply defs_rev_inject in H2 as T; eauto. inv T.
  exploit functions_only_transl; eauto. intros FFP''.
  specialize (IAC _ _ (eq_sym H) _ FFP'').
  rewrite Ptrofs.add_zero. auto.
Qed.

Lemma inject_stack_app:
  forall j P a1 a2,
    inject_stack j P a1 a2 ->
    exists a1' a2',
      a1 = a1' ++ Mem.astack (injw_sup_l w) /\
      a2 = a2' ++ Mem.astack (injw_sup_r w) /\
      length a1' = length a2'.
Proof.
  induction 1. exists nil, nil. auto.
  destruct IHinject_stack as (a1' & a2' & EQ1 & EQ2 & LEN). subst.
  rewrite ! app_comm_cons. do 2 eexists. intuition. simpl. auto.
Qed.

Lemma inject_stack_init':
  forall j P a1 a2,
    inject_stack j P a1 a2 ->
    length a2 = length (Mem.astack (injw_sup_r w)) ->
    a1 = Mem.astack (injw_sup_l w) /\ a2 = Mem.astack (injw_sup_r w).
Proof.
  induction 1. split; auto.
  edestruct inject_stack_app as (a1' & a2' & EQ1 & EQ2 & LEN); eauto. subst.
  intros. exfalso. clear - H2. simpl in H2.
  rewrite app_length in H2. lia.
Qed.

Lemma inner_sp_inj:
  forall j rs1 m1 rs2 m2 live b b',
    match_states j (State rs1 m1 live) (State rs2 m2 live) ->
    Asm.inner_sp (injw_sup_l w) (rs1 RSP) = Some b -> 
    SSAsm.inner_sp (injw_sup_r w) rs2 m2 = Some b' ->
    b = b'.
Proof.
  unfold inner_sp. intros * MS EQ1 EQ2. inv MS.
  generalize (RINJ RSP). intros Hrsp'. rewrite RSPINJ' in Hrsp'.
  inv Hrsp'; simpl in *. 2: rewrite <- H0 in EQ1; simpl in EQ1; congruence.
  rewrite <- H in EQ1. simpl in EQ1. inv EQ1. inv EQ2.
  exploit RSPzero; eauto. intros. subst. rewrite Ptrofs.add_zero_l in *.
  exploit RSPblock; eauto. intros Hhd.
  unfold hd_error in Hhd. destr_in Hhd. inv Hhd.
  destr; destr; exfalso.
  - destruct RSPINJ. unfold SSAsm.init_astack, init_astack in n. congruence.
    inv Heql. congruence.
  - exploit inject_stack_init'; eauto. intros (EQ1 & EQ2).
    exploit init_stkcin_l. eauto. instantiate (1 := b1). red. rewrite <- EQ1, Heql. left. auto. tauto.
Qed.

Lemma support_free':
  forall m b x y m',
    free' m b x y = Some m' ->
    Mem.support m = Mem.support m'.
Proof.
  unfold free'. intros. destr_in H. erewrite <- Mem.support_free; eauto.
Qed.

Lemma free'_left_inject:
  forall (f : meminj) (m1 m2 : mem) (b : block) (lo hi : Z) (m1' : mem),
    Mem.inject f m1 m2 ->
    free' m1 b lo hi = Some m1' -> Mem.inject f m1' m2.
Proof.
  unfold free'. intros. destr_in H0. eapply Mem.free_left_inject; eauto.
Qed.

Lemma stk_unrelated_instr_nosup:
  forall s s' ge f i rs m,
    stk_unrelated_instr i = true ->
    Asm.exec_instr instr_size s ge f i rs m =
    Asm.exec_instr instr_size s' ge f i rs m.
Proof.
  intros * B. destruct i; simpl in B; simpl; congruence.
Qed.

Lemma asm_instr_unchange_rsp_nosup:
  forall s s' i,
    asm_instr_unchange_rsp instr_size s i ->
    asm_instr_unchange_rsp instr_size s' i.
Proof.
  unfold asm_instr_unchange_rsp. intros.
  erewrite stk_unrelated_instr_nosup in H1; eauto.
Qed.

Lemma asm_instr_unchange_sup_nosup:
  forall s s' i,
    asm_instr_unchange_sup instr_size s i ->
    asm_instr_unchange_sup instr_size s' i.
Proof.
  unfold asm_instr_unchange_sup. intros.
  erewrite stk_unrelated_instr_nosup in H1; eauto.
Qed.

Remark not_ltb_not_lt:
  forall a b,
    (a <? b = false)%nat <-> (a >= b)%nat.
Proof.
  split; intros.
  cut (~ (a < b)%nat). lia.
  red. intros. apply Nat.ltb_lt in H0. congruence.
  cut ((a <? b)%nat <> true). intros.
  destruct Nat.ltb. congruence. auto.
  red. intros. apply Nat.ltb_lt in H0. lia.
Qed.

Ltac simpl_ltb :=
  repeat match goal with
  | H: true = Nat.ltb ?a ?b |- _ => symmetry in H
  | H: false = Nat.ltb ?a ?b |- _ => symmetry in H
  | H: Nat.ltb ?a ?b = true |- _ => apply Nat.ltb_lt in H
  | H: Nat.ltb ?a ?b = false |- _ => apply not_ltb_not_lt in H
  | |- Nat.ltb ?a ?b = true => apply Nat.ltb_lt
  | |- Nat.ltb ?a ?b = false => apply not_ltb_not_lt
  end.

Lemma inner_match:
  forall j P a a',
    inject_stack j P a a' ->
    (length (Mem.astack (injw_sup_l w)) <? length a)%nat =
    (length (Mem.astack (injw_sup_r w)) <? length a')%nat.
Proof.
  intros. edestruct inject_stack_app as (a1 & a1' & EQ1 & EQ2 & LEN). eauto. subst.
  rewrite ! app_length.
  destruct Nat.ltb eqn:?;
  match goal with | |- _ = Nat.ltb ?a ?b => destruct (Nat.ltb a b) eqn:? end;
  [auto|exfalso|exfalso|auto]; simpl_ltb; lia.
Qed.

Lemma exec_instr_inject:
  forall j m m' rs rs' f i m1 rs1 live
    (EI: Asm.exec_instr instr_size (injw_sup_l w) ge f i rs m = Next' rs1 m1 live)
    (MS: match_states j (State rs m true) (State rs' m' true))
    (AINR: asm_instr_unchange_rsp instr_size (injw_sup_l w) i)
    (AINS: asm_instr_unchange_sup instr_size (injw_sup_l w) i),
  exists j' m1' rs1',
    exec_instr instr_size (injw_sup_r w) tge f i rs' m' = Next' rs1' m1' live
    /\ match_states j' (State rs1 m1 live) (State rs1' m1' live)
    /\ inject_incr j j'.
Proof.
  intros.
  destruct (stk_unrelated_instr i) eqn:NOTSTKINSTR.
  eapply asm_instr_unchange_rsp_nosup with (s' := injw_sup_r w) in AINR as AINR'.
  eapply asm_instr_unchange_sup_nosup with (s' := injw_sup_r w) in AINS as AINS'.
  (* Normal Instructions *)
  -
    inversion MS.
    edestruct exec_instr_inject_normal as (rs1' & m1' & EI' & MINJ' & RINJ'); eauto.
    exists j, m1', rs1'; split; [|split]; eauto.
    destruct i; simpl in *; eauto; try congruence.
    subst.
    generalize (asm_prog_unchange_support instr_size (injw_sup_l w) i). intro AIUS. red in AIUS.
    generalize (asm_prog_unchange_support instr_size (injw_sup_r w) i). intro AIUS'. red in AIUS'.
    edestruct (AINS NOTSTKINSTR _ _ _ _ _ _ _ EI) as (SUPEQ & STKPERMEQ).
    edestruct (AINS' NOTSTKINSTR _ _ _ _ _ _ _ EI') as (SUPEQ' & STKPERMEQ').
    eapply match_states_intro; eauto.
     + rewrite (AINR _ _ _ _ _ _ _ NOTSTKINSTR EI) in RSPzero. auto.
     + rewrite (AINR _ _ _ _ _ _ _ NOTSTKINSTR EI) in RSPblock. rewrite <- SUPEQ. auto.
     + rewrite <- SUPEQ. auto.
     + unfold current_in_stack in *. rewrite <- SUPEQ. auto.
     + unfold stkcin, current_in_stack in *. rewrite <- SUPEQ. auto.
     + apply AIUS in EI.
       unfold Mem.valid_block. apply EI. auto.
     + intros. intro. eapply STKPERMOFS. eapply STKPERMEQ; eauto.
     + apply AIUS' in EI'.
       unfold Mem.valid_block. apply EI'. auto.
     + constructor.
       ++ intros ofs k p PERM.
          apply STKPERMEQ' in PERM.
          apply STKPERMOFS' in PERM. auto.
       ++ intros ofs k p OFS.
          apply STKPERMEQ'.
          apply STKPERMOFS'. auto.
     + rewrite <- SUPEQ, <- SUPEQ'.
       eapply inject_stack_inv with (P:= Mem.perm m); eauto.
     + rewrite (AINR' _ _ _ _ _ _ _ NOTSTKINSTR EI') in RSPINJ'. congruence.
     + red. intros. apply STKPERMEQ in H0.
       exploit STKINJLWBD; eauto. intros (X & Y).
       split.
       rewrite <- SUPEQ'. auto.
       unfold current_in_stack in *. rewrite <- SUPEQ. auto.
  (* Specail Cases *)
  - destruct i; simpl in *; try congruence.
    (* Pcall_s *)
    + destr_in EI. inv EI. inv MS.
      exploit functions_translated.
        3:eauto. eauto. eapply symbol_address_inject. auto.
      intros FF'. rewrite FF'.
      do 4 eexists. split. eauto. split. econstructor; eauto.
      * intros. apply val_inject_set.
        intros. apply val_inject_set. auto.
        apply Val.offset_ptr_inject. auto.
        eapply symbol_address_inject. auto.
      * red. auto.
    (* Pcall_r *)
    + destr_in EI. inv EI. inv MS. generalize (RINJ r).
      exploit functions_translated. 3:eauto. all:eauto. intros FF'. rewrite FF'.
      unfold Genv.find_funct in Heqo.
      destr_in Heqo. inversion 1. subst. simpl. destr_in Heqo. inv e.
      inversion GLOBINJ. apply Genv.find_funct_ptr_iff in Heqo as H4.
      eapply defs_inject in H4 as [ ]; eauto. subst.
      do 4 eexists. split. eauto. split. econstructor; eauto.
      * intros. apply val_inject_set. auto.
        intros. apply val_inject_set. auto.
        apply Val.offset_ptr_inject. auto.
        eauto.
      * red. auto.
    (* Pret *)
    + destr_in EI. exploit inner_sp_inj; unfold inner_sp; eauto. intros. subst b.
      do 2 destr_in EI.
      * inv EI.
        exploit ra_after_call_inj; eauto. intro.
        inv MS. rewrite (pred_dec_true (check_ra_after_call _ _ _)) by auto.
        remember (if Nat.eq_dec _ _ then false else true) as inner eqn:INNER.
        replace (if inner then _ else _)
        with (Next' (rs' # PC <- (rs' RA)) # RA <- Vundef m' inner) by destr.
        do 4 eexists. split. eauto. split. econstructor; eauto.
        -- intros. apply val_inject_set. apply val_inject_set; auto.
           intros. auto.
        -- red. auto.
      * inv MS.
        do 4 eexists. split. eauto. split. econstructor; eauto.
        -- intros. apply val_inject_set. apply val_inject_set; auto.
           intros. auto.
        -- red. auto.
    (* Pallocframe *)
    + repeat destr_in EI.
      inversion MS. subst.
      edestruct allocframe_inject as (j' & INCR & m1' & RECORDFR & m2' & STORERA & m3' & STORELINK & MS') ; eauto.
      lia.
      apply Ptrofs.unsigned_range_2.
      apply Ptrofs.unsigned_range_2.
      rewrite Ptrofs.repr_unsigned in STORERA.
      rewrite Ptrofs.add_zero_l in STORERA.
      rewrite Ptrofs.repr_unsigned in STORELINK.
      rewrite Ptrofs.add_zero_l in STORELINK.
      unfold Mem.storev in STORERA. destr_in STORERA.
      unfold Val.offset_ptr in Heqv0. destr_in Heqv0. inv Heqv0.
      destr_in Heqv1. inv Heqv1.
      eexists j',_,_; split; eauto.
      rewrite RECORDFR.
      unfold Val.offset_ptr. simpl. rewrite STORERA.
      unfold Val.offset_ptr in STORELINK. simpl in STORELINK.
      rewrite STORELINK. auto.
    (* Pfreeframe *)
    + repeat destr_in EI.
      rename Heqv1 into RSRSP.
      rename Heqo into LOADRA.
      rename Heqo0 into LOADLINK.
      rename Heqo1 into FREE.
      rename Heqo2 into POP.
      rename Heqb0 into INNER.
      rename Heqb1 into CTF.
      rename e0 into RSPTOP.
      inv MS.
      clear NOTSTKINSTR.
      rename v into val_ra. unfold loadvv in LOADRA. destr_in LOADRA.
      exploit Mem.loadv_inject. apply MINJ. apply Heqo.
      apply Val.offset_ptr_inject. rewrite <- RSRSP. auto.
      intros (val_ra' & LOADRA' & INJRA).
      assert (v = val_ra). destr_in LOADRA. subst.
      assert (RA':val_ra' <> Vundef). destruct val_ra; inv INJRA; try congruence.
      erewrite loadv_loadvv; eauto.
      apply support_free' in FREE as SF.
      edestruct Mem.nonempty_pop_stage as (m2 & ?). rewrite SF. eapply Mem.pop_stage_nonempty. eauto.
      assert (NONEMPTY: Mem.astack (Mem.support m') <> nil).
        clear - RSPINJ. induction RSPINJ; congruence.
      exploit free'_left_inject. 2:eauto. eauto. intros FREEINJ.
      edestruct Mem.pop_stage_parallel_inject as (m'' & POP' & POPINJ); eauto. rewrite POP'.
      erewrite <- inner_match; eauto. rewrite INNER.
      exploit Mem.loadv_inject. apply MINJ. apply LOADLINK.
      apply Val.offset_ptr_inject. rewrite <- RSRSP. auto.
      intros (val_link' & LOADLINK' & INJLINK).
      exists j. do 2 eexists. split; [|split]; eauto.
      apply Mem.astack_pop_stage in POP as POPASTK.
      destruct POPASTK as [top ASP].
      unfold check_topframe in CTF.
      repeat destr_in CTF. rewrite SF in Heqs. rewrite ASP in Heqs.
      inv Heqs.
      assert (max_stacksize' - (stack_size ((f0::nil)::Mem.astack (Mem.support m1))) =
              max_stacksize' - frame_size_a f0 - stack_size (Mem.astack (Mem.support m1))).
      assert (stack_size ((f0::nil)::Mem.astack(Mem.support m1)) = frame_size_a f0 + stack_size (Mem.astack (Mem.support m1))). simpl. lia. rewrite H. lia.
      constructor; eauto.
      (* Memory Injection *)
      * apply Mem.sup_include_pop_stage in POP.
        unfold free' in FREE. destr_in FREE.
        apply Mem.support_free in FREE.
        rewrite <- FREE in ENVSUP.
        eapply Mem.sup_include_trans. apply ENVSUP. eauto.
        inv FREE.
        eapply Mem.sup_include_trans. apply ENVSUP. eauto.
      * apply Mem.sup_include_pop_stage in POP'.
        eapply Mem.sup_include_trans. apply ENVSUP'. auto.
      * rewrite nextinstr_rsp. intros.
        rewrite Pregmap.gso in H0.
        rewrite Pregmap.gss in H0.
        unfold parent_sp_stack in H0. repeat destr_in H0.
        destr_in H2.
        congruence.
      * rewrite nextinstr_rsp. intros.
        rewrite Pregmap.gso in H0.
        rewrite Pregmap.gss in H0.
        unfold parent_sp_stack in H0. repeat destr_in H0.
        destr_in H2. inv H2. auto. congruence.
      (* Regset Injection *)
      * intros; apply val_inject_nextinstr.
        intros; apply val_inject_set; auto.
        intros; apply val_inject_set; auto.
        inv RSPINJ; simpl. rewrite <- ASP in *.
          clear - INNER H1. unfold init_astack in H1. rewrite H1, Nat.ltb_lt in INNER. lia.
        assert (FSZ:0 <= frame_size_a (mk_frame b0 size) <= Ptrofs.max_unsigned).
          split. generalize frame_size_a_pos (mk_frame b0 size). intro. auto.
          unfold frame_size_a. simpl.
          simpl in STKLIMIT. unfold frame_size_a in STKLIMIT. simpl in STKLIMIT.
          pose proof max_stacksize_range. pose proof stack_size_pos (Mem.astack (Mem.support m1)). clear - STKLIMIT H0 H1. lia.
        inv IS_REC.
        -- rewrite INIT_PARENT_L. unfold parent_sp_stack. simpl.
           rewrite RSPINJ'. simpl. eauto.
           (* econstructor. eauto.
           rewrite Ptrofs.add_unsigned.
           rewrite <- H2. rewrite ! Ptrofs.unsigned_repr. rewrite Ptrofs.add_zero_l.
           simpl.
           apply f_equal. unfold frame_size_a. simpl. lia. auto.
           split. admit.
           pose proof max_stacksize'_range. pose proof stack_size_pos ((mk_frame stkblock size :: nil) :: Mem.astack (injw_sup_r w)). lia. *)
        -- unfold parent_sp_stack. rewrite RSPINJ'. simpl.
           econstructor. eauto.
           rewrite Ptrofs.add_unsigned. rewrite ! Ptrofs.unsigned_repr, Ptrofs.add_zero_l.
           rewrite <- H2. simpl.
           apply f_equal. unfold frame_size_a. simpl. lia. auto.
           admit.
      * assert ((stack_size ((f0::nil):: Mem.astack(Mem.support m1))) =
            (frame_size_a f0 + stack_size (Mem.astack(Mem.support m1)))). simpl. lia.
        setoid_rewrite H0 in STKLIMIT.
        generalize (frame_size_a_pos f0). lia.
      * inv STKNOREPET. auto.
      * inv RSPINJ.
          rewrite <- ASP in *. clear - INNER H1. unfold init_astack in H1. rewrite H1, Nat.ltb_lt in INNER. lia.
        unfold stkcin, current_in_stack. intros.
        unfold stkcin, current_in_stack in STKCIN. rewrite SF, ASP in STKCIN.
        exploit STKCIN. right. apply H0. intros [R S].
        split. auto.
        eapply Mem.support_pop_stage_1 in POP. apply POP. auto.
      * eapply Mem.support_pop_stage_1 in POP. apply POP.
        unfold free' in FREE. destr_in FREE.
        erewrite Mem.support_free. 2: eauto. auto.
        inv FREE. auto.
      * intros. erewrite <- Mem.perm_pop_stage. 2: eauto.
        intro. eapply STKPERMOFS.
        unfold free' in FREE. destr_in FREE.
        eapply Mem.perm_free_3; eauto.
        inv FREE. auto.
      * red. erewrite <- Mem.support_pop_stage_1; eauto.
      * inv STKPERMOFS'. constructor; intros; erewrite <- Mem.perm_pop_stage in *; eauto.
      * inv RSPINJ.
          rewrite <- ASP in *. clear - INNER H1. unfold init_astack in H1. rewrite H1, Nat.ltb_lt in INNER. lia.
        apply Mem.astack_pop_stage in POP' as (hd' & POP'). rewrite POP' in H2. inv H2.
        eapply inject_stack_inv; eauto.
        {(*cin_perm*)
          intros. unfold top_sp_stack in RSPTOP. simpl in RSPTOP. inv RSPTOP.
          assert (b0 <> b1). intro. subst. inv STKNOREPET. apply H5. auto.
          transitivity (Mem.perm m0 b1 o k p).
          unfold free' in FREE. destr_in FREE.
          split. intro. eapply Mem.perm_free_1; eauto.
          eapply Mem.perm_free_3; eauto.
          erewrite Mem.perm_pop_stage; eauto. reflexivity.
        }
      (* Stack Injection *)
      * rewrite nextinstr_rsp.
        rewrite Pregmap.gso by congruence.
        rewrite Pregmap.gss.
        rewrite RSPINJ'. simpl. f_equal.
        edestruct Mem.astack_pop_stage as [hd EQ]. exact POP'.
        inv RSPINJ.
        rewrite INIT_PARENT_R. rewrite H2, EQ in INIT_PARENT_R. inv INIT_PARENT_R. simpl.
        rewrite H1 in INIT_PARENT_L. inv INIT_PARENT_L.
        rewrite EQ in H2. inv H2. simpl. unfold frame_size_a. simpl. admit.
        (* setoid_rewrite H in STKINJLWBD. setoid_rewrite H in X.
        exists (Ptrofs.repr((Ptrofs.unsigned offset) + frame_size_a f0)).
        split.
        ++
        rewrite Ptrofs.unsigned_repr. lia.
        split. generalize (Ptrofs.unsigned_range offset).
        intro. generalize (frame_size_a_pos f0). intro. lia.
        rewrite X. generalize (stack_size_pos (Mem.astack (Mem.support m1))). intro.
        generalize max_stacksize'_lt_max. intro. lia.
        ++ rewrite Y.
        unfold Mem.loadv in LOADRA'. destr_in LOADRA'.
        unfold Val.offset_ptr in Heqv. destr_in Heqv. inv Heqv.
        simpl.
        unfold Ptrofs.add.
        rewrite (Ptrofs.unsigned_repr (align (frame_size f0) 8)). reflexivity.
        split. apply frame_size_a_pos.
        generalize (Ptrofs.unsigned_range_2 offset). intro.
        rewrite X in H0. generalize (stack_size_pos (Mem.astack (Mem.support m1))). intro.
        generalize max_stacksize'_lt_max. intro. unfold frame_size_a in *. lia. *)
      * unfold stack_inject_lowbound in STKINJLWBD.
        intro. intros.
        generalize (RINJ RSP). intro.
        apply RSPzero in RSRSP as Z. subst.
        rewrite RSRSP in H2. inv H2.
        inv RSPINJ.
          rewrite <- ASP in *. clear - INNER H3. unfold init_astack in H3. rewrite H3, Nat.ltb_lt in INNER. lia.
        unfold top_sp_stack in RSPTOP. simpl in RSPTOP. inv RSPTOP.
        erewrite <- Mem.perm_pop_stage in H1; eauto.
        assert (H9: Mem.perm m b0 ofs k p). {
          unfold free' in FREE. destr_in FREE.
          eapply Mem.perm_free_3; eauto.
        }
        rename b1 into b.
        destruct (eq_block b0 b).
        ++ subst b0. rewrite H0 in H6. inv H6.
           apply H8 in H9 as H10.
           unfold free' in FREE. destr_in FREE.
           exploit Mem.perm_free_2; eauto. simpl. rewrite Ptrofs.unsigned_zero. lia.
           intro. inv H2.
           rewrite Ptrofs.unsigned_zero in g. simpl in *. lia.
        ++ exploit STKINJLWBD. apply H0. eauto.
           intros [SIZE CIN].
           assert (current_in_stack b0 m1).
           { unfold current_in_stack in *.
             rewrite SF, ASP in CIN. destruct CIN. simpl in H2. congruence.
             auto. }
           split. 2: auto.
           exploit cis_perm; eauto. intros [R S].
           edestruct Mem.astack_pop_stage as [hd EQ]. exact POP'.
           rewrite EQ in H4. inv H4. lia.
Admitted.

(* injection in builtin *)
Lemma eval_builtin_arg_inject:
  forall (rs:regset) sp m j (rs':regset) sp' m' a v
    (SPINJ: Val.inject j sp sp')
    (RINJ: forall r, Val.inject j rs#r rs'#r)
    (MINJ: Mem.inject j m m')
    (GLOBINJ: meminj_preserves_globals j),
    eval_builtin_arg ge (fun r => rs#r) sp m a v ->
    exists v', eval_builtin_arg tge (fun r => rs'#r) sp' m' a v' /\ Val.inject j v v'.
Proof.
  intros until 4.
  induction 1.
- exists (rs'#x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto. apply Val.offset_ptr_inject. eauto.
  intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; split; eauto with barg.
  apply Val.offset_ptr_inject; eauto.
- assert (Val.inject j (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs)).
  { unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
    exploit symbol_inject; eauto. intros.
    eapply Genv.find_symbol_transf in FS as (b' & INJ & FS'). 2:apply GLOBINJ.
    rewrite FS'.
    instantiate (1 := prog) in FS'.
    econstructor; eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge id) as [b|] eqn:FS; auto.
  exploit symbol_inject; eauto. intros.
  eapply Genv.find_symbol_transf in FS as (b' & INJ & FS'). 2:apply GLOBINJ.
  rewrite FS'.
  instantiate (1 := prog) in FS'.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  exists (Val.longofwords v1' v2'); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); eauto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); eauto using in_or_app.
  econstructor; split; eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma eval_builtin_args_inject:
  forall (rs:regset) sp m j (rs':regset) sp' m' al vl
    (SPINJ: Val.inject j sp sp')
    (RINJ: forall r, Val.inject j rs#r rs'#r)
    (MINJ: Mem.inject j m m')
    (GLOBINJ: meminj_preserves_globals j),
    eval_builtin_args ge rs sp m al vl ->
    exists vl', eval_builtin_args tge rs' sp' m' al vl' /\  Val.inject_list j vl vl'.
Proof.
  intros until 4.
  induction 1; intros.
- exists (@nil val); split; constructor.
- exploit eval_builtin_arg_inject; eauto using in_or_app. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D); eauto using in_or_app.
  exists (v1' :: vl'); split; constructor; auto.
Qed.

(** injection in extcall *)
Lemma extcall_arg_inject:
  forall j rs1 m1 arg1 loc rs2 m2,
    extcall_arg rs1 m1 loc arg1 ->
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    Mem.inject j m1 m2 ->
    exists arg2,
      extcall_arg rs2 m2 loc arg2 /\
      Val.inject j arg1 arg2.
Proof.
  destruct 1; simpl; intros.
  eexists; split; try econstructor; eauto.
  exploit Mem.loadv_inject; eauto.
  apply Val.offset_ptr_inject; eauto.
  intros (v2 & LOAD & INJ).
  eexists; split; try econstructor; eauto.
Qed.

Lemma extcall_arg_pair_inject:
  forall j rs1 m1 arg1 ty rs2 m2,
    extcall_arg_pair rs1 m1 ty arg1 ->
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    Mem.inject j m1 m2 ->
    exists arg2,
      extcall_arg_pair rs2 m2 ty arg2 /\
      Val.inject j arg1 arg2.
Proof.
  destruct 1; simpl; intros.
  eapply extcall_arg_inject in H; eauto.
  destruct H as (arg2 & EA & INJ);
    eexists; split; try econstructor; eauto.
  eapply extcall_arg_inject in H; eauto.
  destruct H as (arg2 & EA & INJ).
  eapply extcall_arg_inject in H0; eauto.
  destruct H0 as (arg3 & EA1 & INJ1).
  eexists; split; try econstructor; eauto.
  apply Val.longofwords_inject; eauto.
Qed.

Lemma extcall_arguments_inject:
  forall j rs1 m1 args1 sg rs2 m2,
    extcall_arguments rs1 m1 sg args1 ->
    (forall r, Val.inject j (rs1 r) (rs2 r)) ->
    Mem.inject j m1 m2 ->
    exists args2,
      extcall_arguments rs2 m2 sg args2 /\
      Val.inject_list j args1 args2.
Proof.
  unfold extcall_arguments.
  intros j rs1 m1 args1 sg rs2 m2.
  revert args1. generalize (Conventions1.loc_arguments sg).
  induction 1; simpl; intros; eauto.
  exists nil; split; try econstructor.
  eapply extcall_arg_pair_inject in H; eauto.
  decompose [ex and] H.
  edestruct IHlist_forall2 as (a2 & EA & INJ); eauto.
  eexists; split; econstructor; eauto.
Qed.

(** Step Simulation *)
Theorem step_simulation:
  forall S1 t S2,
    Asm.step instr_size (injw_sup_l w) ge S1 t S2 ->
    forall j S1' (MS: match_states j S1 S1'),
    exists j' S2',
      step instr_size (injw_sup_r w) tge S1' t S2' /\
      match_states j' S2 S2'.
Proof.
  destruct 1; intros; inversion MS; subst.
  - (* internal step *)
    generalize (RINJ PC); rewrite H. inversion 1; subst.
    exploit (globinj_to_funinj j GLOBINJ); eauto. intros [ ]. subst.
    assert (asm_instr_unchange_rsp instr_size (injw_sup_l w) i).
    {
      eapply prog_unchange_rsp_l; eauto.
    }
    destruct (exec_instr_inject _ _ _ _ _ _ _ _ _ _ EXEC MS H1 (asm_prog_unchange_sup instr_size (injw_sup_l w) i)) as (j' & rs2' & m2' & EI' & MS' & INCR).
    do 2 eexists; split.
    eapply exec_step_internal; eauto.
    eapply functions_transl; eauto.
    rewrite Ptrofs.add_zero. eauto.
    eauto.
  - (* builtin step *)
    edestruct (eval_builtin_args_inject) as (vargs' & Hargs & Hargsinj); eauto.
    edestruct (external_call_mem_inject_gen' ef)
      as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & STKEQ & STKEQ0 & INCR & GLOB & SEP); try eauto. apply globals_symbols_inject. eauto.
    generalize (RINJ PC); rewrite H. inversion 1; subst.
    exploit (globinj_to_funinj j GLOBINJ); eauto. intros [ ]. subst.
    do 2 eexists; split.
    eapply exec_step_builtin; eauto.
    eapply functions_transl; eauto.
    rewrite Ptrofs.add_zero; eauto.
    generalize (Mem.unchanged_on_support (loc_unmapped j) m m' Unch1).
    intro SUPINCMEM.
    generalize (Mem.unchanged_on_support (loc_out_of_reach j m) m'0 m2' Unch2).
    intro SUPINCMEM1.
    econstructor; eauto.
    (* Memory Injection *)
    + constructor.
      ++ eapply Genv.match_stbls_incr; eauto. apply GLOBINJ. intros.
         exploit GLOB; eauto. unfold is_stack. intros [STK STK']. destr_in STK. destr_in STK'. clear.
         split; intros SUP; apply Genv.genv_sup_glob in SUP as [ ]; congruence.
      ++ inv GLOBINJ. eapply meminj_global_incr; eauto.
    + remember (nextinstr_nf  (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                  (set_res res vres (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs))) as rs'.
      destruct prog_unchange_rsp_l as (INT & BUILTIN & EXTCALL).
      red in BUILTIN.
      destruct (BUILTIN b (Ptrofs.unsigned ofs) f ef args res rs m vargs t vres rs' m'); eauto.
    + remember (nextinstr_nf  (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                  (set_res res vres (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs))) as rs'.
      destruct prog_unchange_rsp_l as (INT & BUILTIN & EXTCALL).
      red in BUILTIN.
      rewrite <- STKEQ.
      destruct (BUILTIN b (Ptrofs.unsigned ofs) f ef args res rs m vargs t vres rs' m'); eauto.
    (* Regset Injection *)
    + intros. apply val_inject_nextinstr_nf.
      apply val_inject_set_res; auto.
      apply val_inject_undef_regs; auto.
      intros; eapply val_inject_incr; eauto.
    (* Stack Injection *)
    + erewrite <- external_call_astack; eauto.
    + erewrite <- external_call_astack; eauto.
    + red. unfold current_in_stack in *. erewrite <- external_call_astack; eauto.
      intros. exploit STKCIN; eauto. intros [A B]. split. auto. apply SUPINCMEM.
      auto.
    + unfold Mem.valid_block. apply SUPINCMEM. auto.
    + intros. exploit external_perm_stack. apply CALL. instantiate (1:= stkblock).
      simpl. auto. auto. intro. intro. eapply STKPERMOFS. apply H2,H3.
    + unfold Mem.valid_block. apply SUPINCMEM1. auto.
    + inv STKPERMOFS'. constructor.
      ++ intros ofs0 k p PERM. eapply stack_perm_offset0.
         exploit external_perm_stack. apply EC. instantiate (1:= stkblock). eauto.
         simpl. auto. auto. intro. eapply H2. eauto.
      ++ intros. exploit stack_offset_perm0; eauto.
         intro. exploit external_perm_stack; eauto.
         simpl. auto. intro. apply H6,H3.
    + eapply inject_stack_incr; eauto. erewrite <- external_call_astack; eauto. rewrite <- STKEQ0.
      eapply inject_stack_inv; eauto. intros. symmetry.
      exploit STKCIN; eauto. intros [A B].
      eapply external_perm_stack; eauto.
    + remember (nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
                  (set_res res vres' (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs'0))) as rs'.
      destruct prog_unchange_rsp_r as (INT & BUILTIN & EXTCALL).
      red in BUILTIN.
      destruct (BUILTIN b (Ptrofs.unsigned ofs) f ef args res rs'0 m'0 vargs' t vres' rs' m2'); eauto.
      eapply functions_transl; eauto.
      rewrite <- STKEQ0. auto.
    + red. intros b0 delta o k p JB1' PERM.
      assert (JB1: j b0 = Some (stkblock, delta)).
      {
        destruct (j b0) eqn:JB1. destruct p0.
        - apply INCR in JB1. rewrite JB1 in JB1'. auto.
        - exploit SEP. apply JB1. apply JB1'.
          intros (NVB1 & NVB2). congruence.
      }
      rewrite <- STKEQ0.
      red in STKINJLWBD. unfold current_in_stack in *.
      rewrite <- STKEQ.
      eapply STKINJLWBD.
      red in INCR.
      apply JB1.
      eapply Mem.perm_max in PERM.
      eapply external_call_max_perm; eauto.
      eapply Mem.valid_block_inject_1; eauto.
  - (* external call *)
    remember (Ptrofs.repr (max_stacksize' - stack_size (Mem.astack (Mem.support m'0)))) as offset eqn:X.
    edestruct (Mem.valid_access_store m'0 Mptr stkblock (Ptrofs.unsigned (Ptrofs.add (offset)
              (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr)))))) as (m'2 & STORERA).
    {
      red. repeat apply conj.
      red; intros. apply STKPERMOFS'.
      split. generalize (Ptrofs.unsigned_range (Ptrofs.add offset (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))); lia. eapply Z.lt_le_trans. apply H2.
      rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub.
      rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)).
      2: vm_compute; intuition congruence.
      rewrite Ptrofs.unsigned_repr. rewrite X. generalize (stack_size_pos (Mem.astack (Mem.support m'0))). rewrite Ptrofs.unsigned_repr. lia.
      admit. admit.
      rewrite X.
      generalize (stack_size_pos (Mem.astack (Mem.support m))).
      generalize (size_chunk_pos Mptr).
      generalize (max_stacksize_range).
      generalize (Ptrofs.unsigned_range offset). rewrite X.
      intros. split. 2: generalize max_stacksize'_range; lia.
      generalize (align_le (size_chunk Mptr) 8). unfold max_stacksize' in *.
      lia.
      unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr_eq.
      rewrite X. apply mod_divides. vm_compute. congruence. rewrite Ptrofs.modulus_power.
        transitivity 8.
        unfold Mptr; unfold align_chunk. destruct Archi.ptr64; simpl.
        exists 1; lia. exists 2; lia.
        exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal.
        vm_compute. congruence. lia.
        apply Z.divide_add_r.
        apply Z.divide_sub_r.
        transitivity 8.
        unfold Mptr; unfold align_chunk. destruct Archi.ptr64; simpl.
        exists 1; lia. exists 2; lia.
        apply Z.divide_add_r.
        apply max_stacksize_aligned.
        apply align_divides. lia.
        transitivity 8.
        unfold Mptr; unfold align_chunk. destruct Archi.ptr64; simpl.
        exists 1; lia. exists 2; lia.
        apply stack_size_aligned.
        unfold Ptrofs.neg. rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)) by (vm_compute; intuition congruence).
        rewrite Ptrofs.unsigned_repr_eq.
        apply mod_divides. vm_compute; congruence.
        rewrite Ptrofs.modulus_power.
        transitivity 8.
        unfold Mptr; unfold align_chunk. destruct Archi.ptr64; simpl.
        exists 1; lia. exists 2; lia.
        exists (two_p (Ptrofs.zwordsize - 3)). change 8 with (two_p 3). rewrite <- two_p_is_exp. f_equal.
        vm_compute. congruence. lia.
        rewrite Z.divide_opp_r.
        apply align_size_chunk_divides.
    }
      exploit Mem.store_outside_inject. apply MINJ. 2: apply STORERA.
      {
        intros b' delta ofs' JB' PERM RNG.
        red in STKINJLWBD.
        generalize (STKINJLWBD _ _ _ _ _ JB' PERM). intros (A & B).
        destruct RNG as (RNG1 & RNG2).
        revert RNG2.
        rewrite <- Ptrofs.sub_add_opp. unfold Ptrofs.sub.
        rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)).
        2: vm_compute; intuition congruence.
        rewrite Ptrofs.unsigned_repr.
        intros; lia.
        erewrite X.
        generalize (stack_size_pos (Mem.astack(Mem.support m))).
        generalize (size_chunk_pos Mptr).
        generalize (max_stacksize_range).
        intros. split. 2: generalize (max_stacksize'_range); lia.
        generalize (align_le (size_chunk Mptr) 8). unfold max_stacksize' in *. lia.
      }
      intro StoreInj.
    edestruct (extcall_arguments_inject) as (vargs' & Hargs & Hargsinj). eauto. eauto. eapply StoreInj.
    edestruct (external_call_mem_inject_gen' ef) as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & STKEQ & STKEQ0 & INCR & GLOB & SEP); try eauto. apply globals_symbols_inject. eauto.
    generalize (RINJ PC); rewrite H.
    intro VINJ; inv VINJ. rename H5 into JB2. rename H4 into EQofs.
    exploit (globinj_to_funinj j GLOBINJ); eauto. intros [ ]. subst.
    do 2 eexists; split.
    eapply exec_step_external; eauto. rewrite Y. simpl. eauto.
    rewrite Y. apply Val.Vptr_has_type.
    generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence; easy.
    congruence.
    generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence; easy.
    unfold inner_sp. eauto.
    exploit inner_sp_inj; eauto. unfold inner_sp. eauto. intros Heqlive LIVE. subst.
    rewrite LIVE in ISP. trim H1. auto.
    eapply ra_after_call_inj; eauto.
    generalize (Mem.unchanged_on_support (loc_unmapped j) m m' Unch1).
    intro SUPINCMEM.
    generalize (Mem.unchanged_on_support (loc_out_of_reach j m) m'2 m2' Unch2).
    intro SUPINCMEM1.
    apply Mem.support_store in STORERA as SUP.
    exploit inner_sp_inj; eauto. unfold inner_sp. eauto. intros Heqlive. rewrite <- Heqlive.
    econstructor; eauto.
    (* Memory Injection *)
    + constructor.
      ++ eapply Genv.match_stbls_incr; eauto. apply GLOBINJ. intros.
         exploit GLOB; eauto. unfold is_stack. intros [STK STK']. destr_in STK. destr_in STK'. clear.
         split; intros SUP; apply Genv.genv_sup_glob in SUP as [ ]; congruence.
      ++ inv GLOBINJ. eapply meminj_global_incr; eauto.
    + eapply Mem.sup_include_trans. apply ENVSUP'. rewrite <- SUP. auto.
    (* Regset Injection *)
    + remember (((set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) # PC <- (rs RA)) # RA <- Vundef) as rs'.
      destruct prog_unchange_rsp as (INT & BUILTIN & EXTCALL).
      red in EXTCALL.
      destruct (EXTCALL b ef args res rs m t rs' m'); eauto.
    + remember (((set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) # PC <- (rs RA)) # RA <- Vundef) as rs'.
      destruct prog_unchange_rsp as (INT & BUILTIN & EXTCALL).
      red in EXTCALL.
      rewrite <- STKEQ.
      destruct (EXTCALL b ef args res rs m t rs' m'); eauto.
    + intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set_pair; auto.
      apply val_inject_undef_caller_save_regs; auto.
      intros; eapply val_inject_incr; eauto.
      intros; eapply val_inject_incr; eauto.
    (* Stack Injection *)
    + erewrite <- external_call_astack; eauto.
    + erewrite <- external_call_astack; eauto.
    + unfold current_in_stack in *. erewrite <- external_call_astack; eauto.
      intros. exploit STKCIN; eauto. intros [A B]. split. auto.
      apply SUPINCMEM. auto.
    + unfold Mem.valid_block. apply SUPINCMEM. auto.
    + intros. exploit external_perm_stack. apply CALL. instantiate (1:= stkblock).
      simpl. auto. auto. intro. intro. eapply STKPERMOFS. apply H2,H3.
    + unfold Mem.valid_block. apply SUPINCMEM1. rewrite SUP. auto.
    + inv STKPERMOFS'. constructor.
      ++ intros ofs0 k p PERM.
         eapply stack_perm_offset0. eapply Mem.perm_store_2; eauto.
      unfold Mem.valid_block in STKVB'. rewrite <- SUP in STKVB'.
         exploit external_perm_stack; eauto.
         unfold stkblock. simpl. auto.
         intro. eapply H2. eauto.
      ++ intros. exploit stack_offset_perm0; eauto.
         intro. eapply Mem.perm_store_1 in H3.  2: eauto.
         unfold Mem.valid_block in STKVB'. rewrite <- SUP in STKVB'.
         exploit external_perm_stack; eauto.
         unfold stkblock. simpl. auto.
         intro. apply H4,H3.
    + eapply inject_stack_incr; eauto.
      erewrite <- external_call_astack; eauto.
      rewrite <- STKEQ0, SUP.
      eapply inject_stack_inv; eauto. intros. symmetry.
      exploit STKCIN; eauto. intros [A B].
      eapply external_perm_stack; eauto.
    + remember (((set_pair (loc_external_result (ef_sig ef)) vres'
     (undef_caller_save_regs rs'0)) # PC <- (rs'0 RA))# RA <- Vundef) as rs'.
      destruct prog_unchange_rsp as (INT & BUILTIN & EXTCALL).
      red in EXTCALL.
      destruct (EXTCALL b ef vargs' vres' rs'0 m'2 t rs' m2'); eauto.
      rewrite <- STKEQ. eauto.
    + red. intros b0 delta o k p JB1' PERM.
      assert (JB1: j b0 = Some (stkblock, delta)).
      {
        destruct (j b0) eqn:JB1. destruct p0.
        - apply INCR in JB1. rewrite JB1 in JB1'. auto.
        - exploit SEP. apply JB1. apply JB1'.
          intros (NVB1 & NVB2). unfold Mem.valid_block in *. rewrite SUP in NVB2. congruence.
      }
      rewrite <- STKEQ.
      red in STKINJLWBD.  unfold current_in_stack in *.
      erewrite <- (external_call_astack _ _ _ _ _ _ _ CALL); eauto.
      eapply STKINJLWBD.
      red in INCR.
      apply JB1.
      eapply Mem.perm_max in PERM.
      eapply external_call_max_perm; eauto.
      eapply Mem.valid_block_inject_1; eauto.
Qed.

End WITH_WORLD.

Let cc : callconv li_asm li_asm := cc_ssasm inj.

Lemma transf_initial_states:
  forall j s1 s2 q1 q2 st1, match_query cc (injw j s1 s2) q1 q2 -> Asm.initial_state ge q1 st1 ->
  Genv.match_stbls j se se ->
  exists st2, SSAsm.initial_state ge q2 st2 /\ match_states s1 j st1 st2.
Proof.
  intros * MQ INIT GE. inv MQ. inv MEM. inv INIT. simpl in *.
  econstructor; split.

  econstructor; eauto.
  pose proof RSINJ Asm.PC.
  unfold Genv.find_funct, Genv.find_funct_ptr in *. do 4 destr_in H2.
  inv H0; try congruence.
  apply Genv.genv_defs_range in Heqo as SUP. apply Genv.genv_sup_glob in SUP as (id & ?). subst b.
  exploit INJG. eauto. intros [ ]. subst. rewrite Heqo, Ptrofs.add_zero.
  destr. inv H2. eauto.
  pose proof RSINJ RSP. inv H0; try congruence.
  pose proof RSINJ RA. inv H0; try congruence.

  constructor; eauto.

- constructor; auto.
-

Lemma transf_initial_states:
  forall st1, Asm.initial_state prog st1 ->
  exists j st2, SSAsm.initial_state prog st2 /\ match_states j st1 st2.
Proof.
  inversion 1. subst.
  rename H into INIT.
  rename H0 into INITMEM.
  exploit Genv.initmem_inject; eauto. intro FLATINJ.
  caseEq (Mem.alloc m0 0 max_stacksize'). intros.
  exploit Genv.init_mem_genv_sup; eauto. intro SUP. fold ge in SUP.
  exploit Genv.init_mem_stack; eauto. intro STK.
  exploit Mem.stack_alloc; eauto. intro STK1. rewrite STK in STK1. simpl in STK1.
  exploit Mem.stack_alloc. apply H1. intro STK2. rewrite STK in STK2. simpl in STK2.
  apply Genv.init_mem_astack in INITMEM as ASTK.
  apply Mem.astack_alloc in H1 as ASTK2. rewrite ASTK in ASTK2.
  apply Mem.astack_alloc in H as ASTK1. rewrite ASTK in ASTK1.
  assert (b = stkblock).
    apply Mem.alloc_result in H as H3. subst.
    unfold Mem.nextblock. unfold Mem.fresh_block.
    erewrite Genv.init_mem_stack; eauto.
    subst.
  assert (b0 = stkblock).
    apply Mem.alloc_result in H1 as H3. subst.
    unfold Mem.nextblock. unfold Mem.fresh_block.
    erewrite Genv.init_mem_stack; eauto.
    subst.
  exploit Mem.alloc_right_inject; eauto. intro.
  exploit Mem.alloc_left_mapped_inject. apply H0. apply H1.
  + instantiate (1:= stkblock). apply Mem.valid_new_block in H.
    auto.
  + instantiate (1:=max_stacksize'). generalize max_stacksize'_lt_max. intro.
    split. vm_compute. intro. inv x. lia.
  + intros. right. exploit Mem.perm_alloc_3; eauto.
    intros. generalize max_stacksize'_lt_max. intro. lia.
  + intros. assert (ofs = 0). lia. subst. exploit Mem.perm_alloc_2; eauto. instantiate (1:= max_stacksize').
    lia. intro. rewrite Z.add_0_l. eapply Mem.perm_implies; eauto. apply perm_F_any.
  + intro. intros. destruct chunk; simpl in H3; extlia.
  + intros. unfold Mem.flat_inj in H3. destr_in H3. inv H3.
    extlia.
  + intros (j' & A & B &C &D).
(*  edestruct (Mem.range_perm_drop_2) with (p:= Writable) as (m3' & DROP).
  red. intros. eapply Mem.perm_alloc_2; eauto.
  exploit Mem.drop_outside_inject; eauto. intros.
  {
    destruct (eq_block b' stkblock).
    subst.
    exploit Mem.perm_alloc_3. 2: apply H4. eauto. intro. lia.
    rewrite D in H3. unfold Mem.flat_inj in H3. destr_in H3.
    auto.
  }
  intro. *)
  eexists j' ,_. split.
  econstructor; eauto.
  constructor; eauto.
  constructor; intros.
  - apply Genv.genv_defs_range in H3. destruct (eq_block b stkblock). subst.
    simpl in H3. rewrite SUP,STK in H3. inv H3. rewrite D.
  unfold Mem.flat_inj. rewrite <- SUP.
  rewrite pred_dec_true. auto. auto. auto.
  - destruct (eq_block b stkblock). subst. rewrite C in H3. inv H3.
    apply Genv.genv_defs_range in H4. simpl in H4. rewrite SUP,STK in H4. inv H4.
    rewrite D in H3.
    unfold Mem.flat_inj in H3. rewrite <- SUP in H3. destr_in H3. auto.
  - destruct (eq_block b stkblock). subst. apply Genv.genv_vars_eq in H3. inv H3.
    rewrite D. unfold Mem.flat_inj. rewrite <- SUP. apply Genv.genv_symb_range in H3. destr. auto.
  - rewrite SUP. eapply Mem.sup_include_alloc; eauto.
  - rewrite SUP. eapply Mem.sup_include_alloc; eauto.
  -
  intros. unfold rs0 in H3. rewrite Pregmap.gss in H3. inv H3. auto.
  - intros. unfold rs0.
    repeat (intros; apply val_inject_set; auto). fold ge0.
    ++ unfold ge0. unfold Genv.symbol_address.
       econstructor; eauto.
       destruct (eq_block bmain stkblock). apply Genv.genv_vars_eq in H2.
       rewrite H2 in e. inv e.
       rewrite D.
       rewrite <- SUP.
       unfold Mem.flat_inj.
       rewrite pred_dec_true. eauto.
       eapply Genv.genv_symb_range; eauto.
       auto. auto.
    ++ constructor.
    ++ econstructor; eauto.
  - apply Genv.init_mem_astack in INITMEM. erewrite Mem.astack_alloc; eauto.
    rewrite INITMEM. simpl. vm_compute. congruence.
  - rewrite ASTK2. constructor.
  - intros. unfold current_in_stack in H3. rewrite ASTK2 in H3.
    simpl in H3. destr_in H3.
  - apply Mem.valid_new_block in H1. auto.
  - intros. intro. exploit Mem.perm_alloc_3. 2: apply H3. eauto. intro. lia.
  - apply Mem.valid_new_block in H. auto.
  - constructor.
    ++ intros ofs k p PERM. subst.
       exploit Mem.perm_alloc_3; eauto. intro.
       assert (max_stacksize' < Ptrofs.max_unsigned).
       {
         unfold max_stacksize'.
         vm_compute. auto.
       }
       lia.
    ++ intros.
       exploit Mem.perm_alloc_2; eauto. instantiate (1:=k).
       intro. eauto. eapply Mem.perm_implies; eauto. constructor.
  - rewrite ASTK2. simpl. constructor. eauto.
  - exists(Ptrofs.repr max_stacksize'). split.
    erewrite Mem.astack_alloc; eauto.
      erewrite Genv.init_mem_astack; eauto.
      rewrite Pregmap.gss. reflexivity.
  - intro. intros. destruct (eq_block b stkblock). subst.
    rewrite C in H3. inv H3. split. generalize (stack_size_pos (Mem.astack(Mem.support m1))). intro.
    exploit Mem.perm_alloc_3. 2: eauto. eauto. intro.
    assert (ofs = 0).  lia. subst. lia.
    exploit Mem.perm_alloc_3. 2: apply H4. eauto. intro. lia.
    rewrite D in H3.
    unfold Mem.flat_inj in H3. destr_in H3. auto.
Qed.

Lemma transf_final_states:
  forall j st1 st2 r,
    match_states j st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct Archi.ptr64; inversion 1; auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Asm.semantics instr_size prog) (SSAsm.semantics instr_size prog).
Proof.
  eapply forward_simulation_step with (fun s1 s2 => exists j o, match_states j s1 s2).
  - simpl. reflexivity.
  - simpl. intros s1 IS; inversion IS.
    exploit transf_initial_states. eauto.
    intros (j & st2 & MIS & MS); eexists; split; eauto. inv MIS. eauto.
  - simpl. intros s1 s2 r (j & o & MS) FS. eapply transf_final_states; eauto.
  - simpl. intros s1 t s1' STEP s2 (j & o & MS).
    edestruct step_simulation as (j' & s2' & STEP' & MS'); eauto.
Qed.

End PRESERVATION.

Instance TransfSSAsmLink : TransfLink match_prog.
Proof.
  red; intros. destruct (link_linkorder _ _ _ H) as (LO1 & LO2).
  eexists p. split. inv H0. inv H1. auto. reflexivity.
Qed.
