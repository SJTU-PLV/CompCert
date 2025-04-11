Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Conventions.
Require Import LanguageInterface CallconvAlgebra CKLR CKLRAlgebra.
Require Import Asm.

Definition stkblock := Stack 1%positive.

Section INSTRSIZE.

Variable instr_size : instruction -> Z.

Section SSASM.

Variable init_sup : sup.
Variable ge: genv.

Definition init_astack := Mem.astack init_sup.

Definition inner_sp (rs: regset) m :=
  Some (if Nat.eq_dec (length init_astack) (length (Mem.astack (Mem.support m))) then false else true).

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  | Pallocframe sz ofs_ra ofs_link =>
    let aligned_sz := align sz 8 in
    let sp := Val.offset_ptr (rs#RSP) (Ptrofs.neg (Ptrofs.repr aligned_sz)) in
    match Mem.record_frame (Mem.push_stage m) (mk_frame stkblock sz) with
    | None => Stuck
    | Some m1 =>
      match Mem.storev Mptr m1 (Val.offset_ptr sp ofs_ra) (rs#RA) with
      | None => Stuck
      | Some m2 =>
        match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_link) rs#RSP with
        | None => Stuck
        | Some m3 => Next (nextinstr_nf (Ptrofs.repr (instr_size i)) (rs #RAX <- (rs#RSP) #RSP <- sp)) m3
        end
      end
    end
  | Pfreeframe sz ofs_ra ofs_link =>
    let aligned_sz := align sz 8 in
    let sp := Val.offset_ptr rs#RSP (Ptrofs.repr aligned_sz) in
    match loadvv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
    | None => Stuck
    | Some ra =>
      match Mem.pop_stage m with
      | None => Stuck
      | Some m' =>
        if (length init_astack <? length (Mem.astack (Mem.support m)))%nat then
        Next (nextinstr (Ptrofs.repr (instr_size i)) (rs#RSP <- sp #RA <- ra)) m'
        else Stuck
      end
    end
  | Pret =>
    match inner_sp rs m with
    | Some true =>
      if check_ra_after_call instr_size ge (rs#RA) then Next' (rs#PC <- (rs#RA) #RA <- Vundef) m true else Stuck
    | Some false =>
      Next' (rs#PC <- (rs#RA) #RA <- Vundef) m false
    | None => Stuck
    end
  | _ => Asm.exec_instr' instr_size ge inner_sp init_sup f i rs m
  end.

Inductive step : state -> trace -> state -> Prop :=
| exec_step_internal:
    forall b ofs f i rs m rs' m' live,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m = Next' rs' m' live ->
      step (State rs m true) E0 (State rs' m' live)
| exec_step_builtin:
    forall b ofs f ef args res rs m vargs t vres rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr instr_size (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs RSP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      rs' = nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
              (set_res res vres
                       (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      step (State rs m true) t (State rs' m' true)
| exec_step_external:
    forall b ef args res rs m t rs' m' m1 live,
      rs PC = Vptr b Ptrofs.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      Mem.storev Mptr m (Val.offset_ptr (rs RSP) (Ptrofs.neg (Ptrofs.repr (size_chunk Mptr))))
                 (rs RA) = Some m1 -> (* Act as a x86 function, push RA for the callee function *)
      extcall_arguments rs m1 (ef_sig ef) args ->
      forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
        (RA_TYPE: Val.has_type (rs RA) Tptr)
        (SP_NOT_VUNDEF: rs RSP <> Vundef)
        (RA_NOT_VUNDEF: rs RA <> Vundef),
      external_call ef ge args m1 t res m' ->
      forall ISP: inner_sp rs m = Some live,
      (live = true -> ra_after_call instr_size ge (rs # RA)) ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))
              #PC <- (rs RA)
              #RA <- Vundef
      ->
      step (State rs m true) t (State rs' m' live).

End SSASM.

(** Execution of whole programs. *)

Inductive initial_state (ge: genv): query li_asm -> state -> Prop :=
  | initial_state_intro rs m f:
      Genv.find_funct ge rs#PC = Some (Internal f) ->
      rs#SP <> Vundef ->
      rs#RA <> Vundef ->
      initial_state ge (rs, m) (State rs (Mem.push_stage m) true).

Inductive at_external (ge: genv): state -> query li_asm -> Prop :=
  | at_external_intro rs m id sg:
      Genv.find_funct ge rs#PC = Some (External (EF_external id sg)) ->
      at_external ge (State rs m true) (rs, m).

Inductive after_external init_sup: state -> reply li_asm -> state -> Prop :=
  | after_external_intro rs m (rs': regset) m' live:
      Mem.sup_include (Mem.support m) (Mem.support m') ->
      inner_sp init_sup rs' m' = Some live ->
      after_external init_sup
        (State rs m true)
        (rs', m')
        (State rs' m' live).

Inductive final_state: state -> reply li_asm -> Prop :=
  | final_state_intro rs m:
      final_state (State rs m false) (rs, m).

(** The same final_state as defined in the Asm.v *)
Definition semantics (p: program) : Smallstep.semantics li_asm li_asm :=
  {|
    skel := erase_program p;
    activate se :=
      let ge := Genv.globalenv se p in
      {|
        Smallstep.step ge '(sup, s) t '(sup', s') := step sup ge s t s' /\ sup' = sup;
        Smallstep.valid_query q := Genv.is_internal ge (entry q);
        Smallstep.initial_state q '(sup, s) := initial_state ge q s /\ sup = Mem.support (snd q);
        Smallstep.at_external '(sup, s) q := at_external ge s q;
        Smallstep.after_external '(sup, s) r '(sup', s') := after_external sup s r s' /\ sup' = sup;
        Smallstep.final_state '(sup, s) := final_state s;
        Smallstep.globalenv := ge;
      |}
  |}.

End INSTRSIZE.

Definition regset_inject j (rs rs': regset) : Prop :=
  forall r, Val.inject j (rs # r) (rs' # r).

Definition max_stacksize' := max_stacksize + align (size_chunk Mptr) 8.

Inductive ssasm_match_astack (j: meminj): stackadt -> stackadt -> Prop :=
  | ssasm_match_astack_nil:
      ssasm_match_astack j nil nil
  | ssasm_match_astack_cons: forall hd hd' t t' tl tl' ofs
      (IHstk: ssasm_match_astack j tl tl')
      (INJ: j (frame_block hd) = Some (stkblock, ofs))
      (SIZE: frame_size hd = frame_size hd'),
      ssasm_match_astack j ((hd :: t) :: tl) ((hd' :: t') :: tl).

Variant cc_ssasm_match R w : regset * mem -> regset * mem -> Prop :=
  cc_ssasm_match_intro: forall rs1 m1 rs2 m2 hd t tl
    (RSINJ: regset_inject (mi R w) rs1 rs2)
    (MEM: match_mem R w m1 m2)
    (STK: ssasm_match_astack (mi R w) (Mem.astack (Mem.support m1)) (Mem.astack (Mem.support m2)))
    (STKCIN: forall b, In b (sp_of_astack (Mem.astack (Mem.support m1))) -> is_stack b /\ sup_In b (Mem.support m1))
    (STKHD: Mem.astack (Mem.support m1) = (hd :: t) :: tl)
    (STKINJ: (mi R w) (frame_block hd) = Some (stkblock, max_stacksize' - stack_size (Mem.astack (Mem.support m1))))
    (PC: rs1#PC <> Vundef),
    cc_ssasm_match R w (rs1, m1) (rs2, m2).

Program Definition cc_ssasm R : callconv li_asm li_asm :=
  {|
    match_senv := match_stbls R;
    match_query := cc_ssasm_match R;
    match_reply := (<> cc_asm_match R)%klr;
  |}.
Next Obligation.
  eapply match_stbls_proj in H. eapply Genv.mge_public; eauto.
Qed.
Next Obligation.
  eapply match_stbls_proj in H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Ltac rewrite_hyps :=
  repeat
    match goal with
      H1 : ?a = _, H2: ?a = _ |- _ => rewrite H1 in H2; inv H2
    end.

Ltac trim H :=
  match type of H with
    ?a -> ?b => let x := fresh in assert a as x; [ clear H | specialize (H x); clear x]
  end.

Lemma semantics_determinate: forall isz p, determinate (semantics isz p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
- (* determ *)
  destruct s as [sup s], s1 as [sup1 s1], s2 as [sup2 s2], H, H0. subst.
  inv H; inv H0; Equalities.
+ split. constructor. auto.
+ discriminate.
+ discriminate.
+ assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
+ assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H5. eexact H12. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
- (* trace length *)
  red; cbn. intros [sup s] t [sup' s'] [H Hnb]. inv H; simpl.
  lia.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  destruct s1 as [sup1 s1], s2 as [sup2 s2], H, H0.
  inv H. inv H0. reflexivity.
- (* final no step *)
  destruct s as [sup s].
  inv H. red; intros; red; intros.
  destruct s' as [sup' s'], H as (H & Hsup). inv H.
  + rewrite H3 in H0. cbn in H0. destruct Ptrofs.eq_dec; congruence.
  + rewrite H3 in H0. cbn in H0. destruct Ptrofs.eq_dec; congruence.
  + rewrite H3 in H0. cbn in H0. destruct Ptrofs.eq_dec; try congruence.
    assert (ef = EF_external id sg) by congruence; subst. contradiction.
- (* at_external determ *)
  destruct s as [sup s].
  inv H; inv H0; auto.
- (* after_external determ *)
  destruct s as [sup s], s1 as [sup1 s1], s2 as [sup2 s2], H, H0. subst.
  inv H; inv H0; f_equal; f_equal. rewrite H2 in H8. inv H8; auto.
- (* final no step *)
  destruct s as [sup s].
  inv H. red; intros; red; intros. destruct s', H, H0. inv H.
- (* at_external no step *)
  destruct s as [sup s].
  inv H; inv H0.
- (* final states *)
  destruct s as [sup s].
  inv H; inv H0. congruence.
Qed.
