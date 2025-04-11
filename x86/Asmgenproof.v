(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm AsmFacts.
Require Import Asmgen Asmgenproof0 Asmgenproof1.
Require Import LanguageInterface CKLR Extends.


Section INSTRSIZE.
Variable instr_size : instruction -> Z.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

(* Notation code_size := (code_size instr_size). *)

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => Asmgen.transf_fundef instr_size f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program instr_size p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.

Variable se: Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv se tprog.

Lemma functions_translated:
  forall vf f,
  Genv.find_funct ge vf = Some f ->
  exists b tf,
  Genv.find_funct_ptr tge b = Some tf /\ Asmgen.transf_fundef instr_size f = OK tf /\ vf = Vptr b Ptrofs.zero.
Proof.
  intros.
  destruct vf; try discriminate. simpl in H. destruct Ptrofs.eq_dec; try discriminate; subst.
  edestruct @Genv.find_funct_transf_partial_id with (v := Vptr b Ptrofs.zero) as (? & ? & ?); eauto.
  - cbn. destruct Ptrofs.eq_dec; eauto. congruence.
  - cbn in *. destruct Ptrofs.eq_dec; try discriminate. eauto.
Qed.

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function instr_size f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit (functions_translated (Vptr fb Ptrofs.zero)); eauto.
  intros [tf' [A [B [C D]]]]. inv D.
  monadInv C. rewrite H0 in EQ; inv EQ; auto.
Qed.

Section WITH_WORLD.
Variable init_rs: regset.
Variable init_sup: sup.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function instr_size f = OK tf -> code_size instr_size (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (code_size instr_size (fn_code x))); monadInv EQ0.
  lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc instr_size ge (rs PC) fb f c ep tf tc ->
  exec_straight instr_size init_sup tge tf tc rs m c' rs' m' ->
  plus (step instr_size init_sup) tge (State rs m true) E0 (State rs' m' true).
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc instr_size ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight instr_size init_sup tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc instr_size ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Hint Resolve tail_nolabel_refl: labels.

Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H. destruct (Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; intros. TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd RAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark mk_sel_label:
  forall xc rd r2 k c,
  mk_sel xc rd r2 k = OK c ->
  tail_nolabel k c.
Proof.
  unfold mk_sel; intros; destruct xc; inv H; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  exploit mk_intconv_label; eauto. intros. simpl. auto.
  exploit mk_intconv_label; eauto. intros. simpl. auto.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
  unfold transl_sel in EQ2. destruct (ireg_eq x x0); monadInv EQ2.
  TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_sel_label; eauto.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function instr_size f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (code_size instr_size (fn_code x))); inv EQ0.
  monadInv EQ. destr_in EQ1. inv EQ1. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function instr_size f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label instr_size tge tf lbl rs m = Next rs' m
  /\ transl_code_at_pc instr_size ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. exploit functions_transl; eauto.
  intro. rewrite H1. rewrite H3. auto.
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. lia.
  generalize (transf_function_no_overflow _ _ H0). lia.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset instr_size f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (code_size instr_size (fn_code x))); inv EQ0.
  monadInv EQ. destr_in EQ1. inv EQ1. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Definition size_of_callstack (l: list stackframe): list (option Z) :=
  (fun x:stackframe =>
     match x with
       |Stackframe fb _ _ _ =>
        match Genv.find_funct ge fb with
          |Some (Internal tf) => Some (Mach.fn_stacksize tf)
          |_ => None
        end
        |Stackbase _ _ => None
     end) ## l.

Inductive size_consistency :  list (option Z) -> stackadt -> Prop :=
  |size_consistency_nil : size_consistency (None::nil) (Mem.astack init_sup)
  |size_consistency_cons : forall lsz astack fr,
      size_consistency lsz astack ->
      size_consistency ((Some (frame_size fr))::lsz) ((fr::nil)::astack).

Remark size_consistency_size:
  forall lsz astack,
    size_consistency lsz astack ->
    (length astack >= length (Mem.astack init_sup))%nat.
Proof. induction 1; simpl; auto. Qed.

Definition sp_of_callstack (l:list stackframe) : list val :=
  (fun x:stackframe =>
     match x with
       |Stackframe _ sp _ _ => sp
       |Stackbase sp _ => sp
     end) ## l.

Inductive sp_consistency : list block -> list val -> Prop :=
  |sp_consistency_nil : forall hd tl,
    Mem.astack init_sup = hd :: tl ->
    sp_consistency (sp_of_astack tl) nil
  |sp_consistency_cons : forall sb sp lb ls,
      sp_consistency lb ls ->
      sp = Vptr sb Ptrofs.zero ->
      sp_consistency (sb :: lb) (sp::ls).


Lemma code_tail_code_size:
  forall a b sz,
    code_tail instr_size sz (a ++ b) b ->
    sz = code_size instr_size a.
Proof.
  intros a b sz.
  remember (a++b).
  intro CT; revert sz l b CT a Heql.
  induction 1; simpl; intros; eauto.
  apply (f_equal (@length _)) in Heql. rewrite app_length in Heql.
  destruct a; simpl in *; try lia.
  destruct a. simpl in *. subst. apply code_tail_no_bigger in CT. simpl in CT. lia. simpl in Heql.
  inv Heql.
  specialize (IHCT _ eq_refl). subst. simpl. lia.
Qed.

Lemma offsets_after_call_app:
  forall y z pos,
    offsets_after_call instr_size (y ++ z) pos =  offsets_after_call instr_size y pos ++ offsets_after_call instr_size z (pos + code_size instr_size y).
Proof.
  induction y; simpl; intros; eauto. rewrite Z.add_0_r. auto.
  rewrite ! IHy. destr. simpl. rewrite Z.add_assoc.  f_equal.
  f_equal. f_equal. lia.
  simpl. rewrite Z.add_assoc. f_equal. f_equal.  lia.
Qed.

Lemma code_size_app:
  forall c1 c2,
    code_size instr_size (c1 ++ c2) = code_size instr_size c1 + code_size instr_size c2.
Proof.
  induction c1; simpl; intros; rewrite ? IHc1; lia.
Qed.

Variant stack_internal : list stackframe -> Prop :=
  stack_internal_intro: forall vf sp ra c s,
    stack_internal (Stackframe vf sp ra c :: s).

Lemma live_is_internal:
  forall s bound,
    inner_sp init_sup (parent_sp s) = Some true ->
    match_stack instr_size ge init_rs init_sup bound s ->
    stack_internal s.
Proof.
  intros. unfold inner_sp in H. do 2 destr_in H.
  unfold parent_sp in Heqv. destr_in Heqv.
  destr_in Heqv. constructor.
  inv H0. inv H7. congruence.
Qed.

Lemma has_code_parent_ra_after_call:
  forall s
    (INT: stack_internal s)
    (HC: callstack_function_defined (return_address_offset instr_size) ge s),
    ra_after_call instr_size tge (parent_ra s).
Proof.
  intros s INT HC.
  inv HC. inv INT.
  split.
  unfold Val.offset_ptr. unfold Genv.find_funct in FINDF. destr_in FINDF. simpl. congruence.
  intros b o EQ; inv EQ.
  edestruct functions_translated as (fb & tf & FFP' & TF & VF); eauto.
  subst vf. simpl in H0. inv H0.
  rewrite FFP'. intros f EQ. inv EQ.
  red. simpl in TF. monadInv TF.
  red in RAU.
  specialize (fun tc => RAU _ tc EQ).
  monadInv EQ. repeat destr_in EQ1.
  monadInv EQ0. repeat destr_in EQ1. simpl in *. rewrite pred_dec_false. 2: inversion 1.
  destruct TAIL as (l' & sg & ros & CODE). rewrite CODE in EQ.
  rewrite transl_code'_transl_code in EQ.
  edestruct transl_code_app as (ep2 & y & TC1 & TC2); eauto.
  monadInv TC2.
  simpl in EQ0. monadInv EQ0.
  specialize (RAU _ EQ1).
  assert (exists icall, x = icall :: x0 /\ is_call icall).
  {
    destr_in EQ2; monadInv EQ2; eexists; split; eauto; constructor.
  }
  destruct H as (icall & ICALL & ISCALL). subst.
  generalize (code_tail_code_size (Pallocframe (Mach.fn_stacksize trf)(fn_retaddr_ofs trf)(fn_link_ofs trf) :: y ++ icall :: nil) x0).
  simpl. rewrite app_ass. simpl. intro EQSZ; specialize (EQSZ _ RAU).
  rewrite offsets_after_call_app.
  apply in_app. right.  unfold offsets_after_call. rewrite pred_dec_true.
  left. rewrite Ptrofs.add_zero_l, EQSZ.
  rewrite code_size_app. simpl. lia. auto.
Qed.

Inductive wf_ra: list stackframe -> Prop :=
  |wf_ra_nil : forall fb ra, wf_ra (Stackbase fb ra :: nil)
  |wf_ra_cons : forall fb sp c b ofs l, wf_ra l -> wf_ra ((Stackframe fb sp (Vptr b ofs) c):: l).

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack instr_size ge init_rs init_sup (Mem.support m') s)
        (SPVB: valid_blockv (Mem.support m') sp)
        (SPLT: inner_sp init_sup sp = Some true)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc instr_size ge (rs PC) fb f c ep tf tc)
        (CODE: callstack_function_defined (return_address_offset instr_size) ge s)
        (TAIL: exists l, Mach.fn_code f = l ++ c)
        (WFRA: wf_ra s)
        (AG: agree ms sp rs)
        (SC: size_consistency
               ((Some (Mach.fn_stacksize f))::(size_of_callstack s))
               (Mem.astack(Mem.support m)))
        (SPC: sp_consistency (sp_of_astack (Mem.astack (Mem.support m))) (sp :: sp_of_callstack s))
        (AXP: ep = true -> rs#RAX = parent_sp s),
      match_states (Mach.State s (Vptr fb Ptrofs.zero) sp c ms m)
                   (Asm.State rs m' true)
  | match_states_call:
      forall s vf ms m m' rs id
        (STACKS: match_stack instr_size ge init_rs init_sup (Mem.support m') s)
        (MEXT: Mem.extends m m')
        (CODE: callstack_function_defined (return_address_offset instr_size) ge s)
        (WFRA: wf_ra s)
        (AG: agree ms (parent_sp s) rs)
        (SC: size_consistency (size_of_callstack s) (Mem.astack(Mem.support m)))
        (SPC: sp_consistency (sp_of_astack (Mem.astack (Mem.support m))) (sp_of_callstack s))
        (VF: vf = Vptr (Global id) Ptrofs.zero)
        (ATPC: Val.lessdef vf (rs PC))
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s vf ms m id)
                   (Asm.State rs m' true)
  | match_states_return:
      forall s ms m m' rs live
        (STACKS: match_stack instr_size ge init_rs init_sup (Mem.support m') s)
        (MEXT: Mem.extends m m')
        (CODE: callstack_function_defined (return_address_offset instr_size) ge s)
        (WFRA: wf_ra s)
        (AG: agree ms (parent_sp s) rs)
        (SC: size_consistency (size_of_callstack s) (Mem.astack(Mem.support m)))
        (SPC: sp_consistency (sp_of_astack (Mem.astack (Mem.support m))) (sp_of_callstack s))
        (ATPC: rs PC = parent_ra s)
        (LIVE: inner_sp init_sup rs#SP = Some live),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m' live).

Lemma exec_instr_support f i rs m rs' m' b:
  exec_instr instr_size init_sup tge f i rs m = Next' rs' m' b ->
  Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  destruct i; simpl;
  try (unfold exec_load; destruct (Mem.loadv _ _ _));
  try (unfold exec_store; destruct (eval_addrmode _ _ _); simpl);
  unfold goto_label;
  unfold free';
  repeat
    match goal with
      | |- match ?x with _ => _ end = Next' _ _ _ -> _ =>
        let H := fresh in
        destruct x eqn:H;
        try apply Mem.support_free in H;
        try apply Mem.support_store in H;
        try apply Mem.support_alloc in H
    end;
  inversion 1;
  try (replace (Mem.support m) with (Mem.support m') by congruence); eauto.
  - subst. red. intros. rewrite H5, H4.
    erewrite <- Mem.support_record_frame_1, <- Mem.support_push_stage_1. 2,3:eauto.
    rewrite H2. apply Mem.sup_incr_in2. auto.
  - subst. destruct zlt.
    + red. intros.
      erewrite <- Mem.support_pop_stage_1, Mem.support_free; eauto.
    + inv H6. red. intros.
      erewrite <- Mem.support_pop_stage_1; eauto.
Qed.

Lemma exec_straight_support tf c rs m k rs' m':
  exec_straight instr_size init_sup tge tf c rs m k rs' m' ->
  valid_blockv (Mem.support m) init_rs#SP ->
  valid_blockv (Mem.support m') init_rs#SP.
Proof.
  induction 1; eauto using valid_blockv_support, exec_instr_support.
Qed.

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack instr_size ge init_rs init_sup (Mem.support m2') s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  callstack_function_defined (return_address_offset instr_size) ge s ->
  (exists l, Mach.fn_code f = l ++ c )->
  size_consistency
    ((Some (Mach.fn_stacksize f))::(size_of_callstack s))
    (Mem.astack(Mem.support m2)) ->
  sp_consistency (sp_of_astack (Mem.astack (Mem.support m2))) (sp :: sp_of_callstack s) ->
  transl_code_at_pc instr_size ge (rs1 PC) fb f (i :: c) ep tf tc ->
  inner_sp init_sup sp = Some true ->
  valid_blockv (Mem.support m2') sp ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight instr_size init_sup tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp s)) ->
  exists st',
  plus (step instr_size init_sup) tge (State rs1 m1' true) E0 st' /\
  match_states (Mach.State s (Vptr fb Ptrofs.zero) sp c ms2 m2) st'.
Proof.
  intros. inversion H6. subst. monadInv H13.
  exploit H9; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2' true); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto.
  eapply exec_straight_at; eauto.
  clear - H H2.
  induction H2. constructor. unfold Val.offset_ptr in *.
  inv H. constructor. apply IHcallstack_function_defined. auto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' (WFRA: wf_ra s),
  match_stack instr_size ge init_rs init_sup (Mem.support m2') s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  callstack_function_defined (return_address_offset instr_size) ge s ->
  (exists l, Mach.fn_code f = l ++ c )->
  size_consistency
    (Some (Mach.fn_stacksize f)::(size_of_callstack s))
    (Mem.astack(Mem.support m2)) ->
  sp_consistency (sp_of_astack (Mem.astack (Mem.support m2))) (sp :: sp_of_callstack s) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc instr_size ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  inner_sp init_sup sp = Some true ->
  valid_blockv (Mem.support m2') sp ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight instr_size init_sup tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr instr_size init_sup tge tf jmp rs2 m2' = goto_label instr_size tge tf lbl rs2 m2') ->
  exists st',
  plus (step instr_size init_sup) tge (State rs1 m1' true) E0 st' /\
  match_states (Mach.State s (Vptr fb Ptrofs.zero) sp c' ms2 m2) st'.
Proof.
  intros. inversion H7. subst. monadInv H15.
  exploit H11; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H13 H14); intro FN.
  generalize (transf_function_no_overflow _ _ H14); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2' true); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail; eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  - inv H6. eapply find_label_ex. eauto.
  - apply agree_exten with rs2; auto with asmgen.
  - congruence.
Qed.

Lemma alloc_sp_fresh m lo hi m' stk ofs:
  Mem.sup_include init_sup (Mem.support m) ->
  Mem.alloc m lo hi = (m', stk) ->
  inner_sp init_sup (Vptr stk ofs) = Some true.
Proof.
  intros Hm Hstk.
  apply Mem.alloc_result in Hstk. cbn. subst.
  destruct Mem.sup_dec; auto. exfalso. eapply freshness; eauto.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

Lemma support_storev chunk m ptr v m':
  Mem.storev chunk m ptr v = Some m' ->
  Mem.support m' = Mem.support m.
Proof.
  destruct ptr; try discriminate. cbn.
  apply Mem.support_store.
Qed.

Lemma code_move:
  forall instr c f,
    (exists l1, Mach.fn_code f = l1 ++ instr :: c) ->
    exists l2, Mach.fn_code f = l2 ++ c.
Proof.
  intros. destruct H as (l & H).
  exists (l++instr::nil). rewrite H. rewrite app_ass. simpl. auto.
Qed.

Lemma pop_stage_match_stack:
  forall m m' s,
    Mem.pop_stage m = Some m' ->
    match_stack instr_size ge init_rs init_sup (Mem.support m) s ->
    match_stack instr_size ge init_rs init_sup (Mem.support m') s.
Proof.
  intros m m' s POP MS. induction MS; econstructor; eauto.
  eapply Mem.sup_include_trans; eauto. eapply Mem.sup_include_pop_stage; auto.
  inv H2. constructor. eapply Mem.sup_include_pop_stage; eauto.
Qed.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step (return_address_offset instr_size) ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus (step instr_size init_sup) tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros. eapply code_move; eauto.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. eapply code_move; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  erewrite <- support_storev in STACKS, SPVB; eauto.
  left; eapply exec_straight_steps; eauto.
  eapply code_move; eauto.
  erewrite <- Mem.support_storev; eauto.
  erewrite <- Mem.support_storev; eauto.  
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; intros. rewrite Q; auto with asmgen.
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.

- (* Mgetparam *)
  cbn in H. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.  eapply code_move; eauto.
  assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
    intros. change (IR RAX) with (preg_of AX). red; intros.
    unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* RAX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite AXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.

(* RAX does not contain parent *)
  monadInv TR.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite U; auto.

- (* Mop *)
  assert (eval_operation tge sp op rs##args m = Some v).
    rewrite <- H. apply eval_operation_preserved. auto.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. eapply code_move; eauto. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. auto.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros.  eapply code_move; eauto. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. auto.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  erewrite <- support_storev in STACKS, SPVB; eauto.
  left; eapply exec_straight_steps; eauto.
 eapply code_move; eauto.
 erewrite <- Mem.support_storev; eauto.
 erewrite <- Mem.support_storev; eauto.
  intros. simpl in TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; congruence.

- (* Mcall *)
  cbn in H. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: code_size instr_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H0; monadInv H6.
+ (* Indirect call *)
  assert (rs rf = Vptr (Global id) Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H0; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr (Global id) Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H0; intros LD; inv LD; auto.
  generalize (code_tail_next_int instr_size instr_size_bound _ _ _ _ NOOV H7). intro CT1.
  assert (TCA: transl_code_at_pc instr_size ge (Vptr fb (Ptrofs.add ofs (Ptrofs.repr (instr_size (Pcall_r x0 sig))))) fb f c false tf x).
    econstructor; auto.
  exploit return_address_offset_correct; eauto. intros; subst ra. destruct H1.
  exploit functions_translated. apply H1. intros (b' & tf' & FFPcalled' & TRANSF' & EQ').
  simpl in EQ'. rewrite H0 in EQ'. inv EQ'.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. rewrite H8. simpl. rewrite pred_dec_true; auto.
  rewrite FFPcalled'. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. rewrite Ptrofs.add_zero_l. eauto.
  econstructor; eauto. destruct TAIL as (l'&TAIL). eauto.
  constructor; auto.
  econstructor; eauto. simpl. Simplifs. eapply agree_sp; eauto. simpl. inv AG. auto.
  simpl. intros. eapply agree_exten; eauto. intros. Simplifs.
  simpl. rewrite H4. auto.
  simpl. rewrite Pregmap.gss. rewrite H6. auto.
  Simplifs. cbn. rewrite Ptrofs.add_zero_l. rewrite <- H3. cbn. auto.
+ (* Direct call *)
  generalize (code_tail_next_int instr_size instr_size_bound _ _ _ _ NOOV H7). intro CT1.
  assert (TCA: transl_code_at_pc instr_size ge (Vptr fb (Ptrofs.add ofs (Ptrofs.repr (instr_size (Pcall_s fid sig))))) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  destruct H1.
  exploit functions_translated. apply H0. intros (b' & tf' & FFPcalled' & TRANSF' & EQ'). simpl in EQ'.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. rewrite EQ'. simpl. rewrite pred_dec_true; auto. rewrite FFPcalled'. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. rewrite Ptrofs.add_zero_l. eauto.
  destruct TAIL; econstructor; eauto. constructor; auto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  simpl. rewrite H4. auto.
  simpl. unfold Genv.symbol_address in *. destr_in EQ'. inv EQ'.
  apply Genv.genv_vars_eq in Heqo. congruence.
  simpl. rewrite EQ'. rewrite Pregmap.gss. auto.
  Simplifs. rewrite <- H3. cbn. rewrite Ptrofs.add_zero_l. auto.

- (* Mtailcall *)
  cbn in H. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: code_size instr_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  destruct H1 as (fd & FFPcalled).
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H3. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  exploit Mem.pop_stage_extends; eauto. intros [m2''' [J K]].
  apply Mem.support_free in H4 as SF. apply Mem.support_free in E as SF'.
  apply Mem.astack_pop_stage in H5 as ASP. destruct ASP as (topfr & ASP).
  assert (INNER: (length (Mem.astack init_sup) <? length (Mem.astack (Mem.support m'0)))%nat = true).
    inv SC. apply size_consistency_size in H11.
    inv F. rewrite <- SF', <- mext_sup, SF, <- H13. simpl.
    rewrite Nat.ltb_lt. lia.
  assert (CTF:check_topframe (Mach.fn_stacksize f) (Mem.astack (Mem.support m'0)) = true).
   unfold check_topframe. inv SC.   inv MEXT. rewrite <- mext_sup. rewrite <- H13.
   rewrite pred_dec_true; auto. unfold frame_size_a. unfold aligned_fsz.
   assert (exists b, inner_sp init_sup (parent_sp s) = Some b) as [b INNERSP].
     inv WFRA; simpl; inv SPC. inv H13. simpl. eauto. inv H14. simpl. eauto.
   assert ((parent_sp_stack (Mem.astack (Mem.support m'0)) = (parent_sp s)) /\
            top_sp_stack (Mem.astack (Mem.support m'0)) = rs0 RSP).
   {
     inv MEXT. rewrite <- mext_sup.
     clear - SPC INNERSP.
     inv SPC. unfold parent_sp_stack, top_sp_stack. rewrite <- H.
     inv H2.
     - destruct s; inv H0. inv INNERSP.
     - destruct s. inv H0. split. simpl.
       destruct s. simpl in H0. inv H0. reflexivity.
       simpl in H0. inv H0. reflexivity.
       simpl. eauto.
   }
  destruct H1 as [CSP CTP].
  (* assert (RA: parent_ra s <> Vundef).
    inv WFRA; simpl. unfold Vnullptr. destr. congruence. *)
  destruct ros as [rf|fid]; simpl in H0; monadInv H9.
+ (* Indirect call *)
  assert (rs rf = Vptr (Global id) Ptrofs.zero).
    simpl in H0.
    destruct (rs rf); try discriminate.
    revert H0; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr (Global id) Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H1; intros LD; inv LD; auto.

  generalize (code_tail_next_int instr_size instr_size_bound _ _ _ _ NOOV H10). intro CT1.
  destruct (zle (Mach.fn_stacksize f) 0).
  * (* fn_stacksize f <= 0 *)
    exploit Mem.free_nothing_extends_reverse. 2:exact H4. lia. intros L.
    exploit Mem.pop_stage_extends. exact L. eauto. intros [m'''' [M N]].
    exploit Mem.pop_stage_extends. exact MEXT. eauto. intros [m''0 [O P]].

    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
    apply transf_function_stacksize_pos in H8 as H8'.
    destr. erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG).
    rewrite INNER, CTF, CSP. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_false by lia.
    rewrite O. eauto. eauto. auto.
    inv WFRA; simpl. inv STACKS. congruence. congruence.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size
                (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))). eauto.
    rewrite <- H6. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. rewrite nextinstr_inv. 2: congruence.
    setoid_rewrite Pregmap.gso. 2: congruence.
    setoid_rewrite Pregmap.gso. 2: eapply ireg_of_not_rsp; eauto. rewrite H9.
    exploit functions_translated. apply FFPcalled. intros (b1 & tf1 & FFPcalled' & TF & ROS).
    simpl in ROS. rewrite H0 in ROS. inv ROS.
    simpl. rewrite pred_dec_true by auto. rewrite FFPcalled'.
    eauto. traceEq.
    econstructor; eauto.
    eapply pop_stage_match_stack; eauto.
    eapply Mem.extends_trans; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. rewrite <- SF in H14.  rewrite ASP in H14. inv H14. auto.
    rewrite <- SF, ASP in SPC. inv SPC. destruct topfr. inv H11. inv H11. eauto.
    rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gso. simpl. rewrite H1, H9. auto.
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). auto.
    generalize (preg_of_not_RA rf). rewrite (ireg_of_eq _ _ EQ1). auto.

  * (* fn_stacksize f > 0 *)
    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
    apply transf_function_stacksize_pos in H8 as H8'.
    destr. erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG).
    rewrite INNER, CTF, CSP. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_true by lia. rewrite E, J. eauto. auto. auto.
    inv WFRA; simpl. inv STACKS. congruence. congruence.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size
                (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))). eauto.
    rewrite <- H6. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. rewrite nextinstr_inv. 2: congruence.
    setoid_rewrite Pregmap.gso. 2: congruence.
    setoid_rewrite Pregmap.gso. 2: eapply ireg_of_not_rsp; eauto. rewrite H9.
    exploit functions_translated. apply FFPcalled. intros (b1 & tf1 & FFPcalled' & TF & ROS).
    simpl in ROS. rewrite H0 in ROS. inv ROS.
    simpl. rewrite pred_dec_true by auto. rewrite FFPcalled'.
    eauto. traceEq.
    econstructor; eauto.
    eapply pop_stage_match_stack; eauto. rewrite SF'. auto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. rewrite <- SF in H14.  rewrite ASP in H14. inv H14. auto.
    rewrite <- SF, ASP in SPC. inv SPC. destruct topfr. inv H11. inv H11. eauto.
    rewrite Pregmap.gss. rewrite Pregmap.gso. rewrite Pregmap.gso. simpl. rewrite H1, H9. auto.
    generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). auto.
    generalize (preg_of_not_RA rf). rewrite (ireg_of_eq _ _ EQ1). auto.
+ (* Direct call *)
  generalize (code_tail_next_int instr_size instr_size_bound _ _ _ _ NOOV H10). intro CT1.
  destruct (zle (Mach.fn_stacksize f) 0).
  * (* fn_stacksize f <= 0 *)
    exploit Mem.free_nothing_extends_reverse. 2:exact H4. lia. intros L.
    exploit Mem.pop_stage_extends. exact L. eauto. intros [m'''' [M N]].
    exploit Mem.pop_stage_extends. exact MEXT. eauto. intros [m''0 [O P]].
    exploit functions_translated. apply FFPcalled. intros (b1 & tf1 & FFPcalled' & TF & ROS). simpl in ROS.

    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
    apply transf_function_stacksize_pos in H8 as H8'. destr.
    erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite INNER, CTF. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_false by lia. rewrite O. eauto. auto. auto.
    inv WFRA; simpl. inv STACKS. congruence. congruence.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size
                (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))). eauto.
    rewrite <- H6. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. rewrite ROS. simpl. rewrite pred_dec_true by auto. rewrite FFPcalled'. eauto.
    traceEq.
    econstructor; eauto.
    eapply pop_stage_match_stack; eauto.
    eapply Mem.extends_trans; eauto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. rewrite <- SF in H11. rewrite ASP in H11. inv H11. auto.
    rewrite <- SF, ASP in SPC. inv SPC. destr_in H0.
    simpl. rewrite ROS.
    unfold Genv.symbol_address in ROS. destr_in ROS. inv ROS. apply Genv.genv_vars_eq in Heqo. subst. auto.
    rewrite Pregmap.gss. simpl. rewrite ROS. auto.
  * (* fn_stacksize f > 0 *)
    exploit functions_translated. apply FFPcalled. intros (b1 & tf1 & FFPcalled' & TF & ROS). simpl in ROS.
    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
    simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
    apply transf_function_stacksize_pos in H8 as H8'. destr.
    erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite INNER, CTF. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_true by lia. rewrite E, J. eauto. auto. auto.
    inv WFRA; simpl. inv STACKS. congruence. congruence.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size
                (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))). eauto.
    rewrite <- H6. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. rewrite ROS. simpl. rewrite pred_dec_true by auto. rewrite FFPcalled'. eauto.
    traceEq.
    econstructor; eauto.
    eapply pop_stage_match_stack; eauto. rewrite SF'. auto.
    apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. rewrite <- SF in H11.  rewrite ASP in H11. inv H11. auto.
    rewrite <- SF, ASP in SPC. inv SPC. destr_in H0.
    simpl. rewrite ROS.
    unfold Genv.symbol_address in ROS. destr_in ROS. inv ROS. apply Genv.genv_vars_eq in Heqo. subst. auto.
    rewrite Pregmap.gss. simpl. rewrite ROS. auto.

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eauto. eauto.
  clear. induction res; simpl; intros; eauto. eapply preg_of_not_rsp; eauto.
  intro. destruct H; congruence.
  eauto.
  assert (Mem.sup_include (Mem.support m'0) (Mem.support m2'))
    by eauto using Mem.unchanged_on_support.
  econstructor; eauto.
  eapply match_stack_incr_bound; eauto.
  eapply valid_blockv_support; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  simpl; intros. intuition congruence.
  eapply code_move; eauto.
  apply agree_nextinstr_nf. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
  erewrite <- external_call_astack; eauto.
  erewrite <- external_call_astack; eauto.
  congruence.

- (* Mgoto *)
  cbn in H. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m' true); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply find_label_ex; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  cbn in H0. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto. 10 : apply AT. all: eauto. eapply code_move; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct init_sup tge tf instr_size cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B. destruct B as [B _].
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr (Ptrofs.repr (instr_size (Pjcc c1 lbl))) rs').
  split. eapply exec_straight_trans. eexact A.
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst.
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. eapply code_move; eauto. intros. simpl in TR.
  destruct (transl_cond_correct init_sup tge tf instr_size cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B. destruct B as [B _].
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B. eauto. auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr (Ptrofs.repr (instr_size (Pjcc2 c1 c2 lbl))) rs'); split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl.
  rewrite TC1; rewrite TC2.
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.

- (* Mjumptable *)
  cbn in H1. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
  exploit (find_label_goto_label f tf lbl rs1); eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto. eapply find_label_ex; eauto.
Transparent destroyed_by_jumptable.
  apply agree_undef_regs with rs0; auto.
  simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
  congruence.

- (* Mreturn *)
  cbn in H. destruct Ptrofs.eq_dec as [_|]; try congruence.
  assert (f0 = f) by congruence. subst f0.
  inv AT.
  assert (NOOV: code_size instr_size tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  assert (exists b, inner_sp init_sup (parent_sp s) = Some b) as [b LIVE].
    pose proof (parent_sp_ptr _ _ _ _ _ _ STACKS) as [? [? ->]].
    unfold inner_sp. eexists. eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]].
  exploit lessdef_parent_sp; eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]].
  exploit lessdef_parent_ra; eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [E F]].
  exploit Mem.pop_stage_extends; eauto. intros [m2'''' [J K]].
  assert (INNER: (length (Mem.astack init_sup) <? length (Mem.astack (Mem.support m'0)))%nat = true).
    inv SC. apply size_consistency_size in H10.
    apply Mem.support_free in E. apply Mem.support_free in H2. inv F.
    rewrite <- E, <- mext_sup, H2, <- H12. simpl.
    rewrite Nat.ltb_lt. lia.
  assert (CTF:check_topframe (Mach.fn_stacksize f) (Mem.astack (Mem.support m'0)) = true).
   unfold check_topframe. inv SC.   inv MEXT. rewrite <- mext_sup. rewrite <- H12.
   rewrite pred_dec_true; auto.
 assert ((parent_sp_stack (Mem.astack (Mem.support m'0)) = (parent_sp s)) /\
            top_sp_stack (Mem.astack (Mem.support m'0)) = rs0 RSP).
   {
     inv MEXT. rewrite <- mext_sup.
     clear - SPC LIVE.
     inv SPC. unfold parent_sp_stack, top_sp_stack. rewrite <- H.
     inv H2.
     - destruct s; inv H0. split; eauto. inv LIVE.
     - destruct s. inv H0. split. simpl.
       destruct s. simpl in H0. inv H0. reflexivity.
       simpl in H0. inv H0. reflexivity.
       simpl. eauto.
   }
  destruct H9 as [CSP CTP].
  assert (RA: parent_ra s <> Vundef).
    inv WFRA; simpl. inv STACKS. congruence. congruence.
  monadInv H7.
  exploit code_tail_next_int; eauto. intro CT1.
  destruct (zle (Mach.fn_stacksize f) 0).
  * (* fn_stacksize f <= 0 *)
    exploit Mem.free_nothing_extends_reverse. 2:exact H2. lia. intros L.
    exploit Mem.pop_stage_extends. exact L. eauto. intros [m'''' [M N]].
    exploit Mem.pop_stage_extends. exact MEXT. eauto. intros [m''0 [O P]].

    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. apply transf_function_stacksize_pos in H6 as H6'. destr.
    erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite INNER, CTF. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_false by lia. rewrite O. eauto. auto. auto.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))).
    auto. rewrite <- H4. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. destr.
    unfold nextinstr in Heqo. repeat rewrite Pregmap.gso in Heqo by congruence. rewrite Pregmap.gss in Heqo.
    rewrite LIVE in Heqo. inv Heqo. destr.
    rewrite pred_dec_true. eauto. rewrite nextinstr_inv by congruence.
    setoid_rewrite Pregmap.gss. eapply has_code_parent_ra_after_call; eauto. eapply live_is_internal; eauto.
    unfold nextinstr in Heqo. repeat rewrite Pregmap.gso in Heqo by congruence. rewrite Pregmap.gss in Heqo.
    rewrite LIVE in Heqo. inv Heqo.
    traceEq.
    constructor; auto.
    eapply pop_stage_match_stack; eauto.
    eapply Mem.extends_trans; eauto.
    apply agree_set_other; auto. apply agree_set_other; auto.
    apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. erewrite <- Mem.support_free in H11; eauto.
    apply Mem.astack_pop_stage in H3. destruct H3. rewrite H3 in H11. inv H11. auto.
    erewrite <- Mem.support_free in SPC; eauto.
    apply Mem.astack_pop_stage in H3; eauto. destruct H3. rewrite H3 in SPC.
    inv SPC. destr_in H7.
  * (* fn_stacksize f > 0 *)
    left; econstructor; split.
    eapply plus_left. eapply exec_step_internal. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. apply transf_function_stacksize_pos in H6 as H6'. destr.
    erewrite loadv_loadvv; eauto.
    rewrite A. rewrite <- (sp_val _ _ _ AG). rewrite INNER, CTF. rewrite pred_dec_true.
    rewrite (sp_val _ _ _ AG). rewrite pred_dec_true.
    unfold free'. rewrite zlt_true by lia. rewrite E, J. eauto. auto. auto.
    apply star_one. eapply exec_step_internal.
    transitivity (Val.offset_ptr rs0#PC (Ptrofs.repr (instr_size (Pfreeframe (Mach.fn_stacksize f)(fn_retaddr_ofs f)(fn_link_ofs f))))).
    auto. rewrite <- H4. simpl. eauto.
    eapply functions_transl; eauto. eapply find_instr_tail; eauto.
    simpl. destr.
    unfold nextinstr in Heqo. repeat rewrite Pregmap.gso in Heqo by congruence. rewrite Pregmap.gss in Heqo.
    rewrite LIVE in Heqo. inv Heqo. destr.
    rewrite pred_dec_true. eauto. rewrite nextinstr_inv by congruence.
    setoid_rewrite Pregmap.gss. eapply has_code_parent_ra_after_call; eauto. eapply live_is_internal; eauto.
    unfold nextinstr in Heqo. repeat rewrite Pregmap.gso in Heqo by congruence. rewrite Pregmap.gss in Heqo.
    rewrite LIVE in Heqo. inv Heqo.
    traceEq.
    constructor; auto.
    eapply pop_stage_match_stack; eauto. erewrite Mem.support_free; eauto.
    apply agree_set_other; auto. apply agree_set_other; auto.
    apply agree_nextinstr. apply agree_set_other; auto.
    eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
    inv SC. erewrite <- Mem.support_free in H11; eauto.
    apply Mem.astack_pop_stage in H3. destruct H3. rewrite H3 in H11. inv H11. auto.
    erewrite <- Mem.support_free in SPC; eauto.
    apply Mem.astack_pop_stage in H3; eauto. destruct H3. rewrite H3 in SPC.
    inv SPC. destr_in H7.

- (* internal function *)
  exploit functions_translated; eauto. intros (b & tf & A & B & C). monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (code_size instr_size (fn_code x0))); inv EQ1.
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1. destr_in EQ2. inv EQ2.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [D E]].
  apply Mem.push_stage_extends in E.
  exploit Mem.record_frame_extends. apply E. eauto. intros [m2' [D' E']].
  exploit Mem.storev_extends. eexact E'. eexact H2. eauto. eauto.
  intros [m3' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H3. eauto. eauto.
  intros [m4' [P Q]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  inv ATPC. eauto.
  simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
  simpl. eapply transf_function_stacksize_pos in EQ as EQ'. destr.
  inv ATPC. rewrite D. rewrite D'.  simpl in F, P.
  replace (chunk_of_type Tptr) with Mptr in F, P by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite ATLR. rewrite F.
  rewrite (sp_val _ _ _ AG) in P. rewrite P. eauto.
  assert (Mem.sup_include (Mem.support m') (Mem.support m4')).
  {
    apply Mem.sup_include_alloc in D.
    apply Mem.sup_include_record_frame in D'.
    apply Mem.support_store in F.
    apply Mem.support_store in P.
    rewrite P, F. red. intros. apply D', D. auto.
  }
  assert (Mem.sup_include (Mem.support m1') (Mem.support m4')).
  {
    apply Mem.sup_include_record_frame in D'.
    apply Mem.support_store in F.
    apply Mem.support_store in P.
    rewrite P, F. auto.
  }
  econstructor; eauto.
  eapply match_stack_incr_bound. apply H4. auto.
  constructor. apply H5. eapply Mem.valid_new_block; eauto.
  eapply alloc_sp_fresh; eauto. eapply match_stack_support; eauto.
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss. rewrite undef_regs_other.
  repeat rewrite Pregmap.gso; auto with asmgen.
  inv ATPC. simpl. constructor; eauto.
  unfold fn_code. eapply code_tail_next_int; eauto. simpl in g. simpl. lia.
  constructor.   simpl; intros. intuition congruence.  exists nil. eauto.
  apply agree_nextinstr_nf. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
  congruence.
  erewrite <- Mem.support_storev; eauto. erewrite <- Mem.support_storev; eauto.
  apply Mem.astack_record_frame in H1. destruct H1 as (hd & tl & AS1 & AS2).
  simpl in AS1. inv AS1. rewrite AS2. simpl.
  assert ((Mach.fn_stacksize f) = frame_size (mk_frame stk (Mach.fn_stacksize f))).
  simpl. rewrite Z.max_r. auto. lia. rewrite H1. simpl. rewrite Z.max_r. 2: auto.
  remember (mk_frame stk (Mach.fn_stacksize f)) as fr. rewrite H1.
  constructor; auto. erewrite Mem.astack_alloc. 2: eauto. eauto.
  erewrite <- Mem.support_storev; eauto. erewrite <- Mem.support_storev; eauto.
  apply Mem.astack_record_frame in H1 as ASTKR. apply Mem.astack_alloc in H0 as ASTKA.
  destruct ASTKR as [hd [tl [X Y]]]. rewrite Y. simpl in X. inv X.
  simpl. constructor. rewrite ASTKA. eauto. reflexivity.
  intros. Simplifs. eapply agree_sp; eauto.

- (* external function *)
  exploit functions_translated; eauto.
  intros (b & tf & A & B & C). simpl in B. inv B.
  assert (exists b, inner_sp init_sup (rs0#SP) = Some b) as [? LIVE].
    inv AG. rewrite agree_sp.
    pose proof (parent_sp_ptr _ _ _ _ _ _ STACKS) as [? [? ->]].
    unfold inner_sp. eexists. eauto.
  exploit extcall_arguments_match; eauto.
  intros [args' [D E]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  inv ATPC. auto.
  { (* rs SP Tptr *)
    erewrite agree_sp by eauto.
    destruct s. simpl. auto.
    inv SPC. destruct s; simpl; rewrite H6; constructor.
  }
  { (* rs RA Tint *)
    rewrite ATLR.
    eapply parent_ra_type; eauto.
  }
  { (* rs SP not Vundef *)
    erewrite agree_sp by eauto.
    destruct s. inv WFRA.
    inv SPC. simpl. destruct s; subst; congruence.
  }
  { (* rs RA not Vundef *)
    rewrite ATLR.
    eapply parent_ra_def; eauto.
  }
  unfold loc_external_result. clear. destruct (loc_result (ef_sig ef)); simpl; try split;
                                       apply preg_of_not_SP.
  intros. rewrite ATLR. subst.
  eapply has_code_parent_ra_after_call; eauto. eapply live_is_internal; eauto.
  inv AG. congruence.
  assert (Mem.sup_include (Mem.support m'0) (Mem.support m2'))
    by eauto using Mem.unchanged_on_support.
  econstructor; eauto.
  eapply match_stack_incr_bound; eauto.
  unfold loc_external_result. do 2 (apply agree_set_other; auto). apply agree_set_pair; auto.
  apply agree_undef_caller_save_regs; auto.
  erewrite <- external_call_astack; eauto.
  erewrite <- external_call_astack; eauto.
  rewrite Pregmap.gso by discriminate.
  unfold set_pair, loc_external_result. induction loc_result; cbn.
  unfold undef_caller_save_regs. rewrite Pregmap.gso by (destruct r; discriminate).
    destruct preg_eq; try congruence. auto.
  rewrite Pregmap.gso by (destruct rlo; cbn; congruence).
  rewrite Pregmap.gso by (destruct rhi; cbn; congruence).
  auto.

- (* return *)
  inv STACKS. simpl in *.
  right. split. lia. split. auto.
  erewrite agree_sp in LIVE by eauto.
  rewrite LIVE in H6. inv H6.
  econstructor; eauto.
  inv CODE. eauto.
  inv CODE. rewrite <- Genv.find_funct_find_funct_ptr in H4. rewrite H4 in FINDF. inv FINDF.
  destruct TAIL as (A&B&C&D). exists (A++ (Mcall B C::nil)). rewrite app_ass. auto.
  inv WFRA. auto. rewrite H4 in SC. auto. congruence.
Qed.

End WITH_WORLD.

Let cc : callconv li_mach li_asm := cc_mach ext @ cc_mach_asm.

Lemma transf_initial_states:
  forall rs0 nb0 q1 q2 st1, match_query cc (se, tt, (rs0, nb0)) q1 q2 -> Mach.initial_state ge q1 st1 ->
  exists st2, Asm.initial_state tge q2 st2 /\ match_states rs0 nb0 st1 st2.
Proof.
  intros. destruct H as (qi & Hq1i & Hqi2). destruct Hq1i. inv Hqi2. inv H0.
  CKLR.uncklr. setoid_rewrite ext_lessdef in H6.
  edestruct functions_translated as (b & tf & ? & Htf & Hpc1); eauto.
  inversion H1; try congruence.
  inversion H3; try congruence.
  inversion H5; try congruence.
  subst.
  monadInv Htf.
  econstructor; split.
  - econstructor; eauto.
    rewrite <- H10, Hpc1, Genv.find_funct_find_funct_ptr, H0. eauto.
  - constructor; cbn; eauto.
    + constructor; eauto.
    + constructor; eauto.
    + constructor; eauto.
    + split; auto.
      setoid_rewrite <- H20; eauto.
    + inv H7. rewrite mext_sup. constructor.
    + inv H19. inv H7. rewrite mext_sup, <- H8, H9. simpl. constructor; auto. econstructor. eauto.
Qed.

Lemma transf_external_states:
  forall rs0 nb0 st1 st2 q1, match_states rs0 nb0 st1 st2 -> Mach.at_external ge st1 q1 ->
  exists wx q2, Asm.at_external tge st2 q2 /\ match_query cc wx q1 q2 /\ match_senv cc wx se se /\
  forall r1 r2 st1', match_reply cc wx r1 r2 -> Mach.after_external st1 r1 st1' ->
  exists st2', Asm.after_external nb0 st2 r2 st2' /\ match_states rs0 nb0 st1' st2'.
Proof.
  intros rs0 nb0 st1 st2 q1 Hst Hq1. inv Hq1. inv Hst.
  edestruct functions_translated as (fb & tf & TFIND & Htf & ?); eauto.
  subst. inv ATPC. monadInv Htf.
  eexists (se, tt, (rs1, Mem.support m')), (rs1, m'). intuition idtac.
  - econstructor.
    rewrite <- H3. cbn. destruct Ptrofs.eq_dec; try congruence. inv H0. eauto.
  - eexists (mq _ _ _ (fun r => rs1 (preg_of r)) m'). split.
    + econstructor; intros; uncklr; eauto.
      * congruence.
      * eapply agree_sp_def; eauto.
      * eapply parent_ra_def; eauto.
      * eapply agree_mregs; eauto.
    + rewrite H3. rewrite <- ATLR. erewrite <- (agree_sp _ _ _ AG).
      constructor; auto.
      * congruence.
      * erewrite agree_sp; eauto.
        inv STACKS; cbn; eauto.
        eapply valid_blockv_support; eauto.
      * rewrite ATLR. eapply parent_ra_def; eauto.
      * rewrite ATLR. eapply parent_ra_type. eauto.
      * inv SPC. destruct s; simpl in H2. inv WFRA. congruence.
        inv MEXT. rewrite <- mext_sup.
        destruct (Mem.astack (Mem.support m)) eqn:?; simpl in H1. congruence. destr_in H1.
        constructor. inv AG. rewrite agree_sp. inv H1.
        destruct s; simpl in H2, H4. inv WFRA. inv H2. simpl. auto.
  - cbn. auto.
  - inv H2. cbn in H1. destruct H1 as (ri & ([ ] & _ & Hr1i) & Hri2).
    inv Hri2. inv Hr1i.
    assert (exists b, inner_sp nb0 (rs'0#SP) = Some b) as [? LIVE].
      rewrite H1. inv AG. rewrite agree_sp.
      pose proof (parent_sp_ptr _ _ _ _ _ _ STACKS) as [? [? ->]].
      eexists. unfold inner_sp. eauto.
    eexists. split; econstructor; eauto.
    + eapply match_stack_incr_bound; eauto.
    + setoid_rewrite ext_lessdef in H10. split; auto.
      * rewrite H1. eapply agree_sp; eauto.
      * eapply agree_sp_def; eauto.
      * intro. rewrite <- H6. eauto.
    + CKLR.uncklr. inv H12. inv MEXT. rewrite mext_sup, <- H5, <- mext_sup0. auto.
    + CKLR.uncklr. inv H12. inv MEXT. rewrite mext_sup, <- H5, <- mext_sup0. auto.
    + congruence.
Qed.

Lemma transf_final_states:
  forall rs0 nb0 st1 st2 r1, match_states rs0 nb0 st1 st2 -> Mach.final_state st1 r1 ->
  exists r2, Asm.final_state st2 r2 /\ match_reply cc (se, tt, (rs0, nb0)) r1 r2.
Proof.
  intros. inv H0. inv H. cbn in *.
  inv STACKS. erewrite agree_sp in LIVE; eauto.
  destruct live. { destruct H5; cbn in *. destruct Mem.sup_dec; congruence. }
  exists (rs1, m'). split.
  - constructor.
  - exists (mr (fun r => rs1 (preg_of r)) m'). split.
    + exists tt. split; [rauto | ]. constructor; intros; uncklr; eauto.
      eapply agree_mregs; eauto.
    + constructor; eauto.
      eapply agree_sp; eauto.
      inv SC. inv MEXT. congruence.
Qed.

Theorem transf_program_unchange_rsp init_sup:
  (forall b, Genv.find_funct_ptr ge b = None -> Genv.find_funct_ptr tge b = None) ->
  asm_prog_unchange_rsp instr_size init_sup tge.
Proof.
  intros.
  red. split.
  red. intros.
  destruct (Genv.find_funct_ptr ge b) eqn:?.
  exploit functions_translated; eauto.
    instantiate (2 := Vptr b Ptrofs.zero). simpl. rewrite dec_eq_true. eauto.
  intros (tfb & tf & FFP & TF & EQ). inv EQ.
  destruct f0; simpl in TF; monadInv  TF; try congruence. rewrite H0 in FFP. inv FFP.
  assert (asm_code_no_rsp instr_size init_sup (fn_code x)).
  apply check_asm_code_no_rsp_correct.
  eapply asmgen_no_change_rsp; eauto.
  apply H2. eapply find_instr_eq; eauto.
  apply H in Heqo. congruence.
  split. apply asm_builtin_unchange_rsp_valid.
  apply asm_external_unchange_rsp_valid.
Qed.

End PRESERVATION.

Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (cc_mach ext @ cc_mach_asm) (cc_mach ext @ cc_mach_asm)
    (Mach.semantics (return_address_offset instr_size) prog)
    (Asm.semantics instr_size tprog).
Proof.
  set (ms := fun '(se, tt, (rs0, nb0)) s1 '(nb, s2) =>
               match_states prog se rs0 nb0 s1 s2 /\ nb = nb0). 
  fsim eapply forward_simulation_star with
      (match_states := ms w)
      (measure := measure);
    destruct w as [[se [ ]] [rs0 nb0]], Hse as [[ ] [ ]];
    intros.
  - destruct H as (qi & Hq1i & Hqi2). destruct Hq1i. inv Hqi2. cbn.
    setoid_rewrite ext_lessdef in H2. inv H2; try congruence.
    uncklr. inv H0; try congruence.
    eapply (Genv.is_internal_transf_partial_id MATCH); eauto.
    intros [|] ? Hf; monadInv Hf; auto.
  - edestruct transf_initial_states as (s2 & Hs2 & Hs); eauto.
    exists (Mem.support (snd q2), s2). cbn. intuition auto.
    destruct H as (? & ? & ?). destruct H1. auto.
  - destruct s2 as [nb s2], H as [H Hnb]; subst.
    edestruct transf_final_states as (? & ? & ?); cbn; eauto.
  - destruct s2 as [nb s2], H as [H Hnb]; subst.
    edestruct transf_external_states as (wA & q2 & Hq2 & Hq & Hse & Hr); eauto.
    exists wA, q2. intuition auto.
    edestruct Hr as (s2' & Hs2' & Hs'); eauto.
    eexists (_, s2'); cbn; eauto.
  - destruct s2 as [nb s2], H0 as [H0 Hnb]; subst.
    edestruct step_simulation as [(s2' & Hs2' & Hs') | ?]; cbn in *; intuition eauto 10.
    left. eexists (_, _). intuition eauto.
    revert Hs2'. generalize nb0, (Genv.globalenv se1 tprog); clear; intros.
    pattern s2, t, s2'. revert s2 t s2' Hs2'. apply plus_ind2; intros.
    * apply plus_one. auto.
    * eapply plus_trans; eauto.
      apply plus_one. auto.
Qed.

End INSTRSIZE.
