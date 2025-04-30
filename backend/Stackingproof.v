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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib Errors.
Require Import Integers AST Linking.
Require Import Values Memory Separation Events Globalenvs Smallstep.
Require Import LTL Op Locations Linear Mach.
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Import Stacking.
Require Import LanguageInterface Invariant cklr.Inject cklr.InjectFootprint.
Require CallConv.

Local Open Scope sep_scope.
Local Opaque Z.add Z.mul Z.divide.

Definition match_prog (p: Linear.program) (tp: Mach.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

(** * Basic properties of the translation *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark align_type_chunk:
  forall ty, align_chunk (chunk_of_type ty) = 4 * Locations.typealign ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma slot_outgoing_argument_valid:
  forall f ofs ty sg,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> slot_valid f Outgoing ofs ty = true.
Proof.
  intros. exploit loc_arguments_acceptable_2; eauto. intros [A B].
  unfold slot_valid. unfold proj_sumbool.
  rewrite zle_true by lia.
  rewrite pred_dec_true by auto.
  auto.
Qed.

Lemma load_result_inject:
  forall j ty v v',
  Val.inject j v v' -> Val.has_type v ty -> Val.inject j v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros until v'; unfold Val.has_type, Val.load_result; destruct Archi.ptr64;
  destruct 1; intros; auto; destruct ty; simpl;
  try contradiction; try discriminate; econstructor; eauto.
Qed.

Section PRESERVATION.

Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Let step := Mach.step return_address_offset.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse tprog.

Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
  intros; discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Ptrofs.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. lia.
  intros; discriminate.
Qed.

Lemma bound_outgoing_no_overflow:
  fe_ofs_arg + 4 * (bound_outgoing (function_bounds f)) <= Ptrofs.max_unsigned.
Proof.
  pose proof size_no_overflow. subst b fe.
  etransitivity; eauto; clear.
  cbv [fe_ofs_arg fe_size make_env].
  assert ((if Archi.ptr64 then 8 else 4) > 0) by (destruct Archi.ptr64; extlia).
  repeat
    match goal with
    | |- context [align ?x ?a] =>
      lazymatch goal with
      | H: x <= align x a |- _ => fail
      | _ => assert (x <= align x a) by (apply (align_le x a); extlia)
      end
    | |- context [size_callee_save_area ?b ?x] =>
      lazymatch goal with
      | H: x <= size_callee_save_area b x |- _ => fail
      | _ => assert (x <= size_callee_save_area b x)
          by apply size_callee_save_area_incr
      end
    end.
  pose proof (bound_local_pos (function_bounds f)).
  pose proof (bound_outgoing_pos (function_bounds f)).
  pose proof (bound_stack_data_pos (function_bounds f)).
  extlia.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Z.le_max_l.
Qed.

(** * Memory assertions used to describe the contents of stack frames *)

(** Accessing the stack frame using [load_stack] and [store_stack]. *)

Lemma contains_get_stack:
  forall spec m ty sp ofs,
  m |= contains (chunk_of_type ty) sp ofs spec ->
  exists v, load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v /\ spec v.
Proof.
  intros. unfold load_stack.
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply loadv_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

Lemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= hasvalue (chunk_of_type ty) sp ofs v ->
  load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) = Some v.
Proof.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). congruence.
Qed.

Lemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= contains (chunk_of_type ty) sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr ofs) v = Some m'
  /\ m' |= contains (chunk_of_type ty) sp ofs spec ** P.
Proof.
  intros. unfold store_stack.
  replace (Val.offset_ptr (Vptr sp Ptrofs.zero) (Ptrofs.repr ofs)) with (Vptr sp (Ptrofs.repr ofs)).
  eapply storev_rule; eauto.
  simpl. rewrite Ptrofs.add_zero_l; auto.
Qed.

(** [contains_locations j sp pos bound sl ls] is a separation logic assertion
  that holds if the memory area at block [sp], offset [pos], size [4 * bound],
  reflects the values of the stack locations of kind [sl] given by the
  location map [ls], up to the memory injection [j].

  Two such [contains_locations] assertions will be used later, one to
  reason about the values of [Local] slots, the other about the values of
  [Outgoing] slots. *)

Program Definition contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint := fun b ofs =>
    b = sp /\ pos <= ofs < pos + 4 * bound
|}.
Next Obligation.
  intuition auto.
- red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit H4; eauto. intros (v & A & B). exists v; split; auto.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros. rewrite size_type_chunk, typesize_typesize in H8.
  split; auto. lia.
Qed.
Next Obligation.
  eauto with mem.
Qed.

Remark valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) sp (pos + 4 * ofs) p.
Proof.
  intros; split.
- red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  apply H0. rewrite size_type_chunk, typesize_typesize in H4. lia.
- rewrite align_type_chunk. apply Z.divide_add_r.
  apply Z.divide_trans with 8; auto.
  exists (8 / (4 * typealign ty)); destruct ty; reflexivity.
  apply Z.mul_divide_mono_l. auto.
Qed.

Lemma get_location:
  forall m j sp pos bound sl ls ofs ty,
  m |= contains_locations j sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) = Some v
  /\ Val.inject j (ls (S sl ofs ty)) v.
Proof.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. intros (v & U & V). exists v; split; auto.
  unfold load_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; auto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). lia.
Qed.

Lemma set_location:
  forall m j sp pos bound sl ls P ofs ty v v',
  m |= contains_locations j sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (pos + 4 * ofs)) v' = Some m'
  /\ m' |= contains_locations j sp pos bound sl (Locmap.set (S sl ofs ty) v ls) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct Mem.valid_access_store as [m' STORE].
  eapply valid_access_location; eauto.
  assert (PERM: Mem.range_perm m' sp pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto with mem. }
  exists m'; split.
- unfold store_stack; simpl. rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr; eauto.
  unfold Ptrofs.max_unsigned. generalize (typesize_pos ty). lia.
- simpl. intuition auto.
+ unfold Locmap.set.
  destruct (Loc.eq (S sl ofs ty) (S sl ofs0 ty0)); [|destruct (Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  eapply Mem.load_store_similar_2; eauto. lia.
  apply Val.load_result_inject; auto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X; eapply Mem.load_store_other; eauto.
  destruct d. congruence. right. rewrite ! size_type_chunk, ! typesize_typesize. lia.
* (* overlapping locations *)
  destruct (Mem.valid_access_load m' (chunk_of_type ty0) sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem.
  eapply valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto.
  eapply Mem.store_unchanged_on; eauto.
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. lia.
Qed.

Lemma initial_locations:
  forall j sp pos bound P sl ls m,
  m |= range sp pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (S sl ofs ty) = Vundef) ->
  m |= contains_locations j sp pos bound sl ls ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem.
  destruct (Mem.valid_access_load m (chunk_of_type ty) sp (pos + 4 * ofs)) as [v LOAD].
  eapply valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed.

Lemma contains_locations_exten:
  forall ls ls' j sp pos bound sl,
  (forall ofs ty, Val.lessdef (ls' (S sl ofs ty)) (ls (S sl ofs ty))) ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j sp pos bound sl ls').
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; split; auto. 
  specialize (H ofs ty). inv H. congruence. auto. 
Qed.

Lemma contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j' sp pos bound sl ls).
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; eauto.
Qed.

(** [contains_callee_saves j sp pos rl ls] is a memory assertion that holds
  if block [sp], starting at offset [pos], contains the values of the
  callee-save registers [rl] as given by the location map [ls],
  up to the memory injection [j].  The memory layout of the registers in [rl]
  is the same as that implemented by [save_callee_save_rec]. *)


Fixpoint contains_callee_saves (j: meminj) (sp: block) (pos: Z) (rl: list mreg) (ls: locset) (rs: regset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      contains (chunk_of_type ty) sp pos1 (fun v => Val.inject j (ls (R r)) v /\ rs r = v)
      ** contains_callee_saves j sp (pos1 + sz) rl ls rs
  end.

Lemma contains_callee_saves_incr:
  forall j j' sp ls rs,
  inject_incr j j' ->
  forall rl pos,
  massert_imp (contains_callee_saves j sp pos rl ls rs)
              (contains_callee_saves j' sp pos rl ls rs).
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_1; auto. apply contains_imp.
  intros v [A B]. split; eauto.
Qed.

Lemma contains_callee_saves_exten:
  forall j sp ls ls' rl pos rs rs',
    (forall r, In r rl -> ls' (R r) = ls (R r)) ->
    (forall r, In r rl -> rs' r = rs r) ->
  massert_eqv (contains_callee_saves j sp pos rl ls rs)
              (contains_callee_saves j sp pos rl ls' rs').
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_2; auto. rewrite H by auto. rewrite H0 by auto. reflexivity.
Qed.

(** Separation logic assertions describing the stack frame at [sp].
  It must contain:
  - the values of the [Local] stack slots of [ls], as per [contains_locations]
  - the values of the [Outgoing] stack slots of [ls], as per [contains_locations]
  - the [parent] pointer representing the back link to the caller's frame
  - the [retaddr] pointer representing the saved return address
  - the initial values of the used callee-save registers as given by [ls0],
    as per [contains_callee_saves].

In addition, we use a nonseparating conjunction to record the fact that
we have full access rights on the stack frame, except the part that
represents the Linear stack data. *)

Definition frame_contents_1 (j: meminj) (sp: block) (ls ls0: locset) (rs0: regset) (parent retaddr: val) :=
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations j sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** hasvalue Mptr sp fe.(fe_ofs_link) parent
 ** hasvalue Mptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 rs0.

Definition frame_contents (j: meminj) (sp: block) (ls ls0: locset) (rs0 : regset) (parent retaddr: val) :=
  mconj (frame_contents_1 j sp ls ls0 rs0 parent retaddr)
        (range sp 0 fe.(fe_stack_data) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

(** Accessing components of the frame. *)


Lemma frame_get_local:
  forall ofs ty j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) = Some v
  /\ Val.inject j (ls (S Local ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  eapply get_location; eauto.
Qed.

Lemma frame_get_outgoing:
  forall ofs ty j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (ls (S Outgoing ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  eapply get_location; eauto.
Qed.

Lemma frame_get_parent:
  forall j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_link)) = Some parent.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

Lemma frame_get_retaddr:
  forall j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  load_stack m (Vptr sp Ptrofs.zero) Tptr (Ptrofs.repr fe.(fe_ofs_retaddr)) = Some retaddr.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick4 in H. rewrite <- chunk_of_Tptr in H.
  eapply hasvalue_get_stack; eauto.
Qed.

(** Assigning a [Local] or [Outgoing] stack slot. *)


Lemma frame_set_local:
  forall ofs ty v v' j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Local ofs ty) v ls) ls0 rs0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0.
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

Lemma frame_set_outgoing:
  forall ofs ty v v' j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Ptrofs.zero) ty (Ptrofs.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Outgoing ofs ty) v ls) ls0 rs0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0.
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

(** Invariance by change of location maps. *)

Lemma frame_contents_exten:
  forall ls ls0 ls' ls0' rs0 rs0' j sp parent retaddr P m,
  (forall ofs ty, Val.lessdef (ls' (S Local ofs ty)) (ls (S Local ofs ty))) ->
  (forall ofs ty, Val.lessdef (ls' (S Outgoing ofs ty)) (ls (S Outgoing ofs ty))) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  (forall r, In r b.(used_callee_save) -> rs0' r = rs0 r) ->
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  m |= frame_contents j sp ls' ls0' rs0' parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite  <- contains_callee_saves_exten by eauto.
  assumption.
Qed.

(** Invariance by assignment to registers. *)


Corollary frame_set_reg:
  forall r v j sp ls ls0 rs0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.set (R r) v ls) ls0 rs0 parent retaddr ** P.
Proof.
  intros. eapply frame_contents_exten; eauto.
Qed.

Corollary frame_undef_regs:
  forall j sp ls ls0 rs0 parent retaddr m P rl,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  m |= frame_contents j sp (LTL.undef_regs rl ls) ls0 rs0 parent retaddr ** P.
Proof.
Local Opaque sepconj.
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto.
Qed.

Corollary frame_callee_save_eq:
  forall j sp ls ls0 rs0 rs0' parent retaddr m P,
    m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
    (forall r, is_callee_save r = true -> rs0 r = rs0' r) ->
    m |= frame_contents j sp ls ls0 rs0' parent retaddr ** P.
Proof.
  intros. eapply frame_contents_exten. eauto. eauto. 3: eauto.
  eauto. intros. rewrite <- H0; eauto.
  eapply used_callee_save_prop; eauto.
Qed.

Corollary frame_set_regpair:
  forall j sp ls0 rs0 parent retaddr m P p v ls,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setpair p v ls) ls0 rs0 parent retaddr ** P.
Proof.
  intros. destruct p; simpl.
  apply frame_set_reg; auto.
  apply frame_set_reg; apply frame_set_reg; auto.
Qed.

Corollary frame_set_res:
  forall j sp ls0 rs0 parent retaddr m P res v ls,
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setres res v ls) ls0 rs0 parent retaddr ** P.
Proof.
  induction res; simpl; intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed.

(** Invariance by change of memory injection. *)

Lemma frame_contents_incr:
  forall j sp ls ls0 rs0 parent retaddr m P j',
  m |= frame_contents j sp ls ls0 rs0 parent retaddr ** P ->
  inject_incr j j' ->
  m |= frame_contents j' sp ls ls0 rs0 parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_locations_incr j j') by auto.
  erewrite  <- contains_callee_saves_incr by eauto.
  assumption.
Qed.


(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, Val.inject j (ls (R r)) (rs r).

(** Agreement over locations *)

Record agree_locs (ls ls0: locset) : Prop :=
  mk_agree_locs {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty,
       In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters f.(Linear.fn_sig))) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)
}.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> Val.inject j (ls (R r)) (rs r).
Proof.
  intros. auto.
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> Val.inject_list j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_pair:
  forall j p v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setpair p v ls) (set_pair p v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_regs_set_reg; auto.
- apply agree_regs_set_reg. apply agree_regs_set_reg; auto.
  apply Val.hiword_inject; auto. apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (set_res res v' rs).
Proof.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]].
  rewrite A. constructor.
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed.

Lemma agree_regs_undef_caller_save_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_caller_save_regs ls) (Mach.undef_caller_save_regs rs).
Proof.
  intros; red; intros. 
  unfold LTL.undef_caller_save_regs, Mach.undef_caller_save_regs. 
  destruct (is_callee_save r); auto. 
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_locs] *)

(** Preservation under assignment of machine register. *)

Lemma agree_locs_set_reg:
  forall ls ls0 r v,
  agree_locs ls ls0 ->
  mreg_within_bounds b r ->
  agree_locs (Locmap.set (R r) v ls) ls0.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  is_callee_save r = false -> mreg_within_bounds b r.
Proof.
  intros; red; intros. congruence.
Qed.

Lemma reg_within_bounds_caller_save:
  forall r,
  ~ mreg_within_bounds b r -> is_callee_save r = true.
Proof.
  intros. destruct (is_callee_save r) eqn:?; eauto.
  elim H. red. intros. congruence.
Qed.

Lemma agree_locs_set_pair:
  forall ls0 p v ls,
  agree_locs ls ls0 ->
  forall_rpair (fun r => is_callee_save r = false) p ->
  agree_locs (Locmap.setpair p v ls) ls0.
Proof.
  intros.
  destruct p; simpl in *.
  apply agree_locs_set_reg; auto. apply caller_save_reg_within_bounds; auto.
  destruct H0.
  apply agree_locs_set_reg; auto. apply agree_locs_set_reg; auto.
  apply caller_save_reg_within_bounds; auto. apply caller_save_reg_within_bounds; auto.
Qed.

Lemma agree_locs_set_res:
  forall ls0 res v ls,
  agree_locs ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs (Locmap.setres res v ls) ls0.
Proof.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed.

Lemma agree_locs_undef_regs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_locs_set_reg; auto.
Qed.

Lemma agree_locs_undef_locs_1:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> is_callee_save r = false) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_regs; eauto.
  intros. apply caller_save_reg_within_bounds. auto.
Qed.

Lemma agree_locs_undef_locs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  existsb is_callee_save regs = false ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_locs_1; eauto.
  intros. destruct (is_callee_save r) eqn:CS; auto.
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence.
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_locs_set_slot:
  forall ls ls0 sl ofs ty v,
  agree_locs ls ls0 ->
  slot_writable sl = true ->
  agree_locs (Locmap.set (S sl ofs ty) v ls) ls0.
Proof.
  intros. destruct H; constructor; intros.
- rewrite Locmap.gso; auto. red; auto.
- rewrite Locmap.gso; auto. red. left. destruct sl; discriminate.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_locs_return:
  forall ls ls0 ls',
  agree_locs ls ls0 ->
  agree_callee_save ls' ls ->
  agree_locs ls' ls0.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite <- agree_incoming0 by auto. apply H0. congruence.
Qed.


Definition agree_unused_rs (rs0 rs :regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> rs0 r = rs r.


Lemma agree_unused_rs_set_reg : forall rs rs0 r v,
    agree_unused_rs rs rs0 ->
    mreg_within_bounds b r ->
    agree_unused_rs (Regmap.set r v rs) rs0.
Proof.
  intros. red. intros. red in H.
  rewrite Regmap.gso. auto. red. intuition congruence.
Qed.

Lemma agree_unused_rs_undef_regs_1:
  forall rs0 regs rs ,
  agree_unused_rs rs rs0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_unused_rs (undef_regs regs rs) rs0.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_unused_rs_set_reg; auto.
Qed.

Lemma agree_unused_rs_undef_regs:
  forall rs0 regs rs,
    agree_unused_rs rs rs0 ->
    existsb is_callee_save regs = false ->
  agree_unused_rs (undef_regs regs rs) rs0.
Proof.
  intros. eapply agree_unused_rs_undef_regs_1; eauto.
  intros. destruct (is_callee_save r) eqn:CS; auto.
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence. congruence.
Qed.

Lemma agree_unused_rs_set_res:
  forall rs0 res v rs,
  agree_unused_rs rs rs0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_unused_rs (set_res res v rs) rs0.
Proof.
  induction res; simpl; intros.
- eapply agree_unused_rs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed.

(** ** Properties of destroyed registers. *)

Definition no_callee_saves (l: list mreg) : Prop :=
  existsb is_callee_save l = false.

Ltac ByCases :=
  reflexivity ||
  match goal with
  | |- no_callee_saves (match ?x with _ => _ end) => destruct x; ByCases
  | _ => idtac
  end.

Remark destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
Proof.
Local Transparent destroyed_by_op.
  intros; unfold destroyed_by_op; ByCases.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
Proof.
Local Transparent destroyed_by_load.
  intros; unfold destroyed_by_load; ByCases.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
Proof.
Local Transparent destroyed_by_store.
  intros; unfold destroyed_by_store; ByCases.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, no_callee_saves (destroyed_by_cond cond).
Proof.
Local Transparent destroyed_by_cond.
  intros; unfold destroyed_by_cond; ByCases.
Qed.

Remark destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
Proof.
  red; reflexivity.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, no_callee_saves (destroyed_by_setstack ty).
Proof.
  unfold no_callee_saves; destruct ty; reflexivity.
Qed.

Remark destroyed_at_function_entry_caller_save:
  no_callee_saves destroyed_at_function_entry.
Proof.
  red; reflexivity.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
Proof.
Local Transparent destroyed_by_setstack destroyed_at_function_entry.
  unfold incl; destruct ty; simpl; tauto.
Qed.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Lemma reg_type_64 : forall r, mreg_type r = Tany64.
Proof. intros. destruct r; eauto. Qed.

Lemma reg_well_type : forall rs r, Val.has_type (rs r) (mreg_type r).
Proof. intros. rewrite reg_type_64. destruct (rs r); constructor. Qed.

Section SAVE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable vf: val.
Variable sp: block.
Variable ls: locset.
Variable rs0: regset.

Hypothesis ls_temp_undef:
  forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: forall r, Val.has_type (ls (R r)) (mreg_type r).


Lemma save_callee_save_rec_correct:
  forall k l pos rs m P,
  (forall r, In r l -> is_callee_save r = true) ->
  m |= range sp pos (size_callee_save_area_rec l pos) ** P ->
  agree_regs j ls rs ->
  (forall r, In r l -> rs0 r = rs r) ->
  exists rs', exists m',
     star step tge
        (State cs vf (Vptr sp Ptrofs.zero) (save_callee_save_rec l pos k) rs m)
     E0 (State cs vf (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp pos l ls rs0 ** P
  /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
  /\ agree_regs j ls rs'
  /\ agree_unused_rs rs' rs
  /\ Mem.support m = Mem.support m'
  /\ Mem.unchanged_on (fun b ofs => b <> sp) m m'.
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros until P; intros CS SEP AG RSS.
- exists rs, m.
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto.
  split; auto.
  split. red. intros. eauto.
  split; eauto with mem.
- set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (SZREC: pos1 + sz <= size_callee_save_area_rec l (pos1 + sz)) by (apply size_callee_save_area_rec_incr).
  assert (POS1: pos <= pos1) by (apply align_le; auto).
  assert (AL1: (align_chunk (chunk_of_type ty) | pos1)).
  { unfold pos1. apply Z.divide_trans with sz.
    unfold sz; rewrite <- size_type_chunk. apply align_size_chunk_divides.
    apply align_divides; auto. }
  apply range_drop_left with (mid := pos1) in SEP; [ | lia ].
  apply range_split with (mid := pos1 + sz) in SEP; [ | lia ].
  unfold sz at 1 in SEP. rewrite <- size_type_chunk in SEP.
  apply range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.inject j (ls (R r)) v' /\ rs0 r = v') (rs r)).
  eexact SEP. split.
  apply load_result_inject; [auto|apply wt_ls].
  erewrite Val.load_result_same. eauto. unfold ty. apply reg_well_type.
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs j ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite undef_regs_other by auto. apply AG. }
  assert (SAVE: forall r, In r l -> rs r = rs1 r).
  { intros. unfold rs1. rewrite undef_regs_other. auto.
    intro.
    generalize (destroyed_by_setstack_caller_save ty).
    intro. red in H1.
    assert ( existsb is_callee_save (destroyed_by_setstack ty) = true).
    eapply existsb_exists. exists r0. split. auto. eauto. congruence.
  }
  rewrite sep_swap in SEP.
  exploit (IHl (pos1 + sz) rs1 m1); eauto. intros. rewrite RSS. eauto. right. auto.
  intros (rs2 & m2 & A & B & C & D & E & F & G).
  exists rs2, m2.
  split. eapply star_left; eauto. constructor. exact STORE. auto. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. unfold store_stack in STORE; simpl in STORE. eapply Mem.perm_store_1; eauto.
  split.  eauto. split. 
  assert (agree_unused_rs rs1 rs). unfold rs1.
  eapply agree_unused_rs_undef_regs; eauto. red. intros. eauto.
  eapply  destroyed_by_setstack_caller_save.
  red. intros. rewrite E; eauto. split.
  erewrite Mem.support_storev. 2: eauto. auto.
  eapply Mem.unchanged_on_trans; eauto. eapply Mem.store_unchanged_on.
  apply STORE. eauto.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction.
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto.
  destruct (Loc.diff_dec (R a) (R r)); auto.
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition.
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto.
Qed.

Remark undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (LTL.undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto.
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed.


Lemma save_callee_save_correct:
  forall j ls ls0 rs sp cs fb k m P,
  m |= range sp fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  agree_callee_save ls ls0 ->
  agree_regs j ls rs ->
  let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) in
  let rs1 := undef_regs destroyed_at_function_entry rs in
  exists rs', exists m',
     star step tge
        (State cs fb (Vptr sp Ptrofs.zero) (save_callee_save fe k) rs1 m)
     E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 rs ** P
  /\ (forall ofs k p, Mem.perm m sp ofs k p -> Mem.perm m' sp ofs k p)
  /\ agree_regs j ls1 rs'
  /\ agree_unused_rs rs' rs
  /\ Mem.support m = Mem.support m'
  /\ Mem.unchanged_on (fun b ofs => b <> sp) m m'.
Proof.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1.
  exploit (save_callee_save_rec_correct j cs fb sp ls1 rs).
- intros. unfold ls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. unfold ls1. apply undef_regs_type. apply TY.
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- intros. unfold rs1. rewrite undef_regs_other. auto. intro.
  generalize (destroyed_at_function_entry_caller_save).
  intro. red in H1.
  assert ( existsb is_callee_save (destroyed_at_function_entry) = true).
  eapply existsb_exists. exists r. split. auto. 
  eapply used_callee_save_prop; eauto. congruence.
- clear SEP. intros (rs' & m' & EXEC & SEP & PERMS & AG' & AG'' & TE').
  exists rs', m'.
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten j sp ls0 ls1). exact SEP.
  intros. apply b.(used_callee_save_prop) in H.
    unfold ls1. rewrite LTL_undef_regs_others. unfold call_regs.
    apply AGCS; auto.
    red; intros.
    assert (existsb is_callee_save destroyed_at_function_entry = false)
       by  (apply destroyed_at_function_entry_caller_save).
    assert (existsb is_callee_save destroyed_at_function_entry = true).
    { apply existsb_exists. exists r; auto. }
    congruence.
    reflexivity.
    split. exact PERMS. split. exact AG'. split.
    assert (agree_unused_rs rs1 rs). unfold rs1. eapply agree_unused_rs_undef_regs. red. intros. eauto.
    eapply destroyed_at_function_entry_caller_save. red. intros. erewrite AG''; eauto.
    exact TE'.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

(* Lemma fe_size_eq: Linear.fn_stacksize f = fe_size fe. *)
(* Proof. *)
(*   unfold fe. unfold b. simpl. *)

Lemma function_prologue_correct:
  forall j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P
    (Hm: Mem.inject j m1 m1'),
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  agree_outgoing_arguments (Linear.fn_sig f) ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tptr -> Val.has_type ra Tptr ->
  m1' |= minjection j m1 ** globalenv_inject se tse j m1 ** P ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5', exists (Hm': Mem.inject j' m2 m5'),
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge
         (State cs fb (Vptr sp' Ptrofs.zero) (save_callee_save fe k) rs1 m4')
      E0 (State cs fb (Vptr sp' Ptrofs.zero) k rs' m5')
  /\ agree_regs j' ls1 rs'
  /\ agree_locs ls1 ls0
  /\ agree_unused_rs rs' rs
  /\ m5' |= frame_contents j' sp' ls1 ls0 rs parent ra ** minjection j' m2 ** globalenv_inject se tse j' m2 ** P
  /\ j' sp = Some(sp', fe.(fe_stack_data))
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ injp_acc (injpw j m1 m1' Hm) (injpw j' m2 m5' Hm').
Proof.
  intros until Hm; intros AGREGS AGCS AGARGS WTREGS LS1 RS1 ALLOC TYPAR TYRA SEP.
  (* assert (TEQ: thread_same j m1 m1'). inv Hm. auto. *)
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Stack layout info *)
Local Opaque b fe.
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto. simpl.
  intros LAYOUT1 LAYOUT2.
  (* Allocation step *)
  destruct (Mem.alloc m1' 0 (fe_size fe)) as [m2' sp'] eqn:ALLOC'.
  exploit alloc_parallel_rule_2.
  eexact SEP. (* eexact TEQ. *) eexact ALLOC. eexact ALLOC'.
  instantiate (1 := fe_stack_data fe). tauto.
  reflexivity.
  instantiate (1 := fe_stack_data fe + bound_stack_data b). rewrite Z.max_comm. reflexivity.
  generalize (bound_stack_data_pos b) size_no_overflow; lia.
  tauto.
  tauto.
  clear SEP. intros (j' & SEP (* & TEQ'  *) & INCR & SAME & INJSEP).  
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
    m2' |= mconj (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                 (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
           ** minjection j' m2 ** globalenv_inject se tse j' m2 ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  apply (frame_env_separated b) in SEP. replace (make_env b) with fe in SEP by auto.
  (* Store of parent *)
  rewrite sep_swap3 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = parent) parent (fun _ => True) m2' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m3' & STORE_PARENT & SEP).
  rewrite sep_swap3 in SEP.
  (* Store of return address *)
  rewrite sep_swap4 in SEP.
  apply (range_contains Mptr) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = ra) ra (fun _ => True) m3' Tptr).
  rewrite chunk_of_Tptr; eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m4' & STORE_RETADDR & SEP).
  rewrite sep_swap4 in SEP.
  (* Saving callee-save registers *)
  rewrite sep_swap5 in SEP.
  exploit (save_callee_save_correct j' ls ls0 rs); eauto.
  apply agree_regs_inject_incr with j; auto.
  replace (LTL.undef_regs destroyed_at_function_entry (call_regs ls)) with ls1 by auto.
  replace (undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & SAVE_CS & SEP & PERMS & AGREGS' & AGREGS''& TE' & UNC).
  rewrite sep_swap5 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations j'). eexact SEP. tauto.
  instantiate (1 := Local). instantiate (1 := ls1).
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  exploit (initial_locations j'). eexact SEP. tauto.
  instantiate (1 := Outgoing). instantiate (1 := ls1).
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents j' sp' ls1 ls0 rs parent ra ** minjection j' m2 ** globalenv_inject se tse j' m2 ** P).
  { eapply frame_mconj. eexact SEPCONJ.
    rewrite chunk_of_Tptr in SEP.
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    assert (forall ofs k p, Mem.perm m2' sp' ofs k p -> Mem.perm m5' sp' ofs k p).
    { intros. apply PERMS.
      unfold store_stack in STORE_PARENT, STORE_RETADDR.
      simpl in STORE_PARENT, STORE_RETADDR.
      eauto using Mem.perm_store_1. }
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  assert (Hm': Mem.inject j' m2 m5').
  {  eapply SEPFINAL. }
  assert (injp_acc (injpw j m1 m1' Hm) (injpw j' m2 m5' Hm')).
  {
    assert (Hm'0 : Mem.inject j' m2 m2').
    apply SEPCONJ. auto.
    assert (injp_acc (injpw j m1 m1' Hm) (injpw j' m2 m2' Hm'0)).
    eapply injp_acc_alloc'. apply ALLOC. eapply ALLOC'. eauto. eauto. eauto.
    inv H. apply Mem.support_storev in STORE_PARENT as SUP23.
    apply Mem.support_storev in STORE_RETADDR as SUP34.
    unfold store_stack in *. simpl in *.
    assert (UNC2: Mem.unchanged_on (fun b ofs => b <> sp') m1' m5').
    eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on; eauto.
    eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on; eauto.
    eauto.
    econstructor; eauto.
    - red. intros.
      erewrite <- Mem.loadbytes_unchanged_on_1; eauto.
      intros. simpl. intro. subst. 
      eapply Mem.fresh_block_alloc; eauto.
    - red. intros. inv UNC2. eapply unchanged_on_perm; eauto.
      intros. simpl. intro. subst. 
      eapply Mem.fresh_block_alloc; eauto.
    - split. rewrite <- TE'. rewrite <- SUP34. rewrite <- SUP23.
      inv H11. eauto.
      eapply mem_unchanged_on_trans_implies_valid. 2: eauto.
      eauto with mem. intros. intro. subst.
      eapply Mem.fresh_block_alloc; eauto.
      intros. eapply Mem.unchanged_on_contents. eauto. 
      simpl. intro. subst.  eapply Mem.fresh_block_alloc; eauto.
      eapply Mem.perm_valid_block; eauto. auto.
    (* - red. intros. exfalso. apply H2. eauto with mem. *)
  }
  
(* Conclusions *)
  exists j', rs2, m2', sp', m3', m4', m5', Hm'.
  split. auto.
  split. exact STORE_PARENT.
  split. exact STORE_RETADDR.
  split. eexact SAVE_CS.
  split. exact AGREGS'.
  split. rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold call_regs. apply AGCS.
    unfold mreg_within_bounds in H0; tauto.
    unfold call_regs. apply AGARGS. apply incoming_slot_in_parameters; auto.
  split. eauto.
  split. exact SEPFINAL.
  split. exact SAME.
  split. exact INCR. split. exact INJSEP. auto.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: val.
Variable sp: block.
Variable ls0: locset.
Variable rs0: regset.
Variable m: mem.

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> Val.inject j (ls0 (R r)) (rs r).


Lemma restore_callee_save_rec_correct:
  forall l ofs rs k,
  m |= contains_callee_saves j sp ofs l ls0 rs0 ->
  agree_unused ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs',
    star step tge
      (State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save_rec l ofs k) rs m)
   E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r, In r l -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r, In r l -> rs' r = rs0 r)
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros.
- (* base case *)
  exists rs. intuition auto. apply star_refl.
- (* inductive case *)
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (ofs1 := align ofs sz).
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (OFSLE: ofs <= ofs1) by (apply align_le; auto).
  assert (BOUND: mreg_within_bounds b r) by eauto.
  exploit contains_get_stack.
    eapply sep_proj1; eassumption.
  intros (v & LOAD & SPEC1 & SPEC2).
  exploit (IHl (ofs1 + sz) (rs#r <- v)).
    eapply sep_proj2; eassumption.
    red; intros. rewrite Regmap.gso. auto. intuition congruence.
    eauto.
  intros (rs' & A & B & C & D & E).
  exists rs'.
  split. eapply star_step; eauto.
    econstructor. exact LOAD. traceEq.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto.
    assert (r = r0) by tauto. subst r0.
    rewrite D by auto. rewrite Regmap.gss. exact SPEC1.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto.
    assert (r = r0) by tauto. subst r0.
    rewrite D by auto. rewrite Regmap.gss. eauto.
  split. intros.
    rewrite D by tauto. apply Regmap.gso. intuition auto.
  exact E.
Qed.

End RESTORE_CALLEE_SAVE.


Lemma restore_callee_save_correct:
  forall m j sp ls ls0 rs0 pa ra P rs k cs fb,
  m |= frame_contents j sp ls ls0 rs0 pa ra ** P ->
  agree_unused j ls0 rs ->
  agree_unused_rs rs0 rs ->
  exists rs',
    star step tge
       (State cs fb (Vptr sp Ptrofs.zero) (restore_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Ptrofs.zero) k rs' m)
  /\ (forall r,
         is_callee_save r = true -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r,
         is_callee_save r = true -> rs0 r = rs' r)
  /\ (forall r,
        is_callee_save r = false -> rs' r = rs r).
Proof.
  intros.
  unfold frame_contents, frame_contents_1 in H.
  apply mconj_proj1 in H. rewrite ! sep_assoc in H. apply sep_pick5 in H.
  exploit restore_callee_save_rec_correct; eauto.
  intros; unfold mreg_within_bounds; auto.
  intros (rs' & A & B & C & D & E).
  exists rs'.
  split. eexact A.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save b)).
  apply B; auto.
  rewrite D by auto. apply H0. unfold mreg_within_bounds; tauto.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save b)).
  rewrite C; eauto.
  rewrite D by auto. apply H1. unfold mreg_within_bounds; tauto.
  apply D. red; intros. apply (used_callee_save_prop b) in H3. congruence.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)


Lemma function_epilogue_correct:
  forall m' j sp' ls ls0 rs0 pa ra P m rs sp m1 k cs fb,
  m' |= frame_contents j sp' ls ls0 rs0 pa ra ** minjection j m ** P -> 
  agree_regs j ls rs ->
  agree_locs ls ls0 ->
  agree_unused_rs rs rs0 ->
  j sp = Some(sp', fe.(fe_stack_data)) ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star step tge
       (State cs fb (Vptr sp' Ptrofs.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Ptrofs.zero) k rs1 m')
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ (forall r, is_callee_save r = true -> rs0 r = rs1 r)
  /\ m1' |= minjection j m1 ** P.
Proof.
  intros until fb; intros SEP AGR AGL AGRS INJ FREE.
  (* Can free *)
  exploit free_parallel_rule.
    rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP. eauto.
    (* eexact FREE. *)
    eexact INJ.
    auto. rewrite Z.max_comm; reflexivity.
  intros (m1' & FREE' & SEP').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
  eexact SEP.
  instantiate (1 := rs).
  red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  red. intros. exploit AGRS; eauto.
  intros (rs' & LOAD_CS & CS & SAVE & NCS).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick3; eexact SEP. intros LOAD_LINK.
  exploit (hasvalue_get_stack Tptr). rewrite chunk_of_Tptr. eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  rewrite unfold_transf_function; simpl.
  exists rs', m1'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. eassumption.
  split. red; unfold return_regs; intros.
    destruct (is_callee_save r) eqn:C.
    apply CS; auto.
    rewrite NCS by auto. apply AGR.
  split. red; unfold return_regs; intros.
  destruct l. rewrite H; auto. destruct sl; auto; contradiction.
  split. assumption. assumption.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariants *)

Section STEP_CORRECT.

Variable w : cc_stacking_world injp.

(** This is the memory assertion that captures the contents of the stack frames
  mentioned in the call stacks. *)


Definition parent_rs (s: list regset)  :=
  match s with
  | nil => stk_rs2 w
  | hd :: tl => hd
  end.

Fixpoint stack_contents (j: meminj) (cs: list Linear.stackframe) (cs': list Mach.stackframe) (lrs' : list regset): massert :=
  match cs, cs', lrs' with
  | Linear.Stackbase ls :: nil, Mach.Stackbase _ ra :: nil, nil =>
      contains_init_args (stk_sg w) j ls (stk_m2 w) (stk_sp2 w)
(*      **  contains_init_sp_ra (stk_sg w) (stk_fsz2 w) (stk_m2 w) (stk_sp2 w) *)
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' _) ra c' :: cs', hd :: tl =>
      frame_contents f j sp' ls (parent_locset cs) (parent_rs tl) (parent_sp cs') (parent_ra cs')
      ** stack_contents j cs cs' tl
  | _, _, _ => pure False
  end.

(** [match_stacks] captures additional properties (not related to memory)
  of the Linear and Mach call stacks. Note that the [signature]
  argument corresponds to the function which is currently executing,
  or the callee in the case of a [Callstate] or [Returnstate], whereas
  the frames correspond to the suspended functions. *)

Definition init_wj := stk_w w.
Definition init_j := match init_wj with injpw j _ _ _ => j end.
Definition init_m1 := match init_wj with injpw _ m1 _ _ => m1 end.
Definition init_m2 := match init_wj with injpw _ _ m2 _ => m2 end.
Definition init_m2' := stk_m2 w.
Definition init_sp2 := stk_sp2 w.

Inductive match_stacks (j: meminj):
       list Linear.stackframe -> list stackframe -> list regset -> signature -> Prop :=
  | match_stacks_base: forall ra sg
        (TY_SP: Val.has_type (stk_sp2 w) Tptr)
        (TY_RA: Val.has_type ra Tptr),
      sg = stk_sg w \/ tailcall_possible sg ->
      inject_incr (init_j) j ->
      (* injw_sup_r (stk_w w) = (Mem.support (stk_m2 w)) -> *)
      init_m2 = init_m2' ->
      (forall b1 b2 delta, init_j b1 = None -> j b1 = Some (b2, delta) ->
         ~ sup_In b1 (Mem.support (init_m1)) /\
         ~ sup_In b2 (Mem.support (init_m2)))  ->
      match_stacks j
                   (Linear.Stackbase (initial_regs (stk_sg w) (stk_ls1 w)) :: nil)
                   (Stackbase (stk_sp2 w) ra :: nil)
                   nil
                   sg
  | match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg trf lrs' rs
        (TAIL: is_tail c (Linear.fn_code f))
        (FINDF: Genv.find_funct tge fb = Some (Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (INJ: j sp = Some(sp', (fe_stack_data (make_env (function_bounds f)))))
        (NEWSP: ~ Mem.valid_block init_m1 sp /\ ~ Mem.valid_block init_m2 sp')
        (TY_RA: Val.has_type ra Tptr)
        (RAN: ra <> Vundef)
        (AGL: agree_locs f ls (parent_locset cs))
        (AGRS: agree_unused_rs f rs (parent_rs lrs'))
        (ARGS: forall ofs ty,
           In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
           slot_within_bounds (function_bounds f) Outgoing ofs ty)
        (SZA: size_arguments sg <= bound_outgoing (function_bounds f))
        (STK: match_stacks j cs cs' lrs' (Linear.fn_sig f)),
      match_stacks j
                   (Linear.Stackframe f (Vptr sp Ptrofs.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Ptrofs.zero) ra c' :: cs')
                   (rs :: lrs')
                   sg.
(** Invariance with respect to change of memory injection. *)

Lemma contains_init_args_incr:
  forall sg j j' ls m0 sp,
  inject_incr j j' ->
  massert_imp (contains_init_args sg j ls m0 sp)
              (contains_init_args sg j' ls m0 sp).
Proof.
  intros. split; auto.
  intros m (UNCH & PERM & ARGS).
  cbn; repeat apply conj; auto.
  intros ofs ty REG. edestruct ARGS as (? & ? & ?); eauto.
Qed.


Lemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall cs cs' lrs P,
  m |= stack_contents j cs cs' lrs ** P ->
  m |= stack_contents j' cs cs' lrs ** P.
Proof.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; destruct lrs; simpl; intros; auto.
- destruct sp0; auto.
  rewrite sep_assoc in *.
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
- destruct cs, cs'; auto.
  erewrite <- contains_init_args_incr; eauto.
Qed.

Lemma match_stacks_change_meminj:
  forall j j' m m',
  inject_incr j j' ->
  inject_separated j j' m m' ->
  Mem.sup_include (Mem.support init_m1) (Mem.support m) ->
  Mem.sup_include (Mem.support init_m2) (Mem.support m') ->
  forall cs cs' lrs sg,
  match_stacks j cs cs' lrs sg ->
  match_stacks j' cs cs' lrs sg.
Proof.
  induction 5; intros.
- constructor; auto.
  + eapply inject_incr_trans; eauto.
  + intros. destruct (j b1) as [[xb2 xdelta] | ] eqn:Hb1; eauto.
    * erewrite H in H8; eauto. inv H8. eauto.
    * edestruct H0; eauto. unfold Mem.valid_block in *. split; eauto.
- econstructor; eauto.
Qed.

Lemma stack_contents_support m j cs cs' lrs sg:
  m |= stack_contents j cs cs' lrs ->
  match_stacks j cs cs' lrs sg ->
  Mem.sup_include (Mem.support init_m2) (Mem.support m).
Proof.
  induction 2.
  - rewrite H2. eapply Mem.unchanged_on_support. apply H.
  - apply IHmatch_stacks. apply H.
Qed.

(** Invariance with respect to change of signature. *)

Lemma match_stacks_change_sig:
  forall sg1 j cs cs' lrs sg,
  match_stacks j cs cs' lrs sg ->
  tailcall_possible sg1 ->
  match_stacks j cs cs' lrs sg1.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  - intros. elim (tailcall_possible_reg _ H0 _ H1).
  - apply zero_size_arguments_tailcall_possible in H0.
    pose proof (size_arguments_above sg). extlia.
Qed.

(** Typing properties of [match_stacks]. *)

Lemma match_stacks_type_sp:
  forall j cs cs' lrs sg,
  match_stacks j cs cs' lrs sg ->
  Val.has_type (parent_sp cs') Tptr.
Proof.
  destruct 1; auto; constructor.
Qed.

Lemma match_stacks_type_retaddr:
  forall j cs cs' lrs sg,
  match_stacks j cs cs' lrs sg ->
  Val.has_type (parent_ra cs') Tptr.
Proof.
  induction 1; unfold parent_ra; auto.
Qed.

(** Accessing the parent's outgoing locations *)


Lemma load_stack_arg m j cs cs' lrs sg ty ofs:
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
  match_stacks j cs cs' lrs sg ->
  m |= stack_contents j cs cs' lrs ->
  exists v,
     load_stack m (parent_sp cs') ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (parent_locset cs (S Outgoing ofs ty)) v.
Proof.
  intros REG MS SEP. destruct MS.
  - destruct H as [? | TCP]; [subst | elim (tailcall_possible_reg _ TCP _ REG)].
    edestruct SEP as (UNCH & FITS & ARGS), ARGS as (v & Hload & Hv); eauto.
  - simpl in SEP. unfold parent_sp.
    eapply frame_get_outgoing; eauto 2.
    destruct (loc_arguments_acceptable_2 _ _ REG) as [? ?].
    unfold slot_valid, proj_sumbool.
    rewrite zle_true by lia. rewrite pred_dec_true by auto. reflexivity.
Qed.

Lemma match_stacks_range_perm_args m j cs cs' lrs sg sb sofs:
  match_stacks j cs cs' lrs sg ->
  m |= stack_contents j cs cs' lrs ->
  parent_sp cs' = Vptr sb sofs ->
  Mem.range_perm m sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) Cur Freeable.
Proof.
  intros MS SEP SP. destruct MS; cbn in *; inv SP.
  - destruct SEP as (? & PERM & ?).
    destruct H as [? | Hsg]; subst; auto.
    + destruct (zlt 0 (size_arguments (stk_sg w))).
      * edestruct PERM as (sb' & sofs' & Hsp & PERM' & FITS). extlia.
        rewrite H4 in Hsp. inv Hsp. auto.
      * intro. unfold offset_sarg. extlia.
    + apply zero_size_arguments_tailcall_possible in Hsg.
      unfold offset_sarg. intro. extlia.
  - eapply mconj_proj1, sep_proj1, sep_proj2, sep_proj1 in SEP. cbn in SEP.
    destruct SEP as (_ & ? & ? & PERM & _).
    intros ofs Hofs. unfold offset_sarg in Hofs.
    rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr in Hofs.
    + eapply PERM. extlia.
    + unfold Ptrofs.max_unsigned. extlia.
Qed.

Lemma match_stacks_args_fit m j cs cs' lrs sg ofs sb sofs:
  match_stacks j cs cs' lrs sg ->
  m |= stack_contents j cs cs' lrs ->
  parent_sp cs' = Vptr sb sofs ->
  0 <= ofs < size_arguments sg ->
  offset_fits sofs ofs.
Proof.
  intros MS SEP SP OFS. red. destruct MS; cbn in *; inv SP.
  - destruct H as [? | Hsg]; subst; auto.
    + edestruct SEP as (? & HH & ?), HH as (sb' & sofs' & Hsp & PERM & FITS). extlia.
      rewrite H4 in Hsp. inv Hsp. apply FITS; eauto.
    + red in Hsg. extlia.
  - eapply mconj_proj1, sep_proj1, sep_proj2, sep_proj1 in SEP. cbn in SEP.
    unfold offset_sarg. (* split; try extlia. *)
    destruct SEP as (_ & ? & ? & _ & ?).
    rewrite !Ptrofs.add_zero_l, !Ptrofs.unsigned_repr;
      unfold Ptrofs.max_unsigned; extlia.
Qed.

Lemma match_stacks_init_args j cs cs' lrs sg m P:
  match_stacks j cs cs' lrs sg ->
  m |= stack_contents j cs cs' lrs ** P ->
  m |= contains_init_args sg j (parent_locset cs) m (parent_sp cs') ** P.
Proof.
  intros MS SEP. split.
  - pose proof MS as MS'. destruct MS.
    + apply sep_proj1 in SEP. cbn in SEP |- *.
      decompose [and] SEP. repeat apply conj.
      * apply Mem.unchanged_on_refl.
      * destruct H; subst; auto.
        apply zero_size_arguments_tailcall_possible in H. extlia.
      * destruct H; subst; auto.
        intros ? ? REG. apply tailcall_possible_reg in REG; auto. contradiction.
    + cbn. repeat apply conj.
      * apply Mem.unchanged_on_refl.
      * intros Hsz. eexists _, _. split; eauto.
        split; eauto 10 using match_stacks_range_perm_args, sep_proj1.
        intros. eapply match_stacks_args_fit; eauto using sep_proj1. reflexivity.
      * intros ofs ty REG.
        edestruct load_stack_arg as (? & ? & ?); eauto using sep_proj1.
  - split; eauto using sep_proj2. destruct SEP as (SEP & _ & DISJ).
    intros b ofs Hofs Hofs'.
    destruct MS; cbn in *.
    + destruct H; subst; eauto.
      apply zero_size_arguments_tailcall_possible in H.
      destruct Hofs. unfold offset_sarg in *. extlia.
    + inv Hofs. unfold offset_sarg in *.
      eapply DISJ; eauto. left. left. right. left. split; eauto.
      cbn [m_footprint contains_locations function_bounds bound_outgoing].
      rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_repr in H3.
      * extlia.
      * eassert (H : m |= contains_locations _ _ fe_ofs_arg _ _ _) by apply SEP.
        cbn in H. unfold Ptrofs.max_unsigned. extlia.
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_save_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (save_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Remark find_label_restore_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (restore_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
- auto.
- rewrite transl_code_eq.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
  simpl. destruct (peq lbl l). reflexivity. auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) =
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl.
  unfold transl_body. unfold save_callee_save. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c',
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed.

Lemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto.
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save.
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved (j: meminj):
  Genv.match_stbls j se tse ->
  forall (s: ident) (b: block),
    Genv.find_symbol ge s = Some b ->
    exists tb, j b = Some (tb, 0) /\ Genv.find_symbol tge s = Some tb.
Proof.
  apply Genv.find_symbol_match.
Qed.

Lemma functions_translated (j: meminj):
  Genv.match_stbls j se tse ->
  forall v tv f,
  Genv.find_funct ge v = Some f -> Val.inject j v tv ->
  exists tf, Genv.find_funct tge tv = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros. eapply (Genv.find_funct_transf_partial TRANSF); eauto.
Qed.

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto.
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m1 m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject se tse j m1 ->
  Genv.find_funct ge (Linear.ros_address ge ros ls) = Some f ->
  exists tf,
     Genv.find_funct tge (ros_address tge ros rs) = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG [??] FF.
  eapply functions_translated; eauto.
  destruct ros; simpl in *; eauto.
  eapply symbol_address_inject; eauto.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable lrs: list regset.
Variable sg: signature.
Variables bound bound': block.
Hypothesis MS: match_stacks j cs cs' lrs sg.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset cs).
Hypothesis AGARGS: agree_outgoing_arguments sg ls (parent_locset cs).
Variable m': mem.
Hypothesis SEP: m' |= stack_contents j cs cs' lrs.

Lemma transl_external_argument:
  forall l,
  In l (regs_of_rpairs (loc_arguments sg)) ->
  exists v, extcall_arg rs m' (parent_sp cs') l v /\ Val.inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l) by (apply loc_arguments_acceptable_2 with sg; auto).
  destruct l; red in H0.
- exists (rs r); split. constructor. auto.
- destruct sl; try contradiction.
  rewrite AGARGS by auto.
  edestruct load_stack_arg as (v & LOAD & INJ); eauto using extcall_arg_stack.
Qed.

Lemma transl_external_argument_2:
  forall p,
  In p (loc_arguments sg) ->
  exists v, extcall_arg_pair rs m' (parent_sp cs') p v /\ Val.inject j (Locmap.getpair p ls) v.
Proof.
  intros. destruct p as [l | l1 l2].
- destruct (transl_external_argument l) as (v & A & B). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists v; split; auto. constructor; auto.
- destruct (transl_external_argument l1) as (v1 & A1 & B1). eapply in_regs_of_rpairs; eauto; simpl; auto.
  destruct (transl_external_argument l2) as (v2 & A2 & B2). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists (Val.longofwords v1 v2); split.
  constructor; auto.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
      list_forall2 (extcall_arg_pair rs m' (parent_sp cs')) locs vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) locs) vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument_2; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
      extcall_arguments rs m' (parent_sp cs') sg vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments.
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** Preservation of the arguments to a builtin. *)

Section BUILTIN_ARGUMENTS.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs0 rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis INJ: j sp = Some(sp', fe.(fe_stack_data)).
Hypothesis AGR: agree_regs j ls rs.
Hypothesis SEP: m' |= frame_contents f j sp' ls ls0 rs0 parent retaddr ** minjection j m ** globalenv_inject se tse j m.


Lemma transl_builtin_arg_correct:
  forall a v,
  eval_builtin_arg se ls (Vptr sp Ptrofs.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg tse rs (Vptr sp' Ptrofs.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
Proof.
  assert (SEINJ: Genv.match_stbls j se tse) by apply SEP.
  pose proof (symbol_address_inject SEINJ) as SAINJ.
Local Opaque fe.
  induction 1; simpl; intros VALID BOUNDS.
- assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + exists (rs r); auto with barg.
  + exploit frame_get_local; eauto. intros (v & A & B).
    exists v; split; auto. constructor; auto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- set (ofs' := Ptrofs.add ofs (Ptrofs.repr (fe_stack_data fe))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.offset_ptr (Vptr sp' Ptrofs.zero) ofs').
  simpl. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto.
- econstructor; split; eauto with barg.
  unfold Val.offset_ptr. rewrite ! Ptrofs.add_zero_l. econstructor; eauto.
- apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg.
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2); auto using in_or_app.
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma transl_builtin_args_correct:
  forall al vl,
  eval_builtin_args se ls (Vptr sp Ptrofs.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args tse rs (Vptr sp' Ptrofs.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; simpl; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End BUILTIN_ARGUMENTS.

(*
Lemma stack_contents_out_of_reach f cs cs' m2 P:
  m2 |= stack_contents f cs cs' ** P ->
  Mem.unchanged_on (loc_out_of_reach (stk_inj w) (stk_m1 w)) (stk_m2 w) m2.
Proof.
  intros (STACK & _ & _); clear P.
  revert cs' STACK.
  induction cs; [contradiction | simpl; intros].
  destruct a, cs'; try contradiction.
  - destruct s, sp0; try contradiction.
    apply sep_proj2 in STACK.
    eauto.
  - destruct cs; contradiction.
  - destruct cs, s, cs'; try contradiction.
    apply STACK.
Qed.

Lemma source_invariants_step f m1 m2 f' m1' cs cs' P:
  source_invariants f m1 ->
  m2 |= stack_contents f cs cs' ** P ->
  inject_incr f f' ->
  inject_separated f f' m1 m2 ->
  Mem.unchanged_on (loc_unmapped f) m1 m1' ->
  (forall b ofs p,
      Mem.valid_block m1 b ->
      Mem.perm m1' b ofs Max p ->
      Mem.perm m1 b ofs Max p) ->
  source_invariants f' m1'.
Proof.
  intros [INCR INJSEP UNCH PERM] SEP INCR' INJSEP' UNCH' PERM'.
  constructor.
  - eapply inject_incr_trans; eauto.
  - intros b1 b2 delta Hbi Hb'.
    destruct (f b1) as [[fb2 delta']|] eqn:Hb.
    + assert (fb2 = b2) by (apply INCR' in Hb; congruence); subst.
      eapply INJSEP; eauto.
    + assert (~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2) as [H1 H2]
        by (eapply INJSEP'; eauto).
      split; intros H.
      eapply H1, Mem.valid_block_unchanged_on; eauto.
      eapply H2, Mem.valid_block_unchanged_on; eauto.
      eapply stack_contents_out_of_reach; eauto.
  - eapply Mem.unchanged_on_implies with (P := loc_unmapped f).
    + eapply Mem.unchanged_on_trans with (m2 := m1); eauto.
      eapply Mem.unchanged_on_implies; eauto.
      unfold loc_unmapped.
      intros b _. specialize (INCR b).
      destruct (stk_inj w b) as [[b2 delta] | ]; eauto.
      erewrite INCR; eauto.
    + unfold loc_unmapped.
      intros b _ Hb Hb1.
      destruct (f b) as [[b2 delta] | ] eqn:Hb2; eauto.
      exfalso.
      destruct (INJSEP b b2 delta); eauto.
  - intros b ofs p Hb.
    assert (Mem.valid_block m1 b).
    {
      unfold Mem.valid_block in Hb |- *.
      apply Mem.unchanged_on_nextblock in UNCH.
      extlia.
    }
    eauto.
Qed.
*)

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Satisfaction of the separation logic assertions that describe the contents
  of memory.  This is a separating conjunction of facts about:
-- the current stack frame
-- the frames in the call stack
-- the injection from the Linear memory state into the Mach memory state
-- the preservation of the global environment.
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs].
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Inductive match_states: Linear.state -> Mach.state -> Prop :=
  | match_states_intro:
      forall cs f sp c ls m cs' fb sp' rs m' j tf lrs
        (NB: Mem.sup_include (Mem.support init_m1) (Mem.support m))
        (STACKS: match_stacks j cs cs' lrs f.(Linear.fn_sig))
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct tge fb = Some (Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGLOCST: agree_unused_rs f rs (parent_rs lrs))
        (AGLOCS: agree_locs f ls (parent_locset cs))
        (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
        (NEWSP: ~ Mem.valid_block init_m1 sp /\ ~ Mem.valid_block init_m2 sp')
        (TAIL: is_tail c (Linear.fn_code f))
        (SEP: m' |= frame_contents f j sp' ls (parent_locset cs) (parent_rs lrs) (parent_sp cs') (parent_ra cs')
                 ** stack_contents j cs cs' lrs
                 ** minjection j m
                 ** globalenv_inject se tse j m)
        (Hm: Mem.inject j m m')
        (ACC: injp_acc init_wj (injpw j m m' Hm)),
      match_states (Linear.State cs f (Vptr sp Ptrofs.zero) c ls m)
                   (Mach.State cs' fb (Vptr sp' Ptrofs.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall cs vf f ls m cs' vf' rs m' j lrs
        (NB: Mem.sup_include (Mem.support init_m1) (Mem.support m))
        (STACKS: match_stacks j cs cs' lrs (Linear.funsig f))
        (FIND: Genv.find_funct ge vf = Some f)
        (FINJ: Val.inject j vf vf')
        (AGREGS: agree_regs j ls rs)
        (TRS: forall r, is_callee_save r = true -> rs r = parent_rs lrs r) (*This could be rs = parent_rs lrs if we do not consider tailcall*)
        (SEP: m' |= stack_contents j cs cs' lrs
                 ** minjection j m
                 ** globalenv_inject se tse j m)
        (Hm: Mem.inject j m m')
        (ACC: injp_acc init_wj (injpw j m m' Hm)),
      match_states (Linear.Callstate cs vf ls m)
                   (Mach.Callstate cs' vf' rs m')
  | match_states_return:
      forall cs ls m cs' rs m' j sg lrs
        (NB: Mem.sup_include (Mem.support init_m1) (Mem.support m))
        (STACKS: match_stacks j cs cs' lrs sg)
        (AGREGS: agree_regs j ls rs)
        (CALLEESAVE: forall r, is_callee_save r = true -> rs r = (parent_rs lrs) r)
        (SEP: m' |= stack_contents j cs cs' lrs
                 ** minjection j m
                 ** globalenv_inject se tse j m)
        (Hm: Mem.inject j m m')
      (ACC: injp_acc init_wj (injpw j m m' Hm)),
      match_states (Linear.Returnstate cs ls m)
                  (Mach.Returnstate cs' rs m').

Theorem transf_step_correct:
  forall s1 t s2, Linear.step ge s1 t s2 ->
  forall (WTS: wt_state prog se s1) s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1; intros;
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

- (* Lgetstack *)
  destruct BOUND as [BOUND1 BOUND2].
  exploit wt_state_getstack; eauto. intros SV.
  unfold destroyed_by_getstack; destruct sl.
+ (* Lgetstack, local *)
  exploit frame_get_local; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. exact A.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_unused_rs_set_reg; auto.
  apply agree_locs_set_reg; auto.
+ (* Lgetstack, incoming *)
  unfold slot_valid in SV. InvBooleans.
  exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  edestruct load_stack_arg as (v & A & B); eauto. apply SEP.
  econstructor; split.
  apply plus_one. eapply exec_Mgetparam; eauto.
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs.
  eapply frame_get_parent. eexact SEP.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto.
  erewrite agree_incoming by eauto. exact B.
  apply agree_unused_rs_set_reg; eauto.
  apply agree_unused_rs_set_reg; eauto.
  eapply  caller_save_reg_within_bounds; eauto.
  apply agree_locs_set_reg; auto. apply agree_locs_undef_locs; auto.
+ (* Lgetstack, outgoing *)
  exploit frame_get_outgoing; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. exact A.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_unused_rs_set_reg; eauto.
  apply agree_locs_set_reg; auto.

- (* Lsetstack *)
  exploit wt_state_setstack; eauto. intros (SV & SW).
  set (ofs' := match sl with
               | Local => offset_local (make_env (function_bounds f)) ofs
               | Incoming => 0 (* dummy *)
               | Outgoing => offset_arg ofs
               end).
  eapply frame_undef_regs with (rl := destroyed_by_setstack ty) in SEP.
  assert (A: exists m'',
              store_stack m' (Vptr sp' Ptrofs.zero) ty (Ptrofs.repr ofs') (rs0 src) = Some m''
           /\ m'' |= frame_contents f j sp' (Locmap.set (S sl ofs ty) (rs (R src))
                                               (LTL.undef_regs (destroyed_by_setstack ty) rs))
                                            (parent_locset s)(parent_rs lrs)(parent_sp cs') (parent_ra cs')
                  ** stack_contents j s cs' lrs ** minjection j m ** globalenv_inject se tse j m).
  { unfold ofs'; destruct sl; try discriminate.
    eapply frame_set_local; eauto.
    eapply frame_set_outgoing; eauto. }
  clear SEP; destruct A as (m'' & STORE & SEP).
  assert (Hm' : Mem.inject j m m''). 
  { apply SEP. }
  assert (INJP: injp_acc_small init_wj (injpw j m m' Hm) (injpw j m m'' Hm')).
  {
    unfold init_m1, init_m2, init_wj in *. destruct NEWSP as [NEW1 NEW2].
    inv ACC. simpl in *. rewrite <- H in *.
    unfold store_stack in STORE. inv STORE.
    econstructor; eauto; try (red; intros; congruence).
    eapply Mem.ro_unchanged_store; eauto.
    red. intros. eapply Mem.perm_store_2; eauto.
    eapply Mem.unchanged_on_refl.
    split. 
    erewrite <- Mem.support_store; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros. intros [X Y]. congruence.
    eapply Mem.store_unchanged_on; eauto.
    intros. intros [X Y]. congruence.
  }
  econstructor; split.
  apply plus_one. destruct sl; try discriminate.
    econstructor. eexact STORE. eauto.
    econstructor. eexact STORE. eauto.
  econstructor. eauto. eauto. eauto. eauto.
  apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
  eapply agree_unused_rs_undef_regs; eauto.
  apply destroyed_by_setstack_caller_save.
  apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
  eauto. eauto with coqlib. eapply is_tail_cons_left. eauto.
  eauto.
  eapply injp_acc_small_implies; eauto.

- (* Lop *)
  assert (exists v',
          eval_operation tse (Vptr sp' Ptrofs.zero) (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v'
       /\ Val.inject j v v').
  eapply eval_operation_inject; eauto.
  apply SEP.
  eapply agree_reglist; eauto.
  destruct H0 as [v' [A B]].
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg; auto.
  rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto.
  apply agree_unused_rs_set_reg; eauto.
  apply agree_unused_rs_undef_regs; auto. apply destroyed_by_op_caller_save.
  apply agree_locs_set_reg; auto. apply agree_locs_undef_locs. auto. apply destroyed_by_op_caller_save.
  apply frame_set_reg. apply frame_undef_regs. exact SEP.

- (* Lload *)
  assert (exists a',
          eval_addressing tse (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  apply SEP.
  eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  exploit loadv_parallel_rule.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. eexact SEP.
  eauto. eauto.
  intros [v' [C D]].
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto with coqlib.
  apply agree_regs_set_reg. rewrite transl_destroyed_by_load. apply agree_regs_undef_regs; auto. auto.
  apply agree_unused_rs_set_reg; auto.
  apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. auto.

- (* Lstore *)
  assert (exists a',
          eval_addressing tse (Vptr sp' Ptrofs.zero) (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a'
       /\ Val.inject j a a').
  eapply eval_addressing_inject; eauto.
  apply SEP.
  eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  rewrite sep_swap3 in SEP.
  exploit storev_parallel_rule. eexact SEP. inversion Hm. eauto. eauto. eauto. 
  clear SEP; intros (m1' & C & SEP).
  rewrite sep_swap3 in SEP.
  assert (Hm' : Mem.inject j m' m1').
  apply SEP. 
  assert (ACC1: injp_acc (injpw j m m'0 Hm) (injpw j m' m1' Hm')).
  eapply injp_acc_storev. apply H0. apply C. eauto.
  eapply agree_reg. auto.
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  destruct a; cbn in H0; try congruence.
  rewrite (Mem.support_store _ _ _ _ _ _ H0). eauto.
  rewrite transl_destroyed_by_store. apply agree_regs_undef_regs; auto.
  apply agree_unused_rs_undef_regs; auto. apply destroyed_by_store_caller_save.
  apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
  auto. eauto with coqlib.
  rewrite globalenv_support in SEP.
  eapply frame_undef_regs; eauto.
  destruct a; try discriminate. apply Mem.support_store in H0. rewrite H0. eauto.
  etransitivity. eauto. eauto.

- (* Lcall *)
  exploit find_function_translated; eauto.
  eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [tf' [A B]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST. intros [ra D].
  econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  econstructor; eauto with coqlib.
  unfold Val.offset_ptr. destruct fb; constructor; eauto.
  destruct fb; try inv FIND. simpl. congruence.
  intros; red.
    apply Z.le_trans with (size_arguments (Linear.funsig f')); auto.
    apply loc_arguments_bounded; auto.
    destruct ros; simpl in *; eauto. eapply symbol_address_inject; eauto. apply SEP.
  reflexivity.
  simpl. rewrite sep_assoc. exact SEP.
  
- (* Ltailcall *)
  rewrite (sep_swap (stack_contents j s cs' lrs)) in SEP.
  exploit function_epilogue_correct; eauto. inversion Hm. auto. inv AGLOCS.
  clear SEP. intros (rs1 & m1' & P & Q & R & S & T & U & V & SEP).
  rewrite sep_swap in SEP.
  exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eexact SEP.
    intros [tf' [A B]].
  assert (Hm': Mem.inject j m' m1').
  apply SEP.
  assert (ACC1: injp_acc_small init_wj (injpw j m m'0 Hm) (injpw j m' m1' Hm')).
  {
    unfold init_m1, init_m2, init_wj in *. destruct NEWSP as [NEW1 NEW2].
    inv ACC. simpl in *. rewrite <- H in *.
    econstructor; eauto; try (red; intros; congruence).
    eapply Mem.ro_unchanged_free; eauto.
    eapply Mem.ro_unchanged_free; eauto.
    red. intros. eapply Mem.perm_free_3; eauto.
    red. intros. eapply Mem.perm_free_3; eauto.
    split. erewrite <- Mem.support_free; eauto.
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence. 
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence.
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence.
  }
  econstructor; split.
  eapply plus_right. eexact S. econstructor; eauto. traceEq.
  econstructor. 
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  apply match_stacks_change_sig with (Linear.fn_sig f); eauto.
  apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
  eauto.
  destruct ros; simpl in *; eauto. eapply symbol_address_inject; eauto. apply SEP.
  eauto. intros. rewrite <- V; eauto.
  rewrite globalenv_support in SEP. eauto. 
  apply Mem.support_free in H2. rewrite H2. eauto.
  eapply injp_acc_small_implies; eauto.

- (* Lbuiltin *)
  destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
    eauto. eauto. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP. inversion Hm. eauto.
    eauto. rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
    exact BND2.
  intros [vargs' [P Q]].
  pose proof SEP as SEP'.
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  exploit external_call_parallel_rule; eauto. inversion Hm. auto.
  clear SEP; intros (j' & res' & m1' & EC & RES & UNCH1 & UNCH2 & SEP &  INCR & ISEP ).
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  assert (Hm': Mem.inject j' m' m1'). apply SEP.
  assert (ACC1: injp_acc (injpw j m m'0 Hm) (injpw j' m' m1' Hm')).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply match_states_intro with (j := j').
  apply Mem.unchanged_on_support in UNCH1. eauto.
  eapply match_stacks_change_meminj. eauto. eauto.
  apply Mem.unchanged_on_support in UNCH1. eauto.
  unfold init_m2.
  inv ACC. eapply Mem.unchanged_on_support. eapply H10.
  eauto. eauto. eauto.
  (*   eauto with coqlib. destruct UNCH1 as [_ UNCH1]. *)
  (* unfold local_t, init_m1. simpl. *)
  (* inv ACCE. destruct H9 as [[_ X] _].  congruence. *)
  (* eapply stack_contents_support; eauto. apply SEP'. *)
  apply agree_regs_set_res; auto. apply agree_regs_undef_regs; auto. eapply agree_regs_inject_incr; eauto.
  apply agree_unused_rs_set_res; auto. apply agree_unused_rs_undef_regs_1; auto.
  apply agree_locs_set_res; auto. apply agree_locs_undef_regs; auto.
  eauto. eauto. eauto with coqlib.
  apply frame_set_res. apply frame_undef_regs. apply frame_contents_incr with j; auto.
  rewrite sep_swap2. apply stack_contents_change_meminj with j; auto. rewrite sep_swap2.
  exact SEP.
  etransitivity. eauto. eauto.

- (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.

- (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto.
  eapply find_label_tail; eauto.

- (* Lcond, true *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_true; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  eapply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_unused_rs_undef_regs. auto. apply destroyed_by_cond_caller_save.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  auto. eauto.
  eapply find_label_tail; eauto.
  apply frame_undef_regs; auto. eauto.

- (* Lcond, false *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_false; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  econstructor. eauto. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_unused_rs_undef_regs. auto. apply destroyed_by_cond_caller_save.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  auto. eauto. eauto with coqlib.
  apply frame_undef_regs; auto. eauto.

- (* Ljumptable *)
  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto. }
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable; eauto.
  apply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto.
  apply agree_unused_rs_undef_regs. auto. apply destroyed_by_jumptable_caller_save.
  apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
  auto. eauto. eapply find_label_tail; eauto.
  apply frame_undef_regs; auto. eauto.

- (* Lreturn *)
  rewrite (sep_swap (stack_contents j s cs' lrs)) in SEP.
  exploit function_epilogue_correct; eauto.
  intros (rs' & m1' & A & B & C & D & E & F & SAVE & G).
  assert (Hm': Mem.inject j m' m1').
  apply G.
  assert (ACC1: injp_acc_small init_wj (injpw j m m'0 Hm) (injpw j m' m1' Hm')).
  {
    unfold init_m1, init_m2, init_wj in *. destruct NEWSP as [NEW1 NEW2].
    inv ACC. simpl in *. rewrite <- H0 in *.
    econstructor; eauto; try (red; intros; congruence).
    eapply Mem.ro_unchanged_free; eauto.
    eapply Mem.ro_unchanged_free; eauto.
    red. intros. eapply Mem.perm_free_3; eauto.
    red. intros. eapply Mem.perm_free_3; eauto.
    split. erewrite <- Mem.support_free; eauto.
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence. 
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence.
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y].
    congruence.
  }
  econstructor; split.
  eapply plus_right. eexact D. econstructor; eauto. traceEq.
  econstructor; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H); eauto.
  intros. rewrite <- SAVE; eauto.
  rewrite globalenv_support in G.
  rewrite sep_swap; exact G.
  apply Mem.support_free in H. rewrite H. eauto.
  eapply injp_acc_small_implies. eauto. eauto.

- (* internal function *)
  rewrite FIND in FIND0. inv FIND0.
  edestruct functions_translated as (tf & TFIND & TRANSL); eauto. apply SEP.
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
  intros EQ; inversion EQ; clear EQ; subst tf.
  pose proof SEP as SEP'.
  rewrite sep_comm, sep_assoc in SEP.
  exploit wt_callstate_agree; eauto. intros [AGCS AGARGS].
  exploit function_prologue_correct; eauto.
  red; intros; eapply wt_callstate_wt_regs; eauto.
  eapply match_stacks_type_sp; eauto.
  eapply match_stacks_type_retaddr; eauto.
  clear SEP;
  intros (j' & rs' & m2' & sp' & m3' & m4' & m5' & Hm' & A & B & C & D & E & E' & F & SEP & J & K & L & M).
  rewrite (sep_comm (globalenv_inject se tse j' m')) in SEP.
  rewrite (sep_swap (minjection j' m')) in SEP.
  econstructor; split.
  eapply plus_left. econstructor; eauto.
  rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
  eexact D. traceEq.
  eapply match_states_intro with (j := j'); eauto with coqlib.
  rewrite (Mem.support_alloc _ _ _ _ _ H); eauto.
  eapply match_stacks_change_meminj; eauto.
  eapply stack_contents_support; eauto. apply SEP'.
  red. intros. rewrite F; eauto. apply TRS.
  eapply reg_within_bounds_caller_save; eauto.
  unfold init_m1, init_m2. inv ACC. 
  split. intro. eapply Mem.fresh_block_alloc. apply H.
  eapply Mem.valid_block_unchanged_on; eauto.
  intro. eapply Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_unchanged_on; eauto.
  rewrite sep_swap in SEP.
  eapply frame_callee_save_eq; eauto.
  rewrite sep_swap. eapply stack_contents_change_meminj; eauto.
  etransitivity. eauto. eauto.    
  
- (* external function *)
  rewrite FIND in FIND0. inv FIND0.
  edestruct functions_translated as (tf & TFIND & TRANSL); eauto. apply SEP.
  simpl in TRANSL. inversion TRANSL; subst tf.
  exploit wt_callstate_agree; eauto. intros [AGCS AGARGS].
  exploit transl_external_arguments; eauto. apply sep_proj1 in SEP; eauto. intros [vl [ARGS VINJ]].
  pose proof SEP as SEP'.
  rewrite sep_comm, sep_assoc in SEP.
  exploit external_call_parallel_rule; eauto.
  intros (j' & res' & m1' & A & B & C & D & E & F & G).
  assert (Hm': Mem.inject j' m' m1'). apply E.
  assert (ACC1: injp_acc (injpw j m m'0 Hm) (injpw j' m' m1' Hm')).
  { econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
    red. intros. eapply external_call_max_perm; eauto.  }
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  eapply match_states_return with (j := j').
  apply Mem.unchanged_on_support in C; eauto.
  (*eauto using external_call_max_perm.*)
  eapply match_stacks_change_meminj; eauto.
  eapply stack_contents_support; eauto. apply SEP'.
  apply agree_regs_set_pair. apply agree_regs_undef_caller_save_regs.
  apply agree_regs_inject_incr with j; auto.
  auto.
  intros. 
  transitivity ((undef_caller_save_regs rs) r).
  generalize (CallConv.loc_result_always_one (ef_sig ef)).
  intros [r0 Hr]. rewrite Hr. simpl. rewrite Regmap.gso. reflexivity.
  generalize (loc_result_caller_save (ef_sig ef)).
  intro Hcs. rewrite Hr in Hcs. simpl in Hcs. congruence.
  unfold undef_caller_save_regs. rewrite H. eauto.
  
  apply stack_contents_change_meminj with j; auto.
  rewrite sep_comm, sep_assoc; auto.
  etransitivity. eauto. eauto.

- (* return *)
  inv STACKS. exploit wt_returnstate_agree; eauto. intros [AGCS OUTU].
  simpl in AGCS. simpl in SEP. rewrite sep_assoc in SEP.
  econstructor; split.
  apply plus_one. apply exec_return.
  econstructor; eauto.
  red. intros. red in AGRS. simpl in CALLEESAVE. rewrite CALLEESAVE.
  eauto. destruct (is_callee_save r) eqn:Hcs. reflexivity.
  elim H. red. intros. congruence.
  apply agree_locs_return with rs0; auto.
  eapply frame_contents_exten with rs0 (parent_locset s) (parent_rs lrs'); auto.
  intros; apply Val.lessdef_same; apply AGCS; red; congruence.
  intros; rewrite (OUTU ty ofs); auto.
Qed.

End STEP_CORRECT.

Let ccA : callconv li_locset li_mach := cc_stacking injp.
Let ccB : callconv li_locset li_mach := cc_stacking injp.

Lemma load_stack_inject j m1 m2 sp1 sp2 ty ofs v1:
  load_stack m1 sp1 ty ofs = Some v1 ->
  Mem.inject j m1 m2 ->
  Val.inject j sp1 sp2 ->
  exists v2,
    load_stack m2 sp2 ty ofs = Some v2 /\
    Val.inject j v1 v2.
Proof.
  intros Hv1 Hm Hsp.
  destruct Hsp; try discriminate. subst.
  edestruct Mem.load_inject as (v2 & Hv2 & Hv); eauto. eapply Hv1. cbn.
  rewrite Ptrofs.add_commut, <- Ptrofs.add_assoc, (Ptrofs.add_commut ofs ofs1).
  apply Mem.load_valid_access in Hv1.
  erewrite Mem.address_inject; eauto.
  eapply Hv1. pose proof (size_chunk_pos (chunk_of_type ty)). extlia.
Qed.

Lemma init_args_initial_regs sg j ls m sp:
  massert_imp (contains_init_args sg j ls m sp)
              (contains_init_args sg j (initial_regs sg ls) m sp).
Proof.
  split; auto. intros m' Hm'. cbn in *. intuition auto.
  unfold initial_regs. replace (loc_is_external _ _) with true; auto.
  symmetry. apply loc_external_is. constructor; auto.
Qed.


Lemma transf_initial_states:
  forall w q1 q2, match_senv ccB w se tse -> match_query ccB w q1 q2 ->
  forall st1, Linear.initial_state ge q1 st1 -> (* wt_locset (lq_rs q1) -> *)
  exists st2, Mach.initial_state tge q2 st2 /\ match_states w st1 st2.
Proof.
  intros w q1 q2 Hse Hq st1 Hst1. inv Hst1. inv Hq. inv Hse. destruct H9. inv H3.
  exploit functions_translated; eauto. intros [tf [FIND TR]].
  eexists. split.
  (* exists (Callstate (Stackbase (Vptr sb sofs) ra2 :: nil) vf2 rs3 m2). split. *)
  - monadInv TR. econstructor; eauto.
  - (* rename f0 into j. rename m into m1. *)
    eapply match_states_call; eauto.
    + constructor; auto. cbn. congruence.
    + reflexivity.
    + cbn [stack_contents stk_sg stk_sp2 stk_m2].
      subst rs0. rewrite <- init_args_initial_regs.
      rewrite <- sep_assoc. repeat (apply conj; auto).
      * intros b ofs Hofs (b0 & delta & Hb & Hp). eapply H11; eauto.
      * intros ? ?. cbn. auto.
    + simpl. reflexivity.
Qed.

Lemma transf_final_states:
  forall w st1 st2 r1, wt_state prog se st1 -> match_states w st1 st2 -> Linear.final_state st1 r1 ->
  exists r2, Mach.final_state st2 r2 /\ match_reply ccB w r1 r2.
Proof.
  intros. inv H0; inv H1. inv STACKS. inv H.
  exists (mr rs m'). split.
  - constructor.
  - destruct w; cbn in *.
    cbn [stack_contents] in SEP. rewrite ! and_assoc in SEP.
    destruct SEP as (UNC1 & ARGS & VINJ & MINJ & GINJ & SUP1 & SUP2 & DISJ & DIS2).
    eapply cc_stacking_mr_intro; cbn; eauto.
    + intros r Hr. simpl in *. erewrite <- CALLEESAVE; eauto.
    + intros sb2 sofs2 H sb1 delta Hsb Hp. eapply DIS2; cbn; eauto.
Qed.

Lemma init_args_agree_outgoing_arguments sg j ls1 ls2 m sp:
  agree_outgoing_arguments sg ls1 ls2 ->
  massert_imp (contains_init_args sg j ls2 m sp)
              (contains_init_args sg j ls1 m sp).
Proof.
  intros Hargs. split; auto. intros m' (PERM & FITS & ARGS). cbn.
  repeat apply conj; auto. intros. rewrite Hargs; eauto.
Qed.

Lemma transf_external_states:
  forall w st1 st2 q1, wt_state prog se st1 ->
  match_states w st1 st2 -> Linear.at_external ge st1 q1 ->
  exists wx q2, Mach.at_external tge st2 q2 /\ match_query ccA wx q1 q2 /\ match_senv ccA wx se tse /\
  forall r1 r2 st1', match_reply ccA wx r1 r2 -> Linear.after_external ge st1 r1 st1' ->
  exists st2', Mach.after_external st2 r2 st2' /\ match_states w st1' st2'.
Proof.
  intros w st1 st2 q1 WTS Hst Hq1. destruct Hst; inv Hq1.
  inv WTS. rewrite FIND in H4; inv H4. fold ge in FIND0. rewrite FIND in FIND0; inv FIND0.
  edestruct functions_translated as (tf & TFIND & TRANSL); eauto. apply SEP.
  simpl in TRANSL. inv TRANSL.
  assert (MINJ: Mem.inject j m m') by apply SEP.
  eexists (stkw injp (injpw _ _ _ MINJ) _ ls rs (parent_sp cs') m'), _. repeat apply conj.
  - econstructor; eauto.
  - eapply match_stacks_init_args in SEP; eauto.
    econstructor; eauto.
    + destruct vf; cbn in *; try congruence.
    + eapply init_args_agree_outgoing_arguments; eauto. apply SEP.
    + constructor.
    + rewrite <- sep_assoc in SEP. destruct SEP as ((_ & _ & DISJ) & _ & _).
      intros b ofs Hofs b' ofs' H' Hp. eapply DISJ; cbn; eauto.
    + eapply match_stacks_type_sp; eauto.
    + eapply match_stacks_type_retaddr; eauto.
  - constructor; apply SEP.
  - intros r1 r2 st1' Hr Hst1'. inv Hr. inv H5. inv Hst1'. inv H10.
    rewrite H19 in FIND. inv FIND.
    eexists. split.
    + econstructor; eauto.
    + eapply match_states_return with (j := f').
      * apply Mem.unchanged_on_support in H7.
        eapply Mem.sup_include_trans. eauto. auto.
      * eapply match_stacks_change_meminj; eauto.
        eapply stack_contents_support; eauto. apply SEP.
      * intros r. cbn. destruct in_dec; eauto.
        destruct is_callee_save eqn:Hr; eauto.
        rewrite <- H9. eauto. eauto.
      * intros. rewrite <- H9; eauto.
      * eapply stack_contents_change_meminj; eauto.
        rewrite sep_comm, sep_assoc in SEP |- *.
        eapply minjection_incr; eauto.
        rewrite sep_comm, sep_assoc in SEP |- *.
        eapply globalenv_inject_incr; eauto.
        eapply Mem.unchanged_on_support; eauto.
      * etransitivity. eauto.
        instantiate (1 := Hm5).
        econstructor; eauto.
Qed.

Lemma wt_prog:
  forall i fd, In (i, Gfun fd) prog.(prog_defs) -> wt_fundef fd.
Proof.
  intros.
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto.
  intros ([i' g] & P & Q & R). simpl in *. inv R. destruct fd; simpl in *.
- monadInv H2. unfold transf_function in EQ.
  destruct (wt_function f). auto. discriminate.
- auto.
Qed.

End PRESERVATION.

Theorem transf_program_correct rao prog tprog:
  (forall f sg ros c, is_tail (Mcall sg ros :: c) (fn_code f) ->
   exists ofs, rao f c ofs) ->
  match_prog prog tprog ->
  forward_simulation (wt_loc @ cc_stacking injp) (wt_loc @ cc_stacking injp)
                     (Linear.semantics prog) (Mach.semantics rao tprog).
Proof.
  intros Hrao MATCH.
  eapply source_invariant_fsim; eauto using linear_wt, wt_prog.
  revert MATCH.
  fsim eapply forward_simulation_plus with (match_states:= match_states rao prog tprog se1 se2 w).
  - intros q1 q2 Hq. destruct Hq. inv Hse. cbn in *.
    destruct w. inv H10.
    eapply (Genv.is_internal_transf_partial MATCH); eauto 1.
    intros [|] ? Hfd; monadInv Hfd; auto.
  - cbn. intuition eauto using transf_initial_states.
  - intros s1 s2 r1 Hs  (Hr1 & [? ?] & Hxse & WTS & WTR). cbn in Hxse. subst.
    eapply transf_final_states; eauto.
  - intros s1 s2 q1 Hs (Hq1 & [? ?] & ? & Hx & WTS & WTQ). cbn in Hx. subst.
    edestruct transf_external_states as (wx & qx2 & ? & ? & ? & ?); eauto.
    exists wx, qx2. intuition auto. destruct H4 as (Hs1' & _).
    edestruct H2 as (st2' & ? & ?); eauto.
  - intros s1 t s1' (Hs1' & [xse ?] & Hx & WTS & WTS') s2 Hs. cbn in Hx, Hs1', Hs. subst.
    eapply transf_step_correct; eauto.
Qed.
