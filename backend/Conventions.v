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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import LanguageInterface.
Require Import CKLR.
Require Import Locations.
Require Export Conventions1.

(** The processor-dependent and EABI-dependent definitions are in
    [arch/abi/Conventions1.v].  This file adds various processor-independent
    definitions and lemmas. *)

Lemma loc_arguments_acceptable_2:
  forall s l,
  In l (regs_of_rpairs (loc_arguments s)) -> loc_argument_acceptable l.
Proof.
  intros until l. generalize (loc_arguments_acceptable s). generalize (loc_arguments s).
  induction l0 as [ | p pl]; simpl; intros.
- contradiction.
- rewrite in_app_iff in H0. destruct H0.
  exploit H; eauto. destruct p; simpl in *; intuition congruence.
  apply IHpl; auto.
Qed.

(** ** Stack size of function arguments *)

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Definition max_outgoing_1 (accu: Z) (l: loc) : Z :=
  match l with
  | S Outgoing ofs ty => Z.max accu (ofs + typesize ty)
  | _ => accu
  end.

Definition max_outgoing_2 (accu: Z) (rl: rpair loc) : Z :=
  match rl with
  | One l => max_outgoing_1 accu l
  | Twolong l1 l2 => max_outgoing_1 (max_outgoing_1 accu l1) l2
  end.

Definition size_arguments (s: signature) : Z :=
  List.fold_left max_outgoing_2 (loc_arguments s) 0.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark fold_max_outgoing_above:
  forall l n, fold_left max_outgoing_2 l n >= n.
Proof.
  assert (A: forall n l, max_outgoing_1 n l >= n).
  { intros; unfold max_outgoing_1. destruct l as [_ | [ ]]; extlia. }
  induction l; simpl; intros. 
  - lia.
  - eapply Zge_trans. eauto.
    destruct a; simpl. apply A. eapply Zge_trans; eauto.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros. apply fold_max_outgoing_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments s)) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty.
  assert (A: forall n l, n <= max_outgoing_1 n l).
  { intros; unfold max_outgoing_1. destruct l as [_ | [ ]]; extlia. }
  assert (B: forall p n,
             In (S Outgoing ofs ty) (regs_of_rpair p) ->
             ofs + typesize ty <= max_outgoing_2 n p).
  { intros. destruct p; simpl in H; intuition; subst; simpl.
  - extlia.
  - eapply Z.le_trans. 2: apply A. extlia.
  - extlia. }
  assert (C: forall l n,
             In (S Outgoing ofs ty) (regs_of_rpairs l) ->
             ofs + typesize ty <= fold_left max_outgoing_2 l n).
  { induction l; simpl; intros.
  - contradiction.
  - rewrite in_app_iff in H. destruct H.
  + eapply Z.le_trans. eapply B; eauto.
    apply Z.ge_le. apply fold_max_outgoing_above.
  + apply IHl; auto.
  }
  apply C. 
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S Outgoing n ty => S Incoming n ty
  | _ => l
  end.

Definition loc_parameters (s: signature) : list (rpair loc) :=
  List.map (map_rpair parameter_of_argument) (loc_arguments s).

Lemma incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sg)) ->
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)).
Proof.
  intros.
  replace (regs_of_rpairs (loc_parameters sg)) with (List.map parameter_of_argument (regs_of_rpairs (loc_arguments sg))) in H.
  change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable_2; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct sl; try contradiction.
  inv A. auto.
  unfold loc_parameters. generalize (loc_arguments sg). induction l as [ | p l]; simpl; intros.
  auto.
  rewrite map_app. f_equal; auto. destruct p; auto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  size_arguments s = 0.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  Z.eqb (size_arguments sg) 0.

Lemma tailcall_is_possible_correct:
  forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof.
  unfold tailcall_is_possible. intros. rewrite Z.eqb_eq in H. auto.
Qed.

Lemma tailcall_is_possible_complete:
  forall s, tailcall_possible s -> tailcall_is_possible s = true.
Proof.
  unfold tailcall_is_possible. intros. rewrite Z.eqb_eq. auto.
Qed.

Lemma tailcall_possible_reg sg:
  tailcall_possible sg ->
  forall l, In l (regs_of_rpairs (loc_arguments sg)) ->
  match l with R _ => True | S _ _ _ => False end.
Proof.
  intros Hsg l Hl.
  pose proof Hl as Hacc. apply loc_arguments_acceptable_2 in Hacc.
  destruct l as [ | [ ]]; cbn in *; auto.
  pose proof Hl as Hbnd. apply loc_arguments_bounded in Hbnd.
  pose proof (typesize_pos ty). red in Hsg. lia.
Qed.

Lemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 <-> tailcall_possible sg.
Proof.
  reflexivity.
Qed.


(** * Callee-save locations *)

(** We classify locations as either
- callee-save, i.e. preserved across function calls:
  callee-save registers, [Local] and [Incoming] stack slots;
- caller-save, i.e. possibly modified by a function call:
  non-callee-save registers, [Outgoing] stack slots.

Concerning [Outgoing] stack slots: several ABIs allow a function to modify
the stack slots used for passing parameters to this function.
The code currently generated by CompCert never does so, but the code
generated by other compilers often does so (e.g. GCC for x86-32).
Hence, CompCert-generated code must not assume that [Outgoing] stack slots
are preserved across function calls, because they might not be preserved
if the called function was compiled by another compiler. 
*)

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

(** * Assigning result locations *)

(** Useful lemmas to reason about the result of an external call. *)

Lemma locmap_get_set_loc_result:
  forall sg v rs l,
  match l with R r => is_callee_save r = true | S _ _ _ => True end ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply Locmap.gpo. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; simpl. congruence. auto. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

Lemma locmap_get_set_loc_result_callee_save:
  forall sg v rs l,
  callee_save_loc l ->
  Locmap.setpair (loc_result sg) v rs l = rs l.
Proof.
  intros. apply locmap_get_set_loc_result. 
  red in H; destruct l; auto.
Qed.


(** * Language interface for locations *)

(** ** External locations *)

(** Locset-based languages keep independent instances of the location
  set for each stack frame. The preservation of callee-save registers
  is expressed as part of the semantics itself, which restores the
  callee-save locations when they transition to [Returnstate]s
  (see also [LTL.return_regs]). In fact, at interaction points, LTL
  programs emitted by the Alloc pass are only sensitive to the values
  of locations used to pass incoming arguments, and those used to
  return the results of outgoing calls. Hence, since we don't need or
  want to precisely model the linking of arbitrary LTL programs, we do
  not pass the values of other locations explicitly across modules.
  Instead, components can harmlessly approximate them with [Vundef]
  and simulation conventions can leave them unconstrained.

  For queries, the set of relevant locations is specified by the
  following predicate. *)

Inductive loc_external (sg : signature) : loc -> Prop :=
  | loc_external_reg r:
      loc_external sg (R r)
  | loc_external_arg ofs ty:
      In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
      loc_external sg (S Outgoing ofs ty).

Definition loc_is_external (sg : signature) (l : loc) : bool :=
  match l with
    | R _ =>
      true
    | S Outgoing ofs ty =>
      if in_dec Loc.eq l (regs_of_rpairs (loc_arguments sg)) then true else false
    | _ =>
      false
  end.

Lemma loc_external_is sg l :
  loc_external sg l <-> loc_is_external sg l = true.
Proof.
  unfold loc_is_external. split.
  - destruct 1; auto. destruct in_dec; auto; contradiction.
  - destruct l as [ | [ ]]; try discriminate; constructor.
    destruct in_dec; congruence.
Qed.

Lemma loc_arguments_external sg p :
  In p (loc_arguments sg) ->
  forall_rpair (loc_external sg) p.
Proof.
  generalize (loc_arguments_acceptable sg p).
  generalize (loc_external_arg sg).
  induction loc_arguments; cbn in *; try contradiction.
  setoid_rewrite in_app.
  intros Hext Hacc [? | ?]; eauto 10; subst.
  specialize (Hacc (or_introl eq_refl)).
  destruct p; cbn in *.
  + destruct r as [ | [ ] ]; cbn in *; try contradiction;
    eauto 10 using loc_external_reg.
  + edestruct Hacc as [? ?].
    destruct rlo as [ | [ ] ]; cbn in *; try contradiction;
    destruct rhi as [ | [ ] ]; cbn in *; try contradiction;
    eauto 10 using loc_external_reg.
Qed.

(** After a query is received, the location state is initialized for
  those locations only, using the following construction. *)

Definition initial_regs (sg : signature) (ls : Locmap.t) (l : loc) : val :=
  if loc_is_external sg l then ls l else Vundef.

Lemma external_initial_regs sg rs l:
  loc_external sg l ->
  initial_regs sg rs l = rs l.
Proof.
  intros Hl. apply loc_external_is in Hl.
  unfold initial_regs. rewrite Hl. auto.
Qed.

Lemma getpair_initial_regs sg rs p:
  In p (loc_arguments sg) ->
  Locmap.getpair p (initial_regs sg rs) = Locmap.getpair p rs.
Proof.
  intros Hp. apply loc_arguments_external in Hp.
  destruct p; cbn in *; f_equal; intuition auto using external_initial_regs.
Qed.

(** A similar phenomenon occurs when external calls return. *)

Definition result_regs (sg : signature) (caller callee : Locmap.t) (l : loc) : val :=
  match l with
    | R r =>
      if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then callee (R r) else
      if is_callee_save r then caller (R r) else
      Vundef
    | S Outgoing _ _ =>
      Vundef
    | _ =>
      caller l
  end.

Lemma get_result_regs_result sg caller callee:
  Locmap.getpair (map_rpair R (loc_result sg)) (result_regs sg caller callee) =
  Locmap.getpair (map_rpair R (loc_result sg)) callee.
Proof.
  unfold result_regs. destruct (loc_result sg); cbn [map_rpair Locmap.getpair].
  - destruct in_dec; cbn in * |- ; intuition congruence.
  - destruct in_dec, in_dec; cbn in * |- ; intuition congruence.
Qed.

(** With the approach outlined above, simulation conventions only need
  to constrain external locations. The following relator is used. *)

Definition loc_external_rel sg (Rv: relation val) (ls1 ls2: Locmap.t): Prop :=
  forall l, loc_external sg l -> Rv (ls1 l) (ls2 l).

Definition loc_result_rel sg (Rv: relation val) (ls1 ls2: Locmap.t): Prop :=
  forall r, In r (regs_of_rpair (loc_result sg)) -> Rv (ls1 (R r)) (ls2 (R r)).

Lemma initial_regs_inject sg j ls1 ls2 :
  loc_external_rel sg (Val.inject j) ls1 ls2 ->
  (forall l, Val.inject j (initial_regs sg ls1 l) (initial_regs sg ls2 l)).
Proof.
  intros Hls l. unfold initial_regs.
  destruct loc_is_external eqn:Hl; auto.
  apply loc_external_is in Hl. auto.
Qed.

Lemma result_regs_inject sg j caller1 caller2 callee1 callee2:
  (forall l, Val.inject j (caller1 l) (caller2 l)) ->
  loc_result_rel sg (Val.inject j) callee1 callee2 ->
  forall l, Val.inject j (result_regs sg caller1 callee1 l) (result_regs sg caller2 callee2 l).
Proof.
  intros Hcaller Hcallee l. unfold result_regs.
  destruct l; auto.
  - destruct in_dec; auto.
    destruct is_callee_save; auto.
  - destruct sl; auto.
Qed.

(** This makes it much easier to to reason about locset-based
  simulation conventions. In particular, proving the commutation of
  [cc_locset_mach] with CKLRs involves constructing a new locset from
  the Mach state and proving that it is related to the source locset
  by the CKLR. The formulation we use makes it easier to avoid issues
  with extraneous locations which don't map to the target's stack or
  register. *)

(** ** Language interface *)

(** Location-based languages (currently LTL and Linear) use the
  following interface. We need to keep the C-level signature until
  Linear because it determines the stack layout used by the Linear
  to Mach calling convention to map locations to memory addresses. *)

Record locset_query :=
  lq {
    lq_vf: val;
    lq_sg: signature;
    lq_rs: Locmap.t;
    lq_mem: mem;
  }.

Record locset_reply :=
  lr {
    lr_rs: Locmap.t;
    lr_mem: mem;
  }.

Canonical Structure li_locset: language_interface :=
  {|
    query := locset_query;
    reply := locset_reply;
    entry := lq_vf;
  |}.

(** * Simulation conventions *)

Unset Program Cases.

(** ** C- to locset-style calling convention *)

(** We first define the calling convention between C and locset
  languages, which relates the C-level argument list to the contents
  of the locations. The Kripke world keeps track of the signature and
  initial values registers, so that the return value can be
  interpreted in the correct way and the preservation of callee-save
  registers can be enforced. *)

Inductive cc_c_locset_mq sg: c_query -> locset_query -> Prop :=
  cc_c_locset_mq_intro vf args rs m:
    args = (map (fun p => Locmap.getpair p rs) (loc_arguments sg)) ->
    cc_c_locset_mq sg (cq vf sg args m) (lq vf sg rs m).

Inductive cc_c_locset_mr sg: c_reply -> locset_reply -> Prop :=
  cc_c_locset_mr_intro res rs' m':
    res = Locmap.getpair (map_rpair R (loc_result sg)) rs' ->
    cc_c_locset_mr sg (cr res m') (lr rs' m').

Program Definition cc_c_locset: callconv li_c li_locset :=
  {|
    ccworld := signature;
    match_senv w := eq;
    match_query := cc_c_locset_mq;
    match_reply := cc_c_locset_mr;
  |}.

(** ** Locset-style CKLR convention *)

Inductive cc_locset_query R sg w: locset_query -> locset_query -> Prop :=
  cc_locset_query_intro vf1 vf2 ls1 ls2 m1 m2:
    Val.inject (mi R w) vf1 vf2 ->
    loc_external_rel sg (Val.inject (mi R w)) ls1 ls2 ->
    match_mem R w m1 m2 ->
    vf1 <> Vundef ->
    cc_locset_query R sg w (lq vf1 sg ls1 m1) (lq vf2 sg ls2 m2).

Inductive cc_locset_reply R sg w: locset_reply -> locset_reply -> Prop :=
  cc_locset_reply_intro ls1' ls2' m1' m2':
    loc_result_rel sg (Val.inject (mi R w)) ls1' ls2' ->
    match_mem R w m1' m2' ->
    cc_locset_reply R sg w (lr ls1' m1') (lr ls2' m2').

Program Definition cc_locset R :=
  {|
    match_senv '(sg, w) := match_stbls R w;
    match_query '(sg, w) := cc_locset_query R sg w;
    match_reply '(sg, w) := (<> cc_locset_reply R sg)%klr w;
  |}.
Next Obligation.
  split; auto.
  (* eapply match_stbls_proj in H. eapply Genv.mge_public; eauto. *)
Qed.
Next Obligation.
  eapply match_stbls_proj in H. eapply Genv.mge_public; eauto.
  (* eapply match_stbls_proj in H. erewrite <- Genv.valid_for_match; eauto. *)
Qed.
Next Obligation.
  split.
  intros.
  eapply match_stbls_proj in H. erewrite <- Genv.valid_for_match; eauto.
  intros.
  eapply match_stbls_proj in H. erewrite Genv.valid_for_match; eauto.
Qed.

Require Import CKLR CKLRAlgebra CallconvAlgebra.

Global Instance cc_locset_ref:
  Monotonic (@cc_locset) (subcklr ++> ccref).
Proof.
  red. red. intros r1 r2 SUB.
  red in SUB. red.
  intros (sg & w) se1 se2 q1 q2 Hse Hq.
  simpl in Hse, Hq. inv Hq.
  exploit SUB; eauto. intros (w2 & Hse2 & Hm2 & INCR & Hr).
  exists (sg, w2). repeat apply conj; eauto.
  econstructor; eauto.
  - red. intros. eapply Values.val_inject_incr; eauto.
  - intros. destruct H3 as (w2' & Hr3 & Hr4). inv Hr4.
    exploit Hr; eauto. 
    intros (w2'' & Hm' & ACC & INCR').
    econstructor. split; eauto.
    econstructor; eauto.
    red. intros. eapply Values.val_inject_incr; eauto.
Qed.

Require Import ClassicalChoice.

Lemma match_locset_query_compose (R12 R23: cklr) (w12: world R12) (w23: world R23) sg:
  eqrel    
    (cc_locset_query (R12 @ R23) sg (w12, w23))
    (rel_compose (cc_locset_query R12 sg w12) (cc_locset_query R23 sg w23)).
Proof.
  split.
  - red. intros _ _ [vf1 vf3 ls1 ls3 m1 m3 Hvf Hlr Hm NUN].
    simpl in *.
    apply val_inject_compose in Hvf. destruct Hvf as (vf2 & Hvf12 & Hv23).
    red in Hlr.
    assert (LOCM: exists ls2, forall (l: loc) ,
               loc_external sg l ->
               Val.inject (mi R12 w12) (ls1 l) (ls2 l)
               /\ Val.inject (mi R23 w23) (ls2 l) (ls3 l)).
    { apply choice with (R := fun (l: loc) w =>
                                loc_external sg l ->
                                Val.inject (mi R12 w12) (ls1 l) w
                                /\ Val.inject (mi R23 w23) w (ls3 l)).        
      intros l.
      destruct (loc_is_external sg l) eqn: EXT.
      eapply loc_external_is in EXT. 
      specialize (Hlr l EXT).
      eapply val_inject_compose in Hlr. destruct Hlr as (v' & Hlr1 & Hlr2).
      exists v'. eauto.
      exists Vundef. intro. eapply loc_external_is in H. congruence. }
    destruct LOCM as (ls2 & LOCM).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (lq vf2 sg ls2 m2); split; constructor; simpl; eauto.
    + red. intros. eapply LOCM; auto.
    + red. intros. eapply LOCM; auto.
    + destruct Hvf12; congruence.
  - intros q1 q3 (q2 & Hq12 & Hq23).
    destruct Hq23 as [vf1 vf2 ls2 ls3 m2 m3 Hvf Hlr23 Hm23 Hvf1].
    inv Hq12.
    constructor; simpl.
    + apply val_inject_compose. ercompose; eauto.
    + red. intros l LOC.
      specialize (Hlr23 l LOC).
      specialize (H4 l LOC).
      eapply val_inject_compose. eauto.
    + ercompose; eauto.
    + auto.
Qed.

Lemma cc_locset_compose R12 R23:
  cceqv (cc_locset (R12 @ R23)) (cc_locset R12 @ cc_locset R23).
Proof.
  split.
  - red. intros (sg & w12 & w23) se1 se3 q1 q3 (se2 & Hse12 & Hse23) Hq.
    apply match_locset_query_compose in Hq as (q2 & Hq12 & Hq23).
    exists (se2, (sg, w12), (sg, w23)).
    repeat apply conj.
    cbn; auto. cbn; eauto.
    intros r1 r3 (r2 & (w12' & Hw21' & Hr12) & (w23' & Hw23' & Hr23)).
    exists (w12', w23'). split. constructor; cbn; auto.
    destruct Hr12; inv Hr23.
    constructor; cbn; eauto.
    red. intros.
    red in H, H3.
    exploit H; eauto. exploit H3; eauto. intros.
    apply val_inject_compose; eauto.
  - intros [[se2 (sg1 & w12)] (sg2 & w23)] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    assert (sg1 = sg2).
    { inv Hq12. inv Hq23. auto. } subst.
    cbn in *. exists (sg2, (w12, w23)). repeat apply conj; eauto.
    + apply match_locset_query_compose; eauto.
    + intros r1 r3 ([w12' w23'] & Hw' & Hr).
      destruct Hr. cbn in *.
      red in H.
      assert (INJ: forall r,
                 In r (regs_of_rpair (loc_result sg2)) ->
                 (rel_compose (Val.inject (mi R12 w12')) (Val.inject (mi R23 w23'))) (ls1' (R r)) (ls2' (R r))).
      { intros. exploit H; eauto. intros INJ1.
        apply val_inject_compose in INJ1. eauto. }
      assert (LOCM: exists ls', forall (l: loc) ,
                 match l with
                 | R r => 
                     In r (regs_of_rpair (loc_result sg2)) ->
                     Val.inject (mi R12 w12') (ls1' (R r)) (ls' l)
                     /\ Val.inject (mi R23 w23') (ls' l) (ls2' (R r))               
                 | _ => True
                 end).
      { apply choice with (R := fun (l: loc) w =>
                 match l with
                 | R r => 
                     In r (regs_of_rpair (loc_result sg2)) ->
                     Val.inject (mi R12 w12') (ls1' (R r)) w
                     /\ Val.inject (mi R23 w23') w (ls2' (R r))
                 | _ => True
                 end).
        
        intros l. destruct l.
        2: { exists Vundef. eauto. }
        destruct (in_dec mreg_eq r (regs_of_rpair (loc_result sg2))).
        specialize (INJ r i). destruct INJ as (v' & INJ1 & INJ2).
        exists v'. intro. eauto.
        exists Vundef. intro. congruence. }
      destruct LOCM as (ls' & LOCM).
      destruct Hw' as [? ?], H0 as (mi & ? & ?).
      exists (lr ls' mi).
      split; eexists; constructor; eauto; constructor; eauto.
      * red. intros. specialize (LOCM (R r) H4) as (LOC1 & LOC2). eauto.
      * red. intros. specialize (LOCM (R r) H4) as (LOC1 & LOC2). eauto.
Qed.
