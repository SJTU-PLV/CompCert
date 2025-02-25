(** This file  provides the simulation convention algebra used in the
  [driver.Compiler] library to compose passes into the corresponding
  correctness theorem. *)

(** The main principle before our approach is to separate the structural
  aspect of calling conventions on one hand, which establish
  connections between the successive language interfaces, and the
  CKLRs used by various passes on the other hand, which can be
  promoted to endogenous simulation conventions for each language
  interface. Although composing the various pass correctness theorems
  directly yields a mixture of stuctural conventions and CKLRs, we use
  commutation properties to separate these two components. *)

(** More precisely, for a structural component [CC], we make sure that
  the following holds for all CKLRs [R]:
<<
                    ccref (CC @ R) (R @ CC)
>>
  In the context of external calls, this allows us to propagate CKLRs
  towards the source level, where they can be satisfied by the
  relational parametricity property of Clight. For incoming calls,
  this allows a target-level injection to be duplicated and propagated
  in order to satisfy the incoming simulation convention of the
  various compiler passes. *)

Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.
Unset Program Cases.

Coercion cc_c : cklr >-> callconv.


(** * Commutation properties *)

(** First, we define a general form for the commutation properties we
  need, and prove the straightforward ones. *)

(** ** Basic setup *)

(** The following class captures a general commutation property.
  In general, [cc] will be a structural simulation convention;
  [R1] and [R2] will be corresponding source- and target-level CKLR
  simulation conventions. *)

Class Commutes {liA liB} (cc: callconv liA liB) R1 R2 :=
  commute : ccref (cc @ R2) (R1 @ cc).

(** The following lemma provides a convenient way to use [commute] for
  rewriting within more complex sequences of simulation conventions. *)

Lemma commute_around `{Commutes} {liC} (x : callconv liB liC):
  ccref (cc @ R2 @ x) (R1 @ cc @ x).
Proof.
  rewrite <- !cc_compose_assoc.
  repeat (rstep; auto).
Qed.

Arguments commute_around {liA liB} cc {R1 R2 H liC x}.

(** Finally, we provide some composite instances for [Commutes]. *)

Instance commut_join {liA liB} cc R1 R2 S1 S2 :
  @Commutes liA liB cc R1 R2 ->
  @Commutes liA liB cc S1 S2 ->
  Commutes cc (R1 + S1) (R2 + S2).
Proof.
  intros. red.
  rewrite cc_join_distr_l, cc_join_distr_r, !commute.
  reflexivity.
Qed.

Instance commut_star `(Commutes):
  Commutes cc (R1^{*}) (R2^{*}).
Proof.
  red.
  rewrite <- (cc_compose_id_left cc), (cc_id_star R1) at 1.
  apply cc_star_ind_r.
  rewrite cc_compose_assoc, commute, <- cc_compose_assoc.
  rewrite (cc_one_star R1) at 2. rewrite cc_star_idemp.
  reflexivity.
Qed.

Instance commut_compose {liA liB liC} cc1 cc2 RA RB RC:
  @Commutes liA liB cc1 RA RB ->
  @Commutes liB liC cc2 RB RC ->
  Commutes (cc1 @ cc2) RA RC.
Proof.
  intros HAB HBC. red.
  rewrite cc_compose_assoc, commute, <- cc_compose_assoc, commute, cc_compose_assoc.
  reflexivity.
Qed.

(** ** [cc_c_locset] *)

(** The commutation of [cc_c_locset] basically follows the way the
  original LTL semantics evaluates calls to external functions:
  for queries, we read out the arguments from the location set;
  once we get a C reply, we write back the
  result and mark the appropriate registers undefined. *)

Lemma locmap_getpair_inject f ls1 ls2 p:
  forall_rpair (fun l => Val.inject f (ls1 l) (ls2 l)) p ->
  Val.inject f (Locmap.getpair p ls1) (Locmap.getpair p ls2).
Proof.
  destruct p; cbn; intuition auto.
  apply Val.longofwords_inject; auto.
Qed.

(** For now we restrict ourselves to 64-bit x86, where no register
  pairs are involved. Eventually we'll want to fold register typing
  into the property below (or maybe the calling conventions
  themselves) to ensure that split integers are the right sizes. *)

Lemma loc_arguments_always_one sg p:
  In p (loc_arguments sg) ->
  exists l, p = One l.
Proof.
  unfold loc_arguments. replace Archi.ptr64 with true by reflexivity.
  destruct Archi.win64.
* cut (forall x y, In p (loc_arguments_win64 (sig_args sg) x y) -> exists l, p = One l).
  - eauto.
  - induction (sig_args sg); cbn.
    + contradiction.
    + intros x y.
      destruct a, (if zeq x _ then _ else _); cbn; intros [? | ?]; eauto.
* cut (forall x y z, In p (loc_arguments_elf64 (sig_args sg) x y z) -> exists l, p = One l).
  - intros. apply (H 0 0 0). apply H0.
  - induction sig_args; cbn -[list_nth_z].
    + tauto.
    + intros x y z.
      destruct a, list_nth_z; cbn; intros [? | ?]; eauto.
Qed.

Lemma loc_result_always_one sg:
  exists r, loc_result sg = One r.
Proof.
  change loc_result with loc_result_64. unfold loc_result_64.
  destruct proj_sig_res as [ | | | | | ]; eauto.
Qed.

Instance commut_c_locset R:
  Commutes cc_c_locset (cc_c R) (cc_locset R).
Proof.
  intros [[_ w] [sg wR]] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hqi2. inv Hq1i.
  exists (se2, wR, sg). repeat apply conj.
  - cbn; auto.
  - set (args1 := (fun p => Locmap.getpair p ls1) ## (loc_arguments sg)).
    set (args2 := (fun p => Locmap.getpair p ls2) ## (loc_arguments sg)).
    exists (cq vf2 sg args2 m2). split.
    + constructor; auto. clear - H0. subst args1 args2.
      unfold loc_external_rel in H0.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + constructor; auto.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2. rename rs' into ls2'.
    set (ls1' := Locmap.setpair (loc_result sg) vres1 (LTL.undef_caller_save_regs ls1)).
    exists (lr ls1' m1'). split.
    + constructor.
      * subst ls1'. clear.
        destruct (loc_result_always_one sg) as [r ->].
        cbn. rewrite Locmap.gss. reflexivity.
    + eexists; split; eauto.
      constructor; auto. subst ls1'. red.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto.
Qed.

(** ** [cc_mach_asm] *)

(** The commutation property for [cc_mach_asm] is straightforward.
  The only subtlety is reconstructing the intermediate [Asm.regset]
  from the source reply's [Mach.regset]. *)

Inductive preg_class :=
  | prc_pc
  | prc_sp
  | prc_preg_of (r : mreg)
  | prc_other.

Inductive preg_classify_spec : preg_class -> preg -> Prop :=
  | prc_pc_spec : preg_classify_spec prc_pc PC
  | prc_sp_spec : preg_classify_spec prc_sp SP
  | prc_preg_spec m : preg_classify_spec (prc_preg_of m) (preg_of m)
  | prc_other_spec r : preg_classify_spec prc_other r.

Definition preg_classify r :=
  match r with
    | PC => prc_pc
    | SP => prc_sp
    | RAX => prc_preg_of AX
    | RBX => prc_preg_of BX
    | RCX => prc_preg_of CX
    | RDX => prc_preg_of DX
    | RSI => prc_preg_of SI
    | RDI => prc_preg_of DI
    | RBP => prc_preg_of BP
    | R8 => prc_preg_of Machregs.R8
    | R9 => prc_preg_of Machregs.R9
    | R10 => prc_preg_of Machregs.R10
    | R11 => prc_preg_of Machregs.R11
    | R12 => prc_preg_of Machregs.R12
    | R13 => prc_preg_of Machregs.R13
    | R14 => prc_preg_of Machregs.R14
    | R15 => prc_preg_of Machregs.R15
    | XMM0 => prc_preg_of X0
    | XMM1 => prc_preg_of X1
    | XMM2 => prc_preg_of X2
    | XMM3 => prc_preg_of X3
    | XMM4 => prc_preg_of X4
    | XMM5 => prc_preg_of X5
    | XMM6 => prc_preg_of X6
    | XMM7 => prc_preg_of X7
    | XMM8 => prc_preg_of X8
    | XMM9 => prc_preg_of X9
    | XMM10 => prc_preg_of X10
    | XMM11 => prc_preg_of X11
    | XMM12 => prc_preg_of X12
    | XMM13 => prc_preg_of X13
    | XMM14 => prc_preg_of X14
    | XMM15 => prc_preg_of X15
    | ST0 => prc_preg_of FP0
    | RA | CR _ => prc_other
  end.

Lemma preg_classify_preg m:
  preg_classify (preg_of m) = prc_preg_of m.
Proof.
  destruct m; auto.
Qed.

Lemma preg_classify_cases r:
  preg_classify_spec (preg_classify r) r.
Proof.
  destruct r as [ | [ ] | [ ] | | | ]; constructor.
Qed.

Instance commut_mach_asm R:
  Commutes cc_mach_asm (cc_mach R) (cc_asm R).
Proof.
  intros [[_ [rs1 nb1]] wR] se1 se2 q1 q2 [[ ] Hse2] (qi & Hq1i & Hqi2).
  cbn in * |- . destruct Hq1i. destruct q2 as [rs2 m2], Hqi2 as (Hrs & Hpc & Hm).
  rename m into m1.
  exists (se2, wR, (rs2, Mem.support m2)). cbn. repeat apply conj; auto.
  - exists (mq rs2#PC rs2#SP rs2#RA (fun r => rs2 (preg_of r)) m2). split.
    + constructor; auto.
      * destruct H0; congruence.
      * setoid_rewrite H2. eauto.
    + constructor; auto.
      * destruct (Hrs PC); cbn in *; congruence.
      * specialize (Hrs SP). destruct Hrs; inv H0. constructor.
        revert H6.
        change (sup_In b1 (Mem.support m1)) with (Mem.valid_block m1 b1).
        change (sup_In b2 (Mem.support m2)) with (Mem.valid_block m2 b2).
        rstep. rstep. rstep. rstep. red. eauto.
      * specialize (Hrs RA). destruct Hrs; congruence.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & Hri2). inv Hri2. inv Hr1i.
    set (rs1' r :=
           match preg_classify r with
             | prc_pc => rs1 RA
             | prc_sp => rs1 SP
             | prc_preg_of m => rs0 m
             | prc_other => Vundef
           end).
    exists (rs1', m0). split.
    + constructor; eauto.
      * eapply cklr_sup_include; eauto. rauto.
      * subst rs1'. intros r. cbn. rewrite preg_classify_preg. auto.
    + exists wR'. split; auto. constructor; eauto.
      intros r. subst rs1'. cbn.
      destruct (preg_classify_cases r).
      * rewrite H4. generalize (Hrs RA). rauto.
      * rewrite H3. generalize (Hrs SP). rauto.
      * rewrite <- H6. eauto.
      * constructor.
Qed.


(** * Typing invariants *)

(** On their own, the typing invariants [wt_c] and [wt_loc] do not
  commute with CKLRs. This is because a source value may be [Vundef],
  hence well-typed, even when the target value is defined but ill-typed.
  However, we can recover a sufficient commutation property by
  introducing some slack as [wt @ lessdef], where [lessdef] is a
  simulation convention allowing values to be refined. Then we can use
  [Val.ensure_type] to make sure that the intermediate values are
  well-typed. *)

(** ** Helper lemmas *)

Lemma val_lessdef_inject_list_compose f vs_ vs1 vs2:
  Val.lessdef_list vs_ vs1 ->
  Val.inject_list f vs1 vs2 ->
  Val.inject_list f vs_ vs2.
Proof.
  intros Hvs_ Hvs. revert vs2 Hvs.
  induction Hvs_.
  - inversion 1; constructor.
  - inversion 1; subst; constructor; eauto.
    eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

Lemma has_type_inject f v1 v2 t:
  Val.has_type v1 t ->
  Val.inject f v1 v2 ->
  Val.inject f v1 (Val.ensure_type v2 t).
Proof.
  intros.
  rewrite <- (Val.has_type_ensure v1 t) by auto.
  apply Val.ensure_type_inject; auto.
Qed.

Lemma has_type_inject_list f vl1 vl2 tl:
  Val.has_type_list vl1 tl ->
  Val.inject_list f vl1 vl2 ->
  exists vl2',
    Val.has_type_list vl2' tl /\
    Val.inject_list f vl1 vl2' /\
    Val.lessdef_list vl2' vl2.
Proof.
  intros Htl Hv. revert tl Htl.
  induction Hv; cbn in *.
  - destruct tl; try contradiction. intros _.
    exists nil. repeat constructor.
  - destruct tl as [ | t tl]; try contradiction. intros [Ht Htl].
    edestruct IHHv as (vl2' & Hvl2' & Hvl & Hvl2); eauto.
    exists (Val.ensure_type v' t :: vl2'). repeat (constructor; auto).
    + apply Val.ensure_has_type.
    + apply has_type_inject; auto.
    + destruct v', t; auto.
Qed.

(** ** C-level typing constraints *)

Inductive lessdef_c_mq: c_query -> c_query -> Prop :=
  lessdef_c_mq_intro vf sg args_ args m:
    Val.lessdef_list args_ args ->
    lessdef_c_mq (cq vf sg args_ m) (cq vf sg args m).

Inductive lessdef_c_mr: c_reply -> c_reply -> Prop :=
  lessdef_c_mr_intro res_ res m:
    Val.lessdef res_ res ->
    lessdef_c_mr (cr res_ m) (cr res m).

Program Definition lessdef_c : callconv li_c li_c :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := lessdef_c_mq;
    match_reply _ := lessdef_c_mr;
  |}.

Lemma lessdef_c_cklr R:
  cceqv (lessdef_c @ cc_c R) (cc_c R).
Proof.
  split.
  - intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in * |-.
    destruct Hqi2. inv Hq1i.
    eexists wR. cbn. repeat apply conj; auto.
    + constructor; auto. clear - H0 H5.
      eapply val_lessdef_inject_list_compose; eauto.
    + intros r1 r2 Hr. exists r1; split; auto.
      destruct r1; constructor; auto.
  - intros wR se1 se2 q1 q2 Hse Hq.
    exists (se1, tt, wR). repeat apply conj; cbn; eauto.
    + exists q1. split; auto. destruct q1. constructor; auto.
      clear. induction cq_args; constructor; auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2).
      exists wR'. split; auto. destruct Hri2; inv Hr1i; constructor; auto.
      eapply Mem.val_lessdef_inject_compose; eauto.
Qed.

Instance commut_wt_c (R : cklr):
  Commutes (wt_c @ lessdef_c) R R.
Proof.
  red. rewrite cc_compose_assoc. rewrite lessdef_c_cklr.
  intros [[_ [ ]] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H4. cbn [cq_sg cq_args] in *.
  eexists (se2, wR, (se2, (se2, sg), tt)). repeat apply conj; cbn.
  + repeat constructor; cbn; auto.
  + edestruct has_type_inject_list as (vl2 & Hvl2 & Hvl & Hvl'); eauto.
    exists (cq vf2 sg vl2 m2). split.
    * constructor; eauto.
    * eexists. split; constructor; cbn; eauto.
  + intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. cbn in *.
    eexists; split.
    * constructor. cbn. eapply val_has_type_inject; eauto.
    * exists wR'. split; auto. constructor; eauto.
      eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

Lemma lessdef_list_refl : forall l,
    Val.lessdef_list l l.
Proof.
  induction l. constructor.
  constructor; eauto.
Qed.

Lemma val_inject_lessdef_list_compose f v1 v2 v3:
  Val.inject_list f v1 v2 ->
  Val.lessdef_list v2 v3 ->
  Val.inject_list f v1 v3.
Proof.
  intros Hv12. revert v3.
  induction Hv12; inversion 1; subst; constructor; eauto.
  eapply Mem.val_inject_lessdef_compose; eauto.
Qed.

(** ** Locset-level typing constraints *)

Inductive lessdef_loc_mq sg: locset_query -> locset_query -> Prop :=
  lessdef_loc_mq_intro vf ls1 ls2 m:
    loc_external_rel sg Val.lessdef ls1 ls2 ->
    lessdef_loc_mq sg (lq vf sg ls1 m) (lq vf sg ls2 m).

Inductive lessdef_loc_mr sg: locset_reply -> locset_reply -> Prop :=
  lessdef_loc_mr_intro ls1' ls2' m:
    loc_result_rel sg Val.lessdef ls1' ls2' ->
    lessdef_loc_mr sg (lr ls1' m) (lr ls2' m).

Program Definition lessdef_loc :=
  {|
    match_senv _ := eq;
    match_query := lessdef_loc_mq;
    match_reply := lessdef_loc_mr;
  |}.

Lemma lessdef_loc_cklr R:
  cceqv (lessdef_loc @ cc_locset R) (cc_locset R).
Proof.
  split.
  - intros [[_ xsg] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
    destruct Hqi2. inv Hq1i.
    exists (sg, wR). cbn. repeat apply conj; auto.
    + constructor; auto. intros l Hl.
      eapply Mem.val_lessdef_inject_compose; auto.
    + intros r1 r2 Hr. exists r1. split; auto.
      destruct r1. constructor. intros l Hl. auto.
  - intros [sg wR] se1 se2 q1 q2 Hse Hq. inv Hq.
    exists (se1, sg, (sg, wR)). repeat apply conj; cbn; auto.
    + eexists. split; constructor; eauto. intros l Hl. auto.
    + intros r1 r2 (ri & Hr1i & wR' & HwR' & Hri2). exists wR'. split; auto.
      destruct Hri2. inv Hr1i. constructor; auto.
      intros l Hl. eapply Mem.val_lessdef_inject_compose; auto.
Qed.

Instance commut_wt_loc R:
  Commutes (wt_loc @ lessdef_loc) (cc_locset R) (cc_locset R).
Proof.
  red. rewrite cc_compose_assoc, lessdef_loc_cklr.
  intros [[_ [xse xsg]] [sg wR]] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. inv H. inv H4.
  exists (se2, (sg, wR), (se2, (se2, sg), sg)). cbn. repeat apply conj; eauto.
  - constructor; auto.
  - set (ls2_ l := Val.ensure_type (ls2 l) (Loc.type l)).
    exists (lq vf2 sg ls2_ m2). split.
    + constructor; auto. intros l Hl. apply has_type_inject; auto.
    + eexists. split; constructor.
      * constructor. intros. apply Val.ensure_has_type.
      * intros l Hl. subst ls2_; cbn. destruct (ls2 l), Loc.type; cbn; auto.
  - intros r1 r2 (ri & (wR' & HwR' & Hr1i) & rj & Hrij & Hrj2).
    destruct Hr1i. inv Hrij. inv Hrj2. inv H6.
    exists (lr ls1' m1'). split.
    + constructor. constructor. intros r Hr.
      eapply val_has_type_inject; eauto. red. eauto.
    + exists wR'. split; auto. constructor; auto.
      intros r Hr. eapply Mem.val_inject_lessdef_compose; auto.
Qed.

(** ** Another option for [wt_c] *)

(** An alternative approach for [wt_c] would be to formulate a typing
  constraint on the target queries and replies, which can be
  propagated towards the source as [ccref (cc @ wt) (wt @ cc @ wt)].
  Then we can use the following property to make it part of the
  source-level compatibility relations to satisfy the typing
  requirements of other components' external calls. *)

Lemma star_inv_prop {li} (R : callconv li li) (I : invariant li) :
  PropagatesReplyInvariant 1 I ->
  PropagatesQueryInvariant R I ->
  PropagatesReplyInvariant R I ->
  cceqv ((R + I)^{*} @ I) (R^{*} @ I).
Proof.
  split.
  - rewrite (proj2 (cc_compose_id_left I)) at 2.
    rewrite (cc_id_star R).
    apply cc_star_ind_l.
    rewrite cc_join_distr_l.
    apply cc_join_lub.
    + rewrite (cc_one_star R) at 1.
      rewrite <- cc_compose_assoc, cc_star_idemp.
      reflexivity.
    + apply (inv_drop _ _).
  - repeat rstep. apply cc_join_ub_l.
Qed.


(** * Stacking *)

(** The simulation conventions for most passes are simple enough that
  we can express them directly as [R @ CC], where [R] is a CKLR
  matching the memory relation used in the simulation proof, and
  [CC] expresses the structural correspondance between source- and
  target-level queries and replies. However, the Stacking pass
  involves fairly complex invariants and it is simpler to formulate
  the corresponding simulation convention as a monolithic one, closely
  coupled with the corresponding simulation proof.

  In the following we show that this simulation convention can then be
  decoupled into a CKLR and a structural convention. This form is then
  used as the outside interface for the pass and integrated to the
  strategy outlined above. *)

Require Import Classical.

(** ** Structural convention *)

(** The first step is to define the structural convention we will be
  using between [li_locset] and [li_mach]. *)

(** *** Dealing with the arguments region *)

(** One key aspect of this convention is the encoding of arguments: at
  the source level, arguments for the call are stored in abstract
  locations, which become either registers or in-memory stack slots at
  the target level. Crucially, these stack slots must not be
  accessible as memory locations in the source program, otherwise the
  invariant relating abstract and concrete stack locations may be
  broken through aliasing. Hence, in the structural convention the
  source memory cannot be *equal* to the target memory, but instead
  must be a version of the target memory where permissions on the
  arguments region of the stack have been removed.

  For queries, this can be expressed using [Mem.free]. We also deal
  separately with the case where no arguments are stored in the stack.
  This is both to ensure the compatibility of [args_removed] with
  injection, and to allow [Vnullptr] as a possible stack pointer for
  the initial call to [main()]. *)

Inductive args_removed sg: val -> mem -> mem -> Prop :=
  | args_removed_tailcall_possible sp m:
      tailcall_possible sg ->
      args_removed sg sp m m
  | args_removed_free sb sofs m m_:
      Mem.free m sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) = Some m_ ->
      (forall ofs, 0 <= ofs < size_arguments sg -> offset_fits sofs ofs) ->
      size_arguments sg > 0 ->
      (forall ofs ty,
        In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
        exists v, load_stack m (Vptr sb sofs) ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) = Some v) ->
      args_removed sg (Vptr sb sofs) m m_.

(** This takes care of how the LTL memory state is obtained from the
  Mach-level one. In addition, the following construction reconstructs
  the LTL-level [locset] from the Mach-level [regset] by reading the
  additional stack locations from the Mach memory. *)

Definition make_locset (rs: Mach.regset) (m: mem) (sp: val) (l: loc) : val :=
  match l with
    | R r => rs r
    | S Outgoing ofs ty =>
      let v := load_stack m sp ty (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) in
      Val.maketotal v
    | _ => Vundef
  end.

(** For replies, in some simulation convention refinement properties
  we want to establish, the source memory state is often given to us
  and we have to establish the relationship. This means we can't use
  [Mem.free] in the same way; fortunately, it is enough to give a more
  extensional characterization in terms of [Mem.unchanged] involving
  the following address predicate. *)

Definition not_init_args (sz: Z) (sp: val) :=
  fun b ofs => ~ loc_init_args sz sp b ofs.


Theorem loc_init_args_dec:
  forall sz sp b ofs,
    {loc_init_args sz sp b ofs} + {not_init_args sz sp b ofs}.
Proof.
  intros. destruct sp.
  right; intro; inv H. 
  right; intro; inv H.
  right; intro; inv H.
  right; intro; inv H.
  right; intro; inv H.
  destruct (eq_block b0 b). subst.
  destruct (zle (offset_sarg i 0) ofs);
  destruct (zlt ofs (offset_sarg i sz)).
  left. constructor; eauto.
  right. intro. inv H. extlia.
  right. intro. inv H. extlia.
  right. intro. inv H. extlia.
  right. intro. inv H. congruence.
Qed.


(** *** Definition *)

(** We can now define the structural convention
  from [li_locset] to [li_mach]. *)

Record cc_lm_world :=
  lmw {
    lmw_sg : signature;
    lmw_rs : Mach.regset;
    lmw_m : mem;
    lmw_sp : val;
  }.

Inductive cc_locset_mach_mq: cc_lm_world -> locset_query -> mach_query -> Prop :=
  cc_locset_mach_mq_intro sg vf m_ rs sp ra m:
    args_removed sg sp m m_ ->
    Val.has_type sp Tptr ->
    Val.has_type ra Tptr ->
    cc_locset_mach_mq
      (lmw sg rs m sp)
      (lq vf sg (make_locset rs m sp) m_)
      (mq vf sp ra rs m).

Inductive cc_locset_mach_mr: cc_lm_world -> locset_reply -> mach_reply -> Prop :=
  cc_locset_mach_mr_intro sg rs ls' m'_ sp m rs' m':
    (forall r, In r (regs_of_rpair (loc_result sg)) -> rs' r = ls' (R r)) ->
    (forall r, is_callee_save r = true -> rs' r = rs r) ->
    Mem.unchanged_on (not_init_args (size_arguments sg) sp) m'_ m' ->
    Mem.unchanged_on (loc_init_args (size_arguments sg) sp) m m' ->
    Mem.support m'_ = Mem.support m' ->
    (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                       ~ Mem.perm m'_ b ofs k p) ->
    (*Mem.extends m'_ m' ->*)
    cc_locset_mach_mr (lmw sg rs m sp) (lr ls' m'_) (mr rs' m').

Program Definition cc_locset_mach: callconv li_locset li_mach :=
  {|
    match_senv _ := eq;
    match_query := cc_locset_mach_mq;
    match_reply := cc_locset_mach_mr;
  |}.

(** ** Commutation property *)

(** For queries, we need to synthesizing the target-level locset by
  extracting arguments from the memory and then removing them. *)

Lemma offset_sarg_inject R w m1 m2 sb1 sofs1 sb2 sofs2 ofs:
  match_mem R w m1 m2 ->
  Mem.perm m1 sb1 (offset_sarg sofs1 0) Cur Freeable ->
  ptrbits_inject (mi R w) (sb1, sofs1) (sb2, sofs2) ->
  ptr_inject (mi R w) (sb1, offset_sarg sofs1 ofs) (sb2, offset_sarg sofs2 ofs).
Proof.
  intros Hm Hp Hsp. inv Hsp.
  unfold offset_sarg in *. rewrite Z.add_0_r in Hp.
  apply ptr_inject_shift.
  eapply ptrbits_ptr_inject; eauto.
  rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr _)), <- Ptrofs.add_assoc.
  constructor; auto.
Qed.

Lemma offset_sarg_expand ofs sofs:
  offset_sarg sofs ofs = offset_sarg sofs 0 + 4 * ofs.
Proof.
  unfold offset_sarg. extlia.
Qed.

Lemma offset_sarg_ptrrange_inject R w m1 m2 sb1 sofs1 sb2 sofs2 ofs:
  match_mem R w m1 m2 ->
  Mem.perm m1 sb1 (offset_sarg sofs1 0) Cur Freeable ->
  ptrbits_inject (mi R w) (sb1, sofs1) (sb2, sofs2) ->
  ptrrange_inject (mi R w)
    (sb1, offset_sarg sofs1 0, offset_sarg sofs1 ofs)
    (sb2, offset_sarg sofs2 0, offset_sarg sofs2 ofs).
Proof.
  intros. rewrite !(offset_sarg_expand ofs).
  rstep. eapply offset_sarg_inject; eauto.
Qed.

Lemma offset_fits_inject R w m1 m2 sb1 sb2 delta sofs1 sofs2 ofs sz:
  match_mem R w m1 m2 ->
  Mem.range_perm m1 sb1 (offset_sarg sofs1 0) (offset_sarg sofs1 sz) Cur Freeable ->
  0 <= ofs < sz ->
  mi R w sb1 = Some (sb2, delta) ->
  sofs2 = Ptrofs.add sofs1 (Ptrofs.repr delta) ->
  offset_fits sofs1 ofs ->
  offset_fits sofs2 ofs.
Proof.
  intros Hm PERM Hofs Hsb Hsofs2 FITS.
  unfold offset_fits, offset_sarg in *. subst sofs2.
  rewrite !(Ptrofs.add_commut sofs1).
  rewrite !(Ptrofs.add_assoc (Ptrofs.repr delta)).
  rewrite !(Ptrofs.add_commut (Ptrofs.repr delta)).
  erewrite cklr_address_inject; eauto.
  rewrite <- (Z.add_assoc _ delta), (Z.add_comm delta), Z.add_assoc.
  setoid_rewrite FITS.
  erewrite <- cklr_address_inject; eauto.
  * eapply PERM. extlia.
  * eapply PERM. extlia.
Qed.

Instance load_stack_inject R:
  Monotonic load_stack
    (|= match_mem R ++> Val.inject @@ [mi R] ++> - ==> - ==>
        k1 option_le (Val.inject @@ [mi R])).
Proof.
  unfold load_stack. rauto.
Qed.

Instance args_removed_cklr R:
  Monotonic args_removed
    (|= - ==> Val.inject @@ [mi R] ++> match_mem R ++> k1 set_le (<> match_mem R)).
Proof.
  intros w sg sp1 sp2 Hsp m1 m2 Hm m1_ Hm1_.
  destruct Hm1_ as [sp m1 | sb1 sofs1 m1 m1_ FREE FITS].
  - exists m2. split; [ | rauto].
    constructor; auto.
  - inversion Hsp. subst.
    set (sofs2 := Ptrofs.add _ _).
    assert (forall ofs,
      ptr_inject (mi R w) (sb1, offset_sarg sofs1 ofs) (b2, offset_sarg sofs2 ofs)).
    {
      intro. eapply offset_sarg_inject; eauto.
      + eapply Mem.free_range_perm; eauto. unfold offset_sarg. extlia.
      + constructor; auto.
    }
    assert
        (ptrrange_inject (mi R w)
                        (sb1, offset_sarg sofs1 0, offset_sarg sofs1 (size_arguments sg))
                        (b2, offset_sarg sofs2 0, offset_sarg sofs2 (size_arguments sg))).
    {
      eapply ptr_ptrrange_inject; split; eauto.
      unfold offset_sarg. extlia.
    }
    generalize FREE. transport FREE. intros FREE.
    eexists; split.
    + eapply args_removed_free; eauto.
      * clear - Hm FITS H3 FREE.
        intros ofs Hofs. eapply offset_fits_inject; eauto.
        -- eapply Mem.free_range_perm; eauto.
        -- reflexivity.
      * intros ofs ty REG. edestruct H0 as [v Hv]; eauto.
        transport Hv. eauto.
    + rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @args_removed : typeclass_instances.

(** For replies, the challenge is to construct a version of the source
  memory state which contains the original arguments, and a version of
  the source [Mach.regset] which contains the right mixture of
  original callee-save registers and results from the reply's
  locset. The following lemmas will help. *)

Class Mixable (R : cklr) :=
  result_mem sz sp1 sp2 w m1 m2 w' m1'_ m2'_ m2':
    w ~> w' ->
    Val.inject (mi R w) sp1 sp2 ->
    match_mem R w m1 m2 ->
    match_mem R w' m1'_ m2'_ ->
    Mem.unchanged_on (loc_init_args sz sp2) m2 m2' ->
    Mem.unchanged_on (not_init_args sz sp2) m2'_ m2' ->
    Mem.extends m2'_ m2' ->
    (forall b ofs,
        loc_init_args sz sp2 b ofs ->
        loc_out_of_reach (mi R w') m1'_ b ofs) ->
    (2 | sz) ->
    (sz > 0 -> valid_blockv (Mem.support m1) sp1) ->
    (sz > 0 -> forall b1 ofs1, sp1 = Vptr b1 ofs1 ->
      Mem.range_perm m1 b1 (offset_sarg ofs1 0) (offset_sarg ofs1 sz) Cur Freeable) ->
    exists w'' m1',
      w ~> w'' /\
      inject_incr (mi R w') (mi R w'') /\
      match_mem R w'' m1' m2' /\
      Mem.unchanged_on (loc_init_args sz sp1) m1 m1' /\
      Mem.unchanged_on (not_init_args sz sp1) m1'_ m1' /\
      Mem.support m1' = Mem.support m1'_.
(*
Instance ext_mixable:
  Mixable ext.
Proof.
  intros sz sp1 sp2 [ ] m1 m2 [ ] m1'_ m2'_ m2' _ Hsp Hm Hm'_ UPD UNCH EXT OOR _ VB.
  uncklr.
  destruct (classic (sz > 0 /\ exists sb1 sofs1, sp1 = Vptr sb1 sofs1)).
  - destruct H as (SZ & sb1 & sofs1 & Hsp1). subst. inv Hsp.
    assert (Mem.mixable m1'_ sb1 m1). {
      split.
      + erewrite (Mem.mext_sup m1) by eauto.
        erewrite (Mem.mext_sup m1'_) by eauto.
        erewrite (Mem.mext_sup m2'_) by eauto.
        eapply Mem.unchanged_on_support; eauto.
      + specialize (VB SZ). inv VB. auto. (* could restrict to sz > 0 case *)
    }
    eapply Mem.mixable_mix in H as [m1' ?].
    exists tt, m1'. repeat apply conj.
    + constructor.
    + apply inject_incr_refl.
    + cbn. eapply Mem.mix_left_extends; eauto.
      * eapply Mem.extends_extends_compose; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros _ ofs [-> Hofs] VLD. constructor; eauto.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_updated.
      inversion 1; auto.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_unchanged.
      intros _ ofs NIA _ [<- Hofs]. apply NIA. constructor; auto.
    + apply Mem.support_mix in H. auto.
  - exists tt, m1'_. repeat apply conj.
    + constructor.
    + apply inject_incr_refl.
    + eapply Mem.extends_extends_compose; eauto.
    + split.
      * erewrite (Mem.mext_sup m1) by eauto.
        erewrite (Mem.mext_sup m1'_) by eauto.
        erewrite (Mem.mext_sup m2'_) by eauto.
        eapply Mem.unchanged_on_support; eauto.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in *. extlia.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in *. extlia.
    + apply Mem.unchanged_on_refl.
    + reflexivity.
Qed.
*)
Instance inj_mixable:
  Mixable inj.
Proof.
  intros sz sp1 sp2 w m1 m2 w' m1'_ m2'_ m2' Hw Hsp Hm Hm'_ UPD UNCH EXT OOR SZ VB.
  destruct SZ as [k Hk]; subst.
  destruct (classic (k > 0 /\ exists sb1 sofs1, sp1 = Vptr sb1 sofs1)).
  - destruct H as (Hk & sb1 & sofs1 & Hsp1). subst. inv Hsp.
    assert (Mem.mixable m1'_ sb1 m1). {
      split.
      + destruct Hm, Hm'_. inv Hw. auto.
      + assert (SZ: k * 2 > 0) by extlia.
        specialize (VB SZ). inv VB. auto.
    }
    eapply Mem.mixable_mix in H as [m1' Hm1'].
    instantiate (1 := offset_sarg sofs1 (k * 2)) in Hm1'.
    instantiate (1 := offset_sarg sofs1 0) in Hm1'.
    exists w', m1'. repeat apply conj.
    + auto.
    + apply inject_incr_refl.
    + inv Hm. inv Hm'_. inv Hw. cbn -[Z.add Z.mul] in *.
      erewrite <- (Mem.support_mix m1'_); eauto.
      erewrite (Mem.mext_sup m2'_); eauto.
      constructor. eapply Mem.mix_left_inject; eauto.
      * eapply Mem.inject_extends_compose; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros _ ofs [-> Hofs] VLD. constructor.
        unfold offset_sarg in *.
        rewrite (Ptrofs.add_commut sofs1), Ptrofs.add_assoc, Ptrofs.add_commut.
        erewrite (Mem.address_inject f m1 m2); eauto. extlia.
        eapply H; eauto. extlia. extlia.
      * intros b1' delta' ofs pk p Hb' Hofs Hp.
        eapply (OOR b2 ofs); eauto.
        -- constructor. unfold offset_sarg in *.
           rewrite (Ptrofs.add_commut sofs1), Ptrofs.add_assoc, Ptrofs.add_commut.
           erewrite (Mem.address_inject f m1 m2); eauto. extlia.
           eapply H; eauto. extlia. extlia.
        -- eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
      * eapply Mem.mi_align with (chunk := Mint64); eauto using (Mem.mi_inj f m1 m2).
        instantiate (2 := offset_sarg sofs1 0). intros ofs Hofs.
        eapply Mem.perm_max, H; eauto; unfold offset_sarg in *; cbn in Hofs; extlia.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_updated.
      inversion 1; auto.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_unchanged.
      intros _ ofs NIA _ [<- Hofs]. apply NIA. constructor; auto.
    + eapply Mem.support_mix; eauto.
  - inv Hm. inv Hm'_. inv Hw. cbn in *.
    eexists (injw f0 (Mem.support m1'_) (Mem.support m2')), m1'_. repeat apply conj.
    + constructor; eauto.
      eapply Mem.unchanged_on_support; eauto.
    + apply inject_incr_refl.
    + constructor. eapply Mem.inject_extends_compose; eauto.
    + split.
      * eauto.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in H3. extlia.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in H3. extlia.
    + apply Mem.unchanged_on_refl.
    + reflexivity.
Qed.

Instance injp_mixable:
  Mixable injp.
Proof.
  intros sz sp1 sp2 w m1 m2 w' m1'_ m2'_ m2' Hw Hsp Hm Hm'_ UPD UNCH EXT OOR SZ VB.
  destruct SZ as [k Hk]; subst.
  destruct (classic (k > 0 /\ exists sb1 sofs1, sp1 = Vptr sb1 sofs1)).
  - destruct H as (Hk & sb1 & sofs1 & Hsp1). subst. inv Hsp.
    assert (Mem.mixable m1'_ sb1 m1). {
      split.
      + destruct Hm, Hm'_. inv Hw. destruct H10 as [_ H10]. inversion H10. auto.
      + assert (SZ: k * 2 > 0) by extlia.
        specialize (VB SZ). inv VB. auto.
    }
    eapply Mem.mixable_mix in H as [m1' Hm1'].
    instantiate (1 := offset_sarg sofs1 (k * 2)) in Hm1'.
    instantiate (1 := offset_sarg sofs1 0) in Hm1'.
    inv Hm. inv Hm'_. inv Hw. intro H.
    assert (Hm'' : Mem.inject f0 m1' m2').
    {
      eapply Mem.mix_left_inject; eauto.
      * eapply Mem.inject_extends_compose; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros _ ofs [-> Hofs] VLD. constructor.
        unfold offset_sarg in *.
        rewrite (Ptrofs.add_commut sofs1), Ptrofs.add_assoc, Ptrofs.add_commut.
        erewrite (Mem.address_inject f m1 m2); eauto. extlia.
        eapply H; eauto. extlia. extlia.
      * intros b1' delta' ofs pk p Hb' Hofs Hp.
        eapply (OOR b2 ofs); eauto.
        -- constructor. unfold offset_sarg in *.
           rewrite (Ptrofs.add_commut sofs1), Ptrofs.add_assoc, Ptrofs.add_commut.
           erewrite (Mem.address_inject f m1 m2); eauto. extlia.
           eapply H; eauto. extlia. extlia.
        -- eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
      * eapply Mem.mi_align with (chunk := Mint64); eauto using (Mem.mi_inj f m1 m2).
        instantiate (2 := offset_sarg sofs1 0). intros ofs Hofs.
        eapply Mem.perm_max, H; eauto; unfold offset_sarg in *; cbn in Hofs; extlia.
    }
    exists (injpw f0 m1' m2' Hm''), m1'. repeat apply conj.
    + destruct H10 as [S10 H10]. destruct H11 as [S11 H11].
      apply Mem.mix_updated in Hm1' as UNCm1tom1'.
      apply Mem.mix_unchanged in Hm1' as UNCm1'_tom1'.
      constructor; eauto.
      * cbn in *. apply Mem.ro_unchanged_memval_bytes.
        apply Mem.ro_unchanged_memval_bytes in H6. red. intros.
        destruct (loc_init_args_dec (k*2) (Vptr sb1 sofs1) b ofs).
        -- inversion UNCm1tom1'. eapply unchanged_on_perm in H2; eauto.
           split. eauto. symmetry. eapply unchanged_on_contents; eauto.
           inv l. split; auto.
           inv l. split. auto. lia.
        -- inversion UNCm1'_tom1'.
           eapply unchanged_on_perm in H2; eauto.
           exploit H6; eauto. intros [A B].
           rewrite unchanged_on_contents; eauto.
           intro. apply n. destruct H4. subst b. constructor; eauto.
           intro. apply n. destruct H5. subst b. constructor; eauto.
           inversion H10. unfold Mem.valid_block in *. eauto.
      * cbn in *. apply Mem.ro_unchanged_memval_bytes.
        apply Mem.ro_unchanged_memval_bytes in H7. red. intros.
        destruct (loc_init_args_dec (k*2) (Vptr b2 (Ptrofs.add sofs1 (Ptrofs.repr delta))) b ofs).
        -- inversion UPD. eapply unchanged_on_perm in H2; eauto.
           split. eauto. symmetry. eapply unchanged_on_contents; eauto.
        -- inversion UNCH.
           eapply unchanged_on_perm in H2; eauto.
           exploit H7; eauto. intros [A B].
           rewrite unchanged_on_contents; eauto.
           inversion H11. unfold Mem.valid_block in *. eauto.
      * red. intros.
        destruct (loc_init_args_dec (k*2) (Vptr sb1 sofs1) b ofs).
        -- inversion UNCm1tom1'. eapply unchanged_on_perm; eauto.
           inv l. split. auto. lia.
        -- red in H8. eapply H8; eauto.
           inversion UNCm1'_tom1'. eapply unchanged_on_perm; eauto.
           intro. apply n. destruct H3. subst b. constructor; eauto.
           inversion H10. unfold Mem.valid_block in *. eauto.
      * red. intros.
        destruct (loc_init_args_dec (k*2) (Vptr b2 (Ptrofs.add sofs1 (Ptrofs.repr delta))) b ofs).
        -- inversion UPD. eapply unchanged_on_perm; eauto.
        -- eapply H9; eauto.
           inversion UNCH. eapply unchanged_on_perm; eauto.
           inversion H11. unfold Mem.valid_block in *. eauto.
      * split. erewrite (Mem.support_mix _ _ _ _ _ _ Hm1'). eauto.
        eapply Mem.unchanged_on_trans; eauto.
        eapply Mem.unchanged_on_implies; eauto.
        intros _ ofs NIA _ [<- Hofs]. red in NIA. cbn in H1. congruence.
      * split. inv EXT. rewrite <- mext_sup. eauto. constructor.
        -- inversion UPD. eauto.
        -- intros.
           destruct (loc_init_args_dec (k*2) (Vptr b2 (Ptrofs.add sofs1 (Ptrofs.repr delta))) b ofs).
           ++ inversion UPD. eauto.
           ++ etransitivity. inversion H11. eauto.
              inversion UNCH. eapply unchanged_on_perm; eauto.
              inversion H11. unfold Mem.valid_block in *. eauto with mem.
        -- intros.
           destruct (loc_init_args_dec (k*2) (Vptr b2 (Ptrofs.add sofs1 (Ptrofs.repr delta))) b ofs).
           ++ inversion UPD. eauto.
           ++ etransitivity. inversion UNCH. eapply unchanged_on_contents; eauto.
              inversion H11. eapply unchanged_on_perm0; eauto.
              eapply Mem.perm_valid_block; eauto.
              inversion H11. eapply unchanged_on_contents; eauto.
    + apply inject_incr_refl.
    +  cbn -[Z.add Z.mul] in *. constructor.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_updated.
      inversion 1; auto.
    + eapply Mem.unchanged_on_implies; eauto using Mem.mix_unchanged.
      intros _ ofs NIA _ [<- Hofs]. apply NIA. constructor; auto.
    + eapply Mem.support_mix; eauto.
  - inv Hm. inv Hm'_. inv Hw. cbn in *.
    assert (Hm'' : Mem.inject f0 m1'_ m2'). eapply Mem.inject_extends_compose; eauto.
    destruct H10 as [S10 H10]. destruct H11 as [S11 H11].
    eexists (injpw f0 m1'_ m2' Hm''), m1'_. repeat apply conj.
    + 
      constructor; eauto.
      * apply Mem.ro_unchanged_memval_bytes. apply Mem.ro_unchanged_memval_bytes in H7.
        red. intros. destruct (loc_init_args_dec (k*2) sp2 b ofs).
        -- inversion UPD.
           eapply unchanged_on_perm in H2; eauto. split.
           eauto. symmetry. eapply unchanged_on_contents; eauto.
        -- inversion UNCH. eapply unchanged_on_perm in H2; eauto.
           exploit H7; eauto. intros [A B].
           rewrite unchanged_on_contents; eauto.
           inversion H11. unfold Mem.valid_block in *. eauto.
      * red. intros.
         destruct (loc_init_args_dec (k*2) sp2 b ofs).
         -- inversion UPD. eapply unchanged_on_perm; eauto.
         -- eapply H9; eauto. inversion UNCH. eapply unchanged_on_perm; eauto.
            eapply Mem.valid_block_extends; eauto. eapply Mem.perm_valid_block; eauto.
      * split. eauto. eauto.
      * split. inv EXT. rewrite <- mext_sup. eauto. constructor. inversion UPD. eauto.
         -- intros.
            destruct (loc_init_args_dec (k*2) sp2 b ofs).
            ++ inversion UPD. eauto.
            ++ etransitivity. inversion H11. eapply unchanged_on_perm; eauto.
               inversion UNCH. eapply unchanged_on_perm; eauto.
               inversion H11. unfold Mem.valid_block in *. eauto.
         -- intros.
            destruct (loc_init_args_dec (k*2) sp2 b ofs).
            ++ inversion UPD. eauto.
            ++ etransitivity.
               inversion UNCH. eapply unchanged_on_contents; eauto.
               inversion H11. eapply unchanged_on_perm0; eauto.
               eapply Mem.perm_valid_block; eauto.
               inversion H11. eapply unchanged_on_contents; eauto.
    + apply inject_incr_refl.
    + constructor.
    + split.
      * inversion H10. eauto.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in H1. extlia.
      * destruct 1; eelim H; eauto. split; eauto.
        unfold offset_sarg in H1. extlia.
    + apply Mem.unchanged_on_refl.
    + reflexivity.
Qed.      
(*
Axiom size_arguments_always_64: forall sg,
  (2 | size_arguments sg).
*)
(*
Proof.
  unfold size_arguments.
  replace Archi.ptr64 with true by reflexivity.
  cut (forall l i j k, (2 | k) -> (2 | size_arguments_64 l i j k));
    eauto using Z.divide_0_r.
  induction l; cbn; auto. intros i j k Hk.
  destruct a; repeat destruct zeq; eauto using Z.divide_add_r, Z.divide_refl.
Qed.
*)

Instance make_locset_cklr R:
  Monotonic make_locset
    (|= (- ==> Val.inject @@ [mi R]) ++> match_mem R ++> Val.inject @@ [mi R] ++>
        (- ==> Val.inject @@ [mi R])).
Proof.
  intros w rs1 rs2 Hrs m1 m2 Hm sp1 sp2 Hsp l.
  unfold make_locset, load_stack. rauto.
Qed.

Lemma unchanged_on_extends P m m':
  Mem.unchanged_on P m m' ->
  Mem.support m = Mem.support m' ->
  (forall b ofs k p, Mem.perm m b ofs k p -> P b ofs) ->
  Mem.extends m m'.
Proof.
  intros UNCH NB PERM. split; auto.
  - split; unfold inject_id.
    + inversion 1; subst. replace (ofs + 0) with ofs by extlia.
      intros Hp. erewrite <- Mem.unchanged_on_perm; eauto.
      eapply Mem.perm_valid_block; eauto.
    + inversion 1; subst. auto using Z.divide_0_r.
    + inversion 1; subst. replace (ofs + 0) with ofs by extlia.
      intros Hp. erewrite <- Mem.unchanged_on_contents; eauto.
      destruct ZMap.get; constructor.
      apply val_inject_id. apply Val.lessdef_refl.
  - intros. destruct (classic (Mem.perm m b ofs Max Nonempty)); auto. left.
    erewrite Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
Qed.

(** With this, we can state and prove the commutation property. *)
(*
Instance commut_locset_mach R `{HR: Mixable R}:
  Commutes cc_locset_mach (cc_locset R) (cc_mach R).
Proof.
  intros [[_ w] wR] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2).
  destruct Hqi2. inv Hq1i. set (ls2 := make_locset rs2 m2 sp2).
  generalize H12. transport H12. intros ARGSm1.
  eexists (se2, (sg, wR'), lmw sg rs2 m2 _). cbn. repeat apply conj; auto.
  - eapply match_stbls_acc; eauto.
  - exists (lq vf2 sg ls2 x). split.
    + constructor; auto; try rauto.
      * intros l Hl. unfold ls2. rewrite <- HwR'. repeat rstep; auto.
    + constructor; auto.
      * destruct H2; congruence.
      * destruct H4; congruence.
  - intros r1 r2 (ri & (wR'' & HwR'' & Hr1i) & Hri2).
    destruct Hr1i. inv Hri2. rename rs' into rs2'.
    set (rs1' r := result_regs sg (make_locset rs1 m1 sp1) ls1' (Locations.R r)).
    edestruct (result_mem (R:=R) (size_arguments sg) sp1 sp2 wR m1 m2 wR'' m1' m2')
      as (wR''' & m1'' & HwR''' & INCR & Hm'' & ? & ? & NB); eauto.
    { etransitivity; eauto. }
    { eapply unchanged_on_extends; eauto.
      intros b ofs k p ? ?. eapply H25; eauto. }
    { destruct 1. intros b1 delta Hb Hp.
      eapply (cklr_perm R wR'' m1' m2' H10 (b1, ofs - delta) (sb, ofs)) in Hp.
      + cbn in Hp. eapply H25; eauto. constructor; eauto.
      + replace (sb, ofs) with (sb, ofs - delta + delta) by (f_equal; extlia).
        constructor; auto. }
    { apply size_arguments_always_64. }
    { destruct H7.
      - apply zero_size_arguments_tailcall_possible in H7. extlia.
      - intro. inv H2; try congruence.
        constructor. eapply cklr_valid_block; eauto. red. red. eauto.
        eapply Mem.perm_valid_block. eapply Mem.free_range_perm; eauto.
        split; [reflexivity |]. unfold offset_sarg. extlia. }
    { destruct ARGSm1.
      - apply zero_size_arguments_tailcall_possible in H11. intros. extlia.
      - intros. subst. inv H18. eapply Mem.free_range_perm; eauto. }
    exists (mr rs1' m1''). split.
    + constructor; auto.
      * intros r Hr. unfold rs1'. cbn. destruct in_dec; tauto.
      * intros r Hr. unfold rs1'. rewrite <- result_regs_agree_callee_save; auto.
      * destruct 1. inv H2. intro.
        eapply (H25 b2 (ofs + delta)).
        -- constructor. unfold offset_sarg in *.
           rewrite (Ptrofs.add_commut sofs), Ptrofs.add_assoc, Ptrofs.add_commut.
           assert (mi R wR''' sb = Some (b2, delta)). { eapply mi_acc; eauto. }
           erewrite cklr_address_inject; eauto.
           ++ extlia.
           ++ erewrite <- (Mem.unchanged_on_perm _ m1 m1''); eauto.
              ** inv ARGSm1.
                 apply zero_size_arguments_tailcall_possible in H17.
                 rewrite H17 in H13. extlia.
                 apply Mem.free_range_perm in H26.
                 eapply H26. unfold offset_sarg. extlia.
              ** constructor. unfold offset_sarg. extlia.
              ** inv ARGSm1.
                 apply zero_size_arguments_tailcall_possible in H17. extlia.
                 eapply Mem.perm_valid_block.
                 eapply Mem.free_range_perm; eauto.
        -- eapply (cklr_perm R _ _ _ H10 (sb, ofs) (b2, ofs + delta)); eauto.
           constructor. eapply mi_acc; eauto. eapply mi_acc; eauto.
    + exists wR'''. split; [rauto | ]. constructor; auto.
      intro r. unfold rs1', result_regs.
      destruct in_dec. { rewrite H19; auto. eapply val_inject_incr; eauto. }
      destruct is_callee_save eqn:Hr; auto.
      rewrite H20 by auto. cbn. generalize (H5 r). rauto.
Qed.
*)

(** ** Matching [cc_stacking] *)

(** Next, we show that [cc_stacking] can be reduced to simulation
  conventions involving [cc_locset_mach]. *)

(** *** Incoming calls *)
(*
Lemma cc_lm_stacking:
  ccref (cc_locset_mach @ cc_mach inj) (cc_stacking inj).
Proof.
  intros [[_ wlm] w] se1 se2 q1 q2 [[ ] Hse] (qi & Hq1i & Hqi2). cbn in *.
  destruct Hqi2. inv Hq1i.
  exists (stkw inj w sg (make_locset rs1 m1 sp1) sp2 m2).
  split; [ | split].
  - cbn. auto.
  - constructor; auto.
    + cbn -[Z.add Z.mul]. repeat apply conj.
      * apply Mem.unchanged_on_refl.
      * intro Hsz.
        destruct H12. { apply zero_size_arguments_tailcall_possible in H7. extlia. }
        inv H2. eexists _, _. split; eauto. split.
        -- eapply transport in H7 as (m2_ & Hm2_ & Hm_).
           2: {
             change ?x with (id x) in H7. repeat rstep.
             eapply offset_sarg_ptrrange_inject; eauto.
             eapply Mem.free_range_perm; eauto.
             rewrite (offset_sarg_expand (size_arguments sg)).
             extlia.
           }
           eapply Mem.free_range_perm; eauto.
        -- intros ofs Hofs.
           eapply offset_fits_inject; eauto.
           eapply Mem.free_range_perm; eauto.
      * intros ofs ty REG. destruct H12.
        -- apply tailcall_possible_reg in REG; auto. contradiction.
        -- edestruct H10 as [v Hv]; eauto. rewrite Hv.
           transport Hv. rewrite H11. eauto.
    + destruct H12 as [ | sb1 sofs1 m1 m1_ ]; auto.
      assert (Mem.extends m1_ m1) by eauto using Mem.free_left_extends, Mem.extends_refl.
      destruct H6; cbn in *. erewrite <- Mem.mext_sup by eauto. constructor.
      eapply Mem.extends_inject_compose; eauto.
    + destruct 1 as [sb2 sofs2 ofs].
      inversion H2 as [ | | | | sb1 sofs1 | ]; clear H2; try congruence. subst b2 ofs2 sp1.
      inversion H12; clear H12.
      { apply zero_size_arguments_tailcall_possible in H2.
        unfold offset_sarg in *. extlia. }
      subst sb sofs m m_0.
      assert (offset_sarg sofs1 0 <= ofs - delta < offset_sarg sofs1 (size_arguments sg)).
      {
        rewrite (offset_sarg_expand (size_arguments sg)) in *.
        exploit (offset_sarg_inject inj w m1 m2 sb1 sofs1 sb2 sofs2 0); eauto.
        * eapply Mem.free_range_perm; eauto. extlia.
        * subst. eauto.
        * inversion 1. assert (delta0 = delta) by congruence. extlia.
      }
      intros sb1' delta' Hsb1' Hp.
      destruct (eq_block sb1 sb1').
      { subst sb1'. assert (delta' = delta) by congruence; subst.
        eapply Mem.perm_free_2; eauto. }
      apply cklr_no_overlap in H6. red in H6.
      edestruct (H6 sb1 sb2 delta sb1' sb2 delta'); eauto.
      * eapply Mem.perm_max, Mem.perm_implies.
        eapply Mem.free_range_perm; eauto.
        constructor.
      * eapply Mem.perm_free_3; eauto.
      * extlia.
    + destruct H2; congruence.
    + destruct H4; congruence.
  - intros r1 r2 Hr. inv Hr.
    edestruct (result_mem (R:=inj) (size_arguments sg) sp1 sp2 w m1 m2 w' m1' m2' m2')
      as (w'' & m1'' & Hw'' & INCR & ? & ? & ? & NB); eauto using Mem.unchanged_on_refl.
    { apply Mem.extends_refl. }
    { apply size_arguments_always_64. }
    { destruct H12. apply zero_size_arguments_tailcall_possible in H7. extlia.
      intro. constructor. eapply Mem.perm_valid_block.
      eapply Mem.free_range_perm; eauto. split. reflexivity.
      unfold offset_sarg. extlia. }
    { destruct H12.
      + intros. apply zero_size_arguments_tailcall_possible in H7. extlia.
      + intros. inv H12. eapply Mem.free_range_perm; eauto. }
    set (rs1' r := if is_callee_save r then rs1 r else
                   if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls1' (R r) else
                   Vundef).
    exists (mr rs1' m1''). split.
    + constructor; auto.
      * subst rs1'. intros r REG. cbn.
        destruct in_dec; try contradiction.
        replace (is_callee_save r) with false; auto.
        pose proof (loc_result_caller_save sg) as Hr.
        destruct loc_result; cbn in *; intuition congruence.
      * subst rs1'. intros r REG. cbn.
        rewrite REG. congruence.
      * destruct 1. inv H2. intro.
        eapply H22; eauto.
        2: eapply mi_acc; eauto.
        instantiate (1 := ofs + delta).
        2: replace (ofs + delta - delta) with ofs by extlia.
        2: eapply Mem.perm_max, Mem.perm_implies; eauto; constructor.
        constructor. unfold offset_sarg in *.
        rewrite (Ptrofs.add_commut sofs), Ptrofs.add_assoc, Ptrofs.add_commut.
        erewrite cklr_address_inject; eauto. extlia.
        2: eapply mi_acc; eauto.
        erewrite <- (Mem.unchanged_on_perm _ m1 m1''); eauto.
        -- inv H12.
           ++ apply zero_size_arguments_tailcall_possible in H11.
              rewrite H11 in H10. extlia.
           ++ eapply Mem.free_range_perm; eauto. unfold offset_sarg. extlia.
        -- constructor. unfold offset_sarg. extlia.
        -- inv H12.
           ++ apply zero_size_arguments_tailcall_possible in H11. extlia.
           ++ eapply Mem.perm_valid_block, Mem.free_range_perm; eauto.
    + exists w''; split; auto.
      constructor; auto.
      * intros r. subst rs1'. cbn.
        destruct is_callee_save eqn:CSR; eauto.
        destruct in_dec; eauto.
Qed.
*)
(** *** Outgoing calls *)

Import Separation.

Lemma inject_incr_separated_inv f f' m1 m2 b1 b2 delta:
  inject_incr f f' ->
  inject_separated f f' m1 m2 ->
  f' b1 = Some (b2, delta) ->
  (Mem.valid_block m1 b1 \/ Mem.valid_block m2 b2) ->
  f b1 = Some (b2, delta).
Proof.
  intros INCR ISEP Hb VALID.
  destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb1.
  - apply INCR in Hb1. congruence.
  - eelim ISEP; eauto. tauto.
Qed.

Lemma unchanged_on_combine P Q m m' :
  Mem.unchanged_on P m m' ->
  Mem.unchanged_on (fun b ofs => Q b ofs /\ ~ P b ofs) m m' ->
  Mem.unchanged_on Q m m'.
Proof.
  clear. intros [ ] [ ].
  split; intros; eauto; destruct (classic (P b ofs)); eauto.
Qed.

Lemma cc_stacking_lm:
  ccref (cc_stacking injp) (cc_locset injp @ cc_locset_mach).
Proof.
  intros w se1 se2 q1 q2 Hse Hq. destruct Hq. cbn -[Z.add Z.mul] in * |- .
  destruct H2 as (UNCH & PERM & ARGS).
  set (ls2 := make_locset rs2 m2 sp2).
  destruct H3; inv Hse; cbn -[Z.add Z.mul] in * |- .
  assert (exists m2_, args_removed sg sp2 m2 m2_ /\ Mem.inject f m1 m2_) as (m2_ & Hm2_ & Hm_).
  {
    destruct (zlt 0 (size_arguments sg)).
    - edestruct PERM as (sb2 & sofs2 & Hsp2 & PERM' & FITS). extlia.
      edestruct (Mem.range_perm_free m2) as (m2_ & Hm2_); eauto.
      exists m2_. subst. split.
      + constructor; eauto.
        * extlia.
        * intros. edestruct ARGS as (? & ? & ?); eauto.
      + eapply Mem.free_right_inject; eauto.
        intros. eapply H4; eauto.
        * constructor; eauto.
        * replace (ofs + delta - delta) with ofs by extlia.
          eapply Mem.perm_max, Mem.perm_implies; eauto. constructor.
    - exists m2. split; auto. constructor.
      rewrite <- zero_size_arguments_tailcall_possible.
      pose proof (size_arguments_above sg). extlia.
  }
  exists (se2, (sg, injpw _ _ _ Hm_), lmw sg rs2 m2 sp2). repeat apply conj.
  - constructor; cbn; auto. constructor; auto.
    destruct Hm2_; eauto. erewrite Mem.support_free; eauto.
  - exists (lq vf2 sg ls2 m2_). split.
    + constructor; eauto.
      * intros r Hr. destruct Hr; cbn -[Z.add Z.mul]; eauto.
        edestruct ARGS as (v2 & Hv2 & Hv); eauto.
        rewrite Hv2. cbn. auto.
      * constructor.
    + econstructor; eauto.
  - intros r1 r2 (ri & (w' & Hw' & Hr1i) & Hri2). cbn -[Z.add Z.mul] in *.
    inv Hw'. inv Hr1i. inv H3. inv Hri2. cbn -[Z.add Z.mul] in *.
    rename m1'0 into m1'. rename m2'0 into m2'_. rename m' into m2'.
    assert (Hm'' : Mem.inject f' m1' m2'). {
      tinv. split.
      change (m_pred (minjection f' m1') m2').
      eapply m_invar; cbn; eauto. tinv. split. rewrite H28. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros b2 ofs2 (b1 & delta & Hb & Hp) Hb2 Harg. inv Harg.
      eapply inject_incr_separated_inv in Hb; [eapply H4 | .. ]; eauto.
      * constructor; eauto.
      * eauto using Mem.valid_block_inject_1.
      * inv Hm2_.
        -- apply zero_size_arguments_tailcall_possible in H7.
           unfold offset_sarg in H3. extlia.
        -- right. eapply Mem.valid_block_free_1; eauto.
           edestruct PERM as (sb2' & sofs2' & Hsp2 & ? & ?); eauto. inv Hsp2.
           eapply Mem.perm_valid_block; eauto.
      * inv Hm'. inv mi_thread. constructor; auto. congruence.
    }
    exists (injpw f' m1' m2' Hm''); cbn.
    destruct H15 as [S15 H15]. destruct H16 as [S16 H16].
    + constructor; eauto.
      * apply Mem.ro_unchanged_memval_bytes. apply Mem.ro_unchanged_memval_bytes in H10.
        red. intros. destruct (loc_init_args_dec (size_arguments sg) sp2 b ofs).
        -- inv H27. eapply unchanged_on_perm in H7; eauto.
           split; eauto. symmetry. eapply unchanged_on_contents; eauto.
        -- inv H26.
           destruct Hm2_.
           ++ eapply unchanged_on_perm in H7; eauto.
              exploit H10; eauto. intros [A B].
              rewrite unchanged_on_contents; eauto.
              inversion H16. eapply unchanged_on_support0; eauto.
           ++
             eapply unchanged_on_perm in H7; eauto.
             eapply Mem.free_unchanged_on with (P:= not_init_args  (size_arguments sg) (Vptr sb sofs)) in H20.
             2: { intros. intro. apply H30. constructor; eauto. }
             inv H20.
             rewrite unchanged_on_contents; eauto.
             rewrite unchanged_on_perm0 in H17; eauto.
             exploit H10; eauto. apply unchanged_on_support0; eauto.
             intros [A B]. apply unchanged_on_perm0 in A; eauto.
             rewrite <- unchanged_on_contents0; eauto.
             inversion H16.
             eapply unchanged_on_support0.
             erewrite Mem.support_free; eauto.
      * intros b ofs p Hb Hp.
        destruct (loc_init_args_dec (size_arguments sg) sp2 b ofs).
        -- eapply Mem.perm_unchanged_on_2; eauto.
        -- cut (Mem.valid_block m2_ b -> Mem.perm m2_ b ofs Max p); intros.
           ++ destruct Hm2_; eauto using Mem.perm_free_3, Mem.valid_block_free_1.
           ++ eapply H14; eauto.
              eapply Mem.valid_block_unchanged_on in H16; eauto.
              eapply Mem.perm_unchanged_on_2; eauto.
      * split. eauto. eauto.
      * split. rewrite <- H28. inv Hm2_. eauto.
        erewrite <- Mem.support_free; eauto.
        eapply unchanged_on_combine; eauto.
        apply Mem.unchanged_on_trans with m2_.
        { destruct Hm2_; eauto using Mem.unchanged_on_refl.
          eapply Mem.free_unchanged_on; eauto.
          intros i Hi [Hoor Hlia]. apply Hlia. constructor. eauto. }
        apply Mem.unchanged_on_trans with m2'_.
        { eapply Mem.unchanged_on_implies; eauto.
          tauto. }
        { eapply Mem.unchanged_on_implies; eauto.
          intros b ofs [_ ?] _. red. auto. }
      * red. inv Hm2_; eauto.
        unfold Mem.valid_block. erewrite <- (Mem.support_free m2); eauto.
    + intros r REG. rewrite H23; eauto.
    + intros r REG. rewrite H24; eauto.
    + constructor.
    + auto.
    + intros b2 ofs2 Hofs2 b1 delta Hb Hp.
      inv Hm2_.
      * apply zero_size_arguments_tailcall_possible in H3.
        destruct Hofs2. unfold offset_sarg in *. extlia.
      * inv Hofs2.
        eapply inject_incr_separated_inv in Hb; eauto.
        -- eapply H13 in Hp; eauto using Mem.valid_block_inject_1.
           eapply Mem.perm_inject in Hp; eauto.
           replace (ofs2 - delta + delta) with ofs2 in Hp by extlia.
           eapply Mem.perm_free_2; eauto.
        -- right.
           eapply Mem.valid_block_free_1; eauto.
           eapply Mem.perm_valid_block.
           eapply Mem.free_range_perm; eauto.
Qed.

(** *** Typing of [cc_locset_mach] source state *)

(** This only works for [Archi.ptr64 = true], in which case there are
  no actual constraints on register typing. But we need to rely on
  this for now because of the way callee-save register preservation is
  formulated in the stacking proof: there is only a guarantee that the
  original query's source-level register still inject into the reply's
  target-level registers, but there is no guarantee that the
  target-level registers are actually unchanged. This means that on
  incoming calls, [cc_locset_mach] must occur first, before the [inj]
  component, if we are to satisfy the associated preservation property.
  But this means that the [lessdef_loc] component which we must insert
  after [wt_loc] for commutation purposes cannot be absorbed into
  [inj], and for similar reasons it cannot be folded into
  [cc_stacking] either.

  So we work around it using the following properties. *)

Lemma type_of_chunk_of_type ty:
  type_of_chunk (chunk_of_type ty) = ty.
Proof.
  destruct ty; cbn; auto.
Qed.

Lemma always_has_mreg_type v r:
  Val.has_type v (mreg_type r).
Proof.
  unfold mreg_type. change Archi.ptr64 with true.
  destruct v, r; cbn; auto.
Qed.

Lemma wt_loc_out_of_thin_air:
  cceqv (wt_loc @ cc_locset_mach) cc_locset_mach.
Proof.
  split.
  - intros [[xse [xxse sg]] w] se1 se2 q1 q2 [[Hsei] Hse] (_ & [Hq1] & Hq).
    inv Hsei. inv Hq1. exists w; repeat apply conj; auto.
    intros r1 r2 Hr. destruct Hr; cbn in *.
    eexists. split; constructor; auto. constructor.
    intros r Hr. apply always_has_mreg_type.
  - intros w se _ q1 q2 [ ] Hq. destruct Hq.
    exists (se, (se, sg), lmw sg rs m sp). cbn. repeat apply conj; auto.
    + constructor. auto.
    + eexists. split; constructor; auto. constructor.
      intros l Hl. destruct Hl.
      * apply always_has_mreg_type.
      * cbn -[Z.add Z.mul]. rewrite <- (type_of_chunk_of_type ty) at 2.
        destruct sp; cbn -[Z.add Z.mul]; auto.
        destruct Mem.load eqn:Hl; cbn; auto.
        eapply Mem.load_type. eauto.
    + intros r1 r2 (_ & [Hr1] & Hr). auto.
Qed.

Instance wt_loc_qprop R:
  PropagatesQueryInvariant (cc_locset R) wt_loc.
Proof.
  constructor. cbn.
  intros [sg wR] [? xsg] se1 se2 q1 q2 Hse Hxse Hq Hq2. subst. inv Hq. inv Hq2.
  exists (se1, sg). split; auto. constructor.
  intros. eapply val_has_type_inject; eauto. red. eauto.
Qed.

Instance wt_loc_rprop R:
  PropagatesReplyInvariant (cc_locset R) wt_loc.
Proof.
  constructor. cbn.
  intros [se ?] [sg wR] [? ?] se1 se2 q1 q2 r1 r2 Hse ? ? Hq Hq1 Hq2 (wR' & HwR' & Hr) Hr2.
  subst. inv Hq. inv Hq1. inv Hq2. inv Hr. inv Hr2. constructor.
  intros. eapply val_has_type_inject; eauto. red. eauto.
Qed.



(** * Refinement Properties for Direct Refinement *)

(** ** Properties about ro *)
Require Import ValueDomain ValueAnalysis.
Require Import Clight.

Inductive sound_state se0 m0 : state -> Prop :=
|ro_inv_state f s c e te m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (State f s c e te m)
|ro_inv_callstate v args c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Callstate v args c m)
|ro_inv_returnstate v c m:
  sound_memory_ro se0 m -> ro_acc m0 m ->
  sound_state se0 m0 (Returnstate v c m).

Definition ro_inv '(row se m) := sound_state se m.

Lemma ro_acc_storebytes : forall m m' b ofs bytes,
    Mem.storebytes m b ofs bytes = Some m' ->
    ro_acc m m'.
Proof.
  intros. constructor.
  - red. intros.
    destruct (Z_le_gt_dec n 0).
    rewrite Mem.loadbytes_empty in H1; eauto. inv H1.
    rewrite Mem.loadbytes_empty. eauto. auto.
    destruct (Z_le_gt_dec (Z.of_nat (Datatypes.length bytes)) 0).
    destruct bytes. simpl in l. inv H.
    assert (m = m'). {
      eapply Mem.storebytes_empty; eauto.
    }
    subst. eauto. cbn in l. extlia.
    erewrite <- Mem.loadbytes_storebytes_other; eauto. lia.
    apply Mem.storebytes_range_perm in H. red in H.
    destruct (eq_block b0 b). subst. right.
    destruct (Z_le_gt_dec (ofs0+n) ofs).
    left. auto.
    destruct (Z_le_gt_dec (ofs + Z.of_nat (Datatypes.length bytes)) ofs0).
    right. auto.
    exfalso.
    destruct (Z_le_gt_dec ofs ofs0).
    exploit H. instantiate (1:= ofs0). lia. intro PERM.
    exploit H2. instantiate (1:= ofs0). lia.  eauto with mem. auto.
    exploit H. instantiate (1:= ofs). lia. intro PERM.
    exploit H2. instantiate (1:= ofs). lia. eauto with mem. auto.
    left. auto.
  - erewrite <- Mem.support_storebytes; eauto.
  - red. eauto using Mem.perm_storebytes_2.
Qed.

                            
Lemma ro_acc_assign_loc : forall m m' ce t b ofs bt v,
    assign_loc ce t m b ofs bt v m' ->
    ro_acc m m'.
Proof.
  intros. inv H.
  - unfold Mem.storev in H1. eapply ro_acc_store; eauto.
  - eapply ro_acc_storebytes; eauto.
  - inv H0. cbn in H5. eapply ro_acc_store; eauto.
Qed.

Lemma ro_acc_free_list : forall l m m',
    Mem.free_list m l = Some m' ->
    ro_acc m m'.
Proof.
  induction l; intros.
  inv H. eapply ro_acc_refl.
  simpl in H. destruct a. destruct p.
  destruct (Mem.free) eqn:F; try congruence.
  eapply ro_acc_trans. eapply ro_acc_free; eauto.
  eapply IHl. eauto.
Qed.

Lemma ro_acc_bind : forall m m' ge e params args,
    bind_parameters ge e m params args m' -> ro_acc m m'.
Proof.
  intros. induction H. eapply ro_acc_refl.
  eapply ro_acc_trans. eapply ro_acc_assign_loc; eauto.
  eauto.
Qed.

Lemma ro_acc_allocs : forall m m' ge pa e1 e2,
    alloc_variables ge e1 m pa e2 m' -> ro_acc m m'.
Proof.
  intros. induction H. eapply ro_acc_refl.
  eapply ro_acc_trans. eapply ro_acc_alloc; eauto. auto.
Qed.

Lemma ro_acc_fe : forall m m' ge f args e te,
    function_entry1 ge f args m e te m' ->
    ro_acc m m'.
Proof.
  intros. inv H.
  eapply ro_acc_trans.
  eapply ro_acc_allocs; eauto.
  eapply ro_acc_bind; eauto.
Qed.

(** Any Clight program can preserve the invariant ro *)
Lemma top_ro_preserves prog:
  preserves (semantics1 prog) ro ro ro_inv.
Proof.
  intros [se0 m0] se1 Hse Hw. cbn in Hw. subst.
  split; cbn in *.
  - intros.
    Ltac Solve :=
      match goal with
      | [H: assign_loc _ _ _ _ _ _ _ _  |- _] => apply ro_acc_assign_loc in H
      | [H: external_call _ _ _ _ _ _ _ |- _] => apply ro_acc_external in H
      | [H: Mem.free_list _ _ = Some _ |- _] => apply ro_acc_free_list in H
      | [H: function_entry1 _ _ _ _ _ _ _ |- _ ] => apply ro_acc_fe in H
      | _ => idtac
      end.  
    inv H0; inv H; Solve; constructor; eauto using ro_acc_sound, ro_acc_trans.
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

(** Any Client program can be self-simulated using ro *)
Lemma top_ro_selfsim:
  forall p: (Clight.program),
    let sem := semantics1 p in
    forward_simulation ro ro sem sem.
Proof.
  intros. eapply preserves_fsim. eapply top_ro_preserves.
Qed.

Lemma compose_meminj_midvalue: forall j1 j2 v1 v3,
    Val.inject (compose_meminj j1 j2) v1 v3 ->
    exists v2, Val.inject j1 v1 v2 /\ Val.inject j2 v2 v3.
Proof.
  intros. inv H.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  eexists. split; econstructor; eauto.
  unfold compose_meminj in H0.
  destruct (j1 b1) as [[b2' d1]|] eqn:M1; try congruence.
  destruct (j2 b2') as [[b3' d2]|] eqn:M2; inv H0.
  eexists. split. econstructor; eauto.
  econstructor; eauto. rewrite add_repr.
  rewrite Ptrofs.add_assoc. auto.
  exists Vundef. split; constructor.
Qed.
(*
(** I ⋅ injp ⋅ I ⋅ injp ⊑  I ⋅ injp for any C-level invariant I*)
Lemma trans_injp_inv_incoming (I: invariant li_c) :
  ccref (I @ injp) ((I @ injp) @ (I @ injp)).
Proof.
  red. intros [[se wi] w] se1 se2 q1' q2 [Hse1 Hse2] [q1 [Hq1 Hq2]].
  inv Hse1. inv Hq1. inv Hse2. inv Hq2. inv H6. rename m0 into m1.
  rename m3 into m2. cbn in H4, H5.
  exists (se, (se,wi, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm))),
      (se,wi, (injpw f m1 m2 Hm))). repeat apply conj.
  - constructor. constructor. red. cbn. constructor. auto.
    constructor; eauto. eapply match_stbls_dom; eauto.
    constructor. constructor. auto.
    constructor; eauto.
  - eexists (cq vf1 sg vargs1 m1). split. eexists. split. constructor. eauto.
    econstructor; cbn; eauto.
    eapply val_inject_dom; eauto.
    eapply val_inject_list_dom; eauto.
    eexists. split. constructor. eauto. constructor; eauto. constructor.
  - intros r1' r3 [r2' [[r1 [Hi1 Hr1]] [r2 [Hi2 Hr2]]]].
    inv Hi1. inv Hi2.
    exists r1. split. red. cbn. constructor. auto.
    clear H6 H8 H0 H.
    destruct Hr1 as [w12' [Hw12' Hr12']]. destruct Hr2 as [w23' [Hw23' Hr23']].
    destruct w12' as [f12' m1' m2' Hm12']. destruct w23' as [f23' m2'' m3' Hm23'].
    inv Hw12'. inv Hw23'. cbn in *.
    inv Hr12'. inv Hr23'. cbn in *. inv H0. inv H27.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'1 into m3'.
    eexists (injpw (compose_meminj f12' f23') m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * destruct H15 as [S15 H15].
        split. eauto. eapply Mem.unchanged_on_implies; eauto.
        intros. red. unfold meminj_dom. rewrite H0. reflexivity.
      * red. intros. unfold compose_meminj.
        erewrite H17. erewrite H25; eauto.
        2: unfold meminj_dom; rewrite H0; reflexivity.
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H18; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H26; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
Qed.

(** ro ⋅ injp ⊑ ro ⋅ injp ⋅ ro ⋅ injp *)
Lemma trans_injp_ro_outgoing:
  ccref ((ro @ injp) @ (ro @ injp)) (ro @ injp).
Proof.
  red.
  intros w se1' se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2' [[se1 wi1] w12]] [[se2 wi2] w23]].
  destruct MSTBL13 as [[Hsi1 MSTBL12] [Hsi2 MSTBL23]].
  destruct MMEM13 as [m2 [[q1' [Hmi1 MMEM12]] [q2' [Hmi2 MMEM23]]]].
  inv Hsi1. inv Hsi2. inv Hmi1. inv Hmi2. rename q1' into q1. rename q2' into q2.
  inv MMEM12. inv H5. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H13. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H12, MSTBL12, H10, MSTBL23,H3, H4. destruct wi1. inv H. inv H1.
  destruct wi2. inv H0. inv H2.
  exists (se1, (row se1 m1), (injpw (compose_meminj j12 j23)
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl.
  repeat apply conj.
  - constructor. eauto.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - exists (cq vf1 sg vargs1 m1). split. constructor; eauto. constructor; eauto.
    constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
    eapply CKLRAlgebra.val_inject_list_compose.
    econstructor; eauto.
  - intros r1 r3 [r2 [Hi2 [w13' [INCR13' Hr13]]]].
    inv Hr13. inv H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2' into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? RO1 RO3 MAXPERM1 MAXPERM3 [S1 UNCHANGE1] [S3 UNCHANGE3] INCR13 DISJ13]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ23).
    intros IMGIN23.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ23).
    intros DOMIN23.
    generalize (inject_implies_dom_in _ _ _ INJ13').
    intros DOMIN13'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE3).
    intros SUPINCL3.
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13).
    intros (j12' & j23' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME).
    subst. cbn in *.
    set (m2' := m2' m1 m2 m1' j12 j23 j12' m2'_sup INJ12 ).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
     (* assert (S2: Mem.match_sup (Mem.support m2) (Mem.support m2')).
    eapply Mem.match_sup_trans. eapply Mem.match_sup_symm. inversion INJ12. apply mi_thread.
    eapply Mem.match_sup_trans. eauto. inversion INJ12'. eauto. *)
    set (w1' := injpw j12' m1' m2' INJ12').
    set (w2' := injpw j23' m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2').
    eapply UNCHANGE21; eauto.
    exists (cr vres2 m2'). split.
    + 
      exists (cr vres1 m1'). split. cbn. auto.
      exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto. split. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. red. unfold compose_meminj.
      rewrite H1. reflexivity. split; eauto. eapply tid_s2; eauto.
      constructor; eauto. constructor; eauto.
    + exists (cr vres2 m2'). split. cbn. econstructor. constructor.
      constructor. eapply ROUNC2; eauto.
      inversion UNC21. eauto.
      eapply MAXPERM2; eauto.
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto. split. eapply tid_s2; eauto.
      eapply UNCHANGE22; eauto. split. eauto. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Qed.

Theorem ro_injp_trans:
  cceqv ((ro @ injp) @ (ro @ injp)) (ro @ injp).
Proof. split. eapply trans_injp_ro_outgoing. eapply trans_injp_inv_incoming. Qed.
 *)


(** ** The reversed version of [commut_wt_c] *)
Theorem wt_R_refinement R:
  ccref (cc_c R @ (wt_c @ lessdef_c)) ((wt_c @ lessdef_c) @ cc_c R).
Proof.
  rewrite cc_compose_assoc. rewrite lessdef_c_cklr.
  intros [[se wR][[se' [se'' sg]] ?]].
  intros se1 se2 q1 q2 [Hse1 [Hse2 Hse3]] [q2' [Hq1 [q2'' [Hq2 Hq3]]]].
  inv Hse2. inv Hse3. cbn in H. cbn in Hq1. subst se''.
  inv Hq1. inv Hq2. inv Hq3. cbn in H3. destruct H3 as [? TYPE]. subst.
  exists (se1,(se1,sg0),wR). repeat apply conj.
  - constructor; cbn; eauto. constructor; eauto.
  - cbn in H0. cbn in H.
    exists (cq vf1 sg0 vargs1 m1). split.
    econstructor; eauto. split.
    econstructor; eauto.
    eapply val_has_type_list_inject; eauto.
    econstructor; eauto.
    eapply val_inject_lessdef_list_compose; eauto.
  - intros r1 r2 [r1' [Hr1 Hr2]].
    inv Hr1. cbn in H3.
    destruct Hr2 as [w [Hw Hr2]].
    inv Hr2.
    set (res' := Val.ensure_type vres2 (proj_sig_res sg0) ).
    exists (cr res' m2'). split. exists w. split. eauto.
    econstructor; eauto.
    unfold res'.
    apply has_type_inject; eauto.
    exists (cr res' m2'). split.
    constructor; eauto. cbn. unfold res'. apply Val.ensure_has_type.
    constructor; eauto. unfold res'.
    destruct vres2, (proj_sig_res sg0); auto.
Qed.

(** Properties of wt_c. lessdef_c here is a helper simulation convention. 
    We have lessdef_c ⋅ R' ≡ R' ([lessdef_c_cklr]), i.e., lessdef_c 
    can be absorbed into or create from a later simulation convention R'.
    The following lemmas depend on this techinique.
*)

(** The helping lemma using lessdef_c, it claims that wt_c ⋅ lessdef_c can commute with R *)
Theorem wt_lessdef_R_equiv R:
  cceqv (cc_c R @ (wt_c @ lessdef_c)) ((wt_c @ lessdef_c) @ cc_c R).
Proof. split. apply wt_R_refinement. apply commut_wt_c. Qed.

(** R ⋅ wt ⊑ wt ⋅ R ⋅ wt, this lemma does not depend on lessdef_c  *)
Theorem R_wt__wt_R_wt R:
  ccref (wt_c @ (cc_c R) @ wt_c) ((cc_c R) @ wt_c).
Proof. apply inv_drop. apply wt_c_reply_prop. Qed.

(** wt ⋅ R ⋅ wt ⊑ R ⋅ wt, this lemma depends on a following R' *)
Theorem wt_R_wt__R_wt R R':
  ccref ((cc_c R) @ wt_c @ (cc_c R')) (wt_c @ (cc_c R) @ wt_c @ (cc_c R')).
Proof.
  etransitivity. rewrite <- (lessdef_c_cklr R').
  rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc R).
  rewrite wt_lessdef_R_equiv.
  rewrite (inv_dup wt_c). rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc wt_c lessdef_c).
  rewrite <- (cc_compose_assoc (wt_c @ lessdef_c)).
  rewrite <- wt_lessdef_R_equiv.
  rewrite !cc_compose_assoc.
  rewrite lessdef_c_cklr. reflexivity. reflexivity.
Qed.

(** R ⋅ wt ⊑ wt ⋅ R, this lemma depends on a following R' *)
Theorem R_wt__wt_R R R':
  ccref (wt_c @ (cc_c R) @ (cc_c R')) ((cc_c R) @ wt_c @ (cc_c R')).
Proof.
  etransitivity.
  rewrite <- lessdef_c_cklr. rewrite <- !cc_compose_assoc.
  rewrite <- wt_lessdef_R_equiv.
  rewrite !cc_compose_assoc. rewrite lessdef_c_cklr.
  reflexivity. reflexivity.
Qed.

(** wt ⋅ R ⊑ R ⋅ wt, this lemma depends on a following R' *)
Theorem wt_R__R_wt R R':
  ccref ((cc_c R) @ wt_c @ (cc_c R')) (wt_c @ (cc_c R) @ (cc_c R')).
Proof.
  etransitivity.
  rewrite <- (lessdef_c_cklr R'). rewrite <- (cc_compose_assoc wt_c).
  rewrite <- (cc_compose_assoc R).
  rewrite wt_lessdef_R_equiv.
  rewrite !cc_compose_assoc.
  rewrite <- (cc_compose_assoc lessdef_c).
  rewrite lessdef_c_cklr.
  reflexivity. reflexivity.
Qed.

