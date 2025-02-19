Require Import Coqlib.
Require Import Errors.
Require Import Mapsrel.
Require Import Integers.
Require Import Floats.
Require Import Valuesrel.
Require Import AST.
Require Import CKLR.
Require Import Eventsrel.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import Smallstep.
Require Import Ctypes.
Require Import Coprel.

Require Import LogicalRelations.
Require Import OptionRel.
Require Import KLR.
Require Export Clight.
Require Import SimplLocalsproof.
Require Import Linking.

Section PROG.

Context (p: program).

(** Global environments *)

Definition genv_match R w : relation genv :=
  (match_stbls R w) !! (fun se => globalenv se p).

Global Instance genv_genv_match R w: (*{C} `{LC: Linker C} (ctx: C):*)
  Monotonic
    genv_genv
    (genv_match R w ++>
     Genv.match_genvs (mi R w) (match_globdef (fun _ => eq) eq p)).
Proof.
  unfold genv_match. repeat rstep. destruct H.
  eapply Genv.globalenvs_match; eauto.
  red. intuition auto.
  induction (@AST.prog_defs fundef type (@program_of_program function p))
    as [ | [id [f|[ ]]] ? ?];
    repeat (econstructor; eauto using linkorder_refl).
  eapply match_stbls_proj; eauto.
Qed.

Global Instance genv_cenv_match R w:
  Monotonic genv_cenv (genv_match R w ++> eq).
Proof.
  unfold genv_match. repeat rstep. destruct H.
  reflexivity.
Qed.

Lemma match_prog {C} `{!Linking.Linker C} (c: C):
  Linking.match_program_gen (fun _ => eq) eq c p p.
Proof.
  repeat apply conj; auto.
  induction (AST.prog_defs p) as [ | [id [f|v]] defs IHdefs];
  repeat (econstructor; eauto).
  - apply Linking.linkorder_refl.
  - destruct v; constructor; auto.
Qed.

(** NB: we have to use [option_rel] here not [option_le], because
  otherwise it is difficult to state the monotonicity property of
  [blocks_of_env] (we would have to introduce some kind of "subset"
  list relator) *)
Definition env_match R w :=
  PTreeRel.r (option_rel (block_inject_sameofs (mi R w) * @eq type)).

Global Instance env_match_acc:
  Monotonic (@env_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  unfold env_match. rauto.
Qed.

Global Instance empty_env_match R w:
  Monotonic (@empty_env) (env_match R w).
Proof.
  unfold env_match, empty_env. rauto.
Qed.

Definition temp_env_match R w: rel temp_env temp_env :=
  PTreeRel.r (option_le (Val.inject (mi R w))).

Global Instance temp_env_match_acc:
  Monotonic (@temp_env_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  unfold temp_env_match. rauto.
Qed.

Global Instance deref_loc_match R w:
  Monotonic
    (@deref_loc)
    (- ==> match_mem R w ++> % ptrbits_inject (mi R w) ++> - ==>
     set_le (Val.inject (mi R w))).
Proof.
  repeat rstep.
  intros a H1.
  assert (Val.inject (mi R w) (Vptr (fst x1) (snd x1)) (Vptr (fst y0) (snd y0))) as VAL.
  {
    rstep.
    destruct x1; destruct y0; assumption.
  }
  inversion H0; subst.
  repeat red.
  simpl in * |- * .
  inversion H1; subst; eauto using @deref_loc_reference, @deref_loc_copy.
- generalize (cklr_loadv R w chunk _ _ H _ _ VAL).
  rewrite H4.
  inversion 1; subst.
  symmetry in H7.
  eauto using @deref_loc_value.
- transport H3.
  eexists; split; eauto.
  constructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @deref_loc : typeclass_instances.

(** [assign_loc] is somewhat involved. *)

Lemma assign_loc_match_alignof_blockcopy R w m1 m2 b1 ofs1 b2 ofs2 env ty:
  match_mem R w m1 m2 ->
  ptrbits_inject (mi R w) (b1, ofs1) (b2, ofs2) ->
  sizeof env ty > 0 ->
  Mem.range_perm m1 b1 (Ptrofs.unsigned ofs1) (Ptrofs.unsigned ofs1 + sizeof env ty) Cur Nonempty ->
  (alignof_blockcopy env ty | Ptrofs.unsigned ofs1) ->
  (alignof_blockcopy env ty | Ptrofs.unsigned ofs2).
Proof.
  intros Hm Hptr Hsz Hperm H.
  inv Hptr.
  erewrite (cklr_address_inject R w); eauto.
  eapply (cklr_aligned_area_inject R w); eauto.
  + eapply alignof_blockcopy_1248.
  + eapply sizeof_alignof_blockcopy_compat.
  + eapply Hperm.
    lia.
Qed.

Global Instance assign_loc_match R:
  Monotonic
    (@assign_loc)
    (|= - ==> - ==> match_mem R ++>
     % ptrbits_inject @@ [mi R] ++>
     - ==>
     Val.inject @@ [mi R] ++>
     k1 set_le (<> match_mem R)).
Proof.
  intros w ce ty m1 m2 Hm [b1 ofs1] [b2 ofs2] Hptr bf v1 v2 Hv m1' Hm1'.
  destruct Hm1' as [v1 chunk m1' | b1' ofs1' bytes1 m1' | sz sg pos width v m' v' Hmv].
  - transport_hyps.
    eexists; split; [ | rauto].
    eapply assign_loc_value; eauto.
  - assert
      (sizeof ce ty > 0 ->
       Mem.range_perm m1 b1
         (Ptrofs.unsigned ofs1)
         (Ptrofs.unsigned ofs1 + sizeof ce ty)
         Cur Nonempty).
    {
      intro.
      eapply Mem.range_perm_implies.
      + replace (sizeof _ _) with (Z.of_nat (length bytes1)).
        * eapply Mem.storebytes_range_perm; eauto.
        * erewrite (Mem.loadbytes_length m1) by eauto.
          apply Z2Nat.id.
          lia.
      + constructor.
    }
    assert
      (sizeof ce ty > 0 ->
       Mem.range_perm m1 b1'
         (Ptrofs.unsigned ofs1')
         (Ptrofs.unsigned ofs1' + sizeof ce ty)
         Cur Nonempty).
    {
      intro.
      eapply Mem.range_perm_implies.
      + eapply Mem.loadbytes_range_perm; eauto.
      + constructor.
    }
    simpl.
    rinversion Hv; clear Hv; inv Hvl.
    transport_hyps.
    eexists; split; [eapply assign_loc_copy | ]; simpl.
    + assumption.
    + eauto using assign_loc_match_alignof_blockcopy.
    + eauto using assign_loc_match_alignof_blockcopy.
    + assert (sizeof ce ty = 0 \/ sizeof ce ty <> 0) as [Hsz | Hsz] by extlia.
      {
        rewrite Hsz.
        right.
        lia.
      }
      assert (Hsz' : sizeof ce ty > 0).
      {
        pose proof (sizeof_pos ce ty).
        lia.
      }
      inv Hptr.
      inv H7.
      erewrite !(cklr_address_inject R w); eauto.
      eapply (cklr_disjoint_or_equal_inject R w); eauto.
      * intros ofs Hofs.
        eapply Mem.perm_cur_max.
        eapply H6; eauto.
      * intros ofs Hofs.
        eapply Mem.perm_cur_max.
        eapply H5; eauto.
      * eapply H5; eauto.
        lia.
      * eapply H6; eauto.
        lia.
    + eassumption.
    + eassumption.
    + rauto.
  - apply Vptr_inject in Hptr. cbn in *.
    eapply (store_bitfield_match R _ _ _ _ _ w _ _ Hm _ _ Hptr _ _ Hv (_,_) ) in Hmv
      as ([m'' v''] & H' & w' & Hw' & ? & ?).
    eexists. split; [ | rauto].
    econstructor; eauto.
Qed.

Hint Extern 1 (Related _ _ _) =>
  eapply assign_loc_match : typeclass_instances.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @assign_loc : typeclass_instances.

Global Instance genv_match_acc R:
  Monotonic (genv_match R) (wacc R ++> subrel).
Proof.
  intros w w' Hw' _ _ [se1 se2 Hge].
  eapply (match_stbls_acc R w w') in Hge; eauto.
  eapply (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p));
    eauto.
Qed.

Global Instance alloc_variables_match R:
  Monotonic
    (@alloc_variables)
    (|= genv_match R ++> env_match R ++> match_mem R ++> - ==>
     % k1 set_le (<> (env_match R * match_mem R))).
Proof.
  intros w ge1 ge2 Hge e1 e2 Henv m1 m2 Hm vars [e1' m1'] H.
  revert H w e2 m2 Hge Henv Hm.
  simpl.
  induction 1 as [e1 m1 | e1 m1 id ty vars m1' b1 m1'' e1'' Hm1' Hm1'' IH].
  - intros.
    exists (e2, m2).
    split.
    + constructor.
    + rauto.
  - intros.
    edestruct (cklr_alloc R w m1 m2 Hm 0 (sizeof ge1 ty)) as (p' & Hp' & Hm' & Hb); eauto.
    destruct (Mem.alloc m2 0 (sizeof ge1 ty)) as [m2' b2] eqn:Hm2'.
    rewrite Hm1' in *. cbn [fst snd] in *.
    specialize (IH p' (PTree.set id (b2, ty) e2) m2').
    edestruct IH as ((e2'' & m2'') & Hvars & p'' & He'' & Hm''); eauto.
    eapply genv_match_acc; eauto.
    {
      (** We only have [ptree_set_le], we would need support for
        multiple instances to declare [ptree_set_rel] as well. *)
      unfold env_match in *.
      intro j.
      destruct (ident_eq j id); subst.
      - rewrite !PTree.gss. rauto.
      - rewrite !PTree.gso by assumption. rauto.
    }
    eexists (e2'', m2'').
    split.
    + simpl.
      econstructor; eauto.
      destruct Hge; eauto.
    + rauto.
Qed.

Global Instance bind_parameters_match R:
  Monotonic
    (@bind_parameters)
    (|= genv_match R ==> env_match R ++> match_mem R ++> - ==>
     k1 list_rel (Val.inject @@ [mi R]) ++>
     k1 set_le (<> match_mem R)).
Proof.
  intros w ge1 ge2 Hge e1 e2 He m1 m2 Hm vars vl1 vl2 Hvl m1' H.
  revert H w Hge He vl2 m2 Hvl Hm.
  induction 1 as [m1 | m1 id ty params v1 vl1 b1 m1' m1'' Hb1 Hm1' Hm1'' IH].
  - intros.
    exists m2.
    split; try rauto.
    inversion Hvl; subst.
    constructor.
  - intros.
    generalize He. intro He_.
    specialize (He id).
    pose proof (fun m => bind_parameters_cons ge2 e2 m id) as Hbp_cons.
    destruct He as [[xb1 xty] [b2 yty] [Hb Hty] | ]; try discriminate.
    simpl in *.
    inversion Hb1; clear Hb1.
    repeat subst.
    inversion Hvl as [ | xv1 v2 Hv xvl1 vl2' Hvl']; subst.
    assert (PTR: ptrbits_inject (mi R w) (b1, Ptrofs.zero) (b2, Ptrofs.zero))
      by rauto.
    clear Hb.
    transport_hyps.
    edestruct (IH w') as (m2'' & Hm2'' & Hm''); eauto.
    + red. destruct Hge as [se1 se2 Hge]. eapply (match_stbls_acc R w w') in Hge; eauto.
      eapply
        (rel_push_rintro (fun se => globalenv se p) (fun se => globalenv se p));
        eauto.
    + rauto.
    + rauto.
    + destruct Hm'' as (w'' & Hw'' & Hm'').
      eexists.
      split; eauto.
      rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @bind_parameters : typeclass_instances.

Global Instance create_undef_temps_match R w:
  Monotonic
    (@create_undef_temps)
    (- ==> temp_env_match R w).
Proof.
  unfold temp_env_match.
  intros temps.
  induction temps as [ | [id t] temps IHtemps]; simpl; try rauto.
Qed.

Global Instance bind_parameter_temps_match R w:
  Monotonic
    (@bind_parameter_temps)
    (- ==> list_rel (Val.inject (mi R w)) ++> temp_env_match R w ++>
     option_rel (temp_env_match R w)).
Proof.
  intros formals args1 args2 Hargs.
  revert formals.
  induction Hargs as [ | v1 v2 Hv args1 args2 Hargs IH].
  - intros [|]; simpl; intros; rauto.
  - intros [| [id t] formals]; simpl; repeat rstep.
    eapply IH.
    rauto.
Qed.

Global Instance block_of_binding_match R w:
  Monotonic
    (@block_of_binding)
    (genv_match R w ++> eq * (block_inject_sameofs (mi R w) * eq) ++>
     ptrrange_inject (mi R w)).
Proof.
  intros ge1 ge2 Hge (id1 & b1 & ty1) (id2 & b2 & ty2) (Hid & Hb & Hty).
  simpl in *.
  eapply block_sameofs_ptrrange_inject; intuition auto.
  f_equal; rauto.
Qed.

Global Instance blocks_of_env_match R w:
  Monotonic
    (@blocks_of_env)
    (genv_match R w ++> env_match R w ++> list_rel (ptrrange_inject (mi R w))).
Proof.
  unfold blocks_of_env. rauto.
Qed.

Global Instance set_opttemp_match R w:
  Monotonic
    (@set_opttemp)
    (- ==> Val.inject (mi R w) ++> temp_env_match R w ++> temp_env_match R w).
Proof.
  unfold set_opttemp. rauto.
Qed.

Instance transport_find_symbol_genv R w ge1 ge2 id b1:
  Transport (genv_match R w) ge1 ge2
    (Genv.find_symbol ge1 id = Some b1)
    (exists b2,
        Genv.find_symbol ge2 id = Some b2 /\
        block_inject_sameofs (mi R w) b1 b2).
Proof.
  intros Hge Hb1. edestruct @Genv.find_symbol_match as (b2 & ? & ?); eauto.
  destruct Hge. eapply match_stbls_proj. eauto.
Qed.

Instance to_senv_match f:
  Monotonic
    (@Genv.to_senv)
    (forallr -, forallr -, rforall Rf, Genv.match_genvs f Rf ++>
     Genv.match_stbls f).
Proof.
  firstorder.
Qed.

Global Instance subrel_refl_rstep {A B} (R : rel A B) :
  RStep True (subrel R R) | 25.
Proof.
  firstorder.
Qed.

Instance env_match_ptree_le R w:
  Related
    (env_match R w)
    (PTreeRel.r (option_le (block_inject_sameofs (mi R w) * eq)))
    subrel.
Proof.
  unfold env_match. rauto.
Qed.

Instance env_match_ptree_ge R w:
  Related
    (env_match R w)
    (PTreeRel.r (option_ge (block_inject_sameofs (mi R w) * eq)))
    subrel.
Proof.
  unfold env_match. rauto.
Qed.

(** [select_switch_default], [select_switch_case], [select_switch]
  and [seq_of_label_statement] are entierly about syntax. *)
Lemma eval_expr_lvalue_match R w (ge1 ge2: genv):
  genv_match R w ge1 ge2 ->
  forall e1 e2, env_match R w e1 e2 ->
  forall le1 le2, temp_env_match R w le1 le2 ->
  forall m1 m2, match_mem R w m1 m2 ->
  (forall expr v1,
     eval_expr ge1 e1 le1 m1 expr v1 ->
     exists v2,
       eval_expr ge2 e2 le2 m2 expr v2 /\
       Val.inject (mi R w) v1 v2) /\
  (forall expr b1 ofs bf,
     eval_lvalue ge1 e1 le1 m1 expr b1 ofs bf ->
     exists b2 ofs2,
       eval_lvalue ge2 e2 le2 m2 expr b2 ofs2 bf /\
       ptrbits_inject (mi R w) (b1, ofs) (b2, ofs2)).
Proof.
  intros Hge e1 e2 He le1 le2 Hle m1 m2 Hm.
  apply eval_expr_lvalue_ind;
  try solve
    [ intros;
      split_hyps;
      transport_hyps;
      repeat (repeat (rstep + f_equal); econstructor) ].

  - intros id b1 ty Hb1.
    transport_hyps.
    destruct x as [b2 ty'], H0 as (Hb & Hty).
    simpl in *; subst.
    repeat (repeat rstep; econstructor).

  - intros expr ty b1 ofs H1 IH.
    destruct IH as (ptr2 & H2 & Hptr).
    inversion Hptr; clear Hptr; subst.
    eexists; eexists; split; eauto.
    constructor; eauto.

  - intros expr fid ty b1 ofs1 sid sflist satt delta bf H1 IH Hs Hf Hdelta.
    destruct IH as (ptr2 & H2 & Hptr).
    rinversion Hptr; inv Hptrl.
    eexists; eexists; split.
    + assert (Hce: genv_cenv ge1 = genv_cenv ge2) by rauto.
      eapply eval_Efield_struct; eauto; rewrite <- Hce; eauto.
    + eauto using ptrbits_inject_shift.

  - intros expr fid ty b1 ofs1 uid uflist uatt ? bf H1 IH Hu.
    assert (Hce: genv_cenv ge1 = genv_cenv ge2) by rauto. rewrite Hce.
    destruct IH as (ptr2 & H2 & Hptr).
    rinversion Hptr; inv Hptrl.
    eauto 10 using @eval_Efield_union, ptrbits_inject_shift.
Qed.

Global Instance eval_expr_match R w:
  Monotonic
    (@eval_expr)
    (genv_match R w ++>
     env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==>
     set_le (Val.inject (mi R w))).
Proof.
  intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm expr v1 Hv1.
  edestruct eval_expr_lvalue_match; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_expr : typeclass_instances.

Global Instance eval_lvalue_match R w:
  Monotonic
    (@eval_lvalue)
    (genv_match R w ++> env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==>
     %% set_le (ptrbits_inject (mi R w) * eq)).
Proof.
  intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm expr [[b1 ofs] bf] Hp1.
  simpl in *.
  edestruct eval_expr_lvalue_match as [_ H]; eauto.
  edestruct H as (b2 & ofs2 & H'); eauto.
  exists ((b2, ofs2), bf).
  split_hyps.
  split; eauto.
  split; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry2_set_le_transport @eval_lvalue : typeclass_instances.

Global Instance eval_exprlist_match R w:
  Monotonic
    (@eval_exprlist)
    (genv_match R w ++> env_match R w ++> temp_env_match R w ++>
     match_mem R w ++> - ==> - ==>
     set_le (list_rel (Val.inject (mi R w)))).
Proof.
  intros ge1 ge2 Hge e1 e2 He le1 le2 Hle m1 m2 Hm exprlist tys vs1 Hvs1.
  induction Hvs1 as [|expr exprs ty tys v1 v1' v1s Hv1 Hv1' Hv1s IHv1s]; simpl.
  - exists nil.
    split; constructor.
  - split_hyps.
    transport_hyps.
    eexists.
    split; econstructor; eauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @eval_exprlist : typeclass_instances.

Inductive cont_match R (w: world R): rel cont cont :=
  | Kstop_match:
      Monotonic (@Kstop) (cont_match R w)
  | Kseq_match:
      Monotonic (@Kseq) (- ==> cont_match R w ++> cont_match R w)
  | Kloop1_match:
      Monotonic (@Kloop1) (- ==> - ==> cont_match R w ++> cont_match R w)
  | Kloop2_match:
      Monotonic (@Kloop2) (- ==> - ==> cont_match R w ++> cont_match R w)
  | Kswitch_match:
      Monotonic (@Kswitch) (cont_match R w ++> cont_match R w)
  | Kcall_match:
      Monotonic
        (@Kcall)
        (- ==> - ==>
         env_match R w ++>
         temp_env_match R w ++>
         cont_match R w ++>
         cont_match R w).

Global Existing Instance Kstop_match.
Global Existing Instance Kseq_match.
Global Existing Instance Kloop1_match.
Global Existing Instance Kloop2_match.
Global Existing Instance Kswitch_match.
Global Existing Instance Kcall_match.

Global Instance cont_match_le:
  Monotonic (@cont_match) (forallr - @ R, acc tt ++> subrel).
Proof.
  repeat red.
  intros R x y H x0 y0 H0.
  revert y H.
  induction H0; constructor; auto; rauto.
Qed.

Global Instance call_cont_match R w:
  Monotonic
    (@call_cont)
    (cont_match R w ++> (cont_match R w /\ lsat is_call_cont)).
Proof.
  intros k1 k2 Hk.
  induction Hk; simpl; try rauto.
  (* XXX prob is now we don't just try I *)
  reexists. rstep. apply I. red. simpl.
  destruct IHHk. split. constructor; eauto. constructor.
Qed.

Global Instance is_call_cont_match_strong R w:
  Monotonic (@is_call_cont) (cont_match R w ++> iff).
Proof.
  intros k1 k2 Hk.
  destruct Hk; rauto.
Qed.

Hint Extern 10 (Transport _ _ _ (is_call_cont _) _) =>
  eapply impl_transport : typeclass_instances.

Inductive state_match R w: rel state state :=
  | State_rel:
      Monotonic
        (@State)
        (- ==> - ==>
         cont_match R w ++>
         env_match R w ++>
         temp_env_match R w ++>
         match_mem R w ++>
         state_match R w)
  | Callstate_rel:
      Monotonic
        (@Callstate)
        (Val.inject (mi R w) ==>
         list_rel (Val.inject (mi R w)) ++>
         cont_match R w ++>
         match_mem R w ++>
         state_match R w)
  | Returnstate_rel:
      Monotonic
        (@Returnstate)
        (Val.inject (mi R w) ++>
         cont_match R w ++>
         match_mem R w ++>
         state_match R w).

Global Existing Instance State_rel.
Global Existing Instance Callstate_rel.
Global Existing Instance Returnstate_rel.

Scheme statement_ind_mutual := Induction for statement Sort Prop
  with ls_ind_mutual := Induction for labeled_statements Sort Prop.

Global Instance find_label_match R w:
  Monotonic
    (@find_label)
    (- ==> - ==> cont_match R w ++> option_rel (eq * cont_match R w)).
Proof.
  intros lbl s.
  pattern s.
  pose proof Some_rel.
  eapply statement_ind_mutual with
    (P0 := fun ls =>
               (cont_match R w ++> option_rel (eq * cont_match R w))%rel
               (find_label_ls lbl ls)
               (find_label_ls lbl ls));
  simpl; intros;
  repeat rstep; try (destruct ident_eq; repeat rstep).
Qed.

Global Instance function_entry1_match R:
  Monotonic
    (@function_entry1)
    (|= genv_match R ++> - ==> k1 list_rel (Val.inject @@ [mi R]) ++> match_mem R ++>
     %% k1 set_le (<> env_match R * temp_env_match R * match_mem R)).
Proof.
  intros w ge1 ge2 Hge f vargs1 vargs2 Hvargs m1 m2 Hm [[e1 le] m1''] H.
  simpl in *.
  destruct H as [m1' Hfvnr Hm1' Hm1'' Hle].
  pose proof (empty_env_match R w) as Hee.
  destruct (alloc_variables_match R w _ _ Hge _ _ Hee _ _ Hm _ (e1, m1') Hm1')
    as ((e2 & m2') & Hm2' & w' & Hw' & He & Hm').
  eapply genv_match_acc in Hge; [ | eauto].
  transport Hm1''.
  exists (e2, le, x).
  cbn [fst snd] in *.
  split.
  - econstructor; eauto.
  - assert (temp_env_match R w'' le le).
    { subst le. generalize (fn_temps f). clear. unfold temp_env_match.
      induction l; cbn; rauto. }
    exists w''. split; rauto.
Qed.

Global Instance function_entry2_match R:
  Monotonic
    (@function_entry2)
    (|= genv_match R ++> - ==> k1 list_rel (Val.inject @@ [mi R]) ++> match_mem R ++>
     %% k1 set_le (<> env_match R * temp_env_match R * match_mem R)).
Proof.
  intros w ge1 ge2 Hge f vargs1 vargs2 Hvargs m1 m2 Hm [[e1 le1] m1'] H.
  simpl in *.
  destruct H as [Hfvnr Hfpnr Hfvpd Hm1' Hle1].
  pose proof (empty_env_match R w) as Hee.
  destruct (alloc_variables_match R w _ _ Hge _ _ Hee _ _ Hm _ (e1, m1') Hm1')
    as ((e2 & m2') & Hm2' & p' & Hp' & He & Hm').
  transport Hle1.
  exists (e2, x, m2').
  simpl in *.
  split.
  - constructor; eauto.
  - rauto.
Qed.

Hint Extern 1 (Transport _ _ _ _ _) =>
  rel_curry2_set_le_transport @function_entry2 : typeclass_instances.


Global Instance find_funct_inject R w ge1 v1 ge2 v2 f:
  Transport (genv_match R w * Val.inject (mi R w)) (ge1, v1) (ge2, v2)
    (Genv.find_funct ge1 v1 = Some f)
    (Genv.find_funct ge2 v2 = Some f).
Proof.
  intros [Hge Hv] Hf. cbn in *.
  destruct Hge. apply match_stbls_proj in H. cbn in Hf.
  edestruct @Genv.find_funct_match as (?&?&?&?&?); eauto using (match_prog tt).
  cbn in *. subst. auto.
Qed.

Global Instance step_rel R:
  Monotonic
    (@step)
    (|= genv_match R ++> 
        (- ==> k1 list_rel (Val.inject @@ [mi R]) ++> match_mem R ++>
         %% k1 set_le (<> env_match R * temp_env_match R * match_mem R)) ++>
        state_match R ++> - ==> k1 set_le (<> state_match R)).
Proof.
  intros w ge1 ge2 Hge fe1 fe2 Hfe s1 s2 Hs t s1' H1.
  deconstruct H1 ltac:(fun x => pose (c := x)); inv Hs;
  try
    (transport_hyps;
       repeat match goal with
         | H: cont_match _ _ (_ _) _ |- _ =>
           let Hl := fresh H "l" in
           let Hr := fresh H "r" in
           rinversion_tac H Hl Hr; clear H; inv Hl
         | H: (eq * cont_match _ _)%rel (_, _) _ |- _ =>
           let Hl := fresh H "l" in
           let Hr := fresh H "r" in
           rinversion_tac H Hl Hr; clear H; inv Hl
       end;
       subst;
       eexists; split;
         [ eapply c; eauto; fail
         | eexists; split; rauto ]).
  - eapply @transport in f0; [ | rel_curry2_set_le_transport fe1 | rauto].
    destruct f0 as (? & ? & ? & ? & ? & ? & ?).
    rinversion H2. inv H2l. inv H2r.
    rinversion H3. inv H3l. inv H3r.
    transport FIND.
    eexists; split.
    + eapply c; eauto.
    + eexists; split; rauto.
Qed.

Global Instance step1_rel R:
  Monotonic
    (@step1)
    (|= genv_match R ++> state_match R ++> - ==> k1 set_le (<> state_match R)).
Proof.
  unfold step1. rauto.
Qed.

Global Instance step1_rel_params:
  Params (@step1) 3 := {}.

Global Instance step2_rel R:
  Monotonic
    (@step2)
    (|= genv_match R ++> state_match R ++> - ==> k1 set_le (<> state_match R)).
Proof.
  unfold step2. rauto.
Qed.

Global Instance step2_rel_params:
  Params (@step2) 3 := {}.

End PROG.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @step1 : typeclass_instances.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @step2 : typeclass_instances.

Lemma semantics1_rel p R:
  forward_simulation (cc_c R) (cc_c R) (Clight.semantics1 p) (Clight.semantics1 p).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[semantics1] in *.
  pose (ms := fun s1 s2 =>
    klr_diam tt (genv_match p R * state_match R) w
      (globalenv se1 p, s1)
      (globalenv se2 p, s2)).
  apply forward_simulation_step with (match_states := ms); cbn.
  - intros _ _ [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1].
    cbn. eapply Genv.is_internal_match; eauto.
    + instantiate (1 := p).
      repeat apply conj; auto.
      induction (AST.prog_defs (_ p)) as [ | [id [f|v]] defs IHdefs];
        repeat (econstructor; eauto).
      * apply incl_refl.
      * apply linkorder_refl.
      * instantiate (1 := fun _ => eq). reflexivity.
      * instantiate (1 := eq). destruct v; constructor; auto.
    + eapply match_stbls_proj; eauto.
    + cbn. congruence.
  - intros q1 q2 s1 Hq Hs1. inv Hs1. inv Hq.
    assert (Hge: genv_match p R w (globalenv se1 p) (globalenv se2 p)).
    {
      cut (match_stbls R w (globalenv se1 p) (globalenv se2 p)); eauto.
      eapply (rel_push_rintro (fun se=>globalenv se p) (fun se=>globalenv se p)).
    }
    transport_hyps.
    exists (Callstate vf2 vargs2 Kstop m2). split.
    + econstructor; eauto.
      * (* revert vargs2 H9. clear - H1. *)
        (* induction H1; inversion 1; subst; constructor; eauto. *)
        revert vargs2 H8. clear - H1.
        induction H1; inversion 1; subst; constructor; eauto.
        eapply val_casted_inject; eauto.
      (* * eapply match_stbls_support; eauto. *)
    + exists w; split; try rauto.
      repeat rstep.
     (* clear -H9. induction H9; constructor; eauto.- *)
      clear -H8. induction H8; constructor; eauto.
  - intros s1 s2 r1 (w' & Hw' & Hge & Hs) H. destruct H as [v1' m1']. cbn in *.
    inv Hs. inv H4.
    eexists. split.
    + constructor.
    + exists w'. split; auto.
      constructor; eauto.
  - intros s1 s2 qx1 (w' & Hw' & Hge & Hs) Hq1.
    destruct Hq1. cbn [fst snd] in *. inv Hs.
    assert (vf <> Vundef) by (destruct vf; cbn in *; congruence).
    transport_hyps.
    eexists w', _. repeat apply conj.
    + econstructor.
      eassumption.
    + econstructor; simpl; eauto.
      clear -H6. induction H6; constructor; eauto.
    + rauto.
    + intros r1 r2 s1' (w'' & Hw'' & Hr) Hs1'. destruct Hr. inv Hs1'.
      eexists. split.
      * constructor.
      * exists w''. split; [rauto | ].
        repeat rstep. eapply genv_match_acc; eauto.
  - intros s1 t s1' Hstep s2 (w' & Hw' & Hge & Hs). cbn [fst snd] in *.
    transport Hstep.
    eexists; split; try rauto.
    exists w''. split; repeat rstep.
    eapply genv_match_acc; eauto.
  - apply well_founded_ltof.
Qed.
