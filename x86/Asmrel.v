Require Import Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Locations Stacklayout Conventions.
Require Import Mach LanguageInterface CallconvAlgebra CKLR CKLRAlgebra.
Require Import Eventsrel.
Require Import Linking.
Require Import Asm Asmgenproof.

Section PROG.
  Context (p: program).

  Definition genv_match R w: relation genv :=
    (match_stbls R w) !! (fun se => Genv.globalenv se p).

  Global Instance genv_genv_match R w:
    Related
      (genv_match R w)
      (Genv.match_genvs (mi R w) (match_globdef (fun _ => eq) eq p))
      subrel.
  Proof.
    unfold genv_match. rstep.
    intros ge1 ge2 Hge. destruct Hge as [se1 se2].
    eapply Genv.globalenvs_match.
    - red. intuition auto.
      induction (AST.prog_defs p)
        as [ | [id [f|[ ]]] ? ?];
        repeat (econstructor; eauto using incl_refl, linkorder_refl).
      apply linkorder_refl.
    - apply match_stbls_proj; auto.
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

  Global Instance find_funct_ptr_inject R w ge1 b1 ge2 b2 f:
    Transport (genv_match R w * block_inject_sameofs (mi R w)) (ge1, b1) (ge2, b2)
              (Genv.find_funct_ptr ge1 b1 = Some f)
              (Genv.find_funct_ptr ge2 b2 = Some f).
  Proof.
    intros [Hge Hb] Hf. cbn in *.
    destruct Hge. apply match_stbls_proj in H. unfold Genv.find_funct_ptr in *.
    destruct Genv.find_def as [[|]|] eqn:Hfd; try congruence. inv Hf.
    edestruct @Genv.find_def_match as (tg &?&?&?); eauto using (match_prog tt).
    inv H0. inv H1. setoid_rewrite H4. auto.
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

  Global Instance genv_match_acc R:
    Monotonic (genv_match R) (wacc R ++> subrel).
  Proof.
    intros w w' Hw' _ _ [se1 se2 Hge].
    eapply (match_stbls_acc R w w') in Hge; eauto.
    eapply (rel_push_rintro (fun se => Genv.globalenv se p) (fun se => Genv.globalenv se p));
      eauto.
  Qed.

  Definition regset_inject R (w: world R): rel regset regset :=
    forallr - @ r, (Val.inject (mi R w)).

  Inductive inject_ptr_sameofs (mi: meminj): val -> val -> Prop :=
  | inj_ptr_sameofs:
      forall b1 b2 ofs,
        mi b1 = Some (b2, 0%Z) ->
        inject_ptr_sameofs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | inj_ptr_undef:
      forall v,
        inject_ptr_sameofs mi Vundef v.
  
  Definition regset_inject' R (w: world R): rel regset regset :=
    fun rs1 rs2 =>
      forall r: preg,
        (r <> PC -> Val.inject (mi R w) (rs1 r) (rs2 r)) /\
        (r = PC -> inject_ptr_sameofs (mi R w) (rs1 r) (rs2 r)).

  Global Instance regset_inj_subrel R w:
    Related
      (regset_inject' R w)
      (regset_inject R w)
      subrel.
  Proof.
    repeat rstep. intros rs1 rs2 rel.
    unfold regset_inject', regset_inject in *.
    intros r. destruct (PregEq.eq r PC) as [-> | ].
    - specialize (rel PC) as [? H].
      destruct H; auto.
      econstructor. eauto.
      rewrite Ptrofs.add_zero; auto.
    - apply rel. auto.
  Qed.
  
  Inductive outcome_match R (w: world R): rel outcome outcome :=
  | Next_match:
      Monotonic
        (@Next')
        (regset_inject R w ++> match_mem R w ++> - ==> outcome_match R w)
  | Stuck_match o:
      Related Stuck o (outcome_match R w).
  Existing Instance Next_match.
  Existing Instance Stuck_match.

  Inductive state_match R w: rel Asm.state Asm.state :=
  | State_rel:
      Monotonic
        (@Asm.State)
        (regset_inject R w ++> match_mem R w ++> - ==> state_match R w).
  Existing Instance State_rel.
  
  Global Instance set_inject R w:
    Monotonic
      (@Pregmap.set val)
      (- ==> Val.inject (mi R w) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold regset_inject, Pregmap.set. rauto.
  Qed.
  Instance set_params: Params (@Pregmap.set) 4 := {}.

  Global Instance get_inject R w rs1 rs2 r:
    RStep
      (regset_inject R w rs1 rs2)
      (Val.inject (mi R w) (rs1 # r) (rs2 # r)) | 70.
  Proof.
    easy.
  Qed.

  Global Instance regset_inject_acc:
    Monotonic
      (@regset_inject)
      (forallr - @ R, acc tt ++> subrel).
  Proof.
    unfold regset_inject. repeat rstep.
    intros rs1 rs2 Hrs i. rauto.
  Qed.

  Lemma set_inject' R w:
    forall r: PregEq.t,
      r <> PC ->
      forall v1 v2: val,
        Val.inject (mi R w) v1 v2 ->
        forall rs1 rs2: regset,
          regset_inject' R w rs1 rs2 ->
          regset_inject' R w (rs1 # r <- v1) (rs2 # r <- v2).
  Proof.
    intros r Hr.
    unfold regset_inject', Pregmap.set.
    intros v1 v2 Hv rs1 rs2 Hrs r'.
    split; intros; destruct PregEq.eq; try congruence.
    - destruct (PregEq.eq r' PC). congruence. now apply Hrs.
    - now apply Hrs.
  Qed.

  Global Instance nextinstr_inject R w:
    Monotonic
      nextinstr
      (- ==> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold nextinstr. rauto.
  Qed.
  
  Global Instance undef_regs_inject R w:
    Monotonic
      undef_regs
      (- ==> regset_inject R w ++> regset_inject R w).
  Proof.
    intros regs. induction regs.
    - rauto.
    - rstep. apply IHregs. rauto.
  Qed.

  Global Instance nextinstr_nf_inject R w:
    Monotonic
      nextinstr_nf
      ( - ==> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold nextinstr_nf. rauto.
  Qed.

  Global Instance eval_addrmode32_inject R w:
    Monotonic
      eval_addrmode32
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode32. admit.
  Admitted.

  Global Instance eval_addrmode64_inject R w:
    Monotonic
      eval_addrmode64
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode64. admit.
  Admitted.

  Global Instance eval_addrmode_inject R w:
    Monotonic
      eval_addrmode
      (genv_match R w ++> - ==> regset_inject R w ++> Val.inject (mi R w)).
  Proof.
    unfold eval_addrmode. rauto.
  Qed.

  Global Instance exec_load_match R:
    Monotonic
      exec_load
      (|= genv_match R ++> - ==> - ==> match_mem R ++>
       - ==> regset_inject R ++> - ==> <> outcome_match R).
  Proof.
    unfold exec_load. rauto.
  Qed.

  Global Instance outcome_stuck_acc R o:
    Related Stuck o (|= (<> outcome_match R)).
  Proof.
    intros w. eexists; split; rauto.
  Qed.
  
  Global Instance exec_store_match R:
    Monotonic
      exec_store
      (|= genv_match R ++> - ==> - ==> match_mem R ++>
       - ==> regset_inject R ++> - ==> - ==> <> outcome_match R).
  Proof.
    unfold exec_store. repeat rstep.
    destruct H4 as (w'&Hw'&Hm).
    eexists; split; rauto.
  Qed.

  Global Instance eval_testcond_le R w:
    Monotonic
      eval_testcond
      (- ==> regset_inject R w ++> option_le eq).
  Proof.
    unfold eval_testcond. rauto.
  Qed.

  Global Instance goto_label_inject R w:
    Monotonic
      goto_label
      ( - ==> genv_match R w ==> - ==> - ==> regset_inject' R w ++> match_mem R w ++> outcome_match R w).
  Proof.
    pose proof rdestruct_remember_intro.
    unfold goto_label. repeat rstep.
    admit. (*find_funct_genv_match*)
    (* eapply H0.
    eapply Next_match.
    constructor.
    specialize (H0 PC) as [? Hpc]. destruct Hpc; try congruence.
    apply block_sameofs_ptrbits_inject.
    inv H5. inv H6. split; auto. *)
  Admitted.

  Definition init_nb_match R w: rel sup sup :=
    (Val.inject (mi R w) ++> option_le eq) @@ inner_sp.

  Global Instance inner_sp_rel R w:
    Monotonic
      inner_sp
      (init_nb_match R w ++> Val.inject (mi R w) ++> option_le eq).
  Proof.
    unfold init_nb_match. repeat rstep. eauto.
  Qed.

 Instance op_maxf_rel f:
    Monotonic Op.maxf (Val.inject f ++> Val.inject f ++> Val.inject f).
  Proof.
    unfold Op.maxf; rauto.
  Qed.

  Instance op_minf_rel f:
    Monotonic Op.minf (Val.inject f ++> Val.inject f ++> Val.inject f).
  Proof.
    unfold Op.minf; rauto.
  Qed.
  
  Global Instance exec_instr_match R:
    Monotonic
      (@exec_instr)
      (|= - ==> init_nb_match R ++> genv_match R ++>
       - ==> - ==> regset_inject' R ++> match_mem R ++>
       (<> outcome_match R)).
  Proof.
    intros w fsr b1 b2 Hb ge1 ge2 Hge f i rs1 rs2 Hrs' m1 m2 Hm.
    destruct i; cbn; apply regset_inj_subrel in Hrs' as Hrs;
      unfold compare_ints, compare_longs, compare_floats, compare_floats32, undef_regs;
      repeat rstep.
    - eexists. split. rauto.
      repeat first [rstep |
        match goal with
        | |- regset_inject _ _ _ match ?x with | _ => _ end => destruct x
        end].
      admit.
    - eexists. split. rauto.
      repeat first [rstep |
        match goal with
        | |- regset_inject _ _ _ match ?x with | _ => _ end => destruct x
        end].
    - eexists. split. rauto.
      rstep; auto.
      admit.
      Admitted.
(*      (*To fix*)
      apply set_inject'; [discriminate | auto | ].
      apply set_inject'; [discriminate | auto | auto ].
    - destruct m as [m1' b1']. destruct n as [m2' b2'].
      destruct H1 as (Hw & Hm' & Hb'). cbn [fst snd] in *.
      repeat rstep. rewrite Ptrofs.add_zero_l.
      destruct H1 as (w2 & Hw2 & Hm2).
      repeat rstep.
      destruct H1 as (w3 & Hw3 & Hm3).
      exists w3. split. rauto.
      repeat rstep. simpl in *.
      apply block_sameofs_ptrbits_inject; split; rauto.
    - destruct (zlt 0 sz).
      + (* sz > 0 *)
        unfold free'. repeat rewrite zlt_true by lia.
        destruct Mem.free eqn: Hfree; try rauto.
        inv H. erewrite cklr_address_inject; eauto.
        * eapply transport in Hfree as (m' & Hfree' & Hm');
            [ | clear Hfree; repeat rstep; eauto ].
          destruct Hm' as (w' & Hw' & Hm'). rewrite Hfree'.
          exists w'. split; rauto.
        * eapply Mem.free_range_perm in Hfree. apply Hfree. lia.
      + (* sz <= 0 *)
        unfold free'. repeat rewrite zlt_false by lia.
        exists w. split; rauto.
  Qed.
*)
  Lemma reg_inj_strengthen R w ge1 ge2 rs1 rs2 b ofs f:
    genv_match R w ge1 ge2 ->
    rs1 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge1 b = Some f ->
    regset_inject R w rs1 rs2 ->
    regset_inject' R w rs1 rs2.
  Proof.
    intros Hge Hpc Hf Hrs r'. split; auto.
    intros ->. specialize (Hrs PC). rewrite Hpc in *.
    inv Hrs. eapply genv_genv_match in Hge.
    unfold Genv.find_funct_ptr in Hf.
    destruct (Genv.find_def ge1 b) eqn: Hfd; try congruence.
    edestruct @Genv.find_def_match_genvs as (?&?&?&?); eauto.
    rewrite H3 in *. rewrite Ptrofs.add_zero. constructor. auto.
  Qed.

  Lemma step_reg_inj_strengthen R w nb ge1 ge2 rs1 rs2 rs1' m1 m1' live1 live1' t is:
    step is nb ge1 (State rs1 m1 live1) t (State rs1' m1' live1') ->
    genv_match R w ge1 ge2 ->
    regset_inject R w rs1 rs2 ->
    regset_inject' R w rs1 rs2.
  Proof.
    inversion 1; intros; eapply reg_inj_strengthen; eauto.
  Qed.

  Global Instance set_res_inject R w:
    Monotonic
      (@set_res)
      (- ==> Val.inject (mi R w) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold set_res. intros res.
    induction res; rauto.
  Qed.

  Global Instance extcall_arg_inject R w:
    Monotonic
      (@extcall_arg)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm l v Hv. inv Hv.
    - eexists. split; eauto. constructor.
    - transport_hyps.
      eexists. split; eauto. econstructor; eauto.
  Qed.
  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @extcall_arg: typeclass_instances.

  Global Instance extcall_arg_pair_inject R w:
    Monotonic
      (@extcall_arg_pair)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject (mi R w))).
  Proof.
    intros rs1 rs2 Hrs m1 m2 Hm lp vs Hvs.
    inv Hvs; transport_hyps; eexists; split; try constructor; rauto.
  Qed.
  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @extcall_arg_pair: typeclass_instances.

  Global Instance extcall_arguments_inject R w:
    Monotonic
      (@extcall_arguments)
      (regset_inject R w ++> match_mem R w ++> - ==> set_le (Val.inject_list (mi R w))).
  Proof.
    unfold extcall_arguments.
    intros rs1 rs2 Hrs m1 m2 Hm sg args1 H.
    remember (loc_arguments sg) as ls. clear Heqls.
    induction H.
    - eexists; split; constructor.
    - destruct IHlist_forall2 as (bs & IH).
      transport_hyps.
      eexists (x :: bs). split; constructor; auto; apply IH.
  Qed.
  Hint Extern 1 (Transport _ _ _ _ _) =>
    set_le_transport @extcall_arguments : typeclass_instances.

  Global Instance set_pair_inject R w:
    Monotonic
      (@set_pair)
      (- ==> Val.inject (mi R w) ++> regset_inject R w ++> regset_inject R w).
  Proof.
    unfold set_pair. rauto.
  Qed.

  Global Instance under_caller_save_regs_inject R w:
    Monotonic
      (@undef_caller_save_regs)
      (regset_inject R w ++> regset_inject R w).
  Proof.
    unfold undef_caller_save_regs.
    repeat rstep. intros r.
    destruct (_ || _); eauto.
  Qed.

  Global Instance exec_instr_transport R w b1 b2 se1 se2 rs1 rs2 m1 m2 f i o is:
    Transport
      (init_nb_match R w * genv_match R w * regset_inject' R w * match_mem R w)%rel
      (b1, se1, rs1, m1)
      (b2, se2, rs2, m2)
      (exec_instr is b1 se1 f i rs1 m1 = o)
      (exists o', exec_instr is b2 se2 f i rs2 m2 = o' /\ (<> outcome_match R)%klr w o o' ).
  Proof.
    intros Hrel H.
    edestruct exec_instr_match; try apply Hrel.
    eexists. split. cbn in *. reflexivity.
    eexists. split; eauto. apply H0. subst o. apply H0.
  Qed.

  Global Instance step_rel R:
    Monotonic
      (@step)
      (|= - ==> init_nb_match R ==> genv_match R ++>
          state_match R ++> - ==> k1 set_le (<> state_match R)).
  Proof.
    intros w is b1 b2 Hb ge1 ge2 Hge [rs1 m1 live1] [rs2 m2 live2] Hs t [rs1' m1' live1'] H1.
    inversion Hs as [? ? Hrs ? ? Hm]. subst.
    assert (Hrs': regset_inject' R w rs1 rs2) by eauto using step_reg_inj_strengthen.
    assert (Genv.match_stbls (mi R w) ge1 ge2) by now apply genv_genv_match.
    assert (Hpc : inject_ptr_sameofs (mi R w) (rs1 PC) (rs2 PC)) by now apply Hrs'.
    inversion Hpc; [ | inversion H1; congruence ].
    assert (block_inject_sameofs (mi R w) b0 b3) by congruence.
    inversion H1; subst; replace b with b0 in * by congruence.
    - transport FIND. transport EXEC. inversion INSTR. inv H6.
      eexists. split.
      + econstructor; eauto. congruence.
      + eexists. split. rauto. easy.
    - transport FIND. transport EVAL. transport CALL.
      eexists. split.
      + econstructor; eauto. rewrite <- INSTR. congruence.
      + eexists. split; rauto.
    - transport FIND. transport ARGS. transport CALL. transport ISP.
      eexists. split.
      + eapply exec_step_external; eauto. congruence.
        destruct (rs2 RSP); inv H8; econstructor; eauto.
        admit. admit. admit. admit.
      + eexists. split; rauto.
  Admitted.
 
End PROG.

Lemma init_nb_match_acc R w w' nb1 nb2 m1 m2:
  match_mem R w m1 m2 ->
  Mem.sup_include nb1 (Mem.support m1) ->
  Mem.sup_include nb2 (Mem.support m2) ->
  w ~> w' ->
  init_nb_match R w nb1 nb2 ->
  init_nb_match R w' nb1 nb2.
Proof.
  intros Hm Hb1 Hb2 Hw Hb.
  unfold init_nb_match. intros v1 v2 Hv. specialize (Hb v1 v2).
  unfold inner_sp. inv Hv; auto.
  destruct (mi R w b1) as [[b1' d] | ] eqn: Hmi.
  - exploit mi_acc; [ apply Hw | apply Hmi | ].
    intros Hmi'. rewrite Hmi' in H. clear Hmi'. inv H.
    apply Hb. econstructor; eauto.
  - exploit mi_acc_separated; eauto.
    intros [Hvb1 Hvb2].
    destruct (Mem.sup_dec b1 nb1); destruct (Mem.sup_dec b2 nb2);
      try rauto; unfold Mem.valid_block in *; exfalso.
    + apply Hvb1. eauto.
    + apply Hvb2. eauto.
Qed.

Inductive init_nb_state_match R w: rel (sup * state) (sup * state) :=
| init_nb_state_match_intro nb1 nb2 rs1 rs2 m1 m2 live:
    init_nb_match R w nb1 nb2 ->
    state_match R w (State rs1 m1 live) (State rs2 m2 live) ->
    Mem.sup_include nb1 (Mem.support m1) ->
    Mem.sup_include nb2 (Mem.support m2) ->
    init_nb_state_match R w (nb1, State rs1 m1 live) (nb2, State rs2 m2 live).

Lemma step_support se p nb rs1 m1 live1 t rs2 m2 live2 is:
  step is nb (Genv.globalenv se p) (State rs1 m1 live1) t (State rs2 m2 live2) ->
  Mem.sup_include (Mem.support m1) (Mem.support m2).
Proof.
  inversion 1; subst; intros.
  - eapply exec_instr_support; eauto.
  - eapply external_call_support; eauto.
  - eapply external_call_support; eauto.
Qed.

Lemma semantics_asm_rel p R is:
  forward_simulation (cc_asm R) (cc_asm R) (Asm.semantics is p) (Asm.semantics is p).
Proof.
  constructor. econstructor; eauto. instantiate (1 := fun _ _ _ => _). cbn beta.
  intros se1 se2 w Hse Hse1. cbn -[semantics] in *.
  pose (ms := fun s1 s2 =>
                klr_diam tt (genv_match p R * init_nb_state_match R)
                         w
                         (Genv.globalenv se1 p, s1)
                         (Genv.globalenv se2 p, s2)).
  apply forward_simulation_step with (match_states := ms); cbn.
  (* valid_query *)
  - intros [rs1 m1] [rs2 m2] [Hrs [Hpc Hm]].
    eapply Genv.is_internal_match; eauto.
    + repeat apply conj; auto.
      induction (prog_defs p) as [ | [id [f|v]] defs IHdefs]; repeat (econstructor; eauto).
      * instantiate (2 := fun _ => eq). reflexivity.
      * instantiate (1 := eq). destruct v. constructor. auto.
    + eapply match_stbls_proj; auto.
    + intros. rewrite H. auto.
  (* initial_state *)
  - intros [rs1 m1] [rs2 m2] [nb1 s1] Hs [Hq Hnb]. destruct Hs as [Hrs [Hpc Hm]]. inv Hq.
    assert (Hge: genv_match p R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)).
    {
      cut (match_stbls R w (Genv.globalenv se1 p) (Genv.globalenv se2 p)); eauto.
      eapply (rel_push_rintro (fun se => Genv.globalenv se p) (fun se => Genv.globalenv se p)).
    }
    specialize (Hrs PC) as Hpc'.
    transport_hyps.
    exists (Mem.support m2, State rs2 m2 true).
    repeat apply conj; auto.
    (* initial_state *)
    + econstructor.
      * eauto. 
      * specialize (Hrs SP) as Hsp. inv Hsp; try congruence.
      * specialize (Hrs RA) as Hsp. inv Hsp; try congruence.
    (* match_state *)
    + cbn. esplit. split. rauto.
      split; cbn; auto.
      split; cbn; first [ reflexivity | constructor; auto | eauto ].
      (* init_nb_match *)
      * unfold init_nb_match. intros v1 v2 Hv.
        unfold inner_sp. inv Hv; rstep.
        edestruct cklr_valid_block as [Hl Hr]; try rstep; eauto.
        destruct Mem.sup_dec; destruct Mem.sup_dec; try congruence; exfalso.
        -- apply n. apply Hl. auto.
        -- apply n. apply Hr. auto.
  (* final_state *)
  - intros [nb1 s1] [nb2 s2] [rs1 m1] (w' & Hw' & Hge & Hs) H.
    cbn [fst snd] in *. inv H. inv Hs. inv H6. eexists. split.
    (* final_state *)
    + constructor.
    (* match_reply *)
    + eexists. split; try rauto. constructor; eauto.
  (* external calls *)
  - intros [nb1 s1] [nb2 s2] qx1 (w' & Hw' & Hge & Hs) H.
    cbn [fst snd] in *.
    inversion Hs as [? ? rs1 rs2 m1 m2 live Hb Hs' Hle1 Hle2]. subst. clear Hs.
    inversion Hs' as [? ? Hrs ? ? Hm ?]. subst. clear Hs'.
    inv H. specialize (Hrs PC) as Hpc. simpl in Hpc.
    assert (rs1#PC <> Vundef). unfold Genv.find_funct in H4. destruct (rs1 PC); congruence.
    transport_hyps.
    eexists w', _. repeat apply conj.
    (* at_external *)
    + econstructor. eauto.
    (* match_query *)
    + repeat apply conj; eauto.
    (* match_stbls *)
    + rauto.
    (* simulation after reply *)
    + intros [rrs1 rm1] [rrs2 rm2] [rb1 rst1] (w'' & Hw'' & Hr) [H1 H2].
      inversion Hr as [Hrs' Hm'].
      inv H1. eexists (_, _). repeat apply conj.
      (* after_nexternal *)
      * econstructor.
        -- erewrite <- cklr_sup_include; eauto.
           eexists. split; eauto.
        -- rewrite <- H9. specialize (Hrs' SP) as Hsp'.
           exploit (init_nb_match_acc R w' w''); eauto.
           intros Hisp. inv Hisp; try congruence.
      (* nb' = nb *)
      * reflexivity.
      (* state_match *)
      * exists w''. split. rauto. split; [ | split].
        (* genv_match *)
        -- eapply genv_match_acc. apply Hw''. apply Hge.
        (* init_nb_match *)
        -- clear Hm'. eapply init_nb_match_acc; eauto.
        (* state_match *)
        -- constructor; auto.
        (* nb1 <= support m1 *)
        -- eauto.
        (* nb2 <= support m2 *)
        -- eapply Mem.sup_include_trans; eauto.
           erewrite <- cklr_sup_include; eauto.
           eexists. split; eauto.
  - intros [nb1 s1] t [nb1' s1'] [Hstep ->] [nb2 s2] (w' & Hw' & Hge & Hs).
    cbn [fst snd] in *.
    inversion Hs as [? ? rs1 rs2 m1 m2 live Hb Hs' Hle1 Hle2]. subst. clear Hs.
    destruct s1' as [rs1' m1' live'].
    assert (Mem.sup_include (Mem.support m1) (Mem.support m1')).
    { eapply step_support. eauto. }
    eapply step_rel in Hstep as (s2' & Hstep' & (w'' & Hw'' & Hs)); eauto.
    eexists (_, _). split.
    (* step *)
    + split; eauto.
    (* state_match *)
    + split with (x:=w''). split. rauto.
      inversion Hs as [? rs2' Hrs' ? m2' Hm' ? ]. subst. clear Hs.
      split; [| split]; cbn.
      (* genv_match *)
      * eapply genv_match_acc. rauto. auto.
      (* init_nb_match *)
      * clear Hm'. eapply init_nb_match_acc; eauto. inv Hs'. auto.
      (* state_match *)
      * constructor; eauto.
      (* nb1 <= support m1 *)
      * eauto.
      (* nb2 <= support m2 *)
      * eapply Mem.sup_include_trans; eauto.
        eapply step_support. eauto.
  - apply well_founded_ltof.
    Unshelve. exact tt. exact tt.
Qed.
