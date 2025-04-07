Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Mach Locations Conventions Asm.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra VCompBig.
Require Import Injp Ext.
Require Import StackingproofC CallConv.
Import GS.

Section TRANS.

  Context {li1 li2} (cc : LanguageInterface.callconv li1 li2).
  Variable L1 : semantics li1 li1.
  Variable L2 : semantics li2 li2.

  Hypothesis FSIM: Smallstep.forward_simulation cc cc L1 L2.

  Lemma forward_simulation_trans: GS.forward_simulation cc L1 L2.
  Proof.
    intros. inv FSIM. constructor.
    inv X. econstructor; eauto.
    intros. exploit fsim_lts0; eauto.
    intros FPros.
    instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  fsim_match_states0 se1 se2 wB idx s1 s2).
    simpl.
    inv FPros. econstructor; eauto.
    - intros. exploit fsim_match_final_states0; eauto.
      intros [r2 [A B]]. exists r2. exists tt. intuition auto. reflexivity. reflexivity.
    - intros. exploit fsim_match_external0; eauto.
    intros (w0 & q2 & A & B & C).
    exists w0, q2. intuition auto. reflexivity.
    eapply H4; eauto.
  Qed.

  Hypothesis BSIM: Smallstep.backward_simulation cc cc L1 L2.

  Lemma backward_simulation_trans: GS.backward_simulation cc L1 L2.
  Proof.
    intros. inv BSIM. constructor.
    inv X. econstructor; eauto.
    intros. exploit bsim_lts0; eauto.
    intros BPros.
    instantiate (1:= fun se1 se2 wB gw idx s1 s2 =>  bsim_match_states0 se1 se2 wB idx s1 s2).
    simpl.
    inv BPros. econstructor; eauto.
    - intros. exploit bsim_match_final_states0; eauto.
      intros [s1' [r1 [B [C D]]]].  exists s1', r1, tt. intuition auto. reflexivity. reflexivity.
    - intros. exploit bsim_match_external0; eauto.
    intros (w0 & s1' & q1 & A & B & C & D & E).
    exists w0, s1', q1. intuition auto. reflexivity.
  Qed.

End TRANS.


(** Compose identity pass *)
Lemma cctrans_id_1 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc_id cc) cc.
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w => eq (snd w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se1,(tt,w2))). econstructor; eauto. reflexivity.
    + econstructor; eauto. split. reflexivity. auto.
    + reflexivity.
    + intros. destruct wp1 as [xx wp2']. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [xy wp2'']. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [tt w2]].
    simpl in H. destruct H as [Heq H]. subst se'.
    simpl in H0. destruct H0 as [q1' [Heq H0]]. subst q1'.
    destruct wp1 as [tt' wp2'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (tt, wp2'). intuition auto.
    split; auto. exists r1. split. econstructor; eauto. auto.
Qed.

Lemma cctrans_id_2 {li1 li2 : language_interface} : forall (cc: callconv li1 li2),
    cctrans (cc_compose cc cc_id) cc.
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w => eq (fst w1) w).
  - econstructor. repeat apply conj; eauto.
    + instantiate (1:= (se2,(w2,tt))). econstructor; eauto. reflexivity.
    + exists q2. split; auto. econstructor; eauto.
    + reflexivity.
    + intros. destruct wp1 as [wp2' xx]. simpl in H1, H2.  subst wp2'.
      destruct wp1' as [wp2'' xy]. destruct H3. destruct H2. simpl in *.
      eexists. split; eauto. split; eauto.
      destruct H4 as [r1' [A B]]. subst. auto.
  - red. intros. destruct w1 as [se' [w2 tt]].
    simpl in H. destruct H as [H Heq]. subst se'.
    simpl in H0. destruct H0 as [q2' [H0 Heq]]. subst q2'.
    destruct wp1 as [wp2' tt'].
    destruct H1. simpl in H1, H3. simpl in H2. subst wp2'.
    exists w2. intuition auto.
    exists (wp2',tt). intuition auto. split; simpl. auto. reflexivity.
    exists r2. split. auto. econstructor; eauto.
Qed.

Lemma oldfsim_newfsim_ccid : forall {li : language_interface} (L1 L2: semantics li li),
    Smallstep.forward_simulation LanguageInterface.cc_id LanguageInterface.cc_id L1 L2 ->
    forward_simulation cc_id L1 L2.
Proof.
  intros. generalize (forward_simulation_trans LanguageInterface.cc_id L1 L2).
  intro. apply H0. auto.
Qed.


Lemma compose_id_new_injp_1 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    Smallstep.forward_simulation 1 1 L1 L2 ->
    forward_simulation cc L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros.
  rewrite <- cctrans_id_1.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
Qed.

Lemma compose_id_new_injp_2 {li1 li2: language_interface} : forall (cc: callconv li1 li2) L1 L2 L3,
    forward_simulation cc L1 L2 ->
    Smallstep.forward_simulation 1 1 L2 L3 ->
    forward_simulation cc L1 L3.
Proof.
  intros. rewrite <- cctrans_id_2.
  eapply st_fsim_vcomp; eauto. eapply oldfsim_newfsim_ccid; eauto.
Qed.



Infix "@" := GS.cc_compose (at level 30, right associativity).

(** * Lemmas about CL cc_c_locset *)


(** Ad-hoc locmap constructions for CL transformations *)
Definition Locmap_set_list (rs : Locmap.t) (vals: list val) (pairs : list (rpair loc)) := rs.

Definition set (l : loc) (v : val) (m: Locmap.t) (p: loc):=
  if Loc.eq l p then v else m p.

Definition setpairloc (p : rpair loc) (v: val) (m: Locmap.t) :=
  match p with
  |One l => set l v m
  |Twolong hi lo => set lo (Val.loword v) (set hi (Val.hiword v) m)
  end.

Lemma setpairloc_gsspair : forall l v m m',
    setpairloc (One l) v m = m' ->
    Locmap.getpair (One l) m'= v.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_true; auto.
Qed.

Lemma setpairloc_gss : forall l v m m',
    setpairloc (One l) v m = m' ->
    m' l = v.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_true; auto.
Qed.

Lemma setpairloc_gso1 : forall l v m m' l',
    setpairloc (One l) v m = m' ->
    l <> l' ->
    Locmap.getpair (One l') m' = Locmap.getpair (One l') m.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_false; auto.
Qed.

Lemma setpairloc_gso : forall l v m m' l',
    setpairloc (One l) v m = m' ->
    l <> l' ->
    m' l' = m l'.
Proof.
  intros.
  - simpl in *. subst m'. unfold set. rewrite pred_dec_false; auto.
Qed.

(**  Prove that the locations  [loc_arguments sg] is norepet *)
Lemma notin_loc_arguments_win64_y : forall l x y1 y2 t,
    y1 < y2 ->
    ~ In (One (S Outgoing y1 t)) (loc_arguments_win64 l x y2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. repeat destr.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
Qed.

Lemma notin_loc_arguments_win64_x_int : forall tys r1 r2 ireg y,
    list_nth_z int_param_regs_win64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_win64 tys r2 y).
Proof.
  induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_win64_x_float : forall tys r1 r2 ireg y,
    list_nth_z float_param_regs_win64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_win64 tys r2 y).
Proof.
    induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_y : forall l x y z1 z2 t,
    z1 < z2 ->
    ~ In (One (S Outgoing z1 t)) (loc_arguments_elf64 l x y z2).
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. repeat destr.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. eapply IHl. 2: eauto. lia.
    + intros [A|B]. inv A. extlia. eapply IHl. 2: eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_x_int : forall tys r1 r2 ireg y z,
    list_nth_z int_param_regs_elf64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_elf64 tys r2 y z).
Proof.
  induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma notin_loc_arguments_elf64_y_float : forall tys r1 r2 ireg x z,
    list_nth_z float_param_regs_elf64 r1 = Some ireg ->
    r1 < r2 ->
    ~ In (One (R ireg)) (loc_arguments_elf64 tys x r2 z).
Proof.
   induction tys; intros.
  - simpl. auto.
  - cbn -[list_nth_z]. repeat destr.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A. simpl in *.
       repeat destr_in H; repeat destr_in Heqo; extlia.
       eapply IHtys. 3: eauto. eauto. lia.
    ++ intros [A|B]. inv A.
       eapply IHtys. 3: eauto. eauto. lia.
Qed.

Lemma loc_arguments_norepet sg:
  list_norepet (loc_arguments sg).
Proof.
  unfold loc_arguments. replace Archi.ptr64 with true by reflexivity.
  destruct Archi.win64.
* cut (forall x y, list_norepet (loc_arguments_win64 (sig_args sg) x y)).
  - eauto.
  - induction (sig_args sg); cbn -[list_nth_z].
    + constructor.
    + intros x y.
      destruct a, (list_nth_z) eqn: Hz;
        cbn; constructor; eauto;
        try (apply notin_loc_arguments_win64_y; lia);
        try (eapply notin_loc_arguments_win64_x_int; try apply Hz; lia);
      try (eapply notin_loc_arguments_win64_x_float; try apply Hz; lia).
* cut (forall x y z, list_norepet (loc_arguments_elf64 (sig_args sg) x y z)).
  - intros. apply (H 0 0 0).
  - induction sig_args; cbn -[list_nth_z].
    + constructor.
    + intros x y z.
      destruct a, list_nth_z eqn: Hz; cbn; constructor; eauto;
        try (apply notin_loc_arguments_elf64_y; lia);
        try (eapply notin_loc_arguments_elf64_x_int; try apply Hz; lia);
      try (eapply notin_loc_arguments_elf64_y_float; try apply Hz; lia).
Qed.

Lemma CL_trans_ext : cctrans (cc_c_locset @ locset_ext) (c_ext @ cc_c_locset).
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w2 => snd w1 = fst w2).
  - red. intros [se' [x sg]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in x,sg. destruct x. inv Hse2. inv Hse1. inv Hq2. inv Hq1.
    cbn in H4, H5, H6. inv H6. clear Hm1 Hm2.
    exists (se2,(sg,(sg,(extw m0 m Hm)))). repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject inject_id (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H5. exists rs. split. auto. intros. reflexivity.
        - inv H5. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto.
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H as [rs1 [A B]].
      exists (lq vf1 sg rs1 m0). split. econstructor; eauto.
      constructor; eauto. constructor.
    + intros. destruct wp1' as [x wp1'].  destruct H0 as [ACE1 ACE2]. simpl in ACE1, ACE2.
      exists (wp1',tt). split. simpl. split. simpl. auto. auto.
      split. split. rewrite <- H. apply H1. reflexivity.
      inv H1.  inv H0.
      destruct H2 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H8. simpl in *.
      clear Hm1 Hm2.
      eexists. simpl. split. 
      constructor; simpl; eauto.
      2: { rewrite <- H0. econstructor. }
      2: { constructor. reflexivity. }
      red in H2. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H2. auto.
  - red. intros [? ?] [? ?] [se [sg [sg' t]]]. simpl in w,w0,w1,w2,sg,sg',t.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2.  inv Hse1. inv Hse2.
    inv Hq1. inv Hq2. simpl in H3, H5,H6. simpl in  A1, A2. inv H6.
    destruct A1 as [ACI1 ACI2]. simpl in ACI2.
    (* Compute (ccworld (c_ext @ cc_c_locset)). *)
    exists (se2,((extw m m2 Hm),sg)). repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor.
    + eexists. split. econstructor; eauto.
      2: { econstructor. }
      2: { econstructor. reflexivity. }
      simpl. red in H5.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros r1 r2 [a b] AC1 Hr. destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H, H0. inv H0.
      exists (tt,(extw m1' m2' Hm3)). split. simpl. split. auto. simpl. destruct AC1. simpl in H0, H1.
      inv H0. constructor; eauto.
      set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')). split.
      econstructor. econstructor. constructor.
      instantiate (1:= rs'').
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity. 
      econstructor.
      red. intros.  unfold rs''. 
      destruct (loc_result_always_one sg) as [r' Hr]. cbn in *. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto. constructor.
      reflexivity.
Qed.

Lemma CL_trans_ext1 : cctrans (c_ext @ cc_c_locset) (cc_c_locset @ locset_ext).
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w2 => fst w1 = snd w2).
  - red. intros [se' [xsg [sg x]]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in x,sg. destruct x. inv Hse2. inv Hse1. inv Hq2. inv Hq1.
    uncklr. cbn in H0, H1. inv H1. clear Hm1 Hm2. 
    (* Compute (ccworld (c_ext @ cc_c_locset)).  *)
    exists (se2,(extw m0 m3 Hm,sg)). repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor.
    + eexists. split. econstructor; eauto. uncklr. eauto.
      2: { econstructor. }
      2: { econstructor. reflexivity. }
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros r1 r2 [wp11 wp12] [wp21 wp22] [wp11' wp12'] Hmatch [ACE1 ACE2] [ACI1 ACI2] Hr.
      destruct Hr as [r1' [Hr1 Hr2]]. inv Hmatch. simpl in ACE1, ACE2, ACI1, ACI2. simpl in H1.
      subst. exists (tt, wp11'). repeat apply conj; simpl; eauto.
      inv Hr1. inv Hr2. simpl in H1, H3. inv H3.
      set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')).
      exists (lr rs'' m1'). split.
      econstructor. 
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity. 
      econstructor.
      red. intros.  unfold rs''. 
      destruct (loc_result_always_one sg) as [r' Hr]. cbn in *. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto. constructor.
  - red. intros [? ?] [? ?] [se [x sg]]. simpl in w,w0,w1,w2,sg. 
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] [AI1 AI2] Hm. simpl in Hm.
    subst w2. simpl in AI1, AI2. clear AI2. inv Hse1. inv Hse2.
    inv Hq1. simpl in H, H0. inv H1. inv Hq2. rename sg0 into sg.
    (* Compute ccworld (cc_c_locset @ locset_ext). *)
    exists (se2,(sg,(sg, (extw m1 m2 Hm)))). repeat apply conj; simpl; eauto.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject inject_id (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H0. exists rs. split. auto. intros. reflexivity.
        - inv H0. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto. 
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H1 as [rs1 [A B]].
      exists (lq vf1 sg rs1 m1). split. econstructor; eauto.
      constructor; simpl; eauto. constructor.
    + intros r1 r2 [a b] [_ AC2] Hr. destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H4, H6. inv H6. simpl in AC2.
      exists ((extw m' m2' Hm3),tt). split. simpl. split. auto. simpl.
      inv AC2. econstructor; eauto. eauto.
      split.
      eexists. simpl. split. 
      constructor; simpl; eauto.
      2: { constructor. }
      2: { constructor. reflexivity. }
      red in H4. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H4. auto. reflexivity.
Qed.

Lemma CL_trans_injp : cctrans (cc_c_locset @ locset_injp) (c_injp @ cc_c_locset).
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w2 => snd w1 = fst w2).
  - red. intros [se' [wp sg]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in sg. inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H9.
    cbn in H7, H8.
    (* Compute (ccworld (cc_c_locset @ locset_injp)). *)
    exists (se1,(sg,(sg,(injpw f m0 m Hm)))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject f (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H8. exists (Locmap.init Vundef).
          split. auto. intros. constructor.
        - inv H8. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto.
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H2 as [rs1 [A B]].
      exists (lq vf1 sg rs1 m0). split. econstructor; eauto.
      constructor; eauto. constructor.
    + intros. destruct wp1 as [a wp1]. simpl in a, wp1.
      destruct wp2 as [wp2 b]. simpl in b, wp2. inv H2.
      destruct wp1' as [a' wp1']. simpl in H6. subst wp2.
      destruct H3. simpl in H2,H3. destruct H4. simpl in H4,H6.
      exists (wp1',tt). split. simpl. split. auto. auto. split.
      destruct b. split; auto.
      destruct H5 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H13.
      simpl in H5, H11. subst wp1'. simpl in *.
      eexists. simpl. split. 
      constructor; simpl; eauto.
      2: {constructor. reflexivity. }
      red in H11. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H11. auto.
  - red. intros [? ?] [? ?] [se [sg [sg' t]]]. simpl in w,w0,w1,w2,sg,sg',t.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2.  inv Hse1. inv Hse2. inv A2. destruct A1. simpl in H4, H5, H2. inv H3. simpl in H6.
    inv H6.
    inv Hq1. inv Hq2. inv H11. simpl in H8, H10.
    (* Compute (ccworld (c_injp @ cc_c_locset)). *)
    exists (se2,((injpw f m m3 Hm),sg)). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + eexists. split. econstructor; eauto.
      2: { econstructor. }
      2: { econstructor. reflexivity. }
      simpl. red in H10.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H2, H3. clear H3.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H6. inv H6. simpl in H3.
      exists (tt,(injpw f0 m1' m2' Hm4)). split. split; auto.
      simpl. inv H2. constructor; auto. split. simpl.
      set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')).
      exists (lr rs'' m1'). split.
      econstructor. 
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity.
      econstructor. simpl.
      red. intros.  unfold rs''.
      destruct (loc_result_always_one sg) as [r' Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto.
      constructor. reflexivity.
Qed.


Lemma CL_trans_injp1 : cctrans (c_injp @ cc_c_locset) (cc_c_locset @ locset_injp).
Proof.
  constructor.
  econstructor. instantiate (1:= fun w1 w2 => fst w1 = snd w2).
  - red. intros [se' [xsg [sg wp]]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in sg. inv Hse2. inv Hse1. inv Hq2. inv Hq1. simpl in H2, H3, H4. subst wp.
    cbn in H3, H4. inv H5.  clear Hm1 Hm2 Hm3.
    (* Compute ccworld (c_injp @ cc_c_locset). *)
    exists (se2,((injpw f m0 m3 Hm),sg)). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + eexists. split. econstructor; eauto.
      2: { econstructor. }
      2: { econstructor. reflexivity. }
      simpl. red in H4.
      pose proof (loc_arguments_external sg).
      induction loc_arguments; cbn in *; auto.
      constructor; auto.
      apply locmap_getpair_inject.
      assert (forall_rpair (loc_external sg) a) by eauto.
      destruct a; cbn in *; intuition auto.
    + intros. destruct wp1 as [wp1 a]. simpl in a, wp1.
      destruct wp2 as [b wp2]. simpl in b, wp2. inv H2.
      destruct wp1' as [wp1' a']. simpl in H9. subst wp2.
      destruct H5. simpl in H2,H5. destruct H7. simpl in H7,H9.
      exists (tt,wp1'). split. simpl. split. auto. auto. split.
      destruct b. split; auto.
      destruct H8 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H10. simpl in H11. subst.
      simpl in H8.
       set (rs'' := Locmap.setpair (loc_result sg) vres1 (rs')).
      exists (lr rs'' m1'). split.
      econstructor. 
      unfold rs''. simpl.
      destruct (loc_result_always_one sg) as [r ->].
      cbn. rewrite Locmap.gss. reflexivity.
      econstructor. simpl.
      red. intros.  unfold rs''.
      destruct (loc_result_always_one sg) as [r' Hr]. rewrite Hr in *. cbn in *.
      intuition subst. rewrite Locmap.gss. auto. constructor.
  - red. intros [? ?] [? ?] [se [t sg]]. simpl in w,w0,w1,w2,sg,t.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] [A1 _] Hm. inv Hse1. inv Hse2. simpl in Hm. subst w2.
    simpl in A1.
    inv Hq1. inv Hq2. inv H4. clear Hm1 Hm2 Hm3. simpl in H3, H2.
    (* Compute (ccworld (c_injp @ cc_c_locset)). *) rename sg0 into sg.
    exists (se1,(sg,(sg,(injpw f m0 m3 Hm0)))). repeat apply conj; simpl; eauto.
    + generalize (loc_arguments_always_one sg). intro Hone.
      generalize (loc_arguments_norepet sg). intro Hnorepet.
      assert (exists rs1, (fun p : rpair loc => Locmap.getpair p rs1) ## (loc_arguments sg) = vargs1 /\
                       forall l : loc, loc_external sg l -> Val.inject f (rs1 l) (rs l)).
      { generalize dependent vargs1.
        induction loc_arguments; cbn; intros.
        - inv H3. exists (Locmap.init Vundef).
          split. auto. intros. constructor.
        - inv H3. exploit IHl; eauto. intros.
          exploit Hone. right. eauto. auto.
          inv Hnorepet. auto.
          exploit Hone. left. reflexivity. intros [la Hla].
          intros [rs1 [A B]].
          exists (setpairloc a v rs1). split.
          + simpl. f_equal.  rewrite Hla.
          erewrite setpairloc_gsspair; eauto.
          rewrite <- A.
          apply map_ext_in. intros. exploit Hone; eauto.
          right. eauto. intros [la0 Hla0]. rewrite Hla0.
          erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
          inv Hnorepet. congruence.
          + intros. rewrite Hla.
            destruct (Loc.eq la l0).
            * subst. erewrite setpairloc_gss; eauto.
            * erewrite setpairloc_gso. 2: eauto. eauto. auto.
      }
      destruct H4 as [rs1 [A B]].
      exists (lq vf1 sg rs1 m0). split. econstructor; eauto.
      constructor; eauto. constructor.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H4, H6. clear H4.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H8. inv H10. simpl in H4. subst b. simpl in H8.
      exists ((injpw f0 m' m2' Hm),tt). split. split; auto. split. 2: reflexivity.
      eexists. simpl. split. 
      constructor; simpl; eauto.
      2: {constructor. reflexivity. }
      red in H8. simpl.
      destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr in *. cbn in *.
      apply H8. auto.
Qed.

(** Lemmas about MA cc_mach_asm *)

Inductive preg_class :=
  | prc_pc
  | prc_sp
  | prc_ra 
  | prc_preg_of (r : mreg)
  | prc_other.

Inductive preg_classify_spec : preg_class -> preg -> Prop :=
  | prc_pc_spec : preg_classify_spec prc_pc PC
  | prc_sp_spec : preg_classify_spec prc_sp SP
  | prc_ra_spec : preg_classify_spec prc_ra RA
  | prc_preg_spec m : preg_classify_spec (prc_preg_of m) (preg_of m)
  | prc_other_spec r : preg_classify_spec prc_other r.

Definition preg_classify r :=
  match r with
    | PC => prc_pc
    | SP => prc_sp
    | RA => prc_ra
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
    | CR _ => prc_other
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

Lemma inject_noundef_eq_trans: forall v1 v2 v1' v2' j,
    v1 = v2 -> v1 <> Vundef ->
    Val.inject j v1 v1' -> Val.inject j v2 v2' ->
    v1' = v2'.
Proof.
  intros. inv H1; inv H2; try congruence.
Qed.

(** * Compose MA with injp *)
Lemma MA_trans_injp1 : cctrans (cc_mach_asm @ asm_injp) (mach_injp @ cc_mach_asm).
Proof.
  constructor.  econstructor.  instantiate (1:= fun w1 w2 => snd w1 = fst w2).
  - red. intros [se' [wp [rs sup]]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H19. clear Hm1 Hm2 Hm3.
    cbn in H12, H15, H17, H18. rename rs1 into mrs1. rename mrs into mrs2. rename m0 into m1. rename m into m2. rename rs into rs3.
     set (rs2 r :=
           match preg_classify r with
             | prc_pc => vf1
             | prc_sp => sp1
             | prc_ra => ra1  
             | prc_preg_of m => mrs1 m
             | prc_other => Vundef
           end).
    (* Compute ccworld (cc_mach_asm @ asm_injp). *)
    exists (se1,(rs2,(Mem.support m1) , injpw f m1 m2 Hm)).
    repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor; eauto.
    + exists (rs2, m1). split.
      replace vf1 with rs2 # PC by reflexivity.
      replace sp1 with rs2 # RSP by reflexivity.
      replace ra1 with rs2 # RA by reflexivity.
      econstructor; eauto.
      unfold rs2. simpl. inv H3. inv H15; try congruence.
      constructor.
      eapply Mem.valid_block_inject_1; eauto.
      intros. simpl. unfold rs2. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto.
      intros. unfold rs2.
      destruct (preg_classify_cases r); eauto.
      rewrite <- H5. eauto.
    + intros. destruct wp1 as [a wp1]. simpl in a, wp1.
      destruct wp2 as [wp2 b]. simpl in b, wp2. inv H6.
      destruct wp1' as [a' wp1']. simpl in H10. subst wp2.
      destruct H7. simpl in H6,H7. destruct H8. simpl in H8,H10.
      exists (wp1',tt). split. simpl. split. auto. auto. split. split; eauto.
      destruct H9 as [r1' [Hr1 Hr2]]. inv Hr1. destruct r2. inv Hr2.
      inv H22. simpl in H23. rename m' into m1'. rename m into m3'.
      simpl in H21. subst wp1'. simpl in H21. rename r into rs3'.
      rename rs' into rs2'.
      exists (mr (fun r => rs3' (preg_of r)) m3'). split.
      econstructor; simpl; eauto. intros. rewrite H20. eauto.
      econstructor; eauto.
      eapply inject_noundef_eq_trans. apply H9. rewrite H9.
      unfold rs2. simpl. eauto. eauto. inv H7. eauto.
      eapply inject_noundef_eq_trans. apply H14. rewrite H14.
      unfold rs2. simpl. eauto. eauto. inv H7. eauto.
      inv H7. destruct H33. apply unchanged_on_e'.
  - red. intros [? ?] [? ?] [se [[rs sup] wp]]. simpl in w,w0,w1,w2.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2. inv Hse1. inv Hse2. simpl in A2.
    inv A2. destruct A1. simpl in H2, H3.
    inv Hq1. destruct q2. inv Hq2. inv H9.  inv H11. simpl in H8, H10.
    (* Compute (ccworld (c_injp @ cc_c_locset)). *)
    exists (se2,((injpw f m m0 Hm),(r, Mem.support m0))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + exists (mq r#PC r#SP r#RA (fun m => r (preg_of m)) m0).
      split. econstructor; simpl; eauto.
      inv H5. congruence. intros. rewrite H7. eauto.
      econstructor; eauto.
      generalize (H8 PC). intro. inv H9; congruence.
      generalize (H8 RSP). intro. inv H5. inv H9; try congruence. constructor.
      eapply Mem.valid_block_inject_2; eauto.
      generalize (H8 RA). intro. inv H9; congruence.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H9, H11. clear H11.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H11. inv H12. simpl in H13. subst a.
      clear Hm4 Hm5.
      exists (tt,(injpw f0 m1 m2 Hm0)). split. split; auto.
      split; auto. simpl.
      set (rs1' r :=
             match preg_classify r with
             | prc_pc => rs RA
             | prc_sp => rs SP
             | prc_preg_of m => rs1 m
             | prc_other => Vundef
             | prc_ra => Vundef
           end).
      exists (rs1', m1). split.
      econstructor. reflexivity. reflexivity. inv H9. destruct H26 as [_ [A _]]. auto.
      intros. unfold rs1'. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto. inv H9.
      intros. unfold rs1'.
      destruct (preg_classify_cases r0); eauto.
      rewrite H16. eauto.
      rewrite H15. eauto. rewrite <- H19. eauto.
Qed.

Lemma MA_trans_injp2 : cctrans (mach_injp @ cc_mach_asm) (cc_mach_asm @ asm_injp).
Proof.
  constructor.  econstructor.  instantiate (1:= fun w1 w2 => fst w1 = snd w2).
  - red. intros [se' [[rs sup] wp]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    inv Hse2. inv Hse1. inv Hq1. destruct q2. inv Hq2. inv H7. inv H9. clear Hm1 Hm2 Hm3.
    cbn in H6.
    rename m0 into m2. rename m into m1. rename r into rs3.
(*     set (rs2 r :=
           match preg_classify r with
             | prc_pc => vf1
             | prc_sp => sp1
             | prc_ra => ra1  
             | prc_preg_of m => mrs1 m
             | prc_other => Vundef
           end).*)
    (* Compute ccworld (mach_injp @ cc_mach_asm). *)
    exists (se2,(injpw f m1 m2 Hm,(rs3,Mem.support m2))).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor.
    + exists (mq rs3#PC rs3#RSP rs3#RA (fun m => rs3 (preg_of m)) m2). split.
      econstructor; eauto. inv H3. congruence. simpl.
      intros. rewrite H5. eauto. constructor.
      econstructor.
      generalize (H6 PC). intro. inv H7; congruence.
      generalize (H6 RSP). intro. inv H3. inv H7; try congruence. constructor.
      eapply Mem.valid_block_inject_2; eauto.
      generalize (H6 RA). intro. inv H7; congruence. reflexivity.
    + intros. destruct wp1 as [wp1 a]. simpl in a, wp1.
      destruct wp2 as [b wp2]. simpl in b, wp2. inv H7.
      destruct wp1' as [wp1' a']. simpl in H12. subst wp2.
      destruct H9. simpl in H7,H9. destruct H10. simpl in H12,H10.
      exists (tt, wp1'). split. simpl. split. auto. auto. split. split; eauto.
      destruct H11 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H13. simpl in H11, H14.
      subst wp1'. simpl. simpl in H11.
      rename m0 into m1'. rename m3 into m2'.
      set (rs1' r :=
             match preg_classify r with
             | prc_pc => rs RA
             | prc_sp => rs SP
             | prc_preg_of m => rs1 m
             | prc_other => Vundef
             | prc_ra => Vundef
             end).
      exists (rs1', m1'). split.
      econstructor. unfold rs1'. simpl. reflexivity.
      reflexivity. inv H7. destruct H27 as [_ [? _]]. auto.
      intros. unfold rs1'. rewrite preg_classify_preg. reflexivity.
      constructor. inv H7. intros. simpl. unfold rs1'.
      destruct (preg_classify_cases r); eauto.
      rewrite H17. eauto.
      rewrite H16. eauto. rewrite <- H20. eauto.
      constructor.
  - red. intros [? ?] [? ?] [se [wp [rs sup]]]. simpl in w,w0,w1,w2.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2. inv Hse1. inv Hse2. simpl in A2.
    inv A2. destruct A1. simpl in H2, H3.
    inv Hq1. destruct q2. inv Hq2. inv H11.  simpl in H5, H7,H9, H10.
    rename rs1 into mrs1. rename rs2 into mrs2. rename m0 into m1.
    rename m into m2. rename r into rs3.
    set (rs2 r :=
           match preg_classify r with
           | prc_pc => vf1
           | prc_sp => sp1
           | prc_ra => ra1  
           | prc_preg_of m => mrs1 m
           | prc_other => Vundef
           end).
    (* Compute (ccworld (cc_mach_asm @ asm_injp)). *)
    exists (se1,((rs2, Mem.support m1,injpw f m1 m2 Hm))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
         + exists (rs2, m1). split.
      replace vf1 with rs2 # PC by reflexivity.
      replace sp1 with rs2 # RSP by reflexivity.
      replace ra1 with rs2 # RA by reflexivity.
      econstructor; eauto. 
      unfold rs2. simpl. inv H21. inv H7; try congruence.
      constructor.
      eapply Mem.valid_block_inject_1; eauto.
      intros. simpl. unfold rs2. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto.
      intros. unfold rs2.
      destruct (preg_classify_cases r); eauto.
      rewrite <- H23. eauto.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H12. clear H11.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. destruct r2. inv Hr2. simpl in H16. inv H18. simpl in H19. subst b.
      simpl in H16.
      clear Hm4 Hm5.
      exists ((injpw f0 m' m Hm0),tt). split. split; auto.
      split; auto. simpl.
      exists (mr (fun m => r (preg_of m)) m).
      split. econstructor; simpl; eauto. intros. rewrite H15. eauto. inv H12.
      econstructor.
      eapply inject_noundef_eq_trans. apply H11. rewrite H11. eauto. eauto.
      eauto.
      eapply inject_noundef_eq_trans. apply H13. rewrite H13. eauto. eauto.
      eauto. destruct H32 as [_ [? _]]. eauto. reflexivity.
Qed.

Lemma MA_trans_ext1 : cctrans (cc_mach_asm @ asm_ext) (mach_ext @ cc_mach_asm).
Proof.
   constructor.  econstructor.  instantiate (1:= fun w1 w2 => snd w1 = fst w2).
  - red. intros [se' [wp [rs sup]]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    inv Hse2. inv Hse1. inv Hq2. inv Hq1. inv H16. clear Hm1.
    cbn in H9, H12, H14, H15.
    rename rs1 into mrs1. rename mrs into mrs2.
    rename m into m2. rename rs into rs3.
     set (rs2 r :=
           match preg_classify r with
             | prc_pc => vf1
             | prc_sp => sp1
             | prc_ra => ra1  
             | prc_preg_of m => mrs1 m
             | prc_other => Vundef
           end).
    (* Compute ccworld (cc_mach_asm @ asm_injp). *)
    exists (se2,(rs2,(Mem.support m1) , extw m1 m2 Hm0)).
    repeat apply conj; eauto.
    + constructor; eauto. constructor. constructor; eauto.
    + exists (rs2, m1). split.
      replace vf1 with rs2 # PC by reflexivity.
      replace sp1 with rs2 # RSP by reflexivity.
      replace ra1 with rs2 # RA by reflexivity.
      econstructor; eauto.
      unfold rs2. simpl. inv H0. rewrite <- H3 in H12. inv H12; try congruence.
      unfold inject_id in H7. inv H7. constructor.
      erewrite Mem.mext_sup; eauto.
      intros. simpl. unfold rs2. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto.
      intros. unfold rs2.
      destruct (preg_classify_cases r); eauto.
      rewrite <- H2. eauto. split.
      unfold rs2. simpl. eauto.
      constructor.
    + intros. destruct wp1 as [a wp1]. simpl in a, wp1.
      destruct wp2 as [wp2 b]. simpl in b, wp2. simpl in H3. subst wp2.
      destruct wp1' as [a' wp1']. simpl in H4.
      destruct H4. simpl in H3,H4. destruct H5. simpl in H5,H7.
      exists (wp1',tt). split. simpl. split. auto. auto. split. split; eauto.
      destruct H6 as [r1' [Hr1 Hr2]]. inv Hr1. destruct r2. inv Hr2.
      inv H19. simpl in H20. rename m' into m1'. rename m into m3'.
      subst wp1'. rename r into rs3'.
      rename rs' into rs2'.
      exists (mr (fun r => rs3' (preg_of r)) m3'). split.
      econstructor; simpl; eauto. intros. rewrite H17. eauto. constructor.
      econstructor; eauto.
      eapply inject_noundef_eq_trans. apply H6. rewrite H6.
      unfold rs2. simpl. eauto. eauto. inv H7. eauto.
      eapply inject_noundef_eq_trans. apply H11. rewrite H11.
      unfold rs2. simpl. eauto. eauto. inv H7. eauto.
      inv H4. eauto.
  - red. intros [? ?] [? ?] [se [[rs sup] wp]]. simpl in w,w0,w1,w2.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2. inv Hse1. inv Hse2. simpl in A2.
    inv A2. destruct A1. simpl in H, H0.
    inv Hq1. destruct q2. inv Hq2. destruct H6 as [Hpc H6]. inv H6. simpl in H5.
    (* Compute (ccworld (c_injp @ cc_c_locset)). *)
    exists (se2,((extw m m0 Hm),(r, Mem.support m0))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + exists (mq r#PC r#SP r#RA (fun m => r (preg_of m)) m0).
      split. econstructor; simpl; eauto.
      inv H2. congruence. intros. rewrite H4. eauto. constructor.
      econstructor; eauto.
      generalize (H5 PC). intro. inv H6; congruence.
      generalize (H5 RSP). intro. inv H2. inv H6; try congruence. constructor.
      rewrite <- H7 in H2. inv H2. inv H10. erewrite <- Mem.mext_sup; eauto.
      generalize (H5 RA). intro. inv H6; congruence.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H6, H7. clear H7.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in H7. inv H8. simpl in H9. subst a.
      clear Hm4 Hm3.
      exists (tt,(extw m1 m2 Hm2)). split. split; auto. simpl.
      inv H6. constructor; eauto.
      split; auto. simpl.
      set (rs1' r :=
             match preg_classify r with
             | prc_pc => rs RA
             | prc_sp => rs SP
             | prc_preg_of m => rs1 m
             | prc_other => Vundef
             | prc_ra => Vundef
           end).
      exists (rs1', m1). split.
      econstructor. reflexivity. reflexivity. inv H6. auto.
      intros. unfold rs1'. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto. inv H6.
      intros. unfold rs1'.
      destruct (preg_classify_cases r0); eauto.
      rewrite H12. eauto.
      rewrite H11. eauto. rewrite <- H15. eauto. constructor.
Qed.

Lemma MA_trans_ext2 : cctrans (mach_ext @ cc_mach_asm) (cc_mach_asm @ asm_ext).
Proof.
    constructor.  econstructor.  instantiate (1:= fun w1 w2 => fst w1 = snd w2).
  - red. intros [se' [[rs sup] wp]] se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]].
    inv Hse2. inv Hse1. inv Hq1. destruct q2. inv Hq2. destruct H4 as [Hpc H4]. inv H4. clear Hm1.
    cbn in H3.
    rename m0 into m2. rename m into m1. rename r into rs3.
(*     set (rs2 r :=
           match preg_classify r with
             | prc_pc => vf1
             | prc_sp => sp1
             | prc_ra => ra1  
             | prc_preg_of m => mrs1 m
             | prc_other => Vundef
           end).*)
    (* Compute ccworld (mach_injp @ cc_mach_asm). *)
    exists (se2,(extw m1 m2 Hm0,(rs3,Mem.support m2))).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor.
    + exists (mq rs3#PC rs3#RSP rs3#RA (fun m => rs3 (preg_of m)) m2). split.
      econstructor; eauto. inv H0. congruence. simpl.
      intros. rewrite H2. eauto. constructor.
      econstructor.
      generalize (H3 PC). intro. inv H4; congruence.
      generalize (H3 RSP). intro. inv H0. inv H4; try congruence. constructor.
      erewrite <- Mem.mext_sup; eauto. inv H8. congruence.
      generalize (H3 RA). intro. inv H4; congruence. reflexivity.
    + intros. destruct wp1 as [wp1 a]. simpl in a, wp1.
      destruct wp2 as [b wp2]. simpl in b, wp2.
      destruct wp1' as [wp1' a']. simpl in H4. subst wp2.
      destruct H5. simpl in H4,H5. destruct H6. simpl in H6,H8.
      exists (tt, wp1'). split. simpl. split. auto. auto. split. split; eauto.
      destruct H7 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H13. simpl in H7, H9.
      inv H9.
      simpl. 
      rename m0 into m1'. rename m3 into m2'.
      set (rs1' r :=
             match preg_classify r with
             | prc_pc => rs RA
             | prc_sp => rs SP
             | prc_preg_of m => rs1 m
             | prc_other => Vundef
             | prc_ra => Vundef
             end).
      exists (rs1', m1'). split.
      econstructor. unfold rs1'. simpl. reflexivity.
      reflexivity. inv H4. auto. 
      intros. unfold rs1'. rewrite preg_classify_preg. reflexivity.
      constructor. inv H4. intros. simpl. unfold rs1'.
      destruct (preg_classify_cases r); eauto.
      rewrite H11. eauto.
      rewrite H12. eauto. rewrite <- H16. eauto.
      constructor.
  - red. intros [? ?] [? ?] [se [wp [rs sup]]]. simpl in w,w0,w1,w2.
    intros se1 se2 q1 q2 [Hse1 Hse2] [q1' [Hq1 Hq2]] A1 A2. inv Hse1. inv Hse2. simpl in A2.
    inv A2. destruct A1. simpl in H, H0.
    inv Hq1. destruct q2. inv Hq2. inv H8.  simpl in H2, H4,H6, H7.
    rename rs1 into mrs1. rename rs2 into mrs2.
    rename m into m2. rename r into rs3.
    set (rs2 r :=
           match preg_classify r with
           | prc_pc => vf1
           | prc_sp => sp1
           | prc_ra => ra1  
           | prc_preg_of m => mrs1 m
           | prc_other => Vundef
           end).
    (* Compute (ccworld (cc_mach_asm @ asm_injp)). *)
    exists (se2,((rs2, Mem.support m1,extw m1 m2 Hm))). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + exists (rs2, m1). split.
      replace vf1 with rs2 # PC by reflexivity.
      replace sp1 with rs2 # RSP by reflexivity.
      replace ra1 with rs2 # RA by reflexivity.
      econstructor; eauto. 
      unfold rs2. simpl. inv H18. rewrite <- H8 in H4. inv H4; try congruence.
      constructor. inv H13. erewrite Mem.mext_sup; eauto.
      intros. simpl. unfold rs2. rewrite preg_classify_preg. reflexivity.
      econstructor; simpl; eauto.
      intros. unfold rs2.
      destruct (preg_classify_cases r); eauto.
      rewrite <- H20. eauto. split. unfold rs2. simpl. eauto. constructor.
    + intros r1 r2 [a b] AC1 Hr. simpl in AC1. destruct AC1.
      simpl in H9. clear H8.
      destruct Hr as [r1' [Hr1 Hr2]].
      inv Hr1. destruct r2. inv Hr2. simpl in H13. inv H15. simpl in H16. subst b.
      clear Hm4 Hm3.
      exists ((extw m' m Hm2),tt). split. split; auto. simpl. inv H9. constructor; eauto.
      split; auto. simpl.
      exists (mr (fun m => r (preg_of m)) m).
      split. econstructor; simpl; eauto. intros. rewrite H12. eauto. constructor.
      econstructor.
      eapply inject_noundef_eq_trans. apply H8. rewrite H8. eauto. eauto.
      eauto.
      eapply inject_noundef_eq_trans. apply H10. rewrite H10. eauto. eauto.
      eauto. inv H9. eauto. reflexivity.
Qed.
(*  
(** * Lemmas about LM and cc_stacking *)



(*cc_locset_mach
Record cc_lm_world :=
  lmw {
    lmw_sg : signature;
    lmw_rs : Mach.regset;
    lmw_m : mem;
    lmw_sp : val;
    }.
*)
Inductive cc_locset_mach_mq: cc_lm_world -> locset_query -> mach_query -> Prop :=
  cc_locset_mach_mq_intro sg vf m_ rs sp ra m (Hra:ra <> Vundef):
    args_removed sg sp m m_ ->
    pointer_tid (Mem.tid (Mem.support m)) sp ->
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

Program Definition cc_locset_mach: LanguageInterface.callconv li_locset li_mach :=
  {|
    LanguageInterface.match_senv _ := eq;
    LanguageInterface.match_query := cc_locset_mach_mq;
    LanguageInterface.match_reply := cc_locset_mach_mr;
  |}.
(*
Definition cc_lm_gworld : Type := val * signature.

Program Instance cc_lm_lens : Lens (cc_lm_world) (cc_lm_gworld) :=
  {
    get := fun w => (lmw_sp w, lmw_sg w);
    set := fun w gw => lmw (snd gw) (lmw_rs w) (lmw_m w) (fst gw);
  }.
Next Obligation.
  destruct a. reflexivity.
Qed.
Next Obligation.
  destruct t. reflexivity.
Qed.

Program Instance LMworld : World cc_lm_world :=
  {
    w_state := cc_lm_gworld;
    w_lens := cc_lm_lens;
    w_acci := fun _ _ => True;
    w_acce := eq;
  }.

Program Definition cc_locset_mach: GS.callconv li_locset li_mach :=
  {|
    ccworld := cc_lm_world;
    ccworld_world := LMworld;
    match_senv _ := eq;
    match_query := cc_locset_mach_mq;
    match_reply := cc_locset_mach_mr;
  |}.
 *)

Lemma free_right_inj':
  forall f m1 m2 b lo hi m2',
  Mem.mem_inj f m1 m2' ->
  Mem.free m2 b lo hi = Some m2' ->
  Mem.mem_inj f m1 m2.
Proof.
  intros. exploit Mem.free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p).
  intros. eapply Mem.perm_free_3; eauto.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align; eauto.
(* mem_contents *)
  intros. rewrite FREE in mi_memval; simpl. eauto.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  Mem.inject f m1 m2' ->
  Mem.free m2 b lo hi = Some m2' ->
  Mem.inject f m1 m2.
Proof.
  intros. inversion H. constructor.
  inv mi_thread. constructor; auto.
  erewrite <- (Mem.support_free _ _ _ _ _ H0); eauto.
(* inj *)
  eapply free_right_inj'; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply Mem.perm_free_inv in H2; eauto. destruct H2.
  right. intro. destruct H2. subst b2. eapply Mem.perm_free_2. eauto. eauto. eapply Mem.perm_inject; eauto.
  eapply mi_perm_inv; eauto with mem.
Qed.

Lemma inject_removed_inject : forall m1 m2 m3 sg sp j,
    Mem.inject j m1 m2 ->
    args_removed sg sp m3 m2 ->
    Mem.inject j m1 m3.
Proof.
  intros. inv H0. eauto.
  eapply free_right_inject; eauto.
Qed.

Lemma args_removed_support : forall sg sp m m',
    args_removed sg sp m m' -> Mem.support m' = Mem.support m.
Proof.
  intros. inv H. auto. erewrite Mem.support_free; eauto.
Qed.

Lemma args_removed_unchanged_on : forall sg sp m m_,
    args_removed sg sp m m_ ->
    Mem.unchanged_on (not_init_args (size_arguments sg) sp) m_ m.
Proof.
  intros. inv H. eauto with mem.
  eapply Mem.free_unchanged_on'; eauto.
  intros. intro. red in H4. apply H4. constructor. auto.
Qed.

Lemma args_removed_noperm : forall sg sp m m_,
    args_removed sg sp m m_ ->
    (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs -> ~ Mem.perm m_ b ofs k p).
Proof.
  intros. inv H. rewrite H1 in H0. inv H0. extlia.
  inv H0.
  eapply Mem.perm_free_2; eauto.
Qed.

Lemma args_removed_acci: forall f m1 m2 m3 f' m1' m3' sg sp Hm13 Hm13' Hm12,
    injp_acci (injpw f m1 m3 Hm13) (injpw f' m1' m3' Hm13') ->
    args_removed sg sp m3 m2 ->
    exists m2' Hm12',
      args_removed sg sp m3' m2' /\
        injp_acci (injpw f m1 m2 Hm12) (injpw f' m1' m2' Hm12').

Compute gworld (cc_locset_mach @ mach_injp).
Lemma args_removed_extends : forall sg sp m1 m2,
    args_removed sg sp m2 m1 -> Mem.extends m1 m2.
Proof.
  intros. inv H. eapply Mem.extends_refl.
  eapply Mem.free_left_extends; eauto. eapply Mem.extends_refl.
Qed.

Inductive stacking_LM_injp_match : injp_world -> (unit * injp_world) -> Prop :=
    |LM_injp_intro: forall f m1 m2 m3 Hm13 Hm23 x,
    Mem.extends m1 m2 ->
    stacking_LM_injp_match (injpw f m1 m3 Hm13) (x, injpw f m2 m3 Hm23).

Instance load_stack_inject R:
  Monotonic load_stack
    (|= match_mem R ++> Val.inject @@ [mi R] ++> - ==> - ==>
        k1 option_le (Val.inject @@ [mi R])).
Proof.
  unfold load_stack. rauto.
Qed.

Lemma Stackingtrans_LM_injp: cctrans (cc_stacking_injp) (cc_locset_mach @ mach_injp).
Proof.
  constructor.
  econstructor. instantiate (1:= stacking_LM_injp_match).
  - red. intros w2 se1 se2 q1 q2 Hse Hq. simpl in w2.
    destruct w2 as [se [[sg mrs2 m2' sp2] [f m2 m3 Hm23]]].
    destruct Hse as [Hse1 Hse2]. simpl in Hse1, Hse2. subst.
    destruct Hq as [q1' [Hq1 Hq2]]. inv Hq1. inv Hq2.
    simpl in H9,H11,H14. inv H16. rename m2' into m2. rename m0 into m3. rename m_ into m1.
    simpl in H15. rename sp0 into sp3. rename rs2 into mrs3.
    assert (Hm13: Mem.inject f m1 m3). eapply Mem.extends_inject_compose.
    eapply args_removed_extends. eauto. eauto.
    exists (stkw injp (injpw f m1 m3 Hm13) sg (make_locset mrs2 m2 sp2) sp3 m3).
    repeat apply conj; eauto.
    + inv Hse2. constructor; eauto. erewrite args_removed_support; eauto.
    + constructor; eauto. inv H6. inv H11. constructor.
      erewrite <- inject_block_tid; eauto.
      erewrite args_removed_support; eauto.
      inv H14; congruence.
      -- constructor. eauto with mem.
         inv H3. split. intros. red in H. extlia. intros.
         apply tailcall_possible_reg in H0. inv H0. eauto.
         split. intros. inv H11. do 2 eexists. split. reflexivity.
         assert (Hmatch: match_mem injp (injpw f m2 m3 Hm23) m2 m3).
         constructor. split.
         eapply transport in H as (m2_ & Hm2_ & Hm_).
           2: {
             change ?x with (id x) in H. repeat rstep.
             eapply offset_sarg_ptrrange_inject; eauto.
             eapply Mem.free_range_perm; eauto.
             rewrite (offset_sarg_expand (size_arguments sg)).
             extlia.
           } 
           eapply Mem.free_range_perm; eauto.
           intros ofs Hofs.
           eapply offset_fits_inject; eauto.
           eapply Mem.free_range_perm; eauto.
           intros.
           edestruct H2 as [v Hv]; eauto.
           exploit StackingproofC.load_stack_inject; eauto.
           intros [v' [A B]]. exists v'. split. eauto.
           simpl. setoid_rewrite Hv. eauto.
      --
        destruct 1 as [sb2 sofs2 ofs]. inv H6. inv H11.
        inv H3. red in H1. rewrite H1 in H. extlia.
      assert (offset_sarg ofs0 0 <= ofs - delta < offset_sarg ofs0 (size_arguments sg)).
      {
        rewrite (offset_sarg_expand (size_arguments sg)) in *.
        exploit (offset_sarg_inject injp (injpw f m2 m3 Hm23) m2 m3 b ofs0 sb2 (Ptrofs.add ofs0 (Ptrofs.repr delta)) 0); eauto.
        * constructor.
        * eapply Mem.free_range_perm; eauto. extlia.
        * inversion 1. simpl in H3.
          assert (delta0 = delta) by congruence. extlia.
      }
      intros sb1' delta' Hsb1' Hp.
      destruct (eq_block b sb1').
      { subst sb1'. assert (delta' = delta) by congruence; subst.
        eapply Mem.perm_free_2; eauto. }
      inversion Hm23. red in mi_no_overlap.
      edestruct (mi_no_overlap b sb2 delta sb1' sb2 delta'); eauto.
      * eapply Mem.perm_max, Mem.perm_implies.
        eapply Mem.free_range_perm; eauto.
        constructor.
      * eapply Mem.perm_free_3; eauto.
      * extlia.
      -- inv H6. inv H11; try congruence.
      -- inv H14; try congruence.
    + constructor. eapply args_removed_extends; eauto.
    + intros until wp1'. intros MATCH ACE ACI MR. simpl in ACE.
      inv MATCH. rename m0 into m1'. rename m4 into m2'. rename m5 into m3'.
      inv MR. rename m2'0 into m3''. rename m1'0 into m1''.
      assert (exists m2'', Mem.inject f' m2'' m3'' /\  Mem.unchanged_on (not_init_args (size_arguments sg) sp2) m1'' m2'' /\  Mem.unchanged_on (loc_init_args (size_arguments sg) sp2) m2 m2'' /\ Mem.support m1'' = Mem.support m2'').
      admit. destruct H0 as [m2'' [Hm23'' [UNC1 [UNC2 SUP]]]].
      (** The construction here is basically compose m1'' and the original arguments in m2 *)
      exists (tt, injpw f' m2'' m3'' Hm23'').
      repeat apply conj; simpl; eauto.
      -- inv ACE. constructor; eauto.
         red. intros. admit. (*seems ok*)
         red. intros. admit.
         admit. destruct H26.
         split; auto.
         eapply Mem.unchanged_on_implies. eauto. intros.
         destruct H0. split; eauto. red. intros. intro.
         exploit H0; eauto. admit.
         admit. (*seems ok*)
      -- inv ACI. 
         admit. (** wrong here, the relation between m1' and m2' can not be extends,
                     should be sth like UNC which ensures the equation of valus and perms*)
      -- set (rs1' r := if is_callee_save r then mrs2 r else
                          if in_dec mreg_eq r (regs_of_rpair (loc_result sg)) then ls1' (R r) else
                            Vundef).
         exists (mr rs1' m2''). split.
         econstructor; simpl; eauto.
      * subst rs1'. intros r REG. cbn.
        destruct in_dec; try contradiction.
        replace (is_callee_save r) with false; auto.
        pose proof (loc_result_caller_save sg) as Hr.
        destruct loc_result; cbn in *; intuition congruence.
      * subst rs1'. intros r REG. cbn.
        rewrite REG. congruence.
      *  destruct 1. inv H11. intro.
         eapply H21; eauto.
         2: { inv ACE. eauto. }
        instantiate (1 := ofs + delta).
        2: replace (ofs + delta - delta) with ofs by extlia; eauto with mem.
        constructor. unfold offset_sarg in *.
        rewrite (Ptrofs.add_commut sofs), Ptrofs.add_assoc, Ptrofs.add_commut.
        erewrite Mem.address_inject; eauto. extlia.
        2: { inv ACE; eauto. }
        erewrite <- (Mem.unchanged_on_perm _ m2 m2''); eauto.
        ** inv H3.
           ++ apply zero_size_arguments_tailcall_possible in H2.
              rewrite H2 in H0. extlia.
           ++ eapply Mem.free_range_perm; eauto. unfold offset_sarg. extlia.
        ** constructor. unfold offset_sarg. extlia.
        ** inv H3.
           ++ apply zero_size_arguments_tailcall_possible in H2. extlia.
           ++ eapply Mem.perm_valid_block, Mem.free_range_perm; eauto.
      * econstructor; simpl; eauto. intros.
        unfold rs1'. cbn.
        destruct (is_callee_save r) eqn:CSR; eauto.
        destruct in_dec; eauto.
  - red. intros. simpl in wp1, wp2, w1.
    inv H2. destruct w1 as [[f' m1' m3'' Hm13'] sg ls spa m3'].
    inv H. inv H0. simpl in H1.
    assert (exists sp2 m2', args_removed sg sp2 m2' m1' /\ Val.inject f' sp2 spa /\ sp2 <> Vundef).
    admit. destruct H as [sp2 [m2' [REMOVE [SPinj SPdef]]]].
    assert (exists ra2', Val.inject f' ra2' ra2 /\ ra2' <> Vundef).
    admit. destruct H as [ra2' [RAinj RAdef]].
    assert (Hm23': Mem.inject f' m2' m3'). admit.
    (* Compute ccworld (cc_locset_mach @ mach_injp). *)
    set (rs2' mr := ls (R mr)).
    exists (se1, (lmw sg rs2' m2' sp2,injpw f' m2' m3' Hm23')).
    repeat apply conj; simpl; eauto.
    + admit.
    + split. auto. constructor; eauto.
      erewrite <- args_removed_support; eauto.
    + exists (mq vf1 sp2 ra2' rs2' m2'). split.
      assert (ls = make_locset rs2' m2' sp2). admit.
      rewrite H. constructor; eauto.
      inversion SPL. subst spa. inversion SPinj. subst b2 ofs2 sp2.
      constructor. erewrite inject_block_tid; eauto.
      erewrite <- args_removed_support; eauto. subst sp2. congruence.
      admit. admit.
      constructor; eauto. constructor.
    + intros r1 r2 [tt [f'' m1'' m3'' Hm23'']]. simpl in tt. intros [ACE1 ACE2]. simpl in ACE2.
      clear ACE1. intros [r2' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H11. rename m' into m2''.
      rename m4 into m3''. rename m'_ into m1''.
      assert (Hm13'': Mem.inject f'' m1'' m3''). admit. simpl in H2.
      exists (injpw f'' m1'' m3'' Hm13''). repeat apply conj.
      -- admit.
      -- econstructor; eauto.
         intros. rewrite <- H5. eauto. eauto.
         intros. unfold rs2' in *. rewrite <- H7; eauto.
         {
           inv ACE2. destruct H29 as [A B].
           eapply Mem.unchanged_on_implies. eauto.
           intros b ofs Hi Hv. split.
           red. intros b2 d INJ23. inv Hi.
           admit.
           inv Hi. inv SPL. erewrite <- inject_tid; eauto.
           
         }
         intros. admit.
      -- econstructor; eauto. admit. (** need a newly defined m1'' and m2'' relation *)
        replace tt with Datatypes.tt. econstructor. admit. constructor.
      (** We have to redesign [cc_locset_mach] and [cc_stacking] for new [cctrans]*)
Abort.
  

Lemma trans_LM_injp : cctrans (cc_locset_mach @ mach_injp @ injp) ()


(*
Inductive match12_stacking : injp_world -> (injp_world * (val * signature * ext_world)) -> Prop :=
|match12_stacking_intro : forall f m1 m2 m3 m4 Hm Hm1 Hm2 sg sp,
    match12_stacking (injpw f m1 m4 Hm) ((injpw f m1 m2 Hm1),(sp, sg, extw m3 m4 Hm2)).

Lemma Stackingtrans : cctrans (cc_stacking_injp) (locset_injp @ cc_locset_mach @ mach_ext).
Proof.
  constructor.
  econstructor. instantiate (1:= match12_stacking).
  - red. intros w2 se1 se2 q1 q2 Hse Hq.
    destruct w2 as [se [[sig wx] [se' [[sig' mrs] [m3 m4 Hm34]]]]].
    destruct Hse as [Hse1 [Hse2 Hse3]]. simpl in Hse1, Hse2, Hse3. subst.
    destruct Hq as [q1' [Hq1 [q2' [Hq2 Hq3]]]]. inv Hq2. simpl in Hq1. inv Hq1.
    inv H10. inv Hq3. uncklr.
    simpl in H5, Hse1, H9. simpl in H18. inv H19.
    rename m2 into m4. rename lmw_m0 into m3.
    rename m_ into m2.
    (* set (rs2 := (make_locset mrs m3 lmw_sp0)). *)
    assert (Hm13 : Mem.inject f m1 m3). eapply inject_removed_inject; eauto.
    assert (Hm14 : Mem.inject f m1 m4).
    eapply Mem.inject_extends_compose; eauto.
    inv H12; try congruence. inv H14; try congruence. inv H17; try congruence.
    exists (stkw injp (injpw f m1 m4 Hm14) sig' ls1 sp2 m4).
    repeat apply conj; eauto.
    + inv Hse1. econstructor; eauto. erewrite <- Mem.mext_sup. 2: eauto.
      erewrite <- args_removed_support; eauto.
    + econstructor; eauto. erewrite inject_tid; eauto.
      intros. red in H9. 
      eapply Mem.val_inject_lessdef_compose.
      eapply H9. constructor. simpl. apply val_inject_id; eauto. 
      constructor; eauto with mem.
      -- split. intros. inv H3. rewrite H0 in H. extlia.
      intros. inv H6. do 2 eexists. split. reflexivity.
      split.
      assert (Hp3: Mem.range_perm m3 sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sig')) Cur Freeable).
      eapply Mem.free_range_perm. eauto.
      red. intros. eapply Mem.perm_extends. eauto. eauto. eauto.
      intros. inv H3. apply tailcall_possible_reg in H. inv H. eauto.
      exploit H4; eauto. intros [v Hv].
      unfold load_stack in Hv.
      exploit Mem.loadv_extends; eauto. intros [v' [Hv' Hless]].
      exists v'. split. auto.
      exploit H9. eapply loc_external_arg. eauto.
      intro. eapply Mem.val_inject_lessdef_compose. eauto. simpl. setoid_rewrite Hv. eauto. 
      -- intros. inv H3. rewrite H0 in H. inv H. extlia. inv H.
         red. intros. intro. exploit Mem.perm_inject. apply H. apply Hm.
         eauto. eapply Mem.perm_free_2; eauto. lia.
    + simpl. econstructor; eauto.
    + intros r1 r2 wp1 wp2 wp1' MATCH ACE ACI MR.
      inv MATCH. simpl in ACE. rename f0 into f'. rename m0 into m1'.
      rename m4 into m2'. rename m5 into m4'. rename m2' into m4.
      destruct wp1' as [f'' m1'' m4'' Hm14''].
      (* exploit args_removed_acci; eauto. intros (m2'' & Hm12'' & REMOVE & ACCI). *)
      assert (exists m2'', args_removed sig' sp2 m4'' m2'').
      admit. destruct H as [m2'' REMOVE].
      assert (Hm12'' : Mem.inject f'' m1'' m2''). admit.
      (*memory construction, should be correct *)
      
      exists ((injpw f'' m1'' m2'' Hm12''), (sp2, sig', extw m4'' m4'' (Mem.extends_refl m4''))). repeat apply conj; simpl; eauto.
      -- simpl. admit.
         (*{ clear - H3 REMOVE ACE.
           inv H3; inv REMOVE. inv ACE. constructor; eauto.
           rewrite H in H2. inv H2. rewrite H3 in H1. inv H1.
           inv ACE. constructor; eauto.
           - red. intros. admit. (*ok*)
           - red. intros.
             eapply Mem.perm_free_4 in H4 as NOTI. 2: eauto.
             eauto with mem.
           - inv H18. split; eauto. erewrite Mem.support_free; eauto.
             rewrite (Mem.support_free _ _ _ _ _ H5). auto.
             inv unchanged_on_e'. constructor; eauto.
             erewrite Mem.support_free. 2: eauto.
             rewrite (Mem.support_free _ _ _ _ _ H5). auto.
             admit. admit. (*ok*)
           - red. intros. exploit H20; eauto. intros [A B].
             split; eauto with mem.
         }*)
      -- simpl. inv ACE. inv Hm3. destruct H21 as [[X1 X2] [Y Z]].
         constructor; eauto. congruence. rewrite mext_sup. eauto.
         admit. (** We have not prove that ext == ext @ ext?*)
      -- admit.
      -- inv MR. admit.
      -- inv MR.
         set (ls2' := make_locset rs2' m4 sp2).
         exists (lr ls2' m2''). split.
         constructor; eauto. constructor.
         set (rs1' r := if is_callee_save r then mrs r else
                  if in_dec mreg_eq r (regs_of_rpair (loc_result sig')) then ls2' (R r) else
                   Vundef).
         exists (mr rs1' m4'' ). split.
         econstructor; eauto. intros. unfold rs1'.
         replace (is_callee_save r) with false; auto.
         rewrite pred_dec_true. reflexivity. auto.
         pose proof (loc_result_caller_save sig') as Hr.
         red in Hr. destruct (loc_result sig'). inv H. congruence. inv H0.
         destruct Hr.
         simpl in H. destruct H. congruence. destruct H. congruence. inv H.
         intros. unfold rs1'. rewrite H. reflexivity.
         eapply args_removed_unchanged_on; eauto.
         admit.
         erewrite args_removed_support; eauto.
         intros. eapply args_removed_noperm; eauto.
         constructor; simpl; eauto.
         (** The problem is still here??? *)
         intros. unfold rs1'. destruct (is_callee_save r).
         
         admit. constructor.
  - red. intros. inv H2. inv H0. simpl in H1, H.
    rename f0 into f'. rename m0 into m1'. rename m4 into m3'.
    assert (exists m2', args_removed sg0 sp2 m3' m2' /\ Mem.inject f' m1' m2').
    admit. destruct H0 as [m2' [REMOVE' Hm12']]. (*construction, should be ok*)
    (* Compute ccworld (locset_injp @ cc_locset_mach). *)
    exists (se2, (sg0, (injpw f' m1' m2' Hm12'), (lmw sg0 rs2 m3' sp2))).
    repeat apply conj; simpl; eauto.
    + admit. (** problem? using different sg and sp *)
    + simpl. split. inv H. constructor; eauto. erewrite args_removed_support; eauto.
      reflexivity.
    + simpl. set (ls2' := make_locset rs2 m3' sp2).
      exists (lq vf2 sg0 ls2' m2'). split.
      econstructor; eauto.
      -- simpl. red. intros. inv H0. simpl. apply H5. destruct H6 as [A [B C]].
         exploit C; eauto. intros [v [D E]]. simpl. setoid_rewrite D.
         rauto.
      -- constructor.
      -- unfold ls2'. econstructor; eauto.
         erewrite <- inject_tid; eauto.
    + intros r1 r2 [[f'' m1'' m2'' Hm12''] [sp3 sg3]].
      intros [ACE b]. simpl in ACE, b. inv b. intros [r2' [Hr1 Hr2]].
      inv Hr1. inv Hr2. inv H10. simpl in H0. rename m' into m3''.
      rename m1'0 into m1''. rename m2'0 into m2''.
      assert (Hm13'' : Mem.inject f'' m1'' m3'').
      {
        eapply CA.inject_unchanged_on_inject; eauto.
        eapply CA.not_init_args_dec. intros. red. intros. intro. exploit Mem.perm_inject; eauto.
        eapply H23. destruct (loc_init_args_dec  (size_arguments sg3) sp3 b ofs).
        replace (ofs - delta + delta) with ofs. eauto. lia. elim H10. auto.
      }
      exists ((injpw f'' m1'' m3'' Hm13'')).
      repeat apply conj; eauto.
      -- admit. (*acce, similar*)
      -- econstructor; eauto.
         intros. rewrite H17. eauto. eauto.
         intros. rewrite H18.
         eapply Values.val_inject_incr. 2: eauto. inv ACE. eauto. eauto.
         intros. red. intros. specialize (H7 _ _ H10).
         intro. exploit Mem.perm_inject. 2: eapply Hm12''. apply H11. eauto. replace (ofs - delta + delta) with ofs by lia.
         eapply H23; eauto.
      -- econstructor; eauto.
         admit.
         
Lemma Stackingtrans : cctrans (cc_stacking_injp) (locset_injp @ cc_locset_mach).
Proof.
  constructor.
  econstructor. instantiate (1:= match12_stacking).
  - red. intros w2 se1 se2 q1 q2 Hse Hq.
    destruct w2 as [se [[sig wx] [sig' rs]]].
    destruct Hse as [Hse1 Hse2]. simpl in Hse1, Hse2. inv Hse2.
    destruct Hq as [q1' [Hq1 Hq2]]. inv Hq2. simpl in Hq1. inv Hq1.
    inv H10. simpl in H5, Hse1, H9.
    set (rs2 := (make_locset rs lmw_m0 lmw_sp0)). rename m_ into m2.
    rename lmw_m0 into m3.
    assert (Hm13 : Mem.inject f m1 m3). eapply inject_removed_inject; eauto.
    exists (stkw injp (injpw f m1 m3 Hm13) sig' ls1 lmw_sp0 m3).
    repeat apply conj; eauto.
    + inv Hse1. econstructor; eauto. erewrite <- args_removed_support; eauto.
    + econstructor; eauto. erewrite inject_tid; eauto.
      intros. apply H9. constructor. constructor; eauto with mem.
      -- split. intros. inv H3. rewrite H0 in H. extlia.
      intros. inv H6. do 2 eexists. split. reflexivity.
      split. eapply Mem.free_range_perm. eauto. eauto.
      intros. inv H3.  apply tailcall_possible_reg in H. inv H. eauto.
      exploit H4; eauto. intros [v Hv]. exists v. split. auto.
      exploit H9. eapply loc_external_arg. eauto.
      simpl. setoid_rewrite Hv. simpl. auto.
      -- intros. inv H3. rewrite H0 in H. inv H. extlia. inv H.
         red. intros. intro. exploit Mem.perm_inject. apply H. apply Hm.
         eauto. eapply Mem.perm_free_2; eauto. lia.
    + econstructor; eauto.
    + intros r1 r2 wp1 wp2 wp1' MATCH ACE ACI MR.
      inv MATCH. simpl in ACE. rename f0 into f'. rename m0 into m1'.
      rename m4 into m2'. rename m5 into m3'.
      destruct wp1' as [f'' m1'' m3'' Hm13''].
      (* exploit args_removed_acci; eauto. intros (m2'' & Hm12'' & REMOVE & ACCI). *)
      assert (exists m2'', args_removed sig' lmw_sp0 m3'' m2'').
      admit. destruct H0 as [m2'' REMOVE].
      assert (Hm12'' : Mem.inject f'' m1'' m2''). admit.
      (*memory construction, should be correct *)      
      exists ((injpw f'' m1'' m2'' Hm12''), (lmw_sp0, sig')). repeat apply conj; simpl; eauto.
      -- simpl.
         { clear - H3 REMOVE ACE.
           inv H3; inv REMOVE. inv ACE. constructor; eauto.
           rewrite H in H2. inv H2. rewrite H3 in H1. inv H1.
           inv ACE. constructor; eauto.
           - red. intros. admit. (*ok*)
           - red. intros.
             eapply Mem.perm_free_4 in H4 as NOTI. 2: eauto.
             eauto with mem.
           - inv H18. split; eauto. erewrite Mem.support_free; eauto.
             rewrite (Mem.support_free _ _ _ _ _ H5). auto.
             inv unchanged_on_e'. constructor; eauto.
             erewrite Mem.support_free. 2: eauto.
             rewrite (Mem.support_free _ _ _ _ _ H5). auto.
             admit. admit. (*ok*)
           - red. intros. exploit H20; eauto. intros [A B].
             split; eauto with mem.
         }
      -- simpl.
         
         admit. (*ACCI, should be ok*)
      -- inv MR.
        set (ls2' := make_locset rs2' m2' lmw_sp0).
        exists (lr ls2' m2''). split.
        constructor; eauto. constructor.
        constructor; eauto. admit. (** The problem : how to protect callee-save regs *)
        eapply args_removed_unchanged_on; eauto.
        erewrite args_removed_support; eauto.
        intros. eapply args_removed_noperm; eauto.
  - red. intros. inv H2. inv H0. simpl in H1, H.
    rename f0 into f'. rename m0 into m1'. rename m4 into m3'.
    assert (exists m2', args_removed sg0 sp2 m3' m2' /\ Mem.inject f' m1' m2').
    admit. destruct H0 as [m2' [REMOVE' Hm12']]. (*construction, should be ok*)
    (* Compute ccworld (locset_injp @ cc_locset_mach). *)
    exists (se2, (sg0, (injpw f' m1' m2' Hm12'), (lmw sg0 rs2 m3' sp2))).
    repeat apply conj; simpl; eauto.
    + admit. (** problem? using different sg and sp *)
    + simpl. split. inv H. constructor; eauto. erewrite args_removed_support; eauto.
      reflexivity.
    + simpl. set (ls2' := make_locset rs2 m3' sp2).
      exists (lq vf2 sg0 ls2' m2'). split.
      econstructor; eauto.
      -- simpl. red. intros. inv H0. simpl. apply H5. destruct H6 as [A [B C]].
         exploit C; eauto. intros [v [D E]]. simpl. setoid_rewrite D.
         rauto.
      -- constructor.
      -- unfold ls2'. econstructor; eauto.
         erewrite <- inject_tid; eauto.
    + intros r1 r2 [[f'' m1'' m2'' Hm12''] [sp3 sg3]].
      intros [ACE b]. simpl in ACE, b. inv b. intros [r2' [Hr1 Hr2]].
      inv Hr1. inv Hr2. inv H10. simpl in H0. rename m' into m3''.
      rename m1'0 into m1''. rename m2'0 into m2''.
      assert (Hm13'' : Mem.inject f'' m1'' m3'').
      {
        eapply CA.inject_unchanged_on_inject; eauto.
        eapply CA.not_init_args_dec. intros. red. intros. intro. exploit Mem.perm_inject; eauto.
        eapply H23. destruct (loc_init_args_dec  (size_arguments sg3) sp3 b ofs).
        replace (ofs - delta + delta) with ofs. eauto. lia. elim H10. auto.
      }
      exists ((injpw f'' m1'' m3'' Hm13'')).
      repeat apply conj; eauto.
      -- admit. (*acce, similar*)
      -- econstructor; eauto.
         intros. rewrite H17. eauto. eauto.
         intros. rewrite H18.
         eapply Values.val_inject_incr. 2: eauto. inv ACE. eauto. eauto.
         intros. red. intros. specialize (H7 _ _ H10).
         intro. exploit Mem.perm_inject. 2: eapply Hm12''. apply H11. eauto. replace (ofs - delta + delta) with ofs by lia.
         eapply H23; eauto.
      -- econstructor; eauto.
         admit.
         (** another problem : shall we unify the 2unchanged_on with args_removed? Maybe the "unchanged_on + noperm relation" is enough?*)
(** Seems can be proved? *)


Inductive match12_LM_ext : GS.gworld (cc_locset_mach @ mach_ext) -> (GS.gworld (locset_ext @ cc_locset_mach)) -> Prop  :=
      |match12_LM_ext_intro sp sg _m1 m1 m3 m3_ Hm1 Hm2:
        args_removed sg sp _m1 m1 ->
        args_removed sg sp m3 m3_ ->
        match12_LM_ext (sp, sg, extw _m1 m3 Hm1) (extw m1 m3_ Hm2, (sp, sg)).

(** We have to change cc_locset_mach. But the problem is how? *)
Lemma LM_trans_ext : cctrans (cc_locset_mach @ mach_ext) (locset_ext @ cc_locset_mach).
Proof.
  constructor. econstructor. instantiate (1:= match12_LM_ext).
  - red. intros [se' [[sg a] [sg' rs]]] se1 se2 q1 q2.
    intros [Hse1 Hse2] [q1' [Hq1 Hq2]].
    simpl in a. inv Hse1. inv Hse2. inv Hq1. inv Hq2.
    simpl in H1, H, H0. rename m2 into m3_.
    rename lmw_m0 into m3. rename lmw_sp0 into sp. inv H1. rename rs into rs3.
    (* set (rs2 := fun r => ls1 (R r)). *)
    assert (exists rs2 _m1, args_removed sg sp _m1 m1 /\ Mem.extends _m1 m3 /\ ls1 = make_locset rs2 _m1 sp).
    admit. destruct H1 as [rs2 [_m1 [REMOVE [Hm13 Hls1]]]].
    (* Compute (ccworld (cc_locset_mach @ mach_ext)).  *)
    exists (se2, ((lmw sg rs2 _m1 sp, (extw _m1 m3 Hm13)))). repeat apply conj; eauto.
    + constructor. constructor. constructor.
    +      (*m3'0 and rs'0 are the result of modifying rs and m3 by values in ls1*)
      eexists. split. simpl. rewrite Hls1.
      econstructor; eauto. erewrite Mem.mext_sup; eauto.
      econstructor; eauto. inversion H13. congruence.
      simpl. reflexivity.
      reflexivity.
      intros. simpl. assert (Hrs2: rs2 = fun r => ls1 (R r)). admit. rewrite Hrs2.
      apply H0. constructor. constructor.
    + simpl. constructor; eauto.
    + intros r1 r2 [[sp0 sg0] wp1] [wp2 [sp1 sg1]] [[sp00 sg00] wp1'] MATCH [ACE1 ACE2] [ACI1 ACI2] Hr. simpl in *.
      inversion ACE1. subst sp00 sg00. clear ACE1 ACI1. inversion MATCH. subst sp2 sg2 wp1 wp2 sp1 sg1.
      rename m0 into m1'. rename _m0 into _m1'. rename m2 into m3'. rename m3_0 into m3'_.
      destruct (wp1') as [_m1'' m3'' Hm13'']. destruct Hr as [r2' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H11.
      rename m' into _m1''. rename m2 into m3''. rename m'_ into m1''.
      assert (exists m3''_, Mem.extends m1'' m3''_ /\ args_removed sg sp m3'' m3''_). admit.
      destruct H1 as [m3''_ [Hm1'' REMOVE'']].
      exists (extw m1'' m3''_ Hm1'', (sp, sg)). repeat apply conj; eauto.
      -- simpl. admit.
      -- simpl. admit.
      -- simpl. exists (lr ls' m3''_). split. econstructor; eauto.
         simpl. red. intros. reflexivity. constructor. econstructor; eauto.
         admit.
         admit.
         admit. (*ok*)
         admit. (* why we need this ?? *)
         eapply args_removed_support; eauto.
         admit. (*can be derived from args_removed *)
  - red. intros [[sp sg] wp1] [wp2 [sp1 sg1]] [sex [[sgx rsx mx] [m0 tm0 hm0]]] se1 se2 q1 q2 Hse [q1' [Hq1 Hq2]] ACI MATCH.
    inv MATCH. inv Hse. inv H. inv H0. inv Hq1. inv Hq2. simpl in H11, H13, H16, H17. inv H18.
    destruct ACI as [ACI1 ACI2]. simpl in ACI1, ACI2. rename mx into _m1'. rename m4 into m3'.
Abort.
*)
Lemma LM_trans_ext : cctrans (cc_locset_mach @ mach_ext ) (locset_ext @ cc_locset_mach).
Proof.


(*    exists (se2,((lmw sg rs lmw_m vf2),tt)).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor.
    + Abort. *)

*)

(** *Compose c_injp @ c_injp into c_injp  *****)
Require Import InjpAccoComp.

Inductive match_injp_comp_world : (injp_world * injp_world) -> injp_world -> Prop :=
|world_comp_intro:
  forall m1 m2 m3 j12 j23 j13 Hm12 Hm23 Hm13,
    j13 = compose_meminj j12 j23 ->
    match_injp_comp_world (injpw j12 m1 m2 Hm12, injpw j23 m2 m3 Hm23) (injpw j13 m1 m3 Hm13).

Inductive injp_trivial_comp_world : (injp_world * injp_world) -> injp_world -> Prop :=
|trivial_comp_intro : forall j m1 m3 Hm12 Hm23 Hm13,
    injp_trivial_comp_world (injpw (meminj_dom j) m1 m1 Hm12, injpw j m1 m3 Hm23)
      (injpw j m1 m3 Hm13).


          
Lemma injp_comp_acce : forall w11 w12 w11' w12' w1 w2,
    injp_trivial_comp_world (w11, w12)  w1 ->
    match_injp_comp_world (w11', w12')  w2 ->
    injp_acce w11 w11' -> injp_acce w12 w12' ->
    injp_acce w1 w2.
Proof.
  intros. inv H. inv H0.
  inv H1. inv H2. rename m0 into m1'. rename m2 into m2'. rename m4 into m3'.
  econstructor; eauto.
  - destruct H11. split. auto. eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split; auto. red. unfold meminj_dom.
    rewrite H. reflexivity.
  - assert (j = compose_meminj (meminj_dom j) j).
    rewrite meminj_dom_compose. reflexivity.
    rewrite H. rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
    destruct (j12 b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j23 bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    exploit H14; eauto. unfold meminj_dom. rewrite Hb. reflexivity.
    intros [X Y].
    destruct (j bi) as [[? ?] | ] eqn:Hfbi.
    {
      eapply Mem.valid_block_inject_1 in Hfbi; eauto.
    }
    edestruct H22; eauto. erewrite <- inject_tid; eauto.
    inv Hm0. inv mi_thread. erewrite <- Hjs; eauto.
  - red. intros. unfold compose_meminj in H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H0.
    destruct (j23 bi) as [[b2' d']|] eqn: Hj2; inv H2.
    exploit H15; eauto. unfold meminj_dom. rewrite H. reflexivity.
    intros [A B]. split; auto.
    intro. apply B. red. erewrite inject_block_tid; eauto.
Qed.


Lemma inject_preserve_tid : forall j m1 m2 b1 b2 d,
    j b1 = Some (b2, d) ->
    Mem.inject j m1 m2 ->
    fst b1 = fst b2 /\ Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2).
Proof.
  intros. inv H0. inv mi_thread. inv Hms. split; eauto.
Qed.

Lemma inject_other_thread : forall j m1 m2 b1 b2 d,
    j b1 = Some (b2, d) ->
    Mem.inject j m1 m2 ->
    fst b1 <> Mem.tid (Mem.support m1) <->
    fst b2 <> Mem.tid (Mem.support m2).
Proof.
  intros. edestruct inject_preserve_tid; eauto.
  split;
  congruence.
Qed.
(*
Inductive external_mid_hidden: injp_world -> injp_world -> Prop :=
|external_mid_hidden_intro :
  forall j12 j23 m1 m2 m3 Hm12 Hm23
    (** This case says that for any related external blocks [j13 b1 = Some b3],
        we have constructed b2 in m2 s.t. j12 b1 = Some b2.*)
    (Hconstr1: forall b1 b2 d, fst b2 <> Mem.tid (Mem.support m2) ->
                 j12 b1 = Some (b2, d) -> j23 b2 <> None)
    (** This cases says that for any external stack block [with permission] in m2
        and *mapped to m3* in m2, it comes from a corresponding position im m1*)
    (Hconstr2: forall b2 ofs2 b3 d2, fst b2 <> Mem.tid (Mem.support m2) ->
                Mem.perm m2 b2 ofs2 Max Nonempty -> j23 b2 = Some (b3, d2) ->
                exists b1 ofs1, Mem.perm m1 b1 ofs1 Max Nonempty /\ j12 b1 = Some (b2, ofs2 - ofs1)),
    external_mid_hidden (injpw j12 m1 m2 Hm12) (injpw j23 m2 m3 Hm23).
 *)

(** From the incoming world [w1], where the internal memory is hidden, we will construct a 
    mid-level memory [m2] to get [w11] and [w12]. This construction is either [I: Initial state]
    or [Y: After external].   

    For I, [m2] is exactlt [m1]. For Y, [m2] is constructed by the "injp construction" algorithm.
    These constructions are defined by us, therefore we can ensure that for any "thread-external block"
    (i.e. allocated by other threads) [b2] in [m2], it must be *public* in both [w11] and [w12].
    Otherwise it should not be created. 
    
    Therefore, we can prove the following lemma, which states that the internal accessbility of
    [w11, w12] to [w11',w12'] can indicate the same accessbility of [w2] which hides the mid-level
    memory
 *)

Lemma inject_val_tid : forall j m1 m2 b1 b2 d,
    Mem.inject j m1 m2 ->
    j b1 = Some (b2, d) ->
    fst b1 = fst b2.
Proof.
  intros. inv H. inv mi_thread. erewrite Hjs; eauto.
Qed.

Lemma injp_comp_acci : forall w11 w12 w11' w12' w1 w2,
    match_injp_comp_world (w11, w12)  w1 ->
    external_mid_hidden w11 w12 ->
    match_injp_comp_world (w11', w12')  w2 ->
    injp_acci w11 w11' -> injp_acci w12 w12' ->
    injp_acci w1 w2.
Proof.
  intros. inv H. inv H1. inv H0.
  rename j0 into j12'. rename j1 into j23'. rename m0 into m1'. rename m4 into m2'.
  rename m5 into m3'.
  inv H2. inv H3.
  constructor; eauto.
  - destruct H11 as [S11 H11]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. red in X. unfold compose_meminj in X.
    destruct (j12 b) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j23 b2) as [[b3 d2]|] eqn:Hj23; try congruence.
    eapply Hconstr1 in Hj12; eauto. congruence.
    erewrite <- inject_other_thread; eauto.
  - destruct H21 as [S21 H21]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. intros. red in X. intro.
    exploit Hconstr2; eauto. erewrite inject_other_thread; eauto.
    intros (b1 & ofs1 & Hp1 & Hj12).
    exploit X. unfold compose_meminj. rewrite Hj12, H. reflexivity.
    replace (ofs - (ofs - delta - ofs1 + delta)) with ofs1 by lia. auto.
    auto.
  - rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
        destruct (j12' b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
        destruct (j23' bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
        inv Hb'.
        destruct (j12 b1) as [[? ?] | ] eqn:Hb1.
        + apply H13 in Hb1 as Heq. rewrite Hb1' in Heq. inv Heq.
          destruct (j23 b) as [[? ?] |] eqn: Hb2.
          unfold compose_meminj in Hb. rewrite Hb1, Hb2 in Hb. congruence.
          exfalso. exploit H23; eauto.
          erewrite <- inject_tid; eauto.
          erewrite <- inject_val_tid. 3: eauto. auto. eauto.
          intros [X Y].
          eapply Mem.valid_block_inject_2 in Hb1; eauto.
        + exploit H14; eauto. intros [X Y].
          destruct (j23 bi) as [[? ?] |] eqn: Hb2.
          exfalso. eapply Mem.valid_block_inject_1 in Hb2; eauto.
          exploit H23; eauto.
  - red. intros. unfold compose_meminj in H, H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H.
    + 
      destruct (j23 bi) as [[b2' d']|] eqn: Hj2; inv H2.
      apply H13 in Hj1 as Hj1'. rewrite Hj1' in H0.
      destruct (j23' bi) as [[b2'' d'']|] eqn: Hj2'; inv H0.
      exploit H24; eauto. intros A. erewrite inject_tid; eauto.
      erewrite inject_block_tid. 3: eauto. eauto. eauto.
    + destruct (j12' b1) as [[bi d]|] eqn: Hj1'; inv H0.
      destruct (j23' bi) as [[b2' d'']|] eqn: Hj2'; inv H1.
      exploit H15; eauto. 
  - red. intros. unfold compose_meminj in H. rename b2 into b3.
    destruct (j12 b1) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j23 b2) as [[b3' d2]|] eqn:Hj23; try congruence. inv H.
    red in H16. specialize (H16 _ _ _ _ Hj12 H0 H1 H2) as Hp2'.
    eapply Mem.perm_inject in H1 as Hp2. 3: eauto. 2: eauto.
    red in H25. inv Hm12. inv mi_thread. inv Hms. rewrite H3 in H0.
    red in Hjs. erewrite Hjs in H0; eauto.
    specialize (H25 _ _ _ _ Hj23 H0 Hp2 Hp2') as Hp3.
    rewrite Z.add_assoc. auto.
Qed.

Definition match_12_cctrans : injp_world * injp_world -> injp_world -> Prop :=
  fun w2 w =>
    match_injp_comp_world w2 w /\ external_mid_hidden (fst w2) (snd w2).

(** Problem : Although the "thread-external" blocks in [m2] is perfectly public from construction.
    It may be changed during the internal execution.

    [b1]                                         [xx] <- freed
     w1                                           w1'
    [b2] -----------------ACCI--------------->   [b2]
     w2                                           w2'
    [b3]                                         [b3]
   
    After internal execution, the [Hconstr2] may be destoryed. Why?
    
    When the block [b] is deliverd to external, and back to internal again.
    It is possible for the internal executions to change the values of [b3] because 
    it is now public in second [w2'] but private in the composed world. 

    Which breaks the ACCI: 
    For values, there is a case such that the value in [b2] is Vundef but [b3] = Vint 1.
    Then L2 does sth like [b++;], therefore Vundef -> Vundef. Vint 1 -> Vint 2. 
    It is possbie according to the definition of ACCI.
    
    But the point here is: "How can L2 opearates on [b2]?" It is a private external block.
    Since L2 cannot even see [b2], the values of its corresponding block in [b3] should
    not change either. 
    In other words, The simulation L1 <= L2 indicates that [b2] is not changed via ACCI.
    But such unchanged property cannot be transfer to [b3] vid L2 <= L3.

    Now the solution is we add [free_preserved] in ACCI, which requires that [b2] is freed
    if its inverse image [b1] is freed. 
    Therefore we can ensure that an [out_of_reach] position in m2 is not only "unchanged",
    but also *inaccessible*. 
    Therefore we do not have to worry the change of values in [b3] because it is also 
    [out_of_reach] now in [w2'].

    *)
Lemma external_mid_hidden_acci: forall j12 j23 m1 m2 m3 Hm12 Hm23 j12' j23' m1' m2' m3' Hm12' Hm23',
    let w1 := injpw j12 m1 m2 Hm12 in
    let w2 := injpw j23 m2 m3 Hm23 in
    let w1' := injpw j12' m1' m2' Hm12' in
    let w2' := injpw j23' m2' m3' Hm23' in
    external_mid_hidden w1 w2 ->
    injp_acci w1 w1' -> injp_acci w2 w2' ->
    external_mid_hidden w1' w2'.
Proof.
  intros. inv H. inv H0. inv H1.
  econstructor; eauto.
  - intros. red in Hnb0. destruct (j12 b1) as [[b2' d']|] eqn:Hj12.
    + apply H13 in Hj12 as Heq. rewrite H0 in Heq. inv Heq.
      destruct (j23 b2') as [[b3 d'']|] eqn:Hj23.
      * apply H22 in Hj23. congruence.
      * exploit Hconstr1; eauto. inv H12. destruct unchanged_on_thread_i. congruence.
    + exploit H14; eauto. erewrite inject_val_tid. 3: eauto. 2: eauto.
      erewrite inject_tid. 2: eauto. inversion H12. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb0; eauto. eapply Mem.valid_block_inject_2; eauto.
      intro. apply H. destruct H20 as [[_ Z] _]. congruence.
  - intros. red in Hnb3. destruct (j23 b2) as [[b3' d']|] eqn:Hj23.
    + apply H22 in Hj23 as Heq. rewrite H1 in Heq. inv Heq.
      destruct (Mem.loc_in_reach_find m1 j12 b2 ofs2) as [[b1 ofs1]|] eqn:FIND12.
      * eapply Mem.loc_in_reach_find_valid in FIND12; eauto. destruct FIND12 as [Hj12 Hpm1].
        exists b1, ofs1. split. edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_]. congruence.
        replace (ofs1 + (ofs2 - ofs1)) with ofs2 by lia.
        auto. auto.
      * eapply Mem.loc_in_reach_find_none in FIND12; eauto. destruct H12 as [[X Y]Z].
        exploit Hconstr2; eauto. congruence. inv Z.
        eapply unchanged_on_perm; eauto. red. split; auto. congruence. eapply Mem.valid_block_inject_1; eauto.
        intros (b1 & ofs1 & Hpm1 & Hj12). exists b1, ofs1. split.
        edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_]. congruence.
        replace (ofs1 + (ofs2 - ofs1)) with ofs2 by lia. auto. auto.
    + exploit H23; eauto. inversion H12. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb3; eauto. eapply Mem.valid_block_inject_2; eauto.
      erewrite inject_other_thread in H. 3: eauto. 2: eauto. intro.
      apply H.
      destruct H21 as [[_ Z]_]. congruence.
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
  econstructor; eauto. rewrite Valuesrel.add_repr.
  rewrite Ptrofs.add_assoc. auto.
  exists Vundef. split; constructor.
Qed.

Lemma cctrans_injp_comp : cctrans (cc_compose c_injp c_injp) (c_injp).
Proof.
  constructor. econstructor. instantiate (1:= match_12_cctrans).
  - (*incoming construction*)
    red. intros. inv H0. inv H3. simpl in H2, H1.
    inv H.
    exists (se1, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm),
              injpw f m1 m2 Hm)).
    repeat apply conj; eauto.
    + simpl. split. constructor; eauto. eapply match_stbls_dom; eauto. constructor; simpl; eauto.
    + exists (cq vf1 sg vargs1 m1). split.
      econstructor; simpl; eauto. eapply val_inject_dom; eauto.
      eapply val_inject_list_dom; eauto.
      econstructor; eauto. simpl. econstructor; eauto.
    + econstructor. rewrite meminj_dom_compose. reflexivity.
    + econstructor; eauto. intros. unfold meminj_dom in H0.
      destruct (f b1) as [[? ?]|] eqn: Hf; inv H0. congruence.
      intros. exists b2, ofs2. split. auto. unfold meminj_dom. rewrite H3.
      replace (ofs2 - ofs2) with 0 by lia. reflexivity.
    + intros r1 r3 wp1 wp2 wp1' Hmatch [Hae1 Hae2] HACCI Hr. simpl in Hae1, Hae2.
      destruct wp1' as [wp11' wp12']. simpl. simpl in *.
      destruct wp1 as [wp11 wp12]. simpl in *. destruct HACCI as [HAci1 HAci2].
      simpl in *. destruct wp11' as [j12 m1' m2' Hm1']. destruct wp12' as [j23 m2'_ m3' Hm2'].
      destruct Hr as [r2 [Hr1 Hr2]].
      inv Hr1. inv Hr2. simpl in *. inv H0. inv H11. rename m1'0 into m1'.
      rename m2'0 into m2'. rename m2'1 into m3'.
      exists (injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm1' Hm2')).
      repeat apply conj; eauto.
      -- eapply injp_comp_acce. 3: apply Hae1. 3:apply Hae2.
         econstructor; eauto.
         econstructor; eauto.
      -- inv Hmatch. eapply injp_comp_acci; eauto. econstructor; eauto.
      -- econstructor; simpl; eauto. eapply val_inject_compose; eauto.
  - (* outgoing construction *)
    red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [x [w11 w12]].
    inv HACI. simpl in H1,H2. 
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    assert (m2'_ = m2').
    { destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2. simpl in *. inv H5. inv H14.
      reflexivity. }
    subst m2'_.
    exists (injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23') ).
    repeat apply conj; eauto.
    + simpl. inv H; simpl in *.
      eapply injp_comp_acci; eauto.
      econstructor; eauto.
      econstructor; eauto.
    + inv Hs. inv H3. inv H4. econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2.
      inv H5. inv H14. simpl in *.
      econstructor; simpl; eauto. eapply val_inject_compose; eauto.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    + (** The accessbility construction : use acco*)
      intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. inv MR. simpl in H3,H4.
      destruct wp2' as [j13'' m1'' m3'' Hm13'].
      simpl in H3, H4.
      assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j23' m2' m3' Hm23')).
      destruct wp1. destruct w, w0.      inv H0.
      exploit external_mid_hidden_acci; eauto. econstructor; eauto.
      exploit injp_acce_outgoing_constr; eauto.
      intros (j12'' & j23'' & m2'' & Hm12'' & Hm23'' & COMPOSE & ACCE1 & ACCE2 & HIDDEN & _).
      exists ((injpw j12'' m1'' m2'' Hm12''),(injpw j23'' m2'' m3'' Hm23'')).
      repeat apply conj; eauto.
      -- inv H4.
         rename vres2 into vres3. exploit compose_meminj_midvalue; eauto.
         intros [vres2 [RES1 RES2]]. 
         exists (cr vres2 m2''). repeat econstructor; eauto.
      -- econstructor; eauto.
Qed.
                                                                                                               
Theorem injp_pass_compose: forall (L1 L2 L3: semantics li_c li_c),
    forward_simulation c_injp L1 L2 ->
    forward_simulation c_injp L2 L3 ->
    forward_simulation c_injp L1 L3.
Proof.
  intros.
  assert (forward_simulation (cc_compose c_injp c_injp) L1 L3).
  eapply st_fsim_vcomp; eauto.
  eapply open_fsim_cctrans; eauto.
  apply cctrans_injp_comp.
Qed.

(** * Compose  c_ext @ c_ext into c_ext *)

Inductive ext_comp_match : (ext_world * ext_world) -> ext_world -> Prop :=
|ext_comp_match_intro m1 m2 m3 Hm12 Hm23 Hm13:
  ext_comp_match ((extw m1 m2 Hm12), (extw m2 m3 Hm23)) (extw m1 m3 Hm13).

Lemma cctrans_ext_comp : cctrans (cc_compose c_ext c_ext) c_ext.
Proof.
  constructor.
  econstructor. instantiate (1:= ext_comp_match).
  - red. intros. inv H.  inv H0. simpl in H, H1, H2. inv H2. clear Hm Hm1. rename Hm0 into Hm12.
    assert (Hm11: Mem.extends m1 m1). apply Mem.extends_refl.
    exists (se2, ((extw m1 m1 (Hm11)),(extw m1 m2 Hm12))).
    intuition auto. econstructor; eauto. reflexivity. reflexivity.
    exists (cq vf1 sg vargs1 m1). split.
    econstructor; eauto. reflexivity. simpl.
    generalize dependent vargs1.
    induction 1. constructor. constructor; eauto. reflexivity.
    constructor.
    econstructor; eauto. constructor.
    constructor.
    destruct wp1' as [[m1' m2' Hm12'] [m2'' m3' Hm23']].
    destruct H5 as [r1' [Hr1 Hr2]]. inv Hr1. inv Hr2. simpl in *. inv H6. inv H11.
    rename m2'1 into m3'. rename m2'0 into m2'. rename m1'0 into m1'.
    assert (Hm13' : Mem.extends m1' m3'). 
    eapply Mem.extends_extends_compose; eauto. inv H0.
    destruct H4 as [ACI1 ACI2]. simpl in ACI1, ACI2.
    destruct H2 as [ACE1 ACE2]. simpl in ACE1, ACE2.
    exists (extw m1' m3' Hm13'). intuition auto.
    {
      clear - ACE1 ACE2. inv ACE1. inv ACE2. constructor; eauto.
    }
    {
      clear - ACI1 ACI2. rename m0 into m1. rename m3 into m2. rename m4 into m3.
      inv ACI1. inv ACI2. constructor; eauto.
      red. intros. eapply FREEP0. inv Hm0. congruence.
      eapply Mem.perm_extends; eauto. eapply FREEP; eauto.
    }
    econstructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    constructor.
  - red. intros. destruct w1 as [se' [w11 w12]]. inv H. inv H3. inv H4. inv H2.
    inv H0. inv H. inv H0. inv H2. inv H4. inv H12.
    simpl in H9, H11, H , H3.  rename m0 into m1'. rename m4 into m2'. rename m6 into m3'.
    assert (Hm13' : Mem.extends m1' m3'). 
    eapply Mem.extends_extends_compose; eauto. 
    exists (extw m1' m3' Hm13'). intuition auto. 
    {
      destruct H1 as [ACI1 ACI2]. simpl in ACI1, ACI2. inv ACI1. inv ACI2.
      constructor; eauto.
      red. intros. eapply FREEP0. inv Hm0. congruence.
      eapply Mem.perm_extends; eauto. eapply FREEP; eauto.
    }
    constructor.
    constructor; simpl; eauto.
    eapply val_inject_id. eapply Val.lessdef_trans; eapply val_inject_id; eauto.
    eapply CallConv.val_inject_lessdef_list_compose. eauto.
    eapply (ext_lessdef_list (extw m2' m3' Hm3)). eauto. constructor.
    destruct wp2' as [m1'' m3'' Hm13''].
    assert (Hm12' : Mem.extends m1'' m1''). apply Mem.extends_refl.
    exists (extw m1'' m1'' Hm12', extw m1'' m3'' Hm13''). split; simpl; eauto.
    split. simpl.
    inv H0. constructor; eauto; try (erewrite <- Mem.mext_sup; eauto).
    red. intros. eapply Mem.perm_extends; eauto. apply MPD1; eauto.
    erewrite Mem.valid_block_extends; eauto.
    simpl. inv H0. constructor; eauto; try (erewrite <- Mem.mext_sup; eauto).
    red. intros. eapply Mem.perm_extends; eauto. apply MPD1; eauto.
    erewrite Mem.valid_block_extends; eauto. split.
    exists r1. inv H2. inv H6. simpl in *.
    split.
    econstructor; simpl; eauto. eapply val_inject_id.
    eapply Val.lessdef_refl. constructor.
    econstructor; eauto. constructor. constructor.
Qed.

(*  {|
    ccworld := unit;
    ccworld_world := world_unit;
    match_senv w := eq;
    match_query w := cc_c_query ext w;
    match_reply w := cc_c_reply ext w;
  |}.
 *)

(** * Compose c_injp @ c_ext @ c_injp into c_injp *)
Require Import InjpExtAccoComp.

Inductive match_injp_ext_comp_world : injp_world -> ext_world -> injp_world -> injp_world -> Prop :=
|world_ext_comp_intro:
  forall m1 m2 m3 m4 j12 j34 j14 Hm12 Hm23 Hm34 Hm14,
    j14 = compose_meminj j12 j34 ->
    match_injp_ext_comp_world (injpw j12 m1 m2 Hm12) (extw m2 m3 Hm23) (injpw j34 m3 m4 Hm34) (injpw j14 m1 m4 Hm14).

Definition injp_ext_cctrans : injp_world * (ext_world * injp_world) -> injp_world -> Prop :=
  fun wjxj w =>
    let w1 := fst wjxj in let w2 := fst (snd wjxj) in let w3 := snd (snd wjxj) in
    match_injp_ext_comp_world w1 w2 w3 w /\ external_mid_hidden_ext w1 w3.

Inductive injp_trivial_comp_world_ext : injp_world -> ext_world -> injp_world -> injp_world -> Prop :=
  trivial_comp_ext_intro :
    forall (j : meminj) (m1 m3 : mem) (Hm12 : Mem.inject (meminj_dom j) m1 m1)
      (Hm34 Hm14 : Mem.inject j m1 m3) Hm23,
      injp_trivial_comp_world_ext (injpw (meminj_dom j) m1 m1 Hm12) (extw m1 m1 Hm23) (injpw j m1 m3 Hm34)
        (injpw j m1 m3 Hm14).
                           
Lemma injp_ext_comp_acce : forall w11 w12 w13 w11' w12' w13' w1 w2,
    injp_trivial_comp_world_ext w11 w12 w13 w1 ->
    match_injp_ext_comp_world w11' w12' w13' w2 ->
    injp_acce w11 w11' -> injp_acce w13 w13' ->
    injp_acce w1 w2.
Proof.
  intros. inv H. inv H0. rename Hm34 into Hm34'.
  rename Hm23 into Hm34. rename m4 into m3'. rename m5 into m4'.
  rename m3 into m4. rename m0 into m1'. rename m2 into m2'.
  inv H1. inv H2.
  econstructor; eauto.
  - destruct H11. split. auto. eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split; auto. red. unfold meminj_dom.
    rewrite H. reflexivity.
  - assert (j = compose_meminj (meminj_dom j) j).
    rewrite meminj_dom_compose. reflexivity.
    rewrite H. rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
    destruct (j12 b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j34 bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    exploit H14; eauto. unfold meminj_dom. rewrite Hb. reflexivity.
    intros [X Y].
    destruct (j bi) as [[? ?] | ] eqn:Hfbi.
    {
      eapply Mem.valid_block_inject_1 in Hfbi; eauto.
    }
    edestruct H22; eauto. erewrite <- inject_tid; eauto.
    inv Hm0. inv mi_thread. erewrite <- Hjs; eauto.
  - red. intros. unfold compose_meminj in H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H0.
    destruct (j34 bi) as [[b2' d']|] eqn: Hj2; inv H2.
    exploit H15; eauto. unfold meminj_dom. rewrite H. reflexivity.
    intros [A B]. split; auto.
    intro. apply B. red. erewrite inject_block_tid; eauto.
Qed.

Lemma injp_ext_comp_acci : forall w11 w12 w13 w11' w12' w13' w1 w2,
    match_injp_ext_comp_world w11 w12 w13 w1 ->
    external_mid_hidden_ext w11 w13 ->
    match_injp_ext_comp_world w11' w12' w13' w2 ->
    injp_acci w11 w11' -> injp_acci w13 w13' ->
    ext_acci  w12 w12' ->
    injp_acci w1 w2.
Proof.
  intros. inv H. inv H1. inv H0.
  rename j0 into j12'. rename j1 into j34'.
  rename m0 into m1'. rename m7 into m4'.
  rename m6 into m3'. rename m5 into m2'.
  inv H2. inv H3.
  constructor; eauto.
  - destruct H12 as [S12 H12]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. red in X. unfold compose_meminj in X.
    destruct (j12 b) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j34 b2) as [[b3 d2]|] eqn:Hj23; try congruence.
    eapply Hconstr1 in Hj12; eauto. congruence.
    erewrite <- inject_other_thread; eauto.
  - destruct H22 as [S22 H22]. split. auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H as [X Y]. split; auto.
    red. intros. red in X. intro.
    exploit Hconstr2; eauto. erewrite inject_other_thread; eauto.
    intros (Hp2 & b1 & ofs1 & Hp1 & Hj12).
    exploit X. unfold compose_meminj. rewrite Hj12, H. reflexivity.
    replace (ofs - (ofs - delta - ofs1 + delta)) with ofs1 by lia. auto.
    auto.
  - rauto.
  - red.
    intros b1 b2 delta Hb Hb' Ht. unfold compose_meminj in Hb'.
    destruct (j12' b1) as [[bi delta12] | ] eqn:Hb1'; try discriminate.
    destruct (j34' bi) as [[xb2 delta23] | ] eqn:Hb2'; try discriminate.
    inv Hb'.
    destruct (j12 b1) as [[? ?] | ] eqn:Hb1.
    + apply H14 in Hb1 as Heq. rewrite Hb1' in Heq. inv Heq.
      destruct (j34 b) as [[? ?] |] eqn: Hb2.
      unfold compose_meminj in Hb. rewrite Hb1, Hb2 in Hb. congruence.
      exfalso. exploit H24; eauto.
      erewrite <- Mem.mext_sup; eauto.
      erewrite <- inject_tid; eauto.
      erewrite <- inject_val_tid. 3: eauto. auto. eauto.
      intros [X Y]. apply X.
      erewrite <- Mem.valid_block_extends; eauto.
      eapply Mem.valid_block_inject_2 in Hb1; eauto.
    + exploit H15; eauto. intros [X Y].
      destruct (j34 bi) as [[? ?] |] eqn: Hb2.
      exfalso. eapply Mem.valid_block_inject_1 in Hb2; eauto.
      exploit H24; eauto.
  - red. intros. unfold compose_meminj in H, H0.
    destruct (j12 b1) as [[bi d]|] eqn: Hj1; inv H.
    + 
      destruct (j34 bi) as [[b2' d']|] eqn: Hj2; inv H2.
      apply H14 in Hj1 as Hj1'. rewrite Hj1' in H0.
      destruct (j34' bi) as [[b2'' d'']|] eqn: Hj2'; inv H0.
      exploit H25; eauto. intros A. erewrite inject_tid; eauto.
      erewrite inject_block_tid. 3: eauto. 2: eauto.
      erewrite Mem.mext_sup; eauto.
    + destruct (j12' b1) as [[bi d]|] eqn: Hj1'; inv H0.
      destruct (j34' bi) as [[b2' d'']|] eqn: Hj2'; inv H1.
      exploit H16; eauto. 
  - red. intros. unfold compose_meminj in H. rename b2 into b3.
    destruct (j12 b1) as [[b2 d]|] eqn: Hj12; try congruence.
    destruct (j34 b2) as [[b3' d2]|] eqn:Hj23; try congruence. inv H.
    red in H17. specialize (H17 _ _ _ _ Hj12 H0 H1 H2) as Hp2'.
    eapply Mem.perm_inject in H1 as Hp2. 3: eauto. 2: eauto.
    red in H26. assert (H0': fst b2 <> Mem.tid (Mem.support m3)).
    erewrite <- inject_block_tid. 3: eauto. 2: eauto.
    erewrite <- Mem.mext_sup. 2: eauto.
    erewrite <- inject_tid; eauto.
    assert (Hp3' : ~ Mem.perm m3' b2 (ofs1 + d) Max Nonempty).
    inv H4. eapply FREEP. 4: eauto. all: eauto.
    erewrite Mem.mext_sup; eauto.
    eapply Mem.perm_extends in Hm23 as Hp3; eauto.
    specialize (H26 _ _ _ _ Hj23 H0' Hp3 Hp3') as Hp4.
    rewrite Z.add_assoc. auto.
Qed.


Lemma external_mid_hidden_ext_acci: forall j12 j34 m1 m2 m3 m4 Hm12 Hm34 j12' j34' m1' m2' m3' m4' Hm12' Hm34',
    let w1 := injpw j12 m1 m2 Hm12 in
    let w2 := injpw j34 m3 m4 Hm34 in
    let w1' := injpw j12' m1' m2' Hm12' in
    let w2' := injpw j34' m3' m4' Hm34' in
    external_mid_hidden_ext w1 w2 ->
    injp_acci w1 w1' -> injp_acci w2 w2' ->
    Mem.extends m2 m3 -> Mem.extends m2' m3' ->
    free_preserved_ext m2 m2' m3' ->
    external_mid_hidden_ext w1' w2'.
Proof.
  intros until w2'. intros H H0 H1 He1 He2 Hacie. inv H. inv H0. inv H1.
  econstructor; eauto.
  - intros. red in Hnb0. destruct (j12 b1) as [[b2' d']|] eqn:Hj12.
    + apply H13 in Hj12 as Heq. rewrite H0 in Heq. inv Heq.
      destruct (j34 b2') as [[b3 d'']|] eqn:Hj23.
      * apply H22 in Hj23. congruence.
      * exploit Hconstr1; eauto. inv H12. destruct unchanged_on_thread_i. congruence.
    + exploit H14; eauto. erewrite inject_val_tid. 3: eauto. 2: eauto.
      erewrite inject_tid. 2: eauto. inversion H12. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb0; eauto. rewrite <- Mem.valid_block_extends; eauto.
      rewrite <- Mem.valid_block_extends; eauto.
      eapply Mem.valid_block_inject_2; eauto.
      intro. apply H. destruct H20 as [[_ Z] _].
      erewrite Mem.mext_sup. 2: eauto.
      congruence.
  - intros. red in Hnb3.
    destruct (j34 b3) as [[b4' d']|] eqn:Hj23.
    + apply H22 in Hj23 as Heq. rewrite H1 in Heq. inv Heq.
      exploit H18; eauto. eapply inject_implies_dom_in; eauto.
      intro Hp3.
      assert (Hp2': Mem.perm m2' b3 ofs3 Max Nonempty).
      {
        destruct (Mem.perm_dec m2' b3 ofs3 Max Nonempty). auto.
        destruct H20 as [[_ XX]_]. 
        exploit Hconstr2; eauto. congruence. intros [Hp2 YY].
        exfalso. eapply Hacie; eauto. erewrite Mem.mext_sup. 2: eauto.
        congruence.
      }
      split. auto.
      destruct (Mem.loc_in_reach_find m1 j12 b3 ofs3) as [[b1 ofs1]|] eqn:FIND12.
      * eapply Mem.loc_in_reach_find_valid in FIND12; eauto. destruct FIND12 as [Hj12 Hpm1].
        exists b1, ofs1. split. edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_].
        erewrite Mem.mext_sup. 2: eauto.
        congruence.
        (* replace (ofs1 + (ofs3 - ofs1)) with ofs3 by lia. 2: auto. *)
        red in Hacie. destruct (Mem.perm_dec m2' b3 (ofs1 + (ofs3 - ofs1)) Max Nonempty).
        auto. exfalso. eapply Hacie; eauto.
        erewrite Mem.mext_sup. 2: eauto.
        destruct H20. inv unchanged_on_thread_i. congruence.
        eapply Mem.perm_inject; eauto.
        replace (ofs1 + (ofs3 - ofs1)) with ofs3 by lia. 2: auto. auto.
      * eapply Mem.loc_in_reach_find_none in FIND12; eauto. destruct H12 as [[X Y]Z].
        exploit Hconstr2; eauto. destruct H20 as [[XX ?]?].
        congruence.
        intros (Hp2 & b1 & ofs1 & Hpm1 & Hj12). exists b1, ofs1. split.
        edestruct Mem.perm_dec; eauto. exfalso.
        eapply H16; eauto.
        erewrite inject_other_thread. 2: eauto. 2: eauto. destruct H20 as [[_ TID]_].
        erewrite Mem.mext_sup. 2: eauto. congruence.
        replace (ofs1 + (ofs3 - ofs1)) with ofs3 by lia. auto. auto.
    + exploit H23; eauto. inversion H20. inv unchanged_on_thread_i. congruence.
      intros [A B].
      exfalso. exploit Hnb3; eauto. eapply Mem.valid_block_inject_2; eauto.
      erewrite inject_other_thread in H. 3: eauto. 2: eauto. intro.
      apply H.
      destruct H21 as [[_ Z]_]. congruence.
Qed.


Lemma cctrans_injp_ext:
  cctrans (c_injp @ c_ext @ c_injp) c_injp.
Proof.
  constructor. econstructor. instantiate (1:= injp_ext_cctrans).
  (* Compute (GS.gworld (c_injp @ c_ext @ c_injp)). *)
  - red. intros w2 se1 se2 q1 q2 Hse Hq. inv Hse. inv Hq.
    inv H4. clear Hm1 Hm2 Hm3. simpl in H2, H3.
    rename m0 into m1. rename m3 into m2.
    (* Compute (GS.ccworld (c_injp @ c_ext @ c_injp)). *)
    exists (se1,((injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm)),(se1,(extw m1 m1 (Mem.extends_refl m1),(injpw f m1 m2 Hm))))).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. eapply match_stbls_dom; eauto.
      constructor. constructor. constructor; eauto.
    + exists (cq vf1 sg vargs1 m1). split. constructor; simpl; eauto.
      eapply val_inject_dom; eauto. eapply val_inject_list_dom; eauto.
      exists (cq vf1 sg vargs1 m1). split. constructor; simpl; eauto.
      reflexivity. generalize dependent vargs1.
      induction 1. constructor. constructor. reflexivity. auto. constructor.
      econstructor; eauto. constructor.
    + constructor. rewrite meminj_dom_compose. auto.
    + constructor. intros. unfold meminj_dom in H6.
      destr_in H6.
      intros. split. auto. eexists. eexists. split. eauto.
      unfold meminj_dom. rewrite H7. do 2 f_equal. lia.
    + intros r1 r4 [wpa [wpe wpb]] wp2 [wpa' [wpe' wpb']] MS.
      intros [ACE1 [X ACE2]] [ACI1 [ACI2 ACI3]] [r2 [Hr1 [r3 [Hr2 Hr3]]]].
      simpl in *. clear X.
      destruct wpa' as [j12 m1' m2' Hm1']. destruct wpb' as [j23 m2'_ m3' Hm2'].
      inv Hr1. inv Hr2. inv Hr3. simpl in *. inv H6. inv H13. inv H11.
      clear Hm1 Hm2 Hm3 Hm4 Hm5 Hm6. rename m1'0 into m1'.
      rename m2'0 into m2'. rename m2'1 into m3'. rename m2'2 into m4'.
      assert (Hm': Mem.inject (compose_meminj j12 j23) m1' m4').
      eapply Mem.inject_compose. eauto.
      eapply Mem.extends_inject_compose. eauto. eauto.
      exists (injpw (compose_meminj j12 j23) m1' m4' Hm').
      repeat apply conj.
      * 
        eapply injp_ext_comp_acce.
        instantiate (2:= extw m1 m1 (Mem.extends_refl m1)). econstructor; eauto.
        instantiate (2:= extw m2' m3' Hm0). econstructor; eauto. eauto. eauto.
      * inv MS. simpl in *.
        eapply injp_ext_comp_acci. 4: apply ACI1. 4: apply ACI3. 4: apply ACI2.
        eauto. eauto. constructor; eauto.
      * econstructor; simpl; eauto.
        eapply val_inject_compose. eauto.
        rewrite <- (compose_meminj_id_left j23).
        eapply val_inject_compose. eauto. eauto.
  - red. intros [wpa [wpe wpb]] wp2 [se2 [w1 [se2' [we w2]]]].
    intros se1 se3 q1 q3 [Hs1 [Hs2 Hs3]] [q2 [Hq1 [q2' [Hq2 Hq3]]]].
    intros [ACI1 [ACI2 ACI3]]. simpl in ACI1, ACI2, ACI3. 
    intros MS. inv MS. simpl in H, H0.
    destruct w1 as [j12' m1' m2' Hm12'].
    destruct w2 as [j34' m3' m4' Hm34'].
    inv H.
    assert (Hm14' : Mem.inject (compose_meminj j12' j34') m1' m4').
    eapply Mem.inject_compose; eauto. eapply Mem.extends_inject_compose; eauto.
    inv Hq1. inv Hq2. inv Hq3. inv H2. inv H15. inv H11. auto.
    exists (injpw (compose_meminj j12' j34') m1' m4' Hm14').
    repeat apply conj.
    + simpl. eapply injp_ext_comp_acci; eauto.
      constructor; eauto. inv Hq1. inv Hq2. inv Hq3.
      inv H2. inv H11. inv H15.
      econstructor; eauto.
    + inv Hs1. inv Hs2. inv Hs3.
      constructor; eauto. eapply Genv.match_stbls_compose; eauto.
    + inv Hq1. inv H2. inv Hq2. inv Hq3. inv H14.
      econstructor; simpl; eauto. eapply val_inject_compose. eauto.
      rewrite <- (compose_meminj_id_left j34').
      eapply val_inject_compose. eauto. eauto.
      eapply CKLRAlgebra.val_inject_list_compose. econstructor.
      split. eauto. rewrite <- (compose_meminj_id_left j34').
      simpl in H10.
      eapply CKLRAlgebra.val_inject_list_compose; eauto.
    +  intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. inv MR. simpl in H,H1.
       destruct wp2' as [j13'' m1'' m3'' Hm13'].
       simpl in H, H1. inv H1.
       assert (Hm23' : Mem.extends m2' m3').
       inv Hq1. inv Hq2. inv Hq3. inv H3. inv H12. inv H16. auto.       
       assert (Hhidden: external_mid_hidden_ext (injpw j12' m1' m2' Hm12') (injpw j34' m3' m4' Hm34')).
       eapply external_mid_hidden_ext_acci; eauto. inv ACI2. inv Hq1. inv Hq2. inv Hq3.
       inv H3. inv H12. inv H16. auto.
       exploit injp_acce_ext_outgoing_constr; eauto.
       intros (j12'' & j34'' & m2'' & m3'' & Hm12'' & Hm34'' & COMPOSE & MEXT'' & ACCE1 & ACCE2 & HIDDEN & _).
       rename m1'0 into m1''. rename m2'0 into m4''.
      exists ((injpw j12'' m1'' m2'' Hm12''),(extw m2'' m3'' MEXT'', injpw j34'' m3'' m4'' Hm34'')).
      repeat apply conj; eauto.
       -- simpl. inv ACCE1. inv ACCE2. inv Hq1. inv Hq2. inv Hq3. inv H3. inv H30. inv H34.
          econstructor; eauto. apply H12. apply H20. apply H12. apply H20.
      -- rewrite COMPOSE in H.
         rename vres2 into vres4. exploit compose_meminj_midvalue; eauto.
         intros [vres2 [RES1 RES2]].
         exists (cr vres2 m2''). split. repeat econstructor; eauto.
         exists (cr vres2 m3''). repeat econstructor; eauto.
         simpl. reflexivity.
      -- econstructor; eauto.
Qed.
