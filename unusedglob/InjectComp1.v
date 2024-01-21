Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.
Require Import InjectFootprint.

Require Import Callconv.

Section CONSTR_PROOF.
  Variable m1 m2 m3 m1' m3': mem.
  Variable j1 j2 j1' j2': meminj.
  Variable gs1 gs2 gs3: sup.
  Variable se1 se2 se3: Genv.symtbl.
  Variable s2': sup.
  Hypothesis ROUNC1: Mem.ro_unchanged m1 m1'.
  Hypothesis ROUNC3: Mem.ro_unchanged m3 m3'.
  Hypothesis DOMIN1: inject_dom_in j1 (Mem.support m1).
  Hypothesis DOMIN1': inject_dom_in j1' (Mem.support m1').
  Hypothesis UNCHANGE1: Mem.unchanged_on (fun b ofs => loc_unmapped (compose_meminj j1 j2) b ofs /\ ~ sup_In b gs1) m1 m1'.
  Hypothesis UNCHANGE3: Mem.unchanged_on (fun b ofs => loc_out_of_reach (compose_meminj j1 j2) m1 b ofs /\ ~ sup_In b gs3) m3 m3'.
  Hypothesis INJ12 Hm1: Mem.inject j1 m1 m2.
  Hypothesis INJ23 Hm2: Mem.inject j2 m2 m3.
  Hypothesis MSTBL12: injp_match_stbls' (injpw j1 gs1 gs2 m1 m2 Hm1) se1 se2.
  Hypothesis MSTBL23 : injp_match_stbls (injpw j2 gs2 gs3 m2 m3 Hm2) se2 se3.
  Hypothesis INJ13': Mem.inject (compose_meminj j1' j2') m1' m3'.
  Hypothesis SUPINCL2 : Mem.sup_include (Mem.support m2) s2'.
  Hypothesis SUPINCL3 : Mem.sup_include (Mem.support m3) (Mem.support m3').
  Hypothesis INCR1 : inject_incr j1 j1'.
  Hypothesis INCR2 : inject_incr j2 j2'.
  Hypothesis INCRDISJ1 :inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2).
  Hypothesis INCRDISJ2 :inject_incr_disjoint j2 j2' (Mem.support m2) (Mem.support m3).
  Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j1 j1'.
  Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'.
  Hypothesis IMGIN1': inject_image_in j1' s2'.
  Hypothesis DOMIN2': inject_dom_in j2' s2'.
  Hypothesis ADDZERO: update_add_zero j1 j1'.
  Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2').
  Hypothesis ADDSAME : update_add_same j2 j2' j1'.

  (** step2 of Definition C.7, defined in common/Memory.v as memory operation *)
  Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.
  (** step3 of Definition C.7, in common/Memory.v *)
  Definition m2'2 := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.
  (** step4 *)
  Definition m2' := Mem.set_empty_sup m1 j1 j2 gs2 m2'2.
  
  Lemma INJNOLAP1' : Mem.meminj_no_overlap j1' m1'.
  Proof. eapply update_meminj_no_overlap1; eauto. Qed.

  (** unchanged_on properties about m2' *)

  Lemma pmap_update_diff': forall (A:Type) b f (map: NMap.t A) b',
  b <> b' ->
  NMap.get b' (Mem.pmap_update b f map) = NMap.get b' map.
  Proof.
    intros. unfold Mem.pmap_update.
    rewrite NMap.gsspec. rewrite pred_dec_false; auto.
  Qed.

  Lemma supext_unchanged_on : forall s m m' P,
    Mem.supext s m = m' ->
    Mem.unchanged_on P m m'.
Proof.
  intros. unfold Mem.supext in H.
  destruct Mem.sup_include_dec in H.
  - constructor; inv H.
    + eauto.
    + intros. reflexivity.
    + intros. reflexivity.
  - subst. eauto with mem.
Qed.

  Lemma unchanged_on_map_block : forall m m' b,
      Mem.map_block m1 m1' j1' b m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    intros. subst.
    unfold Mem.map_block.
    destruct (j1' b) as [[b2 d]|] eqn:j1'b; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    destruct Mem.sup_dec; try eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl.
    erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
    intros. erewrite pmap_update_diff'. reflexivity.
    intro. subst. exploit INCRDISJ1; eauto.
    inversion INJ12. eauto. intros [A B]. apply B. eauto.
  Qed.

  Lemma unchanged_on_map_sup : forall s m m',
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m m'.
  Proof.
    induction s.
    - intros. inv H. simpl. eauto with mem.
    - intros. inv H. simpl.
      eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_map_block; eauto.
      eauto.
  Qed.

  Lemma unchanged_step2: Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m2 m2'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s2' m2). reflexivity.
    eapply unchanged_on_map_sup; eauto. reflexivity.
  Qed.
                                          
  Lemma unchanged1_step2: Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged2_step2: Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged_step2.
    intros. eauto.
  Qed.

  Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.

    Lemma unchanged_on_copy_block1 : forall m m' b,
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_access_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
          - intros. unfold Mem.perm. simpl.
      unfold Mem.pmap_update.
      rewrite NMap.gsspec.
      destruct (eq_block). subst.
      erewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1 o1]|] eqn:LOCIN.
      eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct LOCIN as [A B].
      red in H. exploit H; eauto. replace (ofs - (ofs - o1)) with o1 by lia.
      eauto. intro. inv H1. reflexivity. reflexivity.
  Qed.

  Lemma unchanged_on_copy'1 : forall s m m',
      Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block1; eauto.
      eauto.
  Qed.
  
  Lemma unchanged_on_copy'2 : forall s m m',
      Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block2; eauto.
      eauto.
  Qed.
  
  Lemma unchanged1_step3: Mem.unchanged_on (loc_out_of_reach j1 m1) m2'1 m2'2.
  Proof.
    unfold m2'2.
    eapply unchanged_on_copy'1; eauto.
  Qed.

  Lemma unchanged2_step3: Mem.unchanged_on (loc_unmapped j2) m2'1 m2'2.
  Proof.
    unfold m2'2.
    eapply unchanged_on_copy'2; eauto.
  Qed.

   Definition footprint_step4 (b2 : block) (ofs2 : Z) : Prop :=
     sup_In b2 gs2 /\ loc_out_of_reach j1 m1 b2 ofs2.

   Lemma unchanged_step4: Mem.unchanged_on (fun b ofs => ~ footprint_step4 b ofs) m2'2 m2'.
   Proof.
     eapply Mem.unchanged_on_implies.
     eapply unchanged_on_and.
     eapply unchanged_on_empty. reflexivity.
     eapply unchanged_on_empty_inreach. 2: reflexivity. eauto.
     intros. cbn.  unfold footprint_step4 in H.
     destruct (Mem.sup_dec b gs2). right.
     intro. apply H. split; eauto. left. eauto.
   Qed.

  Lemma freed_step4:  forall b2 o2 k p,
      j2 b2 <> None -> footprint_step4 b2 o2 -> ~ Mem.perm m2' b2 o2 k p.
  Proof.
     intros. destruct H0. eapply freed_sup; eauto. reflexivity.
  Qed.

  Lemma unchanged_content_step4 : forall b2 o2,
      mem_memval m2' b2 o2 = mem_memval m2'2 b2 o2.
  Proof.
    intros. eapply unchanged_content_empty; eauto. reflexivity.
  Qed.

  Lemma perm_decrease_step4: forall b2 o2 k p,
      Mem.perm m2' b2 o2 k p -> Mem.perm m2'2 b2 o2 k p.
  Proof.
    intros. eapply perm_decrease_empty; eauto.
  Qed.

  Lemma unchanged_step4_gs: Mem.unchanged_on (fun b _ => ~ sup_In b gs2) m2'2 m2'.
  Proof.
    unfold m2'.
    eapply unchanged_on_empty; eauto.
  Qed.

  (** Lemma C.8(1) *)

  Theorem UNCHANGE21': Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'2.
  Proof.
    eapply Mem.unchanged_on_trans.
    eapply unchanged1_step2.
    eapply unchanged1_step3.
  Qed.
  
  Theorem UNCHANGE21: Mem.unchanged_on (fun b ofs => loc_out_of_reach j1 m1 b ofs /\ ~ sup_In b gs2) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    (* step2 *)
    eapply Mem.unchanged_on_implies.
    eapply unchanged1_step2.
    intros. apply H.
    eapply Mem.unchanged_on_trans.
    (* step3 *)
    eapply Mem.unchanged_on_implies.
    eapply unchanged1_step3.
    intros. apply H.
    (* step4 *)
    eapply Mem.unchanged_on_implies.
    apply unchanged_step4_gs.
    intros. apply H.
  Qed.
   
  (** Lemma C.8(2) *)
  Theorem UNCHANGE22' : Mem.unchanged_on (loc_unmapped j2) m2 m2'2.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged2_step2.
    eapply unchanged2_step3.
  Qed.

  Theorem UNCHANGE22 : Mem.unchanged_on (fun b ofs => loc_unmapped j2 b ofs /\ ~ sup_In b gs2) m2 m2'.
  Proof.
        eapply Mem.unchanged_on_trans; eauto.
    (* step2 *)
    eapply Mem.unchanged_on_implies.
    eapply unchanged2_step2.
    intros. apply H.
    eapply Mem.unchanged_on_trans.
    (* step3 *)
    eapply Mem.unchanged_on_implies.
    eapply unchanged2_step3.
    intros. apply H.
    eapply Mem.unchanged_on_implies.
    apply unchanged_step4_gs.
    intros. apply H.
  Qed.
  
  (* Lemma unchanged_on_copy_block2 : forall m m' b,
      Mem.copy_block m1 m2 m3 m1' s2' j1 j2 j1' j2' INJ12 INJ23 b m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    intros. subst. unfold Mem.copy_block.
    destruct (j2 b) as [[b3 d]|] eqn: j2b; eauto with mem.
    destruct (Mem.sup_dec); eauto with mem.
    constructor; simpl. eauto with mem.
    intros. unfold Mem.perm. simpl. erewrite pmap_update_diff'. reflexivity.
    congruence.
    intros. rewrite pmap_update_diff'. reflexivity.
    congruence.
  Qed.
   *)

  Lemma m2'1_support : Mem.support m2'1 = s2'.
  Proof. unfold m2'1. erewrite Mem.step2_support; eauto. Qed.
  Lemma m2'2_support : Mem.support m2'2 = s2'.
  Proof. unfold m2'2. erewrite Mem.copy_sup_support; eauto. erewrite m2'1_support; eauto. Qed.
  Lemma m2'_support : Mem.support m2' = s2'.
  Proof. unfold m2'. erewrite Mem.set_empty_sup_support; eauto. apply m2'2_support. Qed.

  Lemma copy_block_perm1 : forall m b1 o1 b2 o2 k p,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Max Nonempty ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold Mem.perm. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_access_block_result.
      destruct Mem.loc_in_reach_find as [[b1' o1']|]eqn:FIND.
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1. reflexivity.
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia. auto.
      intro. inv H3. eauto.
    - exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.

  Lemma copy_block_perm2 : forall m b2 o2 b2' k p,
      b2 <> b2' ->
      Mem.perm (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. rewrite pmap_update_diff'; eauto. reflexivity.
  Qed.
  
  Lemma copy_sup_perm: forall s m b1 o1 b2 o2 k p,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    induction s; intros.
    - inv H2.
    - simpl. destruct H2.
      + subst a.
        eapply copy_block_perm1; eauto.
        erewrite Mem.copy_sup_support; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_perm1; eauto.
          erewrite Mem.copy_sup_support; eauto.
        * 
          exploit IHs; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_perm2; eauto.
  Qed.

  Lemma copy_perm: forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. etransitivity. instantiate (1:= Mem.perm m2'2 b2 o2 k p).
    symmetry.
    eapply Mem.unchanged_on_perm.
    apply unchanged_step4.
    red. intros [A B]. eapply B; eauto.
    replace (o2 - (o2 - o1)) with o1 by lia. eauto.
    unfold Mem.valid_block. rewrite m2'2_support.
    apply SUPINCL2.
    inv INJ12. eapply mi_mappedblocks; eauto.
    eapply copy_sup_perm; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_block_content : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
(*      Mem.perm m1 b1 o1 Max Writable ->
*)
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 =
          if (Mem.perm_dec m1 b1 o1 Max Writable) then
            Mem.memval_map j1' (mem_memval m1' b1 o1)
            else mem_memval m b2 o2.
  Proof.
    intros.
    assert (PERM1 : Mem.perm m1 b1 o1 Max Nonempty).
    {
      eapply MAXPERM1; eauto with mem.
      eapply DOMIN1; eauto.
    }
    unfold Mem.copy_block. destruct (j2 b2); try congruence.
    destruct Mem.sup_dec.
    - unfold mem_memval. simpl. unfold Mem.pmap_update.
      setoid_rewrite NMap.gss. rewrite Mem.copy_content_block_result; eauto.
      destruct Mem.loc_in_reach_find as [[b1' o1']|] eqn:FIND.
      + 
      apply Mem.loc_in_reach_find_valid in FIND. destruct FIND as [A B].
      (* generalize INJNOLAP1'. intro INJNOLAP1'. *)
      assert (b1 = b1').
      {
        destruct (eq_block b1 b1'). auto.
        inversion INJ12. exploit mi_no_overlap; eauto with mem.
        intros [C|D]. congruence. extlia.
      }
      assert (o1 = o1'). subst b1'. rewrite H in A.
      inv A. lia. subst b1 o1.
      destruct Mem.perm_dec; try congruence.
      destruct Mem.perm_dec; try congruence.
      +
      eapply Mem.loc_in_reach_find_none in FIND; eauto.
      red in FIND. exploit FIND; eauto. replace (o2 - (o2 - o1)) with o1 by lia.
      eauto with mem. intro X. inv X.
    - 
      exfalso. rewrite H2 in *. apply n. inversion INJ12.
      exploit mi_mappedblocks; eauto.
  Qed.
  
  Lemma copy_block_content1 : forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_true; eauto.
  Qed.

  Lemma copy_block_content3 : forall m b2 o2 b2',
      b2 <> b2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold mem_memval. simpl. rewrite pmap_update_diff'; eauto.
  Qed.

  Lemma copy_block_content2 :  forall m b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 b2 m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_false; eauto.
  Qed.
  
  Lemma copy_sup_content: forall s m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction s; intros.
    - inv H3.
    - simpl. destruct H3.
      + subst a.
        eapply copy_block_content1; eauto.
        erewrite Mem.copy_sup_support; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_content1; eauto.
          erewrite Mem.copy_sup_support; eauto.
        * 
          exploit IHs; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_content3; eauto.
  Qed.
  
  Lemma copy_sup_content_2: forall s m b1 o1 b2 o2,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        ~ Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m) b2 o2 = mem_memval m b2 o2.
  Proof.
    induction s; intros; cbn.
    - reflexivity.
    - destruct (eq_block a b2). subst a.
      erewrite copy_block_content2; eauto.
      erewrite Mem.copy_sup_support; eauto.
      erewrite copy_block_content3; eauto.
  Qed.

  Lemma copy_content : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    etransitivity.
    apply unchanged_content_step4.
    eapply copy_sup_content; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_content_2 : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable -> ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = mem_memval m2 b2 o2.
  Proof.
    intros. transitivity (mem_memval m2'2 b2 o2).
    apply unchanged_content_step4.
    etransitivity.
    unfold m2'2. eapply copy_sup_content_2; eauto.
    apply m2'1_support.
    apply Mem.ro_unchanged_memval_bytes in ROUNC1.
    exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
    intros [P1 X].
    generalize unchanged_step2. intro U.
    inv U. eapply unchanged_on_contents.
    eapply Mem.valid_block_inject_2; eauto.
    replace o2 with (o1 + (o2 - o1)) by lia.
    eapply Mem.perm_inject; eauto.
  Qed.

  Lemma copy_content_inject : forall b1 o1 b2 o2,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1' b1 o1 Cur Readable ->
          Mem.perm m1 b1 o1 Max Writable ->
          ~ (j2 b2 = None) ->
          memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite copy_content; eauto.
    apply INCR1 in H as MAP1'.
    destruct (j2 b2) as [[b3 d]|] eqn : MAP2; try congruence.
    apply INCR2 in MAP2 as MAP2'.
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto. unfold compose_meminj.
    rewrite MAP1', MAP2'. reflexivity.
  Qed.

  Lemma copy_perm_1 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m1' b1 o1 k p ->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.

  Lemma copy_perm_2 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p ->
          Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit copy_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.


  Lemma unchanged_on_copy_block_old : forall a m m',
      Mem.copy_block m1 m2 m1' j1 j2 j1' INJ12 a m = m' ->
      Mem.unchanged_on (fun b o => a <> b) m m'.
  Proof.
    intros. constructor.
    - erewrite <- Mem.copy_block_support; eauto.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
      reflexivity. reflexivity.
    - intros. subst. unfold Mem.copy_block.
      destruct (j2 a); eauto.
      destruct Mem.sup_dec; eauto. unfold Mem.perm.
      simpl. rewrite pmap_update_diff'; eauto; try reflexivity.
  Qed.
  
  Lemma unchanged_on_copy_sup_old : forall s m m',
      Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m = m' ->
      Mem.unchanged_on (fun b o => ~ sup_In b s) m m'.
  Proof.
    induction s; intros.
    - inv H. simpl. eauto with mem.
    - simpl in H. set (m'0 := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 s m).
      exploit IHs. instantiate (1:= m'0). reflexivity. fold m'0 in H.
      intro UNC1. apply unchanged_on_copy_block_old in H as UNC2.
      apply Mem.copy_block_support in H as SUP1.
      constructor.
      + inversion UNC1. eapply Mem.sup_include_trans.  eauto.
        apply Mem.copy_block_support in H. rewrite H. eauto.
      + intros. etransitivity.
        inversion UNC1. eapply unchanged_on_perm.
        intro. apply H0. right. eauto. eauto.
        inversion UNC2. eapply unchanged_on_perm.
        intro. apply H0. left. subst. eauto.
        unfold m'0. unfold Mem.valid_block in *.
        erewrite Mem.copy_sup_support; eauto.
      + intros. etransitivity.
        inversion UNC2. eapply unchanged_on_contents; eauto.
        intro. apply H0. left. eauto.
        inversion UNC1. eapply unchanged_on_perm0; eauto.
        intro. apply H0. right. auto. eauto with mem.
        inversion UNC1. eapply unchanged_on_contents.
        intro. apply H0. right. auto. eauto.
  Qed.

  (*TODO: to mem*)
  Lemma perm_check_true1:
    forall m b o, Mem.perm m b o Max Nonempty ->
             Mem.perm_check_any  (NMap.get b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_any.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get b (Mem.mem_access m)) Max) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.
  
  Lemma perm_check_true2:
    forall m b o, Mem.perm m b o Cur Readable ->
             Mem.perm_check_readable  (NMap.get b (Mem.mem_access m)) o = true.
  Proof.
    intros. unfold Mem.perm_check_readable.
    unfold Mem.perm in H.
    destruct (Maps.ZMap.get o (NMap.get b (Mem.mem_access m)) Cur) eqn:P; simpl;
      setoid_rewrite P.
    - destruct p; simpl; inv H; eauto.
    - inv H.
  Qed.

  Lemma subinj_dec : forall j j' b1 b2 d,
      inject_incr j j' -> j' b1 = Some (b2,d) ->
      {j b1 = Some (b2,d)} + {j b1 = None}.
  Proof.
    intros.
    destruct (j b1) as [[b' d']|] eqn:H1.
    left.
    apply H in H1. rewrite H0 in H1. inv H1. reflexivity.
    right. reflexivity.
  Qed.


  
  Lemma map_block_perm_1: forall b1 o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm (Mem.map_block m1 m1' j1' b1 m) b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold Mem.perm. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_access_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true1. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_perm_2: forall b1 b1' o1 b2 o2 m k p,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      b1 <> b1' ->
      Mem.perm (Mem.map_block m1 m1' j1' b1' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. 
    simpl. setoid_rewrite NMap.gso. reflexivity.
    assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
    - exploit INCRDISJ1; eauto.
    - intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_1' : forall s m m' b2 o2 b1 o1 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      sup_In b1 s ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    induction s; intros.
    - inv H0.
    - simpl in H.
      destruct H0.
      + subst a. rewrite <- H.
        eapply map_block_perm_1; eauto.
        rewrite Mem.map_sup_support. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          eapply map_block_perm_1; eauto.
          rewrite Mem.map_sup_support. eauto.
        * 
          exploit IHs; eauto.
          intro.
          etransitivity. apply H6. rewrite <- H.
          symmetry.
          eapply map_block_perm_2; eauto.
          rewrite Mem.map_sup_support. eauto. 
  Qed.

  Lemma map_sup_rev : forall s m m' b2 o2 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        sup_In b1 s /\
        ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
    induction s; intros.
    - inv H. simpl in H2. exfalso. apply H1. eauto with mem.
    - simpl in H.
      destruct (Mem.perm_dec (Mem.map_sup m1 m1' j1' s m) b2 o2 k p).
      + exploit IHs; eauto.
        intros (b1 & o1 & A & B & C & D).
        exists b1,o1. repeat apply conj; eauto.
        right. eauto.
      + unfold Mem.map_block in H.
        destruct (j1' a) as [[b d]|] eqn:Hj1'a; try congruence.
        destruct (Mem.sup_dec); try congruence.
        destruct (Mem.sup_dec); try congruence.
        subst. unfold Mem.perm in H2. simpl in H2.
        unfold Mem.perm in n. simpl in n.
        destruct (eq_block b b2).
        -- subst. unfold Mem.pmap_update in H2.
           setoid_rewrite NMap.gss in H2; eauto.
           rewrite Mem.update_mem_access_result in H2.
           destruct Mem.perm_check_any.
           ++
           exists a, (o2 -d). repeat apply conj; eauto.
           left. auto. replace (o2 - (o2 - d)) with d by lia. auto.
           ++
           exfalso. apply n. eauto.
           ++ apply Mem.access_default.
        -- rewrite pmap_update_diff' in H2; eauto.
           unfold Mem.perm in n. exfalso. apply n. eauto.
  Qed.
        
  Lemma map_sup_1 : forall s m m' b2 o2 b1 o1 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      sup_In b1 s ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    intros. split; intro.
    eapply map_sup_1'; eauto with mem.
    exploit map_sup_rev; eauto.
    intros (b1' & o1' & A & B & C & D).
    assert (b1 = b1').
    { destruct (eq_block b1 b1'). auto.
      exploit INCRNOLAP'1; eauto.
      inversion INJ12; eauto. inversion INJ12; eauto.
      intro. inv H6.
    }
    subst. rewrite H4 in C. inv C.
    assert (o1 = o1'). lia. subst. eauto.
  Qed.

  Lemma map_block_memval_1: forall b1 o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      mem_memval (Mem.map_block m1 m1' j1' b1 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    unfold Mem.map_block. rewrite H.
    destruct Mem.sup_dec; try congruence.
    destruct Mem.sup_dec; try congruence.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gss. erewrite Mem.update_mem_content_result; eauto.
       replace (o2 - (o2 - o1)) with o1 by lia.
       rewrite perm_check_true2. reflexivity. eauto.
       apply Mem.access_default.
    -- rewrite H1 in n0.
       exfalso. apply n0. eapply IMGIN1'; eauto.
  Qed.

  Lemma map_block_memval_2: forall b1 b1' o1 b2 o2 m,
      j1' b1 = Some (b2, o2 - o1) ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      Mem.perm m1' b1 o1 Cur Readable ->
      b1 <> b1' ->
      mem_memval (Mem.map_block m1 m1' j1' b1' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.map_block. destruct (j1' b1') as [[b2' o2']|] eqn: Hj1'a; eauto.
    destruct Mem.sup_dec; eauto.
    destruct Mem.sup_dec; eauto.
    -- unfold mem_memval. simpl. 
       simpl. setoid_rewrite NMap.gso. reflexivity.
       assert (Hj1b1: j1 b1 = None). inversion INJ12. eauto.
       destruct (subinj_dec _ _ _ _ _ INCR1 Hj1'a).
       ++ exploit INCRDISJ1; eauto.
       ++ intro. exploit INCRNOLAP'1; eauto.
  Qed.
  
  Lemma map_sup_2 : forall s m m' b2 o2 b1 o1,
            Mem.map_sup m1 m1' j1' s m = m' ->
            sup_In b1 s ->
            ~ sup_In b1 (Mem.support m1) ->
            Mem.support m = s2' ->
            j1' b1 = Some (b2, o2 - o1) ->
            Mem.perm m1' b1 o1 Cur Readable ->
            (mem_memval m' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction s; intros.
    - inv H0.
    - simpl in H. generalize INJNOLAP1'. intro INJNOLAP1'.
      destruct H0.
      + subst a. rewrite <- H. apply map_block_memval_1; eauto.
        rewrite Mem.map_sup_support. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          apply map_block_memval_1; eauto.
          rewrite Mem.map_sup_support. eauto.
        * exploit IHs; eauto.
          intro. rewrite <- H5. rewrite <- H.
          eapply map_block_memval_2; eauto.
          rewrite Mem.map_sup_support. eauto.
  Qed.
  
  Lemma supext_empty : forall b o k p,
      ~ sup_In b (Mem.support m2) ->
      ~ Mem.perm (Mem.supext s2' m2) b o k p.
  Proof.
    intros. unfold Mem.supext.
    destruct Mem.sup_include_dec.
    unfold Mem.perm. simpl.
    erewrite Mem.nextblock_noaccess. eauto. eauto.
    congruence.
  Qed.
      
                        
  Lemma step2_perm: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (forall k p, Mem.perm m1' b1 o1 k p <-> Mem.perm m2' b2 o2 k p).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    transitivity (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence.
      eauto. eauto. eauto.
    - transitivity (Mem.perm m2'2 b2 o2 k p).
      unfold m2'2.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'2). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
      eapply Mem.unchanged_on_perm. eapply unchanged_step4_gs.
      red. intros. inv MSTBL12. apply NOTIN2. eauto.
      unfold Mem.valid_block. rewrite m2'2_support. eauto.
  Qed.

  Lemma step2_perm2: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    erewrite <- Mem.unchanged_on_perm in H1.
    2: apply unchanged_step4_gs.
    assert (Mem.perm m2'1 b2 o2 k p).
    { exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'2). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
    }
    unfold m2'1. unfold Mem.step2.
    assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
    eapply supext_empty. eauto.
    exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
    reflexivity. eauto. eauto.
    unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto.
    intro. unfold m2'1 in H2. apply H3. eauto.
    red. intro. inv MSTBL12. apply NOTIN2. apply H12. rewrite H5. eauto.
    unfold Mem.valid_block. rewrite m2'2_support. eauto.
  Qed.

  Lemma step2_content: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      (mem_memval m2' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    etransitivity. eapply unchanged_content_step4.
    exploit unchanged_on_copy_sup_old. instantiate (1:= m2'2). reflexivity.
    intro UNC2.
    assert (Mem.perm m2'1 b2 o2 Cur Readable).
    { unfold m2'2.
      inversion UNC2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
      eapply unchanged_on_perm. eauto. unfold Mem.valid_block. rewrite m2'1_support. eauto.
      unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto.
      intro. apply H2. eauto.
      (* eapply step2_perm; eauto. eauto with mem. *)
    }
    - etransitivity. inversion UNC2.
      setoid_rewrite unchanged_on_contents. reflexivity. eauto.
      eauto.
      unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_2. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto. eauto.
  Qed.

  Lemma step2_content_inject: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite step2_content; eauto.
    exploit ADDEXISTS; eauto. intros (b3 & o3 & MAP13).
    eapply memval_compose_1; eauto.
    inversion INJ13'. inversion mi_inj.
    eapply  mi_memval; eauto.
  Qed.

  Lemma step2_perm1: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p ->
      Mem.perm m2' b2 o2 k p.
  Proof.
    intros. exploit step2_perm; eauto.
    intro HH. eapply HH; eauto.
  Qed.

    Lemma m2_notglobal : forall b2, j2 b2 = None -> ~ sup_In b2 gs2.
  Proof.
    inv MSTBL23. intros.
    intro. inv H6. exploit mge_dom; eauto.
    intros [b3 A]. congruence.
  Qed.
  

  (** Lemma C.10 *)
  
  Theorem MAXPERM2 : injp_max_perm_decrease m2 m2'.
  Proof.
    red. intros b2 o2 p VALID PERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|]eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
      destruct (j2 b2) as [[b3 d2]|] eqn: Hj2.
      + destruct LOCIN as [MAP1 PERM1_].
        exploit copy_perm_2; eauto. congruence.
        intro PERM1'.
        red in MAXPERM1. exploit MAXPERM1; eauto.
        unfold Mem.valid_block. eauto.
        intro PERM1.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
      + generalize (UNCHANGE22). intro UNC2.
        inversion UNC2. eapply unchanged_on_perm; eauto.
        split. eauto. apply m2_notglobal. eauto.
    - generalize (UNCHANGE21'). intro UNC1.
      inversion UNC1. eapply unchanged_on_perm; eauto.
      eapply Mem.loc_in_reach_find_none; eauto.
      eapply perm_decrease_step4. eauto.
  Qed.

  Lemma ro_unc_step4: Mem.ro_unchanged m2'2 m2'.
  Proof.
    apply Mem.ro_unchanged_memval_bytes.
    red. intros.
    split. eapply perm_decrease_step4. eauto.
    setoid_rewrite unchanged_content_step4. reflexivity.
  Qed.
    
  (** Lemma C.11 *)
  Theorem ROUNC2 : Mem.ro_unchanged m2 m2'.
  Proof.
   (* eapply Mem.ro_unchanged_trans.
    2: apply ro_unc_step4. 2: {rewrite m2'2_support. eauto. } 2: apply *)
    apply Mem.ro_unchanged_memval_bytes.
    red. intros b2 o2 VALID PERM2' NOPERM2.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
      destruct (j2 b2) as [[b3 d2]|] eqn: MAP2.
      + 
        exploit copy_perm_2; eauto. congruence. intro PERM1'.
        assert (NOWRIT1: ~ Mem.perm m1 b1 o1 Max Writable).
        intro. apply NOPERM2.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        split. apply Mem.ro_unchanged_memval_bytes in ROUNC1.
        exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
        intros [READ1 ?].
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto.
        symmetry. eapply copy_content_2; eauto. congruence.
      + generalize UNCHANGE22. intro UNC22. split; inv UNC22.
        rewrite unchanged_on_perm; eauto. split. eauto.
        apply m2_notglobal. eauto.
        symmetry. eapply unchanged_on_contents; eauto.
        split; eauto. apply m2_notglobal. eauto.
        eapply unchanged_on_perm; eauto.
        split; eauto. apply m2_notglobal. eauto.
    - eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
      generalize UNCHANGE21'. intro UNC21.
      split; inv UNC21. rewrite unchanged_on_perm; eauto.
      eapply perm_decrease_step4. eauto.
      symmetry. setoid_rewrite unchanged_content_step4.
      eapply unchanged_on_contents; eauto.
      eapply unchanged_on_perm; eauto.
      eapply perm_decrease_step4. eauto.
  Qed.

  (** Lemma C.13 *)
  Theorem INJ12' : Mem.inject j1' m1' m2'.
  Proof.
    constructor.
    - constructor.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- eapply copy_perm_1; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- generalize UNCHANGE22. intro UNCHANGE22.
             assert (A: loc_unmapped j2 b2 (ofs + delta) /\ ~ sup_In b2 gs2).
             split. eauto. apply m2_notglobal. eauto.
             destruct A as [A B].
             inversion UNCHANGE22. apply unchanged_on_perm; eauto.
             inversion INJ12. eauto.
             eapply Mem.perm_inject; eauto.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             split. red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             intro. apply B. inv MSTBL12.
             erewrite <- Genv.mge_separated'; eauto.
             unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          replace (ofs + 0) with ofs by lia.
          eapply step2_perm1; eauto. replace (ofs - ofs) with 0 by lia.
          eauto. eauto with mem.
      + intros. destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * inversion INJ12. inversion mi_inj.
          eapply mi_align; eauto.
          red. intros. exploit H0; eauto.
          intro. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst.
          exists 0. lia.
      + intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1 b1 ofs Max Writable).
             ++ 
                eapply copy_content_inject; eauto.
                replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
             ++ generalize ROUNC2. intro ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC2.
                apply Mem.ro_unchanged_memval_bytes in ROUNC1 as ROUNC1'.
                exploit ROUNC1'; eauto.
                eapply Mem.valid_block_inject_1; eauto.
                intros [PERM1 MVAL1]. rewrite <- MVAL1.
                exploit ROUNC2; eauto. instantiate (1:= b2).
                eapply Mem.valid_block_inject_2. apply e. apply INJ12.
                instantiate (1:= ofs + delta).
                eapply copy_perm_1; eauto with mem.
                replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
                intro. eapply n. inversion INJ12.
                exploit mi_perm_inv; eauto. intros [|]. auto.
                exfalso. apply H2. eauto with mem.
                intros [PERM2 MVAL2]. rewrite <- MVAL2.
                inversion INJ12. inversion mi_inj.
                eapply memval_inject_incr; eauto.
          -- assert (PERM1 : Mem.perm m1 b1 ofs Cur Readable).
             inversion UNCHANGE1. eapply unchanged_on_perm; eauto. split.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             assert (~ sup_In b2 gs2). apply m2_notglobal. eauto.
             intro. apply H1. inv MSTBL12.
             erewrite <- Genv.mge_separated'; eauto.
             unfold Mem.valid_block. eauto.
             assert (PERM2 : Mem.perm m2 b2 (ofs + delta) Cur Readable).
             eapply Mem.perm_inject; eauto.
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. rewrite unchanged_on_contents; eauto.
             inversion INJ12. eauto.
             inversion UNCHANGE1. rewrite unchanged_on_contents0; eauto.
             inversion mi_inj.
             eapply memval_inject_incr; eauto.
             split.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
              assert (~ sup_In b2 gs2). apply m2_notglobal. eauto.
             intro. apply H1. inv MSTBL12.
             erewrite <- Genv.mge_separated'; eauto.
             split. eauto.
             apply m2_notglobal. eauto.
        * eapply step2_content_inject; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
    - intros.
      destruct (j1' b) as [[b2 d]|] eqn:?.
      exploit ADDEXISTS; eauto. inversion INJ12.
      eapply mi_freeblocks. inversion UNCHANGE1.
      intro. apply H. apply unchanged_on_support. eauto.
      intros (b3 & ofs3 & MAP).
      inversion INJ13'. exploit mi_freeblocks; eauto.
      intro. congruence. reflexivity.
    - intros. unfold Mem.valid_block. rewrite m2'_support. eauto.
    - eapply update_meminj_no_overlap1; eauto.
    - intros. destruct (j1 b) as [[b2' d']|] eqn: Hj1b.
        * apply INCR1 in Hj1b as H'. rewrite H in H'. inv H'.
          inversion INJ12.
          eapply mi_representable; eauto.
          destruct H0.
          left. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
          right. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        * exploit ADDZERO; eauto. intro. subst. split. lia.
          generalize (Ptrofs.unsigned_range_2 ofs). lia.
    - intros.
        destruct (subinj_dec _ _ _ _ _ INCR1 H).
        * destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
          -- destruct (Mem.perm_dec m1' b1 ofs Max Nonempty); eauto.
             left.
             eapply copy_perm_2; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto.
             eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
             eauto with mem. congruence.
          -- 
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. apply unchanged_on_perm in H0 as PERM2; eauto.
             2: inversion INJ12; eauto.
             inversion INJ12. exploit mi_perm_inv; eauto.
             intros [A|B].
             left.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             split.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
              assert (~ sup_In b2 gs2). apply m2_notglobal. eauto.
             intro. apply H1. inv MSTBL12.
             erewrite <- Genv.mge_separated'; eauto.
             unfold Mem.valid_block. eauto.
             right. intro. apply B.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto. split.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             assert (~ sup_In b2 gs2). apply m2_notglobal. eauto.
             intro. apply H2. inv MSTBL12.
             erewrite <- Genv.mge_separated'; eauto.
             unfold Mem.valid_block. eauto. split. eauto.
             apply m2_notglobal. eauto.
             inversion INJ12. eapply mi_mappedblocks; eauto.
        * left. eapply step2_perm2; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
Qed.


  Lemma step2_perm2': forall b1 o1 b2 o2 b3 d k p,
      j1' b1 = Some (b2, o2 - o1) ->
      j2 b2 = None -> j2' b2 = Some (b3, d) ->
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit step2_perm2; eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 H); auto.
    exploit INCRDISJ2; eauto. intros [A B].
    inversion INJ12. exploit mi_mappedblocks; eauto.
  Qed.

  (** Lemma C.14 *)
  Theorem INJ23' : Mem.inject j2' m2' m3'.
  Proof.
     assert (DOMIN2: inject_dom_in j2 (Mem.support m2)).
     eapply inject_implies_dom_in; eauto.
     assert (IMGIN2: inject_image_in j2 (Mem.support m3)).
     eapply inject_implies_image_in; eauto.
    constructor.
    - (*mem_inj*)
      constructor.
      + (*perm*)
        intros b2 b3 d2 o2 k p MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        (* old memory *)
        * assert (MAP2: j2 b2 = Some (b3,d2)). (* we have j2' b2 = Some [] here *)
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          -- (* old & public in m1 *)
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].            
            exploit copy_perm_2; eauto. congruence.
            intro PERM1'.
            apply INCR1 in MAP1 as MAP1'.
            exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
            unfold compose_meminj. rewrite MAP1', MAP2'.
            reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
            auto.
          -- (* old & private *)
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            red in LOCIN.
            destruct (Mem.sup_dec b2 gs2).
            ++
              exfalso. eapply freed_step4; eauto. congruence. split; eauto.
            ++
            assert (PERM2 : Mem.perm m2 b2 o2 k p).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. eapply unchanged_on_perm; eauto. split. eauto.
            inv MSTBL23. intro. apply n. subst gs0. rewrite <- H1. rewrite Genv.mge_separated; eauto.
            inversion INJ23. eauto.
            eapply Mem.perm_inject; eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          eapply Mem.perm_inject. 2: apply INJ13'. unfold compose_meminj.
          rewrite MAP1', MAP2'. eauto. eauto.
      + (*align*)
        intros b2 b3 d2 chunk o2 p MAP2' RP2. destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
        * inversion INJ23. inversion mi_inj. eapply mi_align; eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intro. generalize MAXPERM2. intro UNC2.
          eapply UNC2; eauto. unfold Mem.valid_block in *.
          destruct (Mem.sup_dec b2 (Mem.support m2)).
          eauto.  exploit mi_freeblocks; eauto.
        *
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          inversion INJ13'. inv mi_inj.
          exploit mi_align.
          unfold compose_meminj. rewrite MAP1', MAP2'.
          replace (0 + d2) with d2 by lia. reflexivity.
          2: eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intros. eapply step2_perm2'; eauto.
          replace (ofs - ofs) with 0 by lia. eauto.
      + (*memval*)
        intros b2 o2 b3 d2 MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            apply INCR1 in MAP1 as MAP1'.
            destruct (Mem.perm_dec m1 b1 o1 Max Writable).
            ++
              exploit copy_content; eauto. eapply copy_perm_2; eauto. congruence. congruence.
              intro. setoid_rewrite H.
              eapply memval_compose_2; eauto.
              inversion INJ13'. inversion mi_inj.
              exploit mi_memval; eauto. unfold compose_meminj.
              rewrite MAP1'. rewrite MAP2'. reflexivity.
              eapply copy_perm; eauto. congruence. 
              replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
              eauto.
            ++ generalize ROUNC2. intro ROUNC2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC2.
               assert (NOWRIT2: ~ Mem.perm m2 b2 o2 Max Writable).
               intro. apply n. inversion INJ12. exploit mi_perm_inv; eauto.
               instantiate (3:= o1). replace (o1 + (o2 - o1)) with o2 by lia. eauto.
               intros [|]. eauto. congruence.
               exploit ROUNC2; eauto. intros [PERM2 MVAL2]. rewrite <- MVAL2.
               apply Mem.ro_unchanged_memval_bytes in ROUNC3 as ROUNC3'.
               assert (NOWRIT3 : ~ Mem.perm m3 b3 (o2 + d2) Max Writable).
               intro. apply NOWRIT2. inversion INJ23. exploit mi_perm_inv; eauto.
               intros [|]. eauto. exfalso. apply H0. eauto with mem.
               exploit ROUNC3'; eauto. eapply Mem.valid_block_inject_2; eauto.
               exploit copy_perm_2; eauto. congruence.
               intro PERM1'.
               exploit Mem.perm_inject. 2: apply INJ13'. 2: apply PERM1'.
               unfold compose_meminj. rewrite MAP1', MAP2'.
               reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
               auto.
               intros [PERM3 MVAL3]. rewrite <- MVAL3.
               inversion INJ23. inversion mi_inj. eapply memval_inject_incr; eauto.
          -- 
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            red in LOCIN.
            destruct (Mem.sup_dec b2 gs2).
            exfalso. eapply freed_step4; eauto. congruence. split; eauto.
            assert (PERM2 : Mem.perm m2 b2 o2 Cur Readable).
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (PERM3 : Mem.perm m3 b3 (o2 + d2) Cur Readable).
            eapply Mem.perm_inject; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE3. erewrite unchanged_on_contents; eauto.
            generalize UNCHANGE21. intro UNC2. inversion UNC2.
            erewrite unchanged_on_contents0; eauto.
            eapply memval_inject_incr; eauto.
            inversion INJ23. inversion mi_inj. eauto.
            split. eauto. inv MSTBL23.
            unfold gs6.
            rewrite <- Genv.mge_separated; eauto. subst gs0. rewrite H1. eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ23. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          exploit step2_content; eauto.
          destruct (subinj_dec _ _ _ _ _ INCR1 MAP1'); auto.
          exfalso. apply n. inversion INJ12. exploit mi_mappedblocks; eauto.
          instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro.
          setoid_rewrite H.
          eapply memval_compose_2; eauto.
          inversion INJ13'. inversion mi_inj.
          eapply mi_memval; eauto.
          unfold compose_meminj.
          rewrite MAP1'. rewrite MAP2'. reflexivity.
    - intros. destruct (j2' b) as [[b3 d]|] eqn:?.
      exploit DOMIN2'; eauto.
      unfold Mem.valid_block in H.
      rewrite m2'_support in H. intro. congruence.
      reflexivity.
    - intros. destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. exploit mi_mappedblocks; eauto.
        unfold Mem.valid_block.
        intro. inversion UNCHANGE3. eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_mappedblocks; eauto.
        unfold compose_meminj. rewrite MAP1',H. reflexivity.
    - red. intros b2 b3 d2 b2' b3' d2' o2 o2' NEQ MAP2 MAP2' PERM2 PERM2'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2); destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + inversion INJ23. eapply mi_no_overlap; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
        eapply MAXPERM2; eauto. eapply DOMIN2; eauto.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit ADDSAME. apply e. all: eauto. intros [b1 [MAP1 SAME1]].
        exploit ADDSAME; eauto. intros [b1' [MAP1' SAME1']].
        inversion INJ13'. red in mi_no_overlap.
        assert (b1 <> b1'). intro. subst. rewrite MAP1 in MAP1'. inv MAP1'. congruence.
        eapply mi_no_overlap. eauto.
        unfold compose_meminj. rewrite MAP1, MAP2. eauto.
        unfold compose_meminj. rewrite MAP1', MAP2'. eauto.
        eapply step2_perm2'. instantiate (1:= o2).
        replace (o2 - o2) with 0 by lia. eauto. eauto. eauto. eauto.
        eapply step2_perm2'. instantiate (1:= o2').
        replace (o2' - o2') with 0 by lia. eauto. eauto. eauto. eauto.
    - intros.
      destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ23. eapply mi_representable; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        destruct H0.
        left. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
        right. eapply MAXPERM2; eauto. unfold Mem.valid_block. eapply DOMIN2; eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ13'. eapply mi_representable; eauto.
        unfold compose_meminj. rewrite MAP1',H. eauto.
        destruct H0.
        left. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
        right. eapply step2_perm2'; eauto. rewrite Z.sub_diag. eauto.
    - intros b2 o2 b3 d2 k p MAP2' PERM3'.
      generalize INJ12'. intro INJ12'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
        * eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
          destruct LOCIN as [MAP1 PERM1].
          apply INCR1 in MAP1 as MAP1'.
          inversion INJ13'. exploit mi_perm_inv.
          unfold compose_meminj. rewrite MAP1', MAP2'. reflexivity.
          instantiate (3:= o1). replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
          eauto. intros [A | B].
          left. eapply copy_perm; eauto. congruence.
          right. intro. apply B. eapply copy_perm; eauto. congruence.
        * eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
          destruct (Mem.sup_dec b2 gs2).
          (*freed by step4*)
          right. eapply freed_step4; eauto. congruence. split; eauto.
          destruct (Mem.perm_dec m2' b2 o2 Max Nonempty); auto.
          left. generalize UNCHANGE21. intro UNC2.
          assert (PERM2: Mem.perm m2 b2 o2 Max Nonempty).
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
          assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
          eapply loc_out_of_reach_trans; eauto.
          assert (PERM3: Mem.perm m3 b3 (o2 + d2) k p).
          inversion UNCHANGE3. eapply unchanged_on_perm; eauto.
          split. eauto.
          inv MSTBL23. subst gs6.
          erewrite <- Genv.mge_separated; eauto. subst gs0. rewrite H1. eauto.
          eapply IMGIN2; eauto.
          inversion INJ23. exploit mi_perm_inv. eauto. apply PERM3.
          intros [A|B]; try congruence.
          inversion UNC2. eapply unchanged_on_perm; eauto. eapply DOMIN2; eauto.
      + exploit INCRDISJ2; eauto. intros [A B].
        exploit ADDSAME; eauto. intros [b1 [MAP1' SAME]].
        inversion INJ13'. exploit mi_perm_inv.
        unfold compose_meminj. rewrite MAP1', MAP2'. replace (0 + d2) with d2 by lia.
        reflexivity. eauto.
        destruct (subinj_dec _ _ _ _ _ INCR1 MAP1').
        inversion INJ12. exploit mi_mappedblocks0; eauto.
        intros [P1 | P1].
        left. eapply step2_perm1; eauto. replace (o2 - o2) with 0 by lia. eauto. eauto with mem.
        right. intro. apply P1. eapply step2_perm2; eauto.
        replace (o2 - o2) with 0 by lia. eauto.
Qed.

End CONSTR_PROOF.

Section SYMTBL_CONSTR.

Variable se1 se3 : Genv.symtbl.
Variable f : meminj.

Hypothesis MSE: Genv.match_stbls' f se1 se3.
  
Fixpoint remove_sup (se : Genv.symtbl) (s : sup) :=
  match s with
  | nil => se
  | hd :: tl => remove_sup (Genv.remove_global se hd) tl
  end.

Definition unmap_se1 := filter (fun b => if f b then false else true) (Genv.genv_sup se1).

Definition se2 := remove_sup se1 unmap_se1.


Lemma remove_sup_public : forall sup se,
    Genv.public_symbol se = Genv.public_symbol (remove_sup se sup).
Proof.
  induction sup; intros; cbn; eauto.
  unfold Genv.remove_global.
Abort.

                                               
                            


Lemma se2_public : Genv.public_symbol se1 = Genv.public_symbol se2.
Proof.
  unfold se2. unfold remove_sup.
Admitted.

Lemma se2_sup : forall b, sup_In b (Genv.genv_sup se2) <-> sup_In b (Genv.genv_sup se1) /\ f b <> None.
Admitted.

Lemma se2_symb : forall b1 b2 d, f b1 = Some (b2, d) ->
                            forall id, Genv.find_symbol se1 id = Some b1 <-> Genv.find_symbol se2 id = Some b1.
Admitted.

Lemma se2_info : forall b1 b2 d, f b1 = Some (b2, d) ->
                            Genv.find_info se1 b1 = Genv.find_info se2 b1.
Admitted.

Theorem SUP : Mem.sup_include (Genv.genv_sup se2) (Genv.genv_sup se1).
Proof.
  red. intros. apply se2_sup in H. apply H.
Qed.

Theorem Hse1 : Genv.match_stbls' (meminj_dom f) se1 se2.
Proof.
  constructor.
  - intros. rewrite se2_public. reflexivity.
  - intros. unfold meminj_dom in H0. destruct (f b1); simpl in H0; try congruence.
  - intros. apply se2_sup in H. destruct H. exists b2. unfold meminj_dom.
    destruct (f b2) eqn:H1. reflexivity. congruence.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    eapply se2_symb; eauto.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    eapply se2_info; eauto.
  - intros. unfold meminj_dom in H.  destruct (f b1) as [[b2' d]|] eqn:Hinj; inv H.
    split; intros. eapply se2_sup; eauto. split; eauto. congruence.
    apply se2_sup in H. apply H.
Qed. (* ok *)

Theorem Hse2 : Genv.match_stbls f se2 se3.
Proof.
  constructor.
  - intros. inversion MSE. etransitivity. eauto. rewrite se2_public. reflexivity.
  - intros. apply se2_sup in H. destruct H. destruct (f b1) as [[b2 d]|] eqn:Hinj; try congruence.
    inv MSE. exploit mge_dom'; eauto. intro. subst. eauto.
  - intros. inv MSE. eapply mge_img'; eauto.
  - intros. inversion MSE. setoid_rewrite <- se2_symb; eauto.
    eapply mge_symb'; eauto.
  - intros. inversion MSE. setoid_rewrite <- se2_info; eauto.
    eapply mge_info'; eauto.
  - intros. inversion MSE. split; intros. eapply mge_separated'; eauto.
    eapply se2_sup; eauto. eapply se2_sup. split; eauto.
    eapply mge_separated'; eauto. congruence.
Qed.

End SYMTBL_CONSTR.

Require Import VerComp.

Lemma valid_global_dom : forall f se m,
    valid_global m f se ->
    valid_global m (meminj_dom f) se.
Proof.
  intros. red in *. intros.
  exploit H; eauto. unfold valid_memval.
  destruct (mem_memval m b ofs); eauto.
  destruct v; eauto.
  unfold valid_b, meminj_dom. destruct (f b0); eauto.
Qed.
(* injp' ⋅ injp ⊑ injp' *)
Theorem injp'_injp_ref1:
  ccref'  (cc_c' injp') (cc_compose_2 (cc_c' injp') (cc_c injp)).
Proof.
  red. intros w se1 se3 q1 q2 Hse Hq.
  inv Hse. inv Hq. cbn in H2, H3. inv H4. rename m0 into m1. rename m3 into m2.
  set (se2 := se2 se1 f). 
  exploit Hse1; eauto. intro Hse1. fold se2 in Hse1.
  exploit Hse2. eapply H. intro Hse2. fold se2 in Hse2.
  exists (se2, (injpw (meminj_dom f) (Genv.genv_sup se1) (Genv.genv_sup se2) m1 m1 (mem_inject_dom f m1 m2 Hm)),
      (injpw f (Genv.genv_sup se2) (Genv.genv_sup se3) m1 m2 Hm)).
  repeat apply conj.
  - split; constructor; eauto.
    eapply Mem.sup_include_trans. eapply SUP; eauto. eauto.
    eapply Mem.sup_include_trans. eapply SUP; eauto. eauto.
  - exists (cq vf1 sg vargs1 m1). split.
    econstructor; cbn; eauto.
    eapply Inject.val_inject_dom; eauto.
    eapply Inject.val_inject_list_dom; eauto.
    (*TODO: a lemma about valid_global here*)
    constructor; cbn; eauto.
    eapply valid_global_dom; eauto.
    constructor; eauto. constructor; eauto.
  - intros r1 r3 [r2 [Hr1 Hr2]].
    destruct Hr1 as [w12' [Hw12 Hr1]]. destruct Hr2 as [w23' [Hw23 Hr2]].
    destruct w12' as [f12' ? ? m1' m2' Hm12']. destruct w23' as [f23' ? ? m2'' m3' Hm23'].
    inv Hw12. inv Hw23. cbn in *.
    inv Hr1. inv Hr2. cbn in *. inv H6. inv H11.
    rename m1'0 into m1'. rename m2'0 into m2'. rename m2'3 into m3'.
    eexists (injpw (compose_meminj f12' f23') (Genv.genv_sup se1) (Genv.genv_sup se3) m1' m3'
               (Mem.inject_compose f12' f23' _ _ _ Hm12' Hm23')
            ).
    repeat apply conj.
    + constructor; eauto.
      * eapply Mem.unchanged_on_implies; eauto.
        intros. destruct H6. split. red. unfold meminj_dom. rewrite H6. reflexivity. eauto.
      * red. intros. unfold compose_meminj.
        erewrite H22. erewrite H30; eauto.
        2: unfold meminj_dom; rewrite H6; reflexivity.
        rewrite Z.add_0_l. reflexivity.
      * intros b1 b2 delta Hb Hb'. unfold compose_meminj in Hb'.
        destruct (f12' b1) as [[bi delta12] | ] eqn:Hb1; try discriminate.
        destruct (f23' bi) as [[xb2 delta23] | ] eqn:Hb2; try discriminate.
        inv Hb'.
        edestruct H23; eauto. unfold meminj_dom. rewrite Hb. auto.
        destruct (f bi) as [[? ?] | ] eqn:Hfbi.
        {
          eapply Mem.valid_block_inject_1 in Hfbi; eauto.
        }
        edestruct H31; eauto.
    + constructor; cbn; eauto with mem.
      eapply Values.val_inject_compose; eauto.
      constructor; eauto.

      (*
      [] []          []  []         []    []       []    []


               =>    []       ~>    []         =>  []


      []             []             []             []


      If m1'[b1,o1] is readable and has a ill-defined value Vptr b1' o1'
      we know 1) b1' ∉ sup (ge1)
              2) j23' ∘ j12' (b1') = None

      which means
            a) j12' b1' = None , which is impossible because m1' is valid via j12'
         or b) j12' b1' = Some (b2',o2') and j23' b2' = None

      what we know is that m1 is valid via j,
      also inject_incr (meminj_dom f) j12' and


      It seems that it is possible to have a ill-defined value after external calls,
      but why?

      if a value is well-defined in minj m1' m2', it may be ill-defined in minj m1' m3'

      So it indicates that our now invariant is too strong? not suitable for composition?

      1) release it to a way? but it is quite tight for the upper-level self-simulation using old fsim
      2) do not require the valid_global property on reply sides: But what's the intuition for this?

      Does this indicates a bug or something? what if the ill-type value shows up in real compoilation and execution?


       *)
      (*red.
      intros. red. destruct (mem_memval m1' b ofs) eqn:Hmv1; eauto.
      destruct v; eauto. rename b0 into b1'. rename b into b1.
      red. unfold compose_meminj.
      exploit Genv.mge_dom. eauto.
      inv MSTBL12.
      assert
      destruct (f12' b1').
      *)
      
      (*TODO: A lemma here*)
      admit.
Admitted.

Theorem injp'_injp_ref2:
  ccref' (cc_compose_2 (cc_c' injp') (cc_c injp)) (cc_c' injp') .
Proof.
  red.
  intros w se1 se3 q1 q3 MSTBL13 MMEM13.
  destruct w as [[se2 w12] w23].
  destruct MSTBL13 as [MSTBL12 MSTBL23].
  destruct MMEM13 as [q2 [MMEM12 MMEM23]].
  inv MMEM12. inv H1. rename f into j12. rename Hm0 into INJ12. clear Hm1.
  inv MMEM23. inv H10. rename f into j23. rename Hm1 into INJ23. clear Hm2.
  cbn in H9, H7, MSTBL23, MSTBL12, H, H0.
  assert (gs0 = gs2).
  inv MSTBL12. inv MSTBL23. eauto. subst gs0.                
  exists ((injpw (compose_meminj j12 j23) gs1 gs3
          m1 m3 (Mem.inject_compose _ _ _ _ _ INJ12 INJ23))).
  simpl. repeat apply conj.
  - inv MSTBL12. inv MSTBL23.
    econstructor; simpl; auto.
    eapply Genv.match_stbls'_stbls_compose; eauto.
  - constructor; cbn; eauto.
    eapply val_inject_compose; eauto.
     eapply CKLRAlgebra.val_inject_list_compose.
     econstructor; eauto.
     constructor; eauto.
     red. red in H3.
     intros. exploit H3; eauto.
     destruct (mem_memval m1 b ofs); eauto.
     destruct v; eauto. unfold compose_meminj.
     cbn. unfold valid_b. destruct (j12 b0) as [[b2 d]|] eqn:Hj1; eauto.
     inv MSTBL12. inv MSTBL23.
     admit. (*seems wrong here*)

  - intros r1 r3 [w13' [INCR13' Hr13]].
    inv Hr13. inv H4. cbn in H1. rename f into j13'. rename Hm3 into INJ13'.
    cbn in INCR13'. rename m2'0 into m3'.
    inversion INCR13' as [? ? ? ? ? ? ? ? ? ?  RO1 RO3 MAXPERM1 MAXPERM3 UNCHANGE1 UNCHANGE3 INCR13 DISJ13]. subst.
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
    set (m2' := m2' m1 m2 m1' j12 j23 j12' gs2 m2'_sup INJ12).
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (INJ23' :  Mem.inject j23' m2' m3'). eapply INJ23'; eauto.
    rename gs0 into gs1. rename gs4 into gs3.
    set (w1' := injpw j12' gs1 gs2 m1' m2' INJ12').
    set (w2' := injpw j23' gs2 gs3 m2' m3' INJ23').
    rename vres2 into vres3.
    exploit compose_meminj_midvalue; eauto.
    intros [vres2 [RES1 RES2]].
    assert (UNC21:Mem.unchanged_on (fun b z => loc_out_of_reach j12 m1 b z /\ ~ sup_In b gs2) m2 m2').
    eapply UNCHANGE21; eauto.
    exists (cr vres2 m2'). split.
    + exists w1'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. destruct H4. split; eauto. red. unfold compose_meminj.
      rewrite H4. reflexivity.
      constructor; eauto. constructor; eauto.
      admit.
    +
      exists w2'. cbn. split. constructor; eauto. eapply ROUNC2; eauto.
      eapply MAXPERM2; eauto.
      eapply UNCHANGE22; eauto. eapply out_of_reach_trans; eauto.
      econstructor; eauto. constructor; eauto.
Admitted.

Theorem injp'_injp_c_equiv:
  cceqv' (cc_c' injp') (cc_compose_2 (cc_c' injp') (cc_c injp)).
Proof. split. apply injp'_injp_ref1. apply injp'_injp_ref2. Qed.
