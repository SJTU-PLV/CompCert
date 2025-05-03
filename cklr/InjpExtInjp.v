Require Import Events.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import CKLRAlgebra.
Require Import Inject.
Require Import Extends.
Require Import InjectFootprint.

Section CONSTR_PROOF.
  Variable m1 m2 m3 m4 m1' m4': mem.
  Variable j1 j2 j1' j2': meminj.
  Variable s2': sup.
  Hypothesis ROUNC1: Mem.ro_unchanged m1 m1'.
  Hypothesis ROUNC4: Mem.ro_unchanged m4 m4'.
  Hypothesis DOMIN1: inject_dom_in j1 (Mem.support m1).
  Hypothesis DOMIN1': inject_dom_in j1' (Mem.support m1').
  Hypothesis UNCHANGE1: Mem.unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1'.
  Hypothesis UNCHANGE4: Mem.unchanged_on (loc_out_of_reach (compose_meminj j1 j2) m1) m4 m4'.
  Hypothesis INJ12 : Mem.inject j1 m1 m2.
  Hypothesis EXT23 : Mem.extends m2 m3.
  Hypothesis INJ34 : Mem.inject j2 m3 m4.
  Hypothesis INJ14': Mem.inject (compose_meminj j1' j2') m1' m4'.
  Hypothesis SUPINCL2 : Mem.sup_include (Mem.support m2) s2'.
  Hypothesis SUPINCL4 : Mem.sup_include (Mem.support m4) (Mem.support m4').
  Hypothesis INCR1 : inject_incr j1 j1'.
  Hypothesis INCR2 : inject_incr j2 j2'.
  Hypothesis INCRDISJ1 :inject_incr_disjoint j1 j1' (Mem.support m1) (Mem.support m2).
  Hypothesis INCRDISJ2 :inject_incr_disjoint j2 j2' (Mem.support m3) (Mem.support m4).
  Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j1 j1'.
  Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'.
  Hypothesis IMGIN1': inject_image_in j1' s2'.
  Hypothesis DOMIN2': inject_dom_in j2' s2'.
  Hypothesis ADDZERO: update_add_zero j1 j1'.
  Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2').
  Hypothesis ADDSAME : update_add_same j2 j2' j1'.
  Hypothesis ADDBLOCK: update_add_block (Mem.support m2) s2' j1' j2'.

  Definition m2'1 := Mem.step2 m1 m2 m1' s2' j1'.

  Definition m2' := Mem.copy_sup m1 m2 m1' j1 j2 j1' INJ12 (Mem.support m2) m2'1.

  Definition m3'1 := Mem.step2 m1 m3 m1' s2' j1'.
  
  Lemma INJ13 : Mem.inject j1 m1 m3.
  Proof. eapply Mem.inject_extends_compose; eauto. Qed.
                                                     
  Definition m3' := Mem.copy_sup m1 m3 m1' j1 j2 j1' INJ13 (Mem.support m2) m3'1.

  Lemma INJNOLAP1' : Mem.meminj_no_overlap j1' m1'.
  Proof. eapply update_meminj_no_overlap1; eauto. Qed.

   Lemma unchanged2_step1: Mem.unchanged_on (fun b _ => Mem.valid_block m2 b) m2 m2'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s2' m2). reflexivity.
    eapply unchanged_on_map_sup; eauto. reflexivity.
  Qed.
                                          
  Lemma unchanged2_step2: Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged2_step1.
    intros. eauto.
  Qed.

  Lemma unchanged22_step2: Mem.unchanged_on (loc_unmapped j2) m2 m2'1.
  Proof.
    intros. unfold m2'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m2 b).
    eapply unchanged2_step1.
    intros. eauto.
  Qed.
  
  Lemma unchanged3_step1: Mem.unchanged_on (fun b _ => Mem.valid_block m3 b) m3 m3'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s2' m3). reflexivity.
    eapply unchanged_on_map_sup; eauto. apply INJ13.
    inv EXT23. rewrite <- mext_sup; eauto.
    reflexivity.
  Qed.

  Lemma unchanged31_step2: Mem.unchanged_on (loc_out_of_reach j1 m1) m3 m3'1.
  Proof.
    intros. unfold m3'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m3 b).
    eapply unchanged3_step1.
    intros. eauto.
  Qed.
  
  Lemma unchanged3_step2: Mem.unchanged_on (loc_unmapped j2) m3 m3'1.
  Proof.
    intros. unfold m3'1. unfold Mem.step2.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m3 b).
    eapply unchanged3_step1.
    intros. eauto.
  Qed.

  Lemma unchanged_on_copy_block2 : forall m m' b mx INJx,
      Mem.copy_block m1 mx m1' j1 j2 j1' INJx b m = m' ->
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
  Lemma unchanged_on_copy_block1 : forall m m' b mx INJx,
      Mem.copy_block m1 mx m1' j1 j2 j1' INJx b m = m' ->
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

  Lemma unchanged_on_copy'1 : forall s m m' mx INJx,
      Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx s m = m' ->
      Mem.unchanged_on (loc_out_of_reach j1 m1) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block1; eauto.
      eauto.
  Qed.

  Lemma unchanged_on_copy'2 : forall s m m' mx INJx,
      Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx s m = m' ->
      Mem.unchanged_on (loc_unmapped j2) m m'.
  Proof.
    induction s; intros; subst; simpl.
    - eauto with mem.
    - eapply Mem.unchanged_on_trans.
      2: eapply unchanged_on_copy_block2; eauto.
      eauto. 
  Qed.
  
  Lemma unchanged2_step3: Mem.unchanged_on (loc_out_of_reach j1 m1) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'1; eauto.
  Qed.

  Lemma unchanged31_step3 : Mem.unchanged_on (loc_out_of_reach j1 m1) m3'1 m3'.
  Proof.
     unfold m3'. unfold Mem.copy_sup.
     eapply unchanged_on_copy'1; eauto.
  Qed.
  
  Lemma unchanged22_step3: Mem.unchanged_on (loc_unmapped j2) m2'1 m2'.
  Proof.
    unfold m2'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'2; eauto.
  Qed.
  
  Lemma unchanged3_step3: Mem.unchanged_on (loc_unmapped j2) m3'1 m3'.
  Proof.
    unfold m3'. unfold Mem.copy_sup.
    eapply unchanged_on_copy'2; eauto.
  Qed.

  (** Lemma C.8(1) *)
  Theorem UNCHANGE2 : Mem.unchanged_on (loc_out_of_reach j1 m1) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged2_step2.
    eapply unchanged2_step3.
  Qed.

  Theorem UNCHANGE22 : Mem.unchanged_on (loc_unmapped j2) m2 m2'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged22_step2.
    eapply unchanged22_step3.
  Qed.

  (** Lemma C.8(2) *)
  Theorem UNCHANGE3 : Mem.unchanged_on (loc_unmapped j2) m3 m3'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged3_step2.
    eapply unchanged3_step3.
  Qed.
    
  Theorem UNCHANGE32 : Mem.unchanged_on (loc_out_of_reach j1 m1) m3 m3'.
  Proof.
    eapply Mem.unchanged_on_trans; eauto.
    eapply unchanged31_step2.
    eapply unchanged31_step3.
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

  Lemma m3_support : Mem.support m3 = Mem.support m2.
  Proof. erewrite <- Mem.mext_sup; eauto. Qed.
  
  Lemma m2'1_support : Mem.support m2'1 = s2'.
  Proof. unfold m2'1. erewrite Mem.step2_support; eauto. Qed.
  Lemma m2'_support : Mem.support m2' = s2'.
  Proof. unfold m2'. erewrite Mem.copy_sup_support; eauto. erewrite m2'1_support; eauto. Qed.
  
  Lemma m3'1_support : Mem.support m3'1 = s2'.
  Proof. unfold m3'1. erewrite Mem.step2_support; eauto. rewrite m3_support. eauto. Qed.
  Lemma m3'_support : Mem.support m3' = s2'.
  Proof. unfold m3'. erewrite Mem.copy_sup_support; eauto. erewrite m3'1_support; eauto. Qed.

  Lemma copy_block_perm1 : forall m b1 o1 b2 o2 k p mx INJx,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Max Nonempty ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      Mem.perm (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2 m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
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

  Lemma copy_block_perm2 : forall m b2 o2 b2' k p mx INJx,
      b2 <> b2' ->
      Mem.perm (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2' m) b2 o2 k p <-> Mem.perm m b2 o2 k p.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold Mem.perm. simpl. rewrite pmap_update_diff'; eauto. reflexivity.
  Qed.

  Lemma copy_sup_perm': forall bl m b1 o1 b2 o2 k p mx INJx,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx bl m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    induction bl; intros.
    - inv H2.
    - simpl. destruct H2.
      + subst a.
        eapply copy_block_perm1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_perm1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_perm2; eauto.
  Qed.

  Lemma copy_sup_perm: forall s m b1 o1 b2 o2 k p mx INJX,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        Mem.perm (Mem.copy_sup m1 mx m1' j1 j2 j1' INJX s m) b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. apply Mem.sup_list_in in H2 as H2'.
    unfold Mem.copy_sup. eapply copy_sup_perm'; eauto.
  Qed.

  Lemma copy_perm: forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m2' b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. eapply copy_sup_perm; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_perm_m3 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m3' b2 o2 k p <-> Mem.perm m1' b1 o1 k p.
  Proof.
    intros. eapply copy_sup_perm; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m3'1_support.
  Qed.
  
  Lemma copy_block_content : forall m b1 o1 b2 o2 mx INJx,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2 m) b2 o2 =
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
  
  Lemma copy_block_content1 : forall m b1 o1 b2 o2 mx INJx,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2 m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_true; eauto.
  Qed.

  Lemma copy_block_content3 : forall m b2 o2 b2' mx INJx,
      b2 <> b2' ->
      mem_memval (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2' m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros.
    unfold Mem.copy_block. destruct (j2 b2'); try reflexivity.
    destruct Mem.sup_dec; try reflexivity.
    unfold mem_memval. simpl. rewrite pmap_update_diff'; eauto.
  Qed.

  Lemma copy_block_content2 :  forall m b1 o1 b2 o2 mx INJx,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      Mem.support m = s2' ->
      mem_memval (Mem.copy_block m1 mx m1' j1 j2 j1' INJx b2 m) b2 o2 = mem_memval m b2 o2.
  Proof.
    intros. erewrite copy_block_content; eauto.
    rewrite pred_dec_false; eauto.
  Qed.

  Lemma copy_sup_content': forall bl m b1 o1 b2 o2 mx INJx,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        In b2 bl ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 mx  m1' j1 j2 j1' INJx bl m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H3.
    - simpl. destruct H3.
      + subst a.
        eapply copy_block_content1; eauto.
        erewrite Mem.copy_sup_support'; eauto.
      + destruct (eq_block a b2).
        * subst a.
          eapply copy_block_content1; eauto.
          erewrite Mem.copy_sup_support'; eauto.
        * 
          exploit IHbl; eauto.
          intro.
          etransitivity. 2: eauto.
          eapply copy_block_content3; eauto.
  Qed.
  
  Lemma copy_sup_content: forall s m b1 o1 b2 o2 mx INJx,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        sup_In b2 s ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup m1 mx m1' j1 j2 j1' INJx s m) b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. apply Mem.sup_list_in in H3 as H3'.
    eapply copy_sup_content'; eauto.
  Qed.
  
  Lemma copy_sup_content_2: forall bl m b1 o1 b2 o2 mx INJx,
        j1 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1' b1 o1 Cur Readable ->
        ~ Mem.perm m1 b1 o1 Max Writable ->
        ~ (j2 b2 = None) ->
        Mem.support m = s2' ->
        mem_memval (Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx bl m) b2 o2 = mem_memval m b2 o2.
  Proof.
    induction bl; intros; cbn.
    - reflexivity.
    - destruct (eq_block a b2). subst a.
      erewrite copy_block_content2; eauto.
      erewrite Mem.copy_sup_support'; eauto. 
      erewrite copy_block_content3; eauto.
  Qed.

  Lemma copy_content : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. eapply copy_sup_content; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m2'1_support.
  Qed.

  Lemma copy_content_m3 : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m3' b2 o2 = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros. eapply copy_sup_content; eauto.
    inversion INJ12. eapply mi_mappedblocks; eauto.
    apply m3'1_support.
  Qed.
  
  Lemma copy_content_2 : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable -> ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m2' b2 o2 = mem_memval m2 b2 o2.
  Proof.
    intros. etransitivity.
    unfold m2'. eapply copy_sup_content_2; eauto.
    apply m2'1_support.
    apply Mem.ro_unchanged_memval_bytes in ROUNC1.
    exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
    intros [P1 X].
    generalize unchanged2_step1. intro U.
    inv U. eapply unchanged_on_contents.
    eapply Mem.valid_block_inject_2; eauto.
    replace o2 with (o1 + (o2 - o1)) by lia.
    eapply Mem.perm_inject; eauto.
  Qed.

   Lemma copy_content_2_m3' : forall b1 o1 b2 o2,
      j1 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable -> ~ Mem.perm m1 b1 o1 Max Writable ->
      ~ (j2 b2 = None) ->
      mem_memval m3' b2 o2 = mem_memval m3 b2 o2.
  Proof.
    intros. etransitivity.
    unfold m2'. eapply copy_sup_content_2; eauto.
    apply m3'1_support.
    apply Mem.ro_unchanged_memval_bytes in ROUNC1.
    exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
    intros [P1 X].
    generalize unchanged3_step1. intro U.
    inv U. eapply unchanged_on_contents.
    eapply Mem.valid_block_inject_2; eauto. eapply INJ13; eauto.
    replace o2 with (o1 + (o2 - o1)) by lia.
    eapply Mem.perm_inject; eauto. eapply INJ13; eauto.
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
    inversion INJ14'. inversion mi_inj.
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

    Lemma copy_perm_1_m3 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m1' b1 o1 k p ->
          Mem.perm m3' b2 o2 k p.
  Proof.
    intros. exploit copy_perm_m3; eauto.
    intro HH. eapply HH; eauto.
  Qed.

  Lemma copy_perm_2_m3 : forall b1 o1 b2 o2 k p,
          j1 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          ~ (j2 b2 = None) ->
          Mem.perm m3' b2 o2 k p ->
          Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit copy_perm_m3; eauto.
    intro HH. eapply HH; eauto.
  Qed.

  Lemma unchanged_on_copy_block_old : forall a m m' mx INJx,
      Mem.copy_block m1 mx m1' j1 j2 j1' INJx a m = m' ->
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

  Lemma unchanged_on_copy_sup_old' : forall bl m m' mx INJx,
      Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx bl m = m' ->
      Mem.unchanged_on (fun b o => ~ In b bl) m m'.
  Proof.
    induction bl; intros.
    - inv H. simpl. eauto with mem.
    - simpl in H. set (m'0 := Mem.copy_sup' m1 mx m1' j1 j2 j1' INJx bl m).
      exploit IHbl. instantiate (1:= m'0). reflexivity. fold m'0 in H.
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
        erewrite Mem.copy_sup_support'; eauto.
      + intros. etransitivity.
        inversion UNC2. eapply unchanged_on_contents; eauto.
        intro. apply H0. left. eauto.
        inversion UNC1. eapply unchanged_on_perm0; eauto.
        intro. apply H0. right. auto. eauto with mem.
        inversion UNC1. eapply unchanged_on_contents.
        intro. apply H0. right. auto. eauto.
  Qed.
  
  Lemma unchanged_on_copy_sup_old : forall s m m' mx INJx,
      Mem.copy_sup m1 mx m1' j1 j2 j1' INJx s m = m' ->
      Mem.unchanged_on (fun b o => ~ sup_In b s) m m'.
  Proof.
    intros.
    unfold Mem.copy_sup in H.
    apply unchanged_on_copy_sup_old' in H.
    eapply Mem.unchanged_on_implies. apply H.
    intros. red. intro. apply H0. eapply Mem.sup_list_in; eauto.
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

  Lemma map_sup_1' : forall bl m m' b2 o2 b1 o1 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      In b1 bl ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H.
      destruct H0.
      + subst a. rewrite <- H.
        eapply map_block_perm_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          eapply map_block_perm_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * exploit IHbl; eauto.
          intro.
          etransitivity. apply H6. rewrite <- H.
          symmetry.
          eapply map_block_perm_2; eauto.
          rewrite Mem.map_sup_support'. eauto. 
  Qed.

  Lemma map_sup_rev' : forall bl m m' b2 o2 k p,
      Mem.map_sup' m1 m1' j1' bl m = m' ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      Mem.perm m' b2 o2 k p ->
      exists b1 o1,
        In b1 bl /\
          ~ sup_In b1 (Mem.support m1) /\
        j1' b1 = Some (b2, o2 - o1) /\
        Mem.perm m1' b1 o1 k p.
  Proof.
       induction bl; intros.
    - inv H. simpl in H2. exfalso. apply H1. eauto with mem.
    - simpl in H.
      destruct (Mem.perm_dec (Mem.map_sup' m1 m1' j1' bl m) b2 o2 k p).
      + exploit IHbl; eauto.
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
  
  (*Lemma map_sup_rev : forall s m m' b2 o2 k p,
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
    intros. exploit map_sup_rev'; eauto.
    (* intros (b1 & o1 & A & B & C & D).
    exists b1, o1. repeat apply conj; eauto. apply Mem.sup_list_in; eauto. *)
  Qed.
   *)
   Lemma map_sup_1 : forall s m m' b2 o2 b1 o1 k p,
      Mem.map_sup m1 m1' j1' s m = m' ->
      sup_In b1 s ->
      ~ sup_In b1 (Mem.support m1) ->
      Mem.support m = s2' ->
      ~ Mem.perm m b2 o2 Max Nonempty ->
      j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 k p <-> Mem.perm m' b2 o2 k p.
  Proof.
    intros. apply Mem.sup_list_in in H0 as H0'. split; intro.
    eapply map_sup_1'; eauto with mem.
    exploit map_sup_rev'; eauto.
    intros (b1' & o1' & A & B & C & D).
    assert (b1 = b1').
    { destruct (eq_block b1 b1'). auto.
      exploit INCRNOLAP'1; eauto.
      inv INJ12; eauto. inv INJ12; eauto.
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
  
  Lemma map_sup_2 : forall bl m m' b2 o2 b1 o1,
            Mem.map_sup' m1 m1' j1' bl m = m' ->
            In b1 bl ->
            ~ sup_In b1 (Mem.support m1) ->
            Mem.support m = s2' ->
            j1' b1 = Some (b2, o2 - o1) ->
            Mem.perm m1' b1 o1 Cur Readable ->
            (mem_memval m' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    induction bl; intros.
    - inv H0.
    - simpl in H. generalize INJNOLAP1'. intro INJNOLAP1'.
      destruct H0.
      + subst a. rewrite <- H. apply map_block_memval_1; eauto.
        rewrite Mem.map_sup_support'. eauto.
      + destruct (eq_block a b1).
        * subst a. rewrite <- H.
          apply map_block_memval_1; eauto.
          rewrite Mem.map_sup_support'. eauto.
        * exploit IHbl; eauto.
          intro. rewrite <- H5. rewrite <- H.
          eapply map_block_memval_2; eauto.
          rewrite Mem.map_sup_support'. eauto.
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

  
  Lemma supext_empty_m3 : forall b o k p,
      ~ sup_In b (Mem.support m3) ->
      ~ Mem.perm (Mem.supext s2' m3) b o k p.
  Proof.
    intros. unfold Mem.supext.
    destruct Mem.sup_include_dec.
    unfold Mem.perm. simpl.
    erewrite Mem.nextblock_noaccess. eauto. eauto.
    intro. apply H. eapply Mem.perm_valid_block; eauto.
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
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
  Qed.

   Lemma step2_perm_m3: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (forall k p, Mem.perm m1' b1 o1 k p <-> Mem.perm m3' b2 o2 k p).
  Proof.
    intros.
    exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    transitivity (Mem.perm m3'1 b2 o2 k p).
    - unfold m3'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m3) b2 o2 Max Nonempty).
      eapply supext_empty_m3. rewrite m3_support. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m3))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto.
      rewrite m3_support in n. congruence.
      eauto. eauto. eauto.
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m3'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m3'1_support. eauto.
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
    assert (Mem.perm m2'1 b2 o2 k p).
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m2'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
    - unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto.
      intro. unfold m2'1 in H2. apply H3. eauto.
  Qed.

  Lemma step2_perm2_m3: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m3' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
       exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    assert (Mem.perm m3'1 b2 o2 k p).
    - unfold m2'.
      exploit unchanged_on_copy_sup_old.
      instantiate (1:= m3'). reflexivity.
      intro. inversion H2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m3'1_support. eauto.
    - unfold m3'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m3) b2 o2 Max Nonempty).
      eapply supext_empty_m3. rewrite m3_support. eauto.
      exploit map_sup_1. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m3))).
      reflexivity. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto.
      rewrite m3_support in n. congruence.
      eauto. eauto. 
      intro. unfold m3'1 in H2. apply H3. eauto.
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
    exploit unchanged_on_copy_sup_old. instantiate (1:= m2'). reflexivity.
    intro UNC2.
    assert (Mem.perm m2'1 b2 o2 Cur Readable).
    { unfold m2'.
      inversion UNC2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m2'1_support. eauto.
      eapply step2_perm; eauto. eauto with mem.
    }
    - etransitivity. inversion UNC2.
      setoid_rewrite unchanged_on_contents. reflexivity. eauto.
      eauto.
      unfold m2'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m2) b2 o2 Max Nonempty).
      eapply supext_empty. eauto.
      exploit map_sup_2. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m2))). unfold Mem.map_sup.
      reflexivity. rewrite <- Mem.sup_list_in. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto. congruence. eauto. eauto. eauto.
  Qed.

    Lemma step2_content_m3: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      (mem_memval m3' b2 o2) = Mem.memval_map j1' (mem_memval m1' b1 o1).
  Proof.
    intros.
      exploit INCRDISJ1; eauto. intros [NOTIN1 NOTIN2].
    assert (IN: sup_In b2 s2').
    { eapply IMGIN1'; eauto. }
    exploit unchanged_on_copy_sup_old. instantiate (1:= m3'). reflexivity.
    intro UNC2.
    assert (Mem.perm m3'1 b2 o2 Cur Readable).
    { unfold m2'.
      inversion UNC2. eapply unchanged_on_perm; eauto.
      unfold Mem.valid_block. rewrite m3'1_support. eauto.
      eapply step2_perm_m3; eauto. eauto with mem.
    }
    - etransitivity. inversion UNC2.
      setoid_rewrite unchanged_on_contents. reflexivity. eauto.
      eauto.
      unfold m3'1. unfold Mem.step2.
      assert (EXT_EMPTY: ~ Mem.perm (Mem.supext s2' m3) b2 o2 Max Nonempty).
      eapply supext_empty_m3. rewrite m3_support. eauto.
      exploit map_sup_2. instantiate (1:= (Mem.map_sup m1 m1' j1' (Mem.support m1') (Mem.supext s2' m3))). unfold Mem.map_sup.
      reflexivity. rewrite <- Mem.sup_list_in. eauto. eauto. eauto.
      unfold Mem.supext. destruct Mem.sup_include_dec. eauto.
      rewrite m3_support in n. congruence. eauto. eauto. eauto.
  Qed.

  Lemma step2_content_inject: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. erewrite step2_content; eauto.
    exploit ADDEXISTS; eauto. intros (b3 & o3 & MAP13).
    eapply memval_compose_1; eauto.
    inversion INJ14'. inversion mi_inj.
    eapply  mi_memval; eauto.
  Qed.

   Lemma step2_content_inject_m3: forall b1 o1 b2 o2,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      memval_inject j1' (mem_memval m1' b1 o1) (mem_memval m3' b2 o2).
  Proof.
    intros. erewrite step2_content_m3; eauto.
    exploit ADDEXISTS; eauto. intros (b3 & o3 & MAP13).
    eapply memval_compose_1; eauto.
    inversion INJ14'. inversion mi_inj.
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

  Lemma step2_perm1_m3: forall b1 o1 b2 o2 k p,
      j1 b1 = None -> j1' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      Mem.perm m1' b1 o1 k p ->
      Mem.perm m3' b2 o2 k p.
  Proof.
    intros. exploit step2_perm_m3; eauto.
    intro HH. eapply HH; eauto.
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
    - generalize (UNCHANGE2). intro UNC1.
      inversion UNC1. eapply unchanged_on_perm; eauto.
      eapply Mem.loc_in_reach_find_none; eauto.
  Qed.

  (** Lemma C.11 *)
  Theorem ROUNC2 : Mem.ro_unchanged m2 m2'.
  Proof.
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
        rewrite unchanged_on_perm; eauto.
        symmetry. eapply unchanged_on_contents; eauto.
        eapply unchanged_on_perm; eauto.
    - eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
      generalize UNCHANGE2. intro UNC21.
      split; inv UNC21. rewrite unchanged_on_perm; eauto.
      symmetry. eapply unchanged_on_contents; eauto.
      eapply unchanged_on_perm; eauto.
  Qed.

  Theorem MAXPERM3 : injp_max_perm_decrease m3 m3'.
  Proof.
   red. intros b2 o2 p VALID PERM3.
   destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|]eqn:LOCIN.
   - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
     destruct (j2 b2) as [[b3 d2]|] eqn: Hj2.
     + destruct LOCIN as [MAP1 PERM1_].
       exploit copy_perm_m3; eauto. congruence.
       intro PERM1'.
       red in MAXPERM1. exploit MAXPERM1; eauto.
       unfold Mem.valid_block. eauto. apply PERM1'. eauto.
       intro PERM1.
       replace o2 with (o1 + (o2 - o1)) by lia.
       eapply Mem.perm_inject; eauto. apply INJ13; eauto.
      + generalize (UNCHANGE3). intro UNC2.
        inversion UNC2. eapply unchanged_on_perm; eauto.
   - generalize (UNCHANGE32). intro UNC1.
     inversion UNC1. eapply unchanged_on_perm; eauto.
     eapply Mem.loc_in_reach_find_none; eauto.
  Qed.

  (** Lemma C.11 *)
  Theorem ROUNC3 : Mem.ro_unchanged m3 m3'.
  Proof.
    apply Mem.ro_unchanged_memval_bytes.
    red. intros b2 o2 VALID PERM3' NOPERM3.
    destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
    - eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
      destruct (j2 b2) as [[b3 d2]|] eqn: MAP2.
      + 
        exploit copy_perm_m3; eauto. congruence. intro PERM1'.
        assert (NOWRIT1: ~ Mem.perm m1 b1 o1 Max Writable).
        intro. apply NOPERM3.
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto. eapply INJ13; eauto.
        split. apply Mem.ro_unchanged_memval_bytes in ROUNC1.
        exploit ROUNC1; eauto. eapply Mem.valid_block_inject_1; eauto.
        apply PERM1'. eauto.
        intros [READ1 ?].
        replace o2 with (o1 + (o2 - o1)) by lia.
        eapply Mem.perm_inject; eauto. eapply INJ13; eauto.
        symmetry. eapply copy_content_2_m3'; eauto. apply PERM1'.
        eauto.
        congruence.
      + generalize UNCHANGE3. intro UNC22. split; inv UNC22.
        rewrite unchanged_on_perm; eauto.
        symmetry. eapply unchanged_on_contents; eauto.
        eapply unchanged_on_perm; eauto.
    - eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
      generalize UNCHANGE32. intro UNC21.
      split; inv UNC21. rewrite unchanged_on_perm; eauto.
      symmetry. eapply unchanged_on_contents; eauto.
      eapply unchanged_on_perm; eauto.
  Qed.
  
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
             inversion UNCHANGE22. apply unchanged_on_perm; eauto.
             inversion INJ12. eauto.
             eapply Mem.perm_inject; eauto.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
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
                apply Mem.ro_unchanged_memval_bytes in ROUNC1.
                exploit ROUNC1; eauto.
                eapply Mem.valid_block_inject_1; eauto.
                intros [PERM1 MVAL1]. rewrite <- MVAL1.

                exploit ROUNC2; eauto.
                eapply Mem.valid_block_inject_2. apply e. eauto.
                eapply copy_perm_1; eauto with mem. instantiate (1:= ofs + delta).
                replace (ofs + delta - ofs) with delta by lia. eauto. congruence.
                intro. eapply n. inversion INJ12.
                exploit mi_perm_inv; eauto. intros [|]. auto.
                exfalso. apply H2. eauto with mem.
                intros [PERM2 MVAL2]. rewrite <- MVAL2.
                inversion INJ12. inversion mi_inj.
                eapply memval_inject_incr; eauto.
          -- assert (PERM1 : Mem.perm m1 b1 ofs Cur Readable).
             inversion UNCHANGE1. eapply unchanged_on_perm; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
             assert (PERM2 : Mem.perm m2 b2 (ofs + delta) Cur Readable).
             eapply Mem.perm_inject; eauto.
             generalize UNCHANGE22. intro UNCHANGE22.
             inversion UNCHANGE22. rewrite unchanged_on_contents; eauto.
             inversion INJ12. eauto.
             inversion UNCHANGE1. rewrite unchanged_on_contents0; eauto.
             inversion mi_inj.
             eapply memval_inject_incr; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
        * eapply step2_content_inject; eauto. replace (ofs + delta - ofs) with delta by lia.
          eauto.
    - intros.
      destruct (j1' b) as [[b2 d]|] eqn:?.
      exploit ADDEXISTS; eauto. inversion INJ12.
      eapply mi_freeblocks. inversion UNCHANGE1.
      intro. apply H. apply unchanged_on_support. eauto.
      intros (b3 & ofs3 & MAP).
      inversion INJ14'. exploit mi_freeblocks; eauto.
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
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
             right. intro. apply B.
             inversion UNCHANGE1. eapply unchanged_on_perm0; eauto.
             red. unfold compose_meminj. rewrite e, j2b2. reflexivity.
             unfold Mem.valid_block. eauto.
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
    generalize INJ13. intro INJ13. inv INJ13.
    exploit mi_mappedblocks; eauto.
  Qed.

  Lemma step2_perm2'_m3: forall b1 o1 b2 o2 b3 d k p,
      j1' b1 = Some (b2, o2 - o1) ->
      j2 b2 = None -> j2' b2 = Some (b3, d) ->
      Mem.perm m3' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros. exploit step2_perm2_m3; eauto.
    destruct (subinj_dec _ _ _ _ _ INCR1 H); auto.
     exploit INCRDISJ2; eauto. intros [A B].
     generalize INJ13. intro INJ13. inv INJ13.
     exploit mi_mappedblocks; eauto.
  Qed.

  
  (** Lemma C.14 *)
  Theorem INJ34' : Mem.inject j2' m3' m4'.
  Proof.
     assert (DOMIN2: inject_dom_in j2 (Mem.support m3)).
     eapply inject_implies_dom_in; eauto.
     assert (IMGIN2: inject_image_in j2 (Mem.support m4)).
     eapply inject_implies_image_in; eauto.
     constructor.
    - (*mem_inj*)
      constructor.
      + (*perm*)
        intros b2 b3 d2 o2 k p MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m3)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
           exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            exploit copy_perm_2_m3; eauto. congruence.
            intro PERM1'.
            apply INCR1 in MAP1 as MAP1'.
            exploit Mem.perm_inject. 2: apply INJ14'. 2: apply PERM1'.
            unfold compose_meminj. rewrite MAP1', MAP2'.
            reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
            auto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM3 : Mem.perm m3 b2 o2 k p).
            generalize UNCHANGE32. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            eapply loc_out_of_reach_trans. 2: eauto. apply INJ13. eauto. eauto. eauto.
            inversion UNCHANGE4.
            eapply unchanged_on_perm; eauto.
            inversion INJ34. eauto.
            eapply Mem.perm_inject; eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ34. apply mi_freeblocks. eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'_m3; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          eapply Mem.perm_inject. 2: apply INJ14'. unfold compose_meminj.
          rewrite MAP1', MAP2'. eauto. eauto.
      + (*align*)
        intros b2 b3 d2 chunk o2 p MAP2' RP2. destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
        * inversion INJ34. inversion mi_inj. eapply mi_align; eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intro. generalize MAXPERM3. intro UNC3.
          eapply UNC3; eauto. unfold Mem.valid_block in *.
          destruct (Mem.sup_dec b2 (Mem.support m3)).
          eauto. exfalso. exploit mi_freeblocks.
          apply n. congruence.
        *
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          inversion INJ14'. inv mi_inj.
          exploit mi_align.
          unfold compose_meminj. rewrite MAP1', MAP2'.
          replace (0 + d2) with d2 by lia. reflexivity.
          2: eauto.
          red. red in RP2. intros.
          exploit RP2; eauto.
          intros. eapply step2_perm2'_m3; eauto.
          replace (ofs - ofs) with 0 by lia. eauto.
      + (*memval*)
        intros b2 o2 b3 d2 MAP2' PERM2'.
        destruct (Mem.sup_dec b2 (Mem.support m3)).
        * assert (MAP2: j2 b2 = Some (b3,d2)).
          destruct (subinj_dec _ _ _ _ _ INCR2 MAP2'); auto.
          exploit INCRDISJ2; eauto. intros [A B]. congruence.
          destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
          --
            eapply Mem.loc_in_reach_find_valid in LOCIN; eauto. destruct LOCIN as [MAP1 PERM1].
            apply INCR1 in MAP1 as MAP1'.
            destruct (Mem.perm_dec m1 b1 o1 Max Writable).
            ++
              exploit copy_content_m3; eauto. eapply copy_perm_2_m3; eauto. congruence. congruence.
              intro. setoid_rewrite H.
              eapply memval_compose_2; eauto.
              inversion INJ14'. inversion mi_inj.
              exploit mi_memval; eauto. unfold compose_meminj.
              rewrite MAP1'. rewrite MAP2'. reflexivity.
              eapply copy_perm_m3; eauto. congruence. 
              replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
              eauto.
            ++ assert (NOWRIT2: ~ Mem.perm m2 b2 o2 Max Writable).
               intro. apply n. inversion INJ12. exploit mi_perm_inv; eauto.
               instantiate (3:= o1). replace (o1 + (o2 - o1)) with o2 by lia. eauto.
               intros [|]. eauto. congruence.
               apply Mem.ro_unchanged_memval_bytes in ROUNC4.
               assert (PERM2: Mem.perm m2 b2 o2 Max Nonempty).
               replace o2 with (o1 + (o2 - o1)) by lia.
               eapply Mem.perm_inject. apply MAP1. eauto. eauto.
               assert (NOWRIT3 : ~ Mem.perm m3 b2 o2 Max Writable).
               intro.
               exploit Mem.perm_extends_inv. eauto. apply H.
               intros [|]. eauto. apply H0. eauto with mem.
               generalize ROUNC3. intro ROUNC3.
               apply Mem.ro_unchanged_memval_bytes in ROUNC3.
               exploit ROUNC3; eauto. intros [PERM3 MVAL3].
               rewrite <- MVAL3.
               assert (NOWRIT4 : ~ Mem.perm m4 b3 (o2 + d2) Max Writable).
               intro. apply NOWRIT3. inversion INJ34. exploit mi_perm_inv; eauto.
               intros [|]. eauto. exfalso. apply H0. eauto with mem.
               exploit ROUNC4; eauto. eapply Mem.valid_block_inject_2; eauto.
               exploit copy_perm_2_m3; eauto. congruence.
               intro PERM1'.
               exploit Mem.perm_inject. 2: apply INJ14'. 2: apply PERM1'.
               unfold compose_meminj. rewrite MAP1', MAP2'.
               reflexivity. intro. replace (o1 + (o2 - o1 + d2)) with (o2 + d2) in H by lia.
               auto.
               intros [PERM4 MVAL4]. rewrite <- MVAL4.
               inversion INJ34. inversion mi_inj. eapply memval_inject_incr; eauto.
          --
            eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
            assert (PERM2 : Mem.perm m3 b2 o2 Cur Readable).
            generalize UNCHANGE32. intro UNC2. inversion UNC2.
            eapply unchanged_on_perm; eauto.
            assert (PERM4 : Mem.perm m4 b3 (o2 + d2) Cur Readable).
            eapply Mem.perm_inject; eauto.
            assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
            generalize INJ13. intro INJ13.
            eapply loc_out_of_reach_trans; eauto.
            inversion UNCHANGE4.
            erewrite unchanged_on_contents; eauto.
            generalize UNCHANGE32. intro UNC2. inversion UNC2.
            erewrite unchanged_on_contents0; eauto.
            eapply memval_inject_incr; eauto.
            inversion INJ34. inversion mi_inj.
            eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ34. apply mi_freeblocks; eauto. }
          exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
          exploit step2_perm2'_m3; eauto. instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro PERM1'.
          exploit step2_content_m3; eauto.
          destruct (subinj_dec _ _ _ _ _ INCR1 MAP1'); auto.
          exfalso. apply n. rewrite m3_support.
          inversion INJ12. exploit mi_mappedblocks; eauto.
          instantiate (1:= o2).
          replace (o2 - o2) with 0 by lia. eauto. intro.
          setoid_rewrite H.
          eapply memval_compose_2; eauto.
          inversion INJ14'. inversion mi_inj.
          eapply mi_memval; eauto.
          unfold compose_meminj.
          rewrite MAP1'. rewrite MAP2'. reflexivity.
    - intros. destruct (j2' b) as [[b3 d]|] eqn:?.
      exploit DOMIN2'; eauto.
      unfold Mem.valid_block in H.
      rewrite m3'_support in H. intro. congruence.
      reflexivity.
    - intros. destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ34. exploit mi_mappedblocks; eauto.
        unfold Mem.valid_block.
        intro. inversion UNCHANGE4. eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ14'. eapply mi_mappedblocks; eauto.
        unfold compose_meminj. rewrite MAP1',H. reflexivity.
    - 
      red. intros b2 b3 d2 b2' b3' d2' o2 o2' NEQ MAP2 MAP2' PERM2 PERM2'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2); destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + inversion INJ34. eapply mi_no_overlap; eauto.
        generalize MAXPERM2. intro MAXPERM2.
        eapply MAXPERM3; eauto. eapply DOMIN2; eauto.
        eapply MAXPERM3; eauto. eapply DOMIN2; eauto.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit IMGIN2; eauto. intro.
        exploit INCRDISJ2; eauto. intros [A B].
        left. intro. congruence.
      + exploit ADDSAME. apply e. all: eauto. intros [b1 [MAP1 SAME1]].
        exploit ADDSAME; eauto. intros [b1' [MAP1' SAME1']].
        inversion INJ14'. red in mi_no_overlap.
        assert (b1 <> b1'). intro. subst. rewrite MAP1 in MAP1'. inv MAP1'. congruence.
        eapply mi_no_overlap. eauto.
        unfold compose_meminj. rewrite MAP1, MAP2. eauto.
        unfold compose_meminj. rewrite MAP1', MAP2'. eauto.
        eapply step2_perm2'_m3. instantiate (1:= o2).
        replace (o2 - o2) with 0 by lia. eauto. eauto. eauto. eauto.
        eapply step2_perm2'_m3. instantiate (1:= o2').
        replace (o2' - o2') with 0 by lia. eauto. eauto. eauto. eauto.
    - intros.
      destruct (subinj_dec _ _ _ _ _ INCR2 H).
      + inversion INJ34. eapply mi_representable; eauto.
        generalize MAXPERM3. intro MAXPERM3.
        destruct H0.
        left. eapply MAXPERM3; eauto. 
        eapply DOMIN2; eauto.
        right.
        eapply MAXPERM3; eauto.
        eapply DOMIN2; eauto.
      + exploit ADDSAME; eauto. intros (b1 & MAP1' & SAME).
        inversion INJ14'. eapply mi_representable; eauto.
        unfold compose_meminj. rewrite MAP1',H. eauto.
        destruct H0.
        left. eapply step2_perm2'_m3; eauto. rewrite Z.sub_diag. eauto.
        right. eapply step2_perm2'_m3; eauto. rewrite Z.sub_diag. eauto.
    - intros b2 o2 b3 d2 k p MAP2' PERM3'.
      generalize INJ12'. intro INJ12'.
      destruct (subinj_dec _ _ _ _ _ INCR2 MAP2').
      + destruct (Mem.loc_in_reach_find m1 j1 b2 o2) as [[b1 o1]|] eqn:LOCIN.
        * eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
          destruct LOCIN as [MAP1 PERM1].
          apply INCR1 in MAP1 as MAP1'.
          inversion INJ14'. exploit mi_perm_inv.
          unfold compose_meminj. rewrite MAP1', MAP2'. reflexivity.
          instantiate (3:= o1). replace (o1 + (o2 - o1 + d2)) with (o2 + d2) by lia.
          eauto. intros [A | B].
          left. eapply copy_perm_m3; eauto. congruence.
          right. intro. apply B. eapply copy_perm_m3; eauto. congruence.
        * eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
          destruct (Mem.perm_dec m3' b2 o2 Max Nonempty); auto.
          left. generalize UNCHANGE32. intro UNC2.
          assert (PERM2: Mem.perm m3 b2 o2 Max Nonempty).
          inversion UNC2. eapply unchanged_on_perm; eauto.
          eapply DOMIN2; eauto.
          assert (loc_out_of_reach (compose_meminj j1 j2) m1 b3 (o2 + d2)).
          generalize INJ13. intro INJ13.
          eapply loc_out_of_reach_trans; eauto. 
          assert (PERM4: Mem.perm m4 b3 (o2 + d2) k p).
          inversion UNCHANGE4. eapply unchanged_on_perm; eauto.
          eapply IMGIN2; eauto.
          inversion INJ34. exploit mi_perm_inv. eauto. apply PERM4.
          intros [A|B]; try congruence.
          inversion UNC2. eapply unchanged_on_perm; eauto.
          eapply DOMIN2; eauto. 
      +  exploit INCRDISJ2; eauto. intros [A B].
         exploit ADDSAME; eauto. intros [b1 [MAP1' SAME]].
        inversion INJ14'. exploit mi_perm_inv.
        unfold compose_meminj. rewrite MAP1', MAP2'. replace (0 + d2) with d2 by lia.
        reflexivity. eauto.
        destruct (subinj_dec _ _ _ _ _ INCR1 MAP1').
        generalize INJ13. intro INJ13. inversion INJ13. exploit mi_mappedblocks0; eauto.
        intros [P1 | P1].
        left. eapply step2_perm1_m3; eauto. replace (o2 - o2) with 0 by lia. eauto. eauto with mem.
        right. intro. apply P1. eapply step2_perm2_m3; eauto.
        replace (o2 - o2) with 0 by lia. eauto.
  Qed.

  Theorem EXT23' : Mem.extends m2' m3'.
  Proof.
    generalize INJ12'. intro INJ12'.
    generalize INJ34'. intro INJ34'.
    constructor.
    - rewrite m2'_support. rewrite m3'_support. reflexivity.
    - constructor.
      + intros. unfold inject_id in H. inv H. rewrite Z.add_0_r.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        *
          destruct (j2 b2) as [[b3 delta2]|] eqn: Hj2b.
          -- destruct (Mem.loc_in_reach_find m1 j1 b2 ofs) as [[b1 o1]|] eqn:LOCIN.
             ++ eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
                destruct LOCIN as [MAP1 PERM1].
                exploit copy_perm; eauto. congruence. intro.
                exploit copy_perm_m3; eauto. congruence. intro.
                apply H1. apply H. auto.
             ++ eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
                generalize UNCHANGE32. intro UNC3.
                generalize UNCHANGE2. intro UNC2.
                inv UNC3. apply unchanged_on_perm. auto. unfold Mem.valid_block.
                rewrite m3_support. auto. eapply Mem.perm_extends; eauto.
                inv UNC2. apply unchanged_on_perm0. auto. auto. auto. 
          -- generalize UNCHANGE3. intro UNC3.
             generalize UNCHANGE22. intro UNC2.
             inv UNC3. apply unchanged_on_perm. auto. unfold Mem.valid_block.
             rewrite m3_support. auto. eapply Mem.perm_extends; eauto.
             inv UNC2. apply unchanged_on_perm0. auto. auto. auto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ34. apply mi_freeblocks. unfold Mem.valid_block.
            rewrite m3_support. eauto. }
          assert (exists b1 b3 d, j1' b1 = Some (b2,0) /\ j2' b2 = Some (b3 ,d)).
          apply ADDBLOCK; eauto. rewrite <- m2'_support. eapply Mem.perm_valid_block; eauto.
          destruct H as (b1 & b3 & d & Hj1' & Hj2').
          assert (MAP1: j1 b1 = None).
          {
            destruct (subinj_dec _ _ _ _ _ INCR1 Hj1').
            inversion INJ12. exploit mi_mappedblocks; eauto. auto.
          }
          exploit step2_perm2'; eauto. replace (ofs - ofs) with 0 by lia.
          eauto. intro Hp1'.
          eapply step2_perm_m3; eauto. replace (ofs - ofs) with 0 by lia.
          eauto. eauto with mem.
      + intros. unfold inject_id in H.
        inv H. apply Z.divide_0_r.
      + intros. unfold inject_id in H. inv H. rewrite Z.add_0_r.
        destruct (Mem.sup_dec b2 (Mem.support m2)).
        *
          destruct (j2 b2) as [[b3 delta2]|] eqn: Hj2b.
          -- destruct (Mem.loc_in_reach_find m1 j1 b2 ofs) as [[b1 o1]|] eqn:LOCIN.
             ++ eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
                destruct LOCIN as [MAP1 PERM1].
                destruct (Mem.perm_dec m1 b1 o1 Max Writable).
                **
                setoid_rewrite copy_content; eauto.
                setoid_rewrite copy_content_m3; eauto.
                {
                  destruct (Mem.memval_map j1' (mem_memval m1' b1 o1)); constructor.
                  reflexivity.
                }
                eapply copy_perm_2; eauto. congruence. congruence.
                eapply copy_perm_2; eauto. congruence. congruence.
                ** generalize ROUNC2. intro ROUNC2. 
                   generalize ROUNC3. intro ROUNC3.
                   apply Mem.ro_unchanged_memval_bytes in ROUNC2.
                   apply Mem.ro_unchanged_memval_bytes in ROUNC3.
                   assert (NOWRIT2: ~ Mem.perm m2 b2 ofs Max Writable).
                   intro. apply n. inversion INJ12. exploit mi_perm_inv; eauto.
                   instantiate (3:= o1). replace (o1 + (ofs - o1)) with ofs by lia. eauto.
                   intros [|]. eauto. congruence.
                   assert (PERM2: Mem.perm m2 b2 ofs Max Nonempty).
                   replace ofs with (o1 + (ofs - o1)) by lia.
                   eapply Mem.perm_inject. apply MAP1. eauto. eauto.
                   assert (NOWRIT3 : ~ Mem.perm m3 b2 ofs Max Writable).
                   intro.
                   exploit Mem.perm_extends_inv. eauto. apply H.
                   intros [|]. eauto. apply H1. eauto with mem.
                   exploit ROUNC2; eauto.
                   intros [Hp2 MVAL2]. rewrite <- MVAL2.
                   exploit ROUNC3; eauto. unfold Mem.valid_block. rewrite m3_support. eauto.
                   exploit copy_perm; eauto. congruence. intro.
                   exploit copy_perm_m3; eauto. congruence. intro.
                   apply H1. apply H. auto.
                   intros [Hp3 MVAL3]. rewrite <- MVAL3.
                   inversion EXT23. inv mext_inj. exploit mi_memval; eauto.
                   reflexivity. rewrite Z.add_0_r. auto.
             ++ eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
                generalize UNCHANGE32. intro UNC3.
                generalize UNCHANGE2. intro UNC2.
                inv UNC3. rewrite unchanged_on_contents; auto.
                inv UNC2. rewrite unchanged_on_contents0; auto.
                inversion EXT23. inv mext_inj. exploit mi_memval.
                instantiate (1:= 0). instantiate (1:= b2). reflexivity.
                apply unchanged_on_perm0; eauto. rewrite Z.add_0_r. auto.
                apply unchanged_on_perm0; eauto.
                eapply Mem.perm_extends; eauto.
                inv UNC2. 
                apply unchanged_on_perm0; eauto.
          -- generalize UNCHANGE3. intro UNC3.
             generalize UNCHANGE22. intro UNC2.
             inv UNC3. inv UNC2.
             rewrite unchanged_on_contents; auto.
             rewrite unchanged_on_contents0; auto.
             inversion EXT23. inv mext_inj. exploit mi_memval.
             instantiate (1:= 0). instantiate (1:= b2). reflexivity.
             apply unchanged_on_perm0; eauto. rewrite Z.add_0_r. auto.
             apply unchanged_on_perm0; eauto.
             eapply Mem.perm_extends; eauto.
             apply unchanged_on_perm0; eauto.
        * assert (MAP2: j2 b2 = None).
          { inversion INJ34. apply mi_freeblocks. unfold Mem.valid_block.
            rewrite m3_support. eauto. }
          assert (exists b1 b3 d, j1' b1 = Some (b2,0) /\ j2' b2 = Some (b3 ,d)).
          eapply ADDBLOCK; eauto. rewrite <- m2'_support. eapply Mem.perm_valid_block; eauto.
          destruct H as (b1 & b3 & d & Hj1' & Hj2').
          assert (MAP1: j1 b1 = None).
          {
            destruct (subinj_dec _ _ _ _ _ INCR1 Hj1').
            inversion INJ12. exploit mi_mappedblocks; eauto. auto.
          }
          setoid_rewrite step2_content; eauto.
          2:{ replace (ofs - ofs) with 0 by lia. auto. }
          setoid_rewrite step2_content_m3; eauto.
          2:{ replace (ofs - ofs) with 0 by lia. auto. }
          destruct (Mem.memval_map j1' (mem_memval m1' b1 ofs)); constructor. reflexivity.
          eapply step2_perm2'; eauto. replace (ofs - ofs) with 0 by lia. auto.
          eapply step2_perm2'; eauto. replace (ofs - ofs) with 0 by lia. auto.
    - intros b2 ofs2 k p Hp3'.
      destruct (Mem.sup_dec b2 (Mem.support m2)).
      + 
        destruct (j2 b2) as [[b3 delta2]|] eqn:j2b2.
        -- destruct (Mem.loc_in_reach_find m1 j1 b2 ofs2) as [[b1 o1]|] eqn:LOCIN.
           ++ eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
              destruct LOCIN as [MAP1 PERM1].
              exploit copy_perm; eauto. congruence. intro.
              exploit copy_perm_m3; eauto. congruence. intro.
              left. apply H. apply H0. auto.
           ++ eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
              generalize UNCHANGE32. intro UNC3. inv UNC3.
              apply unchanged_on_perm in Hp3' as Hp3.
              exploit Mem.perm_extends_inv; eauto.
              generalize UNCHANGE2. intro UNC2. inv UNC2.
              intros [A|B]. left. apply unchanged_on_perm0; eauto.
              right. rewrite <- unchanged_on_perm0; eauto. auto.
              unfold Mem.valid_block.
              rewrite m3_support. auto.
        -- generalize UNCHANGE3. intro UNC3. inv UNC3.
           eapply unchanged_on_perm in Hp3' as Hp3; eauto.
           generalize UNCHANGE22. intro UNC2.
           inversion EXT23. exploit mext_perm_inv; eauto.
           intros [A|B]. left.
           inv UNC2. apply unchanged_on_perm0; eauto with mem.
           right. intro. apply B.
           inv UNC2. apply unchanged_on_perm0; eauto with mem.
           rewrite <- Mem.valid_block_extends. 2: eauto. eauto with mem.
      + 
        assert (MAP2: j2 b2 = None).
        { inversion INJ34. apply mi_freeblocks. unfold Mem.valid_block.
          rewrite m3_support. eauto. }
        assert (exists b1 b3 d, j1' b1 = Some (b2,0) /\ j2' b2 = Some (b3 ,d)).
        eapply ADDBLOCK; eauto. rewrite <- m3'_support. eapply Mem.perm_valid_block; eauto.
        destruct H as (b1 & b3 & d' & Hj1' & Hj2').
          assert (MAP1: j1 b1 = None).
          {
            destruct (subinj_dec _ _ _ _ _ INCR1 Hj1').
            inversion INJ12. exploit mi_mappedblocks; eauto. auto.
          }
          exploit step2_perm2'_m3; eauto. replace (ofs2 - ofs2) with 0 by lia.
          eauto. intro Hp1'. left.
          eapply step2_perm; eauto. replace (ofs2 - ofs2) with 0 by lia.
          eauto. eauto with mem.
  Qed.

  
 Lemma OUT_OF_REACH_34' : forall b4 ofs4,
      loc_out_of_reach j2 m3 b4 ofs4 ->
      loc_out_of_reach (compose_meminj j1' j2') m1' b4 ofs4 ->
      loc_out_of_reach j2' m3' b4 ofs4.
  Proof.
    assert (DOMIN3: inject_dom_in j2 (Mem.support m3)).
    eapply inject_implies_dom_in; eauto.
    intros. red in H, H0. red. intros b3 d MAP2'.
    destruct (subinj_dec _ _ _ _ _ INCR2 MAP2') as [MAP2 | NONE].
    - destruct (Mem.loc_in_reach_find m1 j1 b3 (ofs4 -d )) as [[b1 o1]|] eqn:LOCIN.
      + eapply Mem.loc_in_reach_find_valid in LOCIN; eauto.
        destruct LOCIN as [MAP1 PERM1].
        intro. eapply H0. unfold compose_meminj. apply INCR1 in MAP1. rewrite MAP1.
        rewrite MAP2'. reflexivity. replace (ofs4 - (ofs4 - d  - o1 + d)) with o1 by lia.
        eapply copy_perm_m3. eauto. eauto. congruence. eauto.
      + eapply Mem.loc_in_reach_find_none in LOCIN; eauto.
        generalize UNCHANGE32. intro UNC3. intro. eapply H; eauto.
        inv UNC3. apply unchanged_on_perm. eauto. eapply DOMIN3; eauto. eauto.
    - intro. exploit ADDSAME; eauto. intros [b1 [MAP1' SAME]].
      destruct (subinj_dec _ _ _ _ _ INCR1 MAP1') as [MAP1 | NONE1 ].
      exfalso.
      exploit INCRDISJ2; eauto. intros [A B].
      generalize INJ13. intro INJ13. inv INJ13.
      exploit mi_mappedblocks; eauto.
      eapply H0; eauto. unfold compose_meminj. rewrite MAP1', MAP2'.
      rewrite Z.add_0_l. reflexivity. eapply step2_perm2'_m3; eauto.
      replace (ofs4 - d - (ofs4 - d)) with 0 by lia. eauto.
  Qed.
End CONSTR_PROOF.

Lemma injp_ext_injp__injp:
  subcklr (injp @ ext @ injp) injp.
Proof.
  red.
  intros w se1 se4 m1 m4 MSTBL14 MMEM14. destruct w as [w12 [w23 w34]].
  destruct MMEM14 as [m2 [MMEM12 [m3 [MMEM23 MMEM34]]]].
  simpl in *.
  inv MMEM12. rename f into j12. rename Hm0 into INJ12. clear Hm1. rename MMEM23 into EXT23.
  inv MMEM34. rename f into j34. rename Hm1 into INJ34. clear Hm2.
  assert (INJ14: Mem.inject (compose_meminj j12 j34) m1 m4).
  eapply Mem.inject_compose. eauto.
  eapply Mem.extends_inject_compose. eauto. eauto.
  exists (injpw (compose_meminj j12 j34) m1 m4 INJ14).
  simpl.
  repeat apply conj.
  - inv MSTBL14. inv H. inv H0. inv H1. inv H. inv H1.
    econstructor; simpl; auto.
    eapply Genv.match_stbls_compose; eauto.
  - constructor.
  - rewrite compose_meminj_id_left.
    apply inject_incr_refl.
  - intros w14' m1' m4' MMEM14' INCR14'.
    unfold rel_compose.
    clear MSTBL14.
    cbn in INCR14'.
    inv MMEM14'. rename f into j14'. rename Hm3 into INJ14'.
    cbn.
    inversion INCR14' as [? ? ? ? ? ? ? ? ROUNC1 ROUNC4 MAXPERM1 MAXPERM4 UNCHANGE1 UNCHANGE4 INCR14 DISJ14]. subst.
    generalize (inject_implies_image_in _ _ _ INJ12).
    intros IMGIN12.
    generalize (inject_implies_image_in _ _ _ INJ34).
    intros IMGIN34.
    generalize (inject_implies_dom_in _ _ _ INJ12).
    intros DOMIN12.
    generalize (inject_implies_dom_in _ _ _ INJ34).
    intros DOMIN34.
    generalize (inject_implies_dom_in _ _ _ INJ14').
    intros DOMIN14'.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE1).
    intros SUPINCL1.
    generalize (Mem.unchanged_on_support _ _ _ UNCHANGE4).
    intros SUPINCL4.
    assert (DOMIN24 : inject_dom_in j34 (Mem.support m2)).
    erewrite Mem.mext_sup; eauto. 
    generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN24 DOMIN14' SUPINCL1 INCR14 DISJ14).
    intros (j12' & j34' & m2'_sup & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME & ADDNB).
    subst.
    set (m2' := m2' m1 m2 m1' j12 j34 j12' m2'_sup INJ12).
    set (m3' := m3' m1 m2 m3 m1' j12 j34 j12' m2'_sup INJ12 EXT23).
    erewrite Mem.mext_sup in INCRDISJ23. 2: eauto.
    assert (INJ12' :  Mem.inject j12' m1' m2'). eapply INJ12'; eauto.
    assert (EXT23' :  Mem.extends m2' m3'). eapply EXT23'; eauto.
    assert (INJ34' :  Mem.inject j34' m3' m4'). eapply INJ34'; eauto.
    set (w1' := injpw j12' m1' m2' INJ12').
    set (w3' := injpw j34' m3' m4' INJ34').
    exists (w1',(tt, w3')).
    cbn.
    repeat apply conj; cbn.
    + exists m2'. split.
      repeat apply conj; constructor; auto. exists m3'. split; eauto. constructor.
    + unfold w1'. constructor; auto.
      -- eapply ROUNC2; eauto.
      -- eapply MAXPERM2; eauto.
      -- (** * main content of Lemma A.12 *)
         eapply Mem.unchanged_on_implies; eauto.
         intros. red. red in H. unfold compose_meminj.
         rewrite H. reflexivity.
      -- eapply UNCHANGE21; eauto.
    + reflexivity.
    + unfold w3'. constructor; eauto.
      -- eapply ROUNC3; eauto.
      -- eapply MAXPERM3; eauto.
      -- eapply UNCHANGE3; eauto.
      -- eapply out_of_reach_trans; eauto. eapply INJ13; eauto.
    + rewrite compose_meminj_id_left.
    apply inject_incr_refl.
Qed.
