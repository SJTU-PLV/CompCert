Require Import LanguageInterface CallconvAlgebra Invariant.
Require Import CKLR Inject InjectFootprint Extends.
Require Import Linear Mach Locations Conventions.
Require Import ValueAnalysis.
Require Import Allocproof Lineartyping Asmgenproof0.
Require Import Maps Stacklayout.

Require Import CallconvBig CallConvAlgebra InjpAccoComp InjpExtAccoComp VCompBig.
Require Import Injp Ext CAnew.
Require Import Separation StackingproofC CallConv CallConvLibs.
Import GS.

Local Open Scope sep_scope.

Lemma cctrans_locset_injp_stacking : cctrans (locset_injp @ cc_stacking_injp) cc_stacking_injp.
Proof.
  constructor.
  econstructor. instantiate (1:= match_12_cctrans).
  - red. intros [w sg ls1 rs3 sp3 m3] se1 se2 q1 q2 Hse Hq.
    inv Hse. simpl in H2. inv Hq. inv H3. clear Hm Hm0.
    (* Compute  ccworld (locset_injp @ cc_stacking_injp). *)
    exists (se1, (sg, injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm1), (stkjw(injpw f m1 m2 Hm1) sg ls1 rs3 sp3 m2))).
    repeat apply conj.
    + simpl. split. econstructor; eauto. eapply match_stbls_dom; eauto.
      econstructor; eauto.
    + simpl. exists (lq vf1 sg ls1 m1). split. econstructor; simpl; eauto.
      eapply val_inject_dom; eauto. red. intros.
      inv H2.
      eapply val_inject_dom; eauto. destruct H14 as [A [B C]].
      exploit C; eauto. intros [v' [D E]].
      eapply val_inject_dom; eauto.
      econstructor; eauto.
    + simpl. constructor; eauto. rewrite meminj_dom_compose. reflexivity.
    + simpl. econstructor; eauto. intros. unfold meminj_dom in H3.
      destruct (f b1) as [[? ?]|] eqn: Hf; inv H3. congruence.
      intros. exists b2, ofs2. split. auto. unfold meminj_dom. rewrite H4.
      replace (ofs2 - ofs2) with 0 by lia. reflexivity.
    + simpl. intros r1 r3 wp1 wp2 wp1' Hmatch [Hae1 Hae2] [Hai1 Hai2] Hr.
      simpl in Hae1, Hae2. destruct wp1' as [wp11' wp12'].
      destruct wp1 as [wp11 wp12]. simpl in *.
      destruct wp11' as [j12 m1' m2' Hm1'].
      destruct wp12' as [j23 m2'_ m3' Hm2'].
      destruct Hr as [r' [Hr1 Hr2]]. inv Hr1. inv Hr2. inv H3. clear Hm'0 Hm'2 Hm'1.
      clear Hm0 Hm2 Hm3. rename m1'0 into m1'. rename m2'0 into m2'.
      exists (injpw (compose_meminj j12 j23) m1' m3' (Mem.inject_compose _ _ _ _ _ Hm1' Hm2')).
      repeat apply conj; eauto.
      -- eapply injp_comp_acce. 3: apply Hae1. 3: apply Hae2.
         econstructor; eauto.
         econstructor; eauto.
      -- inv Hmatch. eapply injp_comp_acci; eauto. econstructor; eauto.
      -- econstructor; eauto. intros.
         eapply val_inject_compose; eauto.
         intros.  red. intros.
         specialize (H25 _ _ H3). red in H25.
         unfold compose_meminj in H4. repeat destr_in H4.
         intro. exploit H25; eauto.
         replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
         eapply Mem.perm_inject; eauto.
  - red. intros wp1 wp2 w1 se1 se2 q1 q3 Hs Hq HACI Hmatch.
    inv Hmatch. destruct w1 as [x [[sg' w11] [w12 sg ls2 rs3 sp3 m3]]].
    inv HACI. simpl in H1,H2. simpl in wp1, wp2.
    (** Basiclly the same as old injp_comp (the hard part), plus a ACCI preservation *)
    destruct w11 as [j12' m1' m2' Hm12'].
    destruct w12 as [j23' m2'_ m3' Hm23'].
    destruct Hs as [Hs1 Hs2]. inv Hs1. inv Hs2.
    destruct Hq as [q2 [Hq1 Hq2]]. inv Hq1. inv Hq2. inv H5. simpl in H4. rename ls0 into ls2.
    rename m1 into m1'. rename m2 into m2'. rename m3 into m3'.
    exists (stkjw (injpw (compose_meminj j12' j23')  m1' m3' (Mem.inject_compose _ _ _ _ _ Hm12' Hm23')) sg' ls1 rs3 sp3 m3' ).
    repeat apply conj; eauto.
    + simpl. inv H; simpl in *.
      eapply injp_comp_acci; eauto.
      econstructor; eauto.
      econstructor; eauto.
    + econstructor; eauto.
      eapply Genv.match_stbls_compose; eauto.
    + simpl.
      econstructor; simpl; eauto. inv SPL. constructor.
      erewrite inject_tid; eauto.
      eapply val_inject_compose; eauto.
      intros. eapply val_inject_compose; eauto. eapply H4; eauto. constructor.
      destruct H29 as [A [B C]]. split. auto. split. auto. intros.
      exploit C; eauto. intros [v [Hl Hinj]].  exists v.
      split. eauto. eapply val_inject_compose. eapply H4; eauto. constructor. eauto.
      eauto.
      intros.  red. intros.
      specialize (H30 _ _ H5). red in H30.
      unfold compose_meminj in H11. repeat destr_in H11.
      intro. exploit H30; eauto.
      replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
      eapply Mem.perm_inject; eauto.
    + (** The accessbility construction : use acco*)
      intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1. simpl in MR.
      destruct wp2' as [j13'' m1'' m3'' Hm13']. inv MR.
      simpl in H3, H4. 
      assert (Hhidden: external_mid_hidden (injpw j12' m1' m2' Hm12') (injpw j23' m2' m3' Hm23')).
      destruct wp1 as [w w0]. destruct w, w0.  inv H0.
      exploit external_mid_hidden_acci; eauto. econstructor; eauto.
      exploit injp_acce_outgoing_constr; eauto.
      intros (j12'' & j23'' & m2'' & Hm12'' & Hm23'' & COMPOSE & ACCE1 & ACCE2 & HIDDEN & OUT).
      exists ((injpw j12'' m1'' m2'' Hm12''),(injpw j23'' m2'' m3'' Hm23'')).
      repeat apply conj; eauto.
      -- simpl.
         generalize (loc_result_always_one sg'). intro Hresult.
         destruct Hresult as [r Hresult]. rewrite Hresult in *.
         exploit H22; eauto. simpl. left. reflexivity. intro Hinjresult.
         exploit compose_meminj_midvalue. rewrite COMPOSE in Hinjresult. eauto.
         intros [vres2 [RES1 RES2]]. 
         set (ls2' l := if Loc.eq l (R r) then vres2 else ls1' l).
         exists (lr ls2' m2''). split. econstructor; eauto. simpl.
         red. intros. rewrite Hresult in H5.  inv H5. simpl.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H11.
         constructor.
         econstructor; eauto. intros. rewrite Hresult in H5. inv H5.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H11.
      -- simpl. econstructor; eauto.
Qed.
        
      
Lemma cctrans_injp_ext_ccstacking : cctrans (locset_injp @ locset_ext @ cc_stacking_injp) cc_stacking_injp.
Proof.
  constructor. econstructor. instantiate (1:= injp_ext_cctrans).
  (* Compute (GS.gworld (c_injp @ c_ext @ c_injp)). *)
  - red. intros w2 se1 se2 q1 q2 Hse Hq. inv Hse. inv Hq. simpl in H. inv H.
    simpl in H2, H3.
    rename m0 into m1. rename m3 into m2. rename f0 into f.
    exists (se1,(sg, (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m2 Hm)),(se1,(sg, extw m1 m1 (Mem.extends_refl m1), stkjw (injpw f m1 m2 Hm) sg ls1 rs2 sp2 m2 )))).
    repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. eapply match_stbls_dom; eauto.
      constructor. constructor. constructor; eauto.
    + exists (lq vf1 sg ls1 m1). split. constructor; simpl; eauto.
      eapply val_inject_dom; eauto. red. intros. inv H.
      eapply val_inject_dom; eauto.
      destruct H6 as [A [B C]]. exploit C; eauto. intros [v' [Hl Hj]].
      eapply val_inject_dom; eauto.
      exists (lq vf1 sg ls1 m1). split. constructor; simpl; eauto.
      reflexivity. red. intros. reflexivity. constructor.
      econstructor; eauto.
    + constructor. rewrite meminj_dom_compose. auto.
    + constructor. intros. unfold meminj_dom in H10.
      destr_in H10.
      intros. split. auto. eexists. eexists. split. eauto.
      unfold meminj_dom. rewrite H11. do 2 f_equal. lia.
    + intros r1 r4 [wpa [wpe wpb]] wp2 [wpa' [wpe' wpb']] MS.
      intros [ACE1 [X ACE2]] [ACI1 [ACI2 ACI3]] [r2 [Hr1 [r3 [Hr2 Hr3]]]].
      simpl in *. clear X.
      destruct wpa' as [j12 m1' m2' Hm1']. destruct wpb' as [j23 m2'_ m3' Hm2'].
      inv Hr1. inv Hr2. inv Hr3. simpl in *. inv H10. inv H15.
      clear  Hm2 Hm3 Hm4 Hm5 Hm6. clear Hm'0 Hm'1 Hm'2. rename m1'0 into m1'.
      rename m2'0 into m2'. rename m3' into m4'. rename m2'1 into m3'.
      assert (Hm': Mem.inject (compose_meminj j12 j23) m1' m4').
      eapply Mem.inject_compose. eauto.
      eapply Mem.extends_inject_compose. eauto. eauto.
      exists (injpw (compose_meminj j12 j23) m1' m4' Hm').
      repeat apply conj.
      * 
        eapply injp_ext_comp_acce.
        instantiate (2:= extw m1 m1 (Mem.extends_refl m1)). econstructor; eauto.
        instantiate (2:= extw m2' m3' Hm1). econstructor; eauto. eauto. eauto.
      * inv MS. simpl in *.
        eapply injp_ext_comp_acci. 4: apply ACI1. 4: apply ACI3. 4: apply ACI2.
        eauto. eauto. constructor; eauto.
      * econstructor; simpl; eauto.
        intros.
        eapply val_inject_compose. eauto.
        rewrite <- (compose_meminj_id_left j23).
        eapply val_inject_compose. eauto. eauto.
        red. intros. unfold compose_meminj in H11. intro Hpm1'.
        repeat destr_in H11. eapply H27; eauto.
        eapply Mem.perm_extends; eauto.
        replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
        eapply Mem.perm_inject; eauto.
  - red. intros [wpa [wpe wpb]] wp2 [se2 [w1 [se2' [[xsg we] w2]]]].
    intros se1 se3 q1 q3 [Hs1 [Hs2 Hs3]] [q2 [Hq1 [q2' [Hq2 Hq3]]]].
    intros [ACI1 [ACI2 ACI3]]. simpl in ACI1, ACI2, ACI3. 
    intros MS. inv MS. simpl in H, H0.
    destruct w1 as [sg [j12' m1' m2' Hm12']].
    destruct w2 as [[j34' m3' m4' Hm34'] xxsg ls3 rs4 sp4 xm4].
    inv H.
    inv Hq1. inv H2. inv Hq2. inv H10. simpl in H2. subst we. inv Hq3. rename ls4 into ls3.
    rename xm4 into m4'. rename m7 into m3'. rename m5 into m2'. rename m0 into m1'.
    assert (Hm14' : Mem.inject (compose_meminj j12' j34') m1' m4').
    eapply Mem.inject_compose; eauto. eapply Mem.extends_inject_compose; eauto.
    exists (stkjw (injpw (compose_meminj j12' j34') m1' m4' Hm14') sg ls1 rs4 sp4 m4').
    repeat apply conj.
    + simpl. eapply injp_ext_comp_acci; eauto.
      constructor; eauto.
      econstructor; eauto.
    + inv Hs1. inv Hs2. inv Hs3.
      constructor; eauto. eapply Genv.match_stbls_compose; eauto.
    + econstructor; simpl; eauto. inv SPL. constructor.
      erewrite inject_tid. 2: eauto. erewrite <- inject_tid; eauto.
      eapply val_inject_compose. eauto.
      rewrite <- (compose_meminj_id_left j34').
      eapply val_inject_compose. eauto. eauto.
      simpl in *.
      intros. eapply val_inject_compose. eapply H1; eauto. constructor.
      rewrite <- (compose_meminj_id_left j34').
      eapply val_inject_compose. eapply H9. constructor. eauto.
      simpl in *. destruct H22 as [A [B C]].
      split. eauto with mem. split. intros.
      exploit B; eauto. intros.
      exploit C; eauto. intros [v4 [Hl Hj]].
      exists v4. split. auto. eapply val_inject_compose. eapply H1. constructor. eauto.
       rewrite <- (compose_meminj_id_left j34').
      eapply val_inject_compose. eapply H9. constructor. eauto. eauto.
      intros. red. intros. intro Hpm1'. unfold compose_meminj in H4. repeat destr_in H4.
      eapply H23; eauto. eapply Mem.perm_extends; eauto.
      replace (ofs - z0) with (ofs - (z + z0) + z) by lia.
      eapply Mem.perm_inject; eauto.
    + intros r1 r3 wp2' ACCO1 MR. simpl in ACCO1.
      destruct wp2' as [j13'' m1'' m4'' Hm13']. inv MR.
      assert (Hhidden: external_mid_hidden_ext (injpw j12' m1' m2' Hm12') (injpw j34' m3' m4' Hm34')).
      eapply external_mid_hidden_ext_acci; eauto. inv ACI2. eauto.
      exploit injp_acce_ext_outgoing_constr; eauto.
      intros (j12'' & j34'' & m2'' & m3'' & Hm12'' & Hm34'' & COMPOSE & MEXT'' & ACCE1 & ACCE2 & HIDDEN & OUT).
      exists ((injpw j12'' m1'' m2'' Hm12''),(extw m2'' m3'' MEXT'', injpw j34'' m3'' m4'' Hm34'')).
      repeat apply conj; eauto.
      -- simpl. inv ACCE1. inv ACCE2. destruct H28 as [[A B] [C _]].
         destruct H36 as [[D E] [F _]].
         econstructor; eauto.
      -- simpl.
         rename rs2' into rs4'.
         generalize (loc_result_always_one sg). intro Hresult.
         destruct Hresult as [r Hresult]. rewrite Hresult in *.
         exploit H16; eauto. simpl. left. reflexivity. intro Hinjresult.
         exploit compose_meminj_midvalue. rewrite COMPOSE in Hinjresult. eauto.
         intros [vres2 [RES1 RES2]]. 
         set (ls2' l := if Loc.eq l (R r) then vres2 else ls1' l).
         exists (lr ls2' m2''). split. econstructor; eauto. simpl.
         red. intros. rewrite Hresult in H2.  inv H2. simpl.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H4.
         constructor.
         exists (lr ls2' m3''). split. econstructor; eauto. simpl.
         red. intros. reflexivity. constructor.
         econstructor; eauto. intros. rewrite Hresult in H2. inv H2.
         unfold ls2'.
         rewrite pred_dec_true. eauto. reflexivity. inv H4.
      -- econstructor; eauto.
Qed.
