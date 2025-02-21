Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import MultiLibs CMulti AsmMulti.
Require Import InjectFootprint CA.
Require Import CallconvBig Injp CAnew Composition ThreadLinking.


Lemma Concur_sem_c_receptive : forall L,
    receptive L -> Closed.receptive (Concur_sem_c L).
Proof.
  intros L H. unfold receptive in H.
  generalize (H (Closed.symbolenv (Concur_sem_c L))). intro H1.
  inv H1. constructor; eauto.
  - intros. 
    inv H0.
    + simpl. simpl in H3.
      exploit sr_receptive; eauto.
      intros [s2 Hs]. eexists. econstructor; eauto.
    + inv H1. eexists. simpl. eapply CMulti.step_thread_create; eauto.
    + inv H1. eexists. simpl. admit.
      (* eapply CMulti.step_switch; eauto. *)
  - red. intros. inv H0.
    + simpl in H2. exploit sr_traces; eauto.
    + simpl. lia.
    + simpl. lia.
Admitted.

Lemma query_is_pthread_create_asm_determ :
  forall L qp rp qs rp' qs',
    query_is_pthread_create_asm L qp rp qs ->
    query_is_pthread_create_asm L qp rp' qs' ->
    rp = rp' /\ qs = qs'.
Proof.
  intros. inv H. inv H0.
  rewrite MEM_CREATE in MEM_CREATE0. inv MEM_CREATE0.
  assert (P0 = P1).  apply Axioms.proof_irr. subst P0.
  rewrite MEM_ALLOCSP in MEM_ALLOCSP0. inv MEM_ALLOCSP0.
  assert (P2 = P3).  apply Axioms.proof_irr. subst P3.
  split. reflexivity.
  rewrite RS_RDX in RS_RDX0. inv RS_RDX0.
  rewrite RS_RSI in RS_RSI0. inv RS_RSI0.
  reflexivity.
Qed.

(* Lemma swtich_out_determ : forall L s s1 s2 t mem1 mem2,
    switch_out L s s1 t mem1 ->
    switch_out L s s2 t mem2 ->
    mem1 = mem2 /\ s1 = s2.
Proof.
  intros. inv H; inv H0.
  - rewrite GET_C in GET_C0. inv GET_C0.
    exploit sd_at_external_determ. apply AT_E. apply AT_E0.
*)
Lemma Concur_sem_asm_determinate : forall L,
    determinate L -> Closed.determinate (Concur_sem_asm L).
Proof.
  intros. unfold determinate in H.
  generalize (H (Closed.symbolenv (Concur_sem_asm L))).
  clear H. intro H. inv H.
  econstructor; eauto.
  - intros.
    inv H.
    + inv H0.
      -- rewrite H1 in H. inv H.
         exploit sd_determ. apply H2. apply H3. intros [A B].
         split. eauto. intros. apply B in H. subst. reflexivity.
      -- rewrite H1 in H. inv H. exfalso.
         exploit sd_at_external_nostep; eauto.
      -- inv H; rewrite H1 in GET_C; inv GET_C.
         exfalso. eapply sd_at_external_nostep; eauto.
         exfalso. eapply sd_at_external_nostep; eauto.
         exfalso. eapply sd_final_nostep; eauto.
    + inv H0.
      -- rewrite H1 in H. inv H.
         exfalso. eapply sd_at_external_nostep; eauto.
      -- rewrite H1 in H. inv H.
         exploit sd_at_external_determ. apply H2. apply H5.
         intro. inv H.
         exploit query_is_pthread_create_asm_determ.
         apply H3. apply H6. intros [A B].
         subst. exploit sd_after_external_determ.
         apply H4. apply H7. intro. subst.
         split. constructor. intro. reflexivity.
      -- inv H; rewrite H1 in GET_C; inv GET_C.
         ++ exploit sd_at_external_determ. apply H2.
            apply AT_E. intro. inv H.
            inv H3. inv Q_YIE. rewrite RS_PC in H6.
            inv H6. apply Genv.find_invert_symbol in FINDPTC.
            apply Genv.find_invert_symbol in H3.
            rewrite FINDPTC in H3. inv H3.
         ++ exploit sd_at_external_determ. apply H2.
            apply AT_E. intro. inv H.
            inv H3. inv Q_JOIN. rewrite RS_PC in RS_PC0.
            inv RS_PC0. apply Genv.find_invert_symbol in FINDPTC.
            apply Genv.find_invert_symbol in FINDPTJ.
            rewrite FINDPTC in FINDPTJ. inv FINDPTJ.
         ++ exfalso. exploit sd_final_noext; eauto.
    + inv H0.
      -- inv H1; rewrite H in GET_C; inv GET_C.
         ++ exfalso. eapply sd_at_external_nostep; eauto.
         ++ exfalso. eapply sd_at_external_nostep; eauto.
         ++ exfalso. eapply sd_final_nostep; eauto.
      -- inv H1; rewrite H in GET_C; inv GET_C.
         ++ exploit sd_at_external_determ. apply H3.
            apply AT_E. intro. inv H.
            inv H4. inv Q_YIE. rewrite RS_PC in H4.
            inv H4. apply Genv.find_invert_symbol in FINDPTC.
            apply Genv.find_invert_symbol in H1.
            rewrite FINDPTC in H1. inv H1.
         ++ exploit sd_at_external_determ. apply H3.
            apply AT_E. intro. inv H.
            inv H4. inv Q_JOIN. rewrite RS_PC in RS_PC0.
            inv RS_PC0. apply Genv.find_invert_symbol in FINDPTC.
            apply Genv.find_invert_symbol in FINDPTJ.
            rewrite FINDPTC in FINDPTJ. inv FINDPTJ.
         ++ exfalso. eapply sd_final_noext; eauto.
      -- split. constructor. intro. inv H0.
         assert (s' = s'0 /\ gmem'0 = gmem').
         {
           admit.
         }
         destruct H0. subst.
         {
           inv H2; inv H3; rewrite GET_T in GET_T0; inv GET_T0.
           - generalize (sd_after_external_determ _ _ _ _ AFT_E AFT_E0). intro. subst. reflexivity.
           - destruct WAIT_THE. destruct WAIT_THE0. rewrite H0 in H3.
             inv H3.
             rewrite GET_WAIT in GET_WAIT0. inv GET_WAIT0.
             setoid_rewrite MEM_RES in MEM_RES0. inv MEM_RES0.
             generalize (sd_after_external_determ _ _ _ _ AFT_E AFT_E0). intro. subst. reflexivity.
           - generalize (sd_initial_determ _ _ _ INITIAL INITIAL0). intro. subst.
             reflexivity.
         }
  - red. intros. inv H. exploit sd_traces; eauto.
    simpl. lia. simpl. lia.
  - intros. inv H. inv H0.
    rewrite H2 in H4. inv H4. rewrite H3 in H6. inv H6.
    rewrite H1 in H. inv H.
    exploit sd_initial_determ. apply H5. apply H8. congruence.
  - intros. inv H. red.
    intros. intro. inv H.
    + rewrite H1 in H5. inv H5.
      eapply sd_final_nostep; eauto.
    + rewrite H1 in H5. inv H5.
      eapply sd_final_noext; eauto.
    + inv H5.
      rewrite H1 in GET_C. inv GET_C.
      eapply sd_final_noext; eauto.
      rewrite H1 in GET_C. inv GET_C.
      eapply sd_final_noext; eauto.
      extlia.
  - intros. inv H. inv H0.
    rewrite H2 in H6. inv H6.
    exploit sd_final_determ. apply H5. apply H9. congruence.
Abort.

Theorem Flip_Globalsim' : forall p tp,
    let OpenC := Clight.semantics1 p in let OpenA := Asm.semantics tp in
    Closed.forward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA) ->
    Closed.backward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  


  
Theorem Flip_Globalsim : forall p tp,
    let OpenC := Clight.semantics1 p in let OpenA := Asm.semantics tp in
    GS.forward_simulation cc_compcert OpenC OpenA ->
    Closed.backward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
Proof.
  intros.
  eapply Closed.forward_to_backward_simulation.
  eapply Opensim_to_Globalsim; eauto.
  eapply Concur_sem_c_receptive. eapply Clight.semantics_receptive.
  eapply Concur_sem_asm_determinate. eapply Asm.semantics_determinate.
Qed.

