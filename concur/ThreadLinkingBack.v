Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers Asm.
Require Import LanguageInterface.
Require Import Smallstep SmallstepClosed.
Require Import ValueAnalysis.
Require Import MultiLibs CMulti AsmMulti.
Require Import Extends InjectFootprint CA.
Require Import CallconvBig Ext Injp CAnew Composition.
Require Import ThreadLinking.

Section ConcurSim.

  (** Hypothesis *)
  Variable OpenC : semantics li_c li_c.

  Variable OpenA : semantics li_asm li_asm.

  (** * Get the concurrent semantics *)

  Let ConcurC := Concur_sem_c OpenC.
  Let ConcurA := Concur_sem_asm OpenA.

  (** * Initialization *)
  Let se := CMulti.initial_se OpenC.
  Let tse := initial_se OpenA.

  Section BSIM.

    Variable bsim_index : Type.
    Variable bsim_order : bsim_index -> bsim_index -> Prop.
    Variable bsim_match_states : Genv.symtbl -> Genv.symtbl -> GS.ccworld cc_compcert -> GS.gworld cc_compcert -> bsim_index ->
                                 Smallstep.state OpenC -> Smallstep.state OpenA -> Prop.
    Hypothesis bsim_skel : skel OpenC = skel OpenA.
    Hypothesis bsim_lts : forall (se1 se2 : Genv.symtbl) (wB : GS.ccworld cc_compcert),
        GS.match_senv cc_compcert wB se1 se2 ->
        Genv.valid_for (skel OpenC) se1 ->
        GS.bsim_properties cc_compcert se1 se2 wB (OpenC se1) 
          (OpenA se2) bsim_index bsim_order (bsim_match_states se1 se2 wB).
    
    Hypothesis bsim_order_wf : well_founded bsim_order.
    (** Utilizing above properties *)
    
  Definition match_local_states := bsim_match_states se tse.

  Lemma SE_eq : se = tse.
  Proof.
    unfold se, tse. destruct OpenC, OpenA.
    unfold CMulti.initial_se. unfold initial_se.
    simpl in *. congruence.
  Qed.

  Lemma valid_se : Genv.valid_for (skel OpenC) se.
    Proof.
      unfold se. unfold CMulti.initial_se. red.
      intros.
      apply Genv.find_info_symbol in H. destruct H as [b [A B]].
      exists b,g. split. auto. split. auto.
      apply Linking.linkorder_refl.
    Qed.
    
    Lemma match_se_initial : forall m skel,
      Genv.init_mem skel = Some m ->
      Genv.match_stbls (Mem.flat_inj (Mem.support m)) (Genv.symboltbl skel) (Genv.symboltbl skel).
    Proof.
      intros. exploit Genv.init_mem_genv_sup; eauto. intro SUP.
      constructor; intros; eauto.
      - rewrite <- SUP. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
      - rewrite <- SUP. exists b2. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
      - unfold Mem.flat_inj in H0. destruct Mem.sup_dec in H0; inv H0. reflexivity.
    Qed.
         
    (** Definition of match_state *)
    Let thread_state_C := CMulti.thread_state OpenC.
    Let thread_state_A := AsmMulti.thread_state OpenA.

    (* Definition worlds : Type := NatMap.t (option cc_cainjp_world). *)


    (** Global index *)

    Definition global_index : Type := list bsim_index.
    
    Inductive global_order : global_index -> global_index -> Prop :=
    |gorder_intro : forall hd tl li1 li2,
        bsim_order li1 li2 ->
        global_order (hd ++ (li1 :: tl)) (hd ++ (li2 :: tl)).

    Lemma global_order_decrease : forall i i' li li' n,
        nth_error i n = Some li ->
        set_nth_error i n li' = Some i' ->
        bsim_order li' li ->
        global_order i' i.
    Proof.
      intros. assert (exists hd tl, i = hd ++ (li::tl) /\ length hd = n).
      eapply nth_error_split; eauto.
      destruct H2 as [hd [tl [Heqi Hl]]].
      assert (Heqi': i' = hd ++ (li' :: tl)).
      eapply set_nth_error_split; eauto.
      rewrite Heqi, Heqi'.
      constructor. eauto.
    Qed.

    
   (** prove the well_founded property of global_order*)

   Inductive global_order_n : nat -> global_index -> global_index -> Prop :=
   |gon_intro : forall n i1 i2 li1 li2 hd tl,
       length i1 = n -> bsim_order li1 li2 ->
       i1 = hd ++ (li1 :: tl) -> i2 = hd ++ (li2 :: tl) ->
       global_order_n n i1 i2.

   Lemma go_length : forall n i, length i = n ->
                            Acc global_order i <-> Acc (global_order_n n) i.
   Proof.
     intros. split; intro.
     - induction H0. constructor. intros. apply H1.
       inv H2. constructor. auto. inv H2. auto.
     - induction H0. constructor. intros. apply H1.
       inv H2. econstructor; eauto. rewrite !app_length.
       simpl. lia. inv H2. rewrite !app_length. simpl. lia.
   Qed.

   Lemma global_order_n_wf: forall n,
       well_founded (global_order_n n).
   Proof.
     induction n.
     - red. intros. constructor. intros. inv H.
       destruct hd; simpl in H0; extlia.
     - red. destruct a.
       constructor. intros. inv H. destruct hd; inv H3.
       rename a into l. rename b into a.
       revert a l.
       induction a using (well_founded_induction bsim_order_wf).
       set (Q := fun l => Acc (global_order_n (S n)) (a::l)).
       apply well_founded_induction with (R:= (global_order_n n))(P:=Q). auto.
       intros. unfold Q. unfold Q in H0.
       constructor. intros. inv H1. destruct hd; simpl in *.
       + inv H5. apply H. auto.
       + inv H5. apply H0. econstructor; eauto.
   Qed.

   Lemma well_founed_go' : forall n i, length i = n -> Acc global_order i.
   Proof.
     intros. rewrite go_length; eauto. apply global_order_n_wf.
   Qed.

   Theorem global_index_wf : well_founded global_order.
   Proof.
     red. intros. eapply well_founed_go'; eauto.
   Qed.

   
   Section Initial.
     
     Variable m0 : mem.
     Variable main_b : block.
     Variable tm0 : mem.
     Variable sp0 : block.

     Definition main_id := prog_main (skel OpenC).
     
     Hypothesis INITM: Genv.init_mem (skel OpenC) = Some m0.
     Hypothesis FINDMAIN: Genv.find_symbol se main_id = Some main_b.
     Hypothesis DUMMYSP: Mem.alloc m0 0 0 = (tm0, sp0).
     
     Let j0 := Mem.flat_inj (Mem.support m0).
     Let Hm0_ := Genv.initmem_inject (skel OpenC) INITM.

     Lemma Hm0 : Mem.inject j0 m0 tm0.
     Proof.
       eapply Mem.alloc_right_inject; eauto.
     Qed.
     
     Definition wj0 := injpw j0 m0 tm0 Hm0.

     Lemma Hvalid: Mach.valid_blockv (Mem.support tm0) (Vptr sp0 Ptrofs.zero).
     Proof.
       constructor.
       eapply Mem.valid_new_block. eauto.
     Qed.

     Lemma Hlocal: StackingproofC.pointer_tid (Mem.tid (Mem.support tm0)) (Vptr sp0 Ptrofs.zero).
     Proof.
       constructor. apply Mem.alloc_result in DUMMYSP as RES.
       subst. simpl. apply Mem.support_alloc in DUMMYSP.
       rewrite DUMMYSP. reflexivity.
     Qed.
     
     Let rs0 := initial_regset (Vptr main_b Ptrofs.zero) (Vptr sp0 Ptrofs.zero).

     Lemma Hme : Mem.extends tm0 tm0.
     Proof. eapply Mem.extends_refl. Qed.
     
     Definition init_w_cainjp := cajw wj0 main_sig rs0.
     
     Definition init_w_ext := extw tm0 tm0 Hme.
          
     Definition init_w : GS.ccworld cc_compcert :=
       (se,(row se m0,(se,(se,main_sig,(tse,(init_w_cainjp,init_w_ext)))))).


     Theorem sound_ro : sound_memory_ro se m0.
     Proof.
       eapply initial_ro_sound; eauto.
     Qed.
     
   End Initial.

   Definition initial_indexs (i: bsim_index) := i :: nil.

   Inductive match_thread_states : GS.ccworld cc_compcert -> (option (GS.ccworld cc_compcert)) -> GS.gworld cc_compcert -> bsim_index -> thread_state_C -> thread_state_A -> Prop :=
    |match_local : forall wB i sc sa wp
        (M_STATES: match_local_states wB wp i sc sa),
        match_thread_states wB None wp i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall wB i cqv rs m tm
        (M_QUERIES: GS.match_query cc_compcert wB (get_query cqv m) (rs,tm))
        (SG_STR: cqv_sg cqv = start_routine_sig),
        match_thread_states wB None (get wB) i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
    |match_returny : forall wB wA i sc sa wp wp' rs
        (M_STATES: match_local_states wB wp i sc sa)
        (WT_WA: wt_w_compcert wA)
        (WA_SIG : sig_w_compcert wA = yield_sig)
        (GET: get wA = wp')
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        match_local_states wB wp'' i' sc' sa'),
        match_thread_states wB (Some wA) wp' i (CMulti.Returny OpenC sc) (Returny OpenA sa rs)
    |match_returnj : forall wB wA i sc sa wp wp' wait vptr int rs
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)                     
        (M_STATES: match_local_states wB wp i sc sa)
        (WAIT: rs # RDI = Vint int /\ int_to_nat int = wait)
        (VPTR: Val.inject (injp_mi (injp_w_compcert wA)) vptr (rs # RSI))
        (WT_WA: wt_w_compcert wA)
        (WA_SIG : sig_w_compcert wA = pthread_join_sig)
        (GET: get wA = wp')
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        match_local_states wB wp'' i' sc' sa'),
        match_thread_states wB (Some wA) wp' i (CMulti.Returnj OpenC sc wait vptr) (Returnj OpenA sa rs)
    |match_final_sub : forall wB wp i res tres
      (VRES: Val.inject (injp_mi (injp_gw_compcert wp)) res tres),
      (* the signature for all sub threads are start_routine_sig *)
      match_thread_states wB None wp i (CMulti.Final OpenC res) (Final OpenA tres).

    Inductive match_states' : global_index -> (NatMap.t (option (GS.gworld cc_compcert))) -> CMulti.state OpenC -> state OpenA -> Prop :=
      |global_match_intro : forall threadsC threadsA cur next (worldsA : NatMap.t (option (GS.ccworld cc_compcert))) worldsB worldsP gi (w0 : GS.ccworld cc_compcert) m0 main_b wPcur tm0 sp0
      (CUR_VALID: (1 <= cur < next)%nat)
      (INDEX_LENGTH : length gi = (next -1)%nat)                      
      (INITMEM: Genv.init_mem (skel OpenC) = Some m0)
      (DUMMYSP : Mem.alloc m0 0 0 = (tm0, sp0))
      (FINDMAIN: Genv.find_symbol se main_id = Some main_b)
      (INITW: w0 = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP)
      (INITVALID: forall cqv, ~ NatMap.get 1%nat threadsC = Some (CMulti.Initial OpenC cqv))
      (MAIN_THREAD_INITW: NatMap.get 1%nat worldsB = Some w0)
      (SUB_THREAD_SIG: forall n wB, (n <> 1)%nat -> NatMap.get n worldsB = Some wB ->
                               (sig_w_compcert wB) = start_routine_sig /\
                                 cajw_sg (cainjp_w_compcert wB) = start_routine_sig )
      (CUR_GWORLD: NatMap.get cur worldsP = Some wPcur)
      (CUR_INJP_TID: cur = gw_tid wPcur /\ next = gw_nexttid wPcur)
      (FIND_TID: forall n wp, NatMap.get n worldsP = Some wp -> gw_tid wp = n /\ (1<= n < next)%nat)
      (THREADS_DEFAULTC: fst threadsC = None)
      (THREADS_DEFAULTA: fst threadsA = None)
      (THREADS: forall n, (1 <= n < next)%nat -> exists wB owA wP lsc lsa i,
            NatMap.get n worldsB = Some wB /\
              nth_error gi (n-1)%nat = Some i /\
              GS.match_senv cc_compcert wB se tse /\
              (* injp_match_stbls (injp_w_compcert wB) se tse /\ *)
              NatMap.get n threadsC = Some lsc /\
              NatMap.get n threadsA = Some lsa /\
              NatMap.get n worldsA = owA /\
              match_thread_states wB owA wP i lsc lsa /\
              NatMap.get n worldsP = Some wP /\
              (n <> cur -> gw_accg wP wPcur)
              ),
          match_states' gi worldsP (mk_gstate OpenC threadsC cur next) (mk_gstate_asm OpenA threadsA cur next).
    
    Inductive match_states : global_index -> CMulti.state OpenC -> state OpenA -> Prop :=
    |ms_intro: forall gi worldsP gsc gsa ,
        match_states' gi worldsP gsc gsa ->
        match_states gi gsc gsa.


    Lemma concur_initial_states_exist :
      forall s1, Closed.initial_state ConcurC s1 ->
            exists s2, Closed.initial_state ConcurA s2.
    Proof.
      intros. inv H.
       apply Genv.initmem_inject in H1 as Hm0.
      exploit Genv.init_mem_genv_sup; eauto. intro SUP.
      case_eq (Mem.alloc m0 0 0). intros tm0 sp0 DUMMY.
      (* set (j0 := Mem.flat_inj (Mem.support m0)).
        se   t (wj0 := injpw j0 m0 m0 Hm0). *)
      set (w0 := init_w m0 main_b tm0 sp0 H1 DUMMY). unfold init_w, wj0 in w0.
      generalize valid_se. intro VALID.
      simpl in bsim_lts.
      assert (MSE': GS.match_senv cc_compcert w0 se tse).
      (* assert (MSE': injp_match_stbls (injp_w_compcert w0) se tse). *)
      { constructor. constructor. constructor.
        constructor. constructor. constructor.
        constructor.
        constructor.  rewrite <- SE_eq. apply match_se_initial; eauto.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem. rewrite <- SE_eq.
        unfold se, CMulti.initial_se. rewrite SUP.
        apply Mem.support_alloc in DUMMY as SUPA. rewrite SUPA.
        simpl. eauto with mem.
        constructor. }
      specialize (bsim_lts se tse w0 MSE' VALID) as BSIM.
      set (rs0 := initial_regset (Vptr main_b Ptrofs.zero) (Vptr sp0 Ptrofs.zero)).
      set (q2 := (rs0,tm0)).
      set (q1 := {| cq_vf := Vptr main_b Ptrofs.zero; cq_sg := main_sig; cq_args := nil; cq_mem := m0 |}).
      assert (MQ: GS.match_query cc_compcert w0 q1 q2).
      { (* match initial query *)
        assert (NONEARG: Conventions1.loc_arguments main_sig = nil).
        unfold main_sig. unfold Conventions1.loc_arguments. destruct Archi.ptr64; simpl; eauto.
        destruct Archi.win64; simpl; eauto.
        (*ro*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        exploit sound_ro; eauto.
        (*wt*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        reflexivity. simpl. constructor.
        (*CAinjp*)
        econstructor. split. instantiate (1:= q2).
        { econstructor.
        - rewrite NONEARG. simpl. constructor.
        - econstructor. unfold Mem.flat_inj. rewrite pred_dec_true.
          reflexivity.  rewrite <- SUP.
          eapply Genv.genv_symb_range; eauto. reflexivity.
        - intros. unfold Conventions.size_arguments in H.
          rewrite NONEARG in H. simpl in H. inv H. extlia.
        - simpl. unfold Tptr. replace Archi.ptr64 with true. reflexivity.
          eauto.
        - simpl. unfold initial_regset. rewrite Pregmap.gso.
          rewrite Pregmap.gss. unfold Vnullptr. replace Archi.ptr64 with true.
            econstructor. eauto. congruence.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hvalid; eauto.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hlocal; eauto.
        - econstructor. simpl. red.
          unfold Conventions.size_arguments. rewrite NONEARG.
          reflexivity.
        - congruence.
        - unfold initial_regset. rewrite Pregmap.gso. rewrite Pregmap.gss. unfold Vnullptr.
          destruct Archi.ptr64; congruence. congruence. }
        econstructor; eauto. intros. simpl. apply val_inject_id. eauto.
        split. unfold rs0. unfold initial_regset.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gss. congruence.
        constructor.
      }
      eapply GS.bsim_match_initial_states in BSIM as FINI; eauto.
      inv FINI. exploit bsim_match_cont_exist; eauto.
      intros (s2 & A). eexists. econstructor; eauto.
      unfold AsmMulti.main_id, initial_se.
      unfold CMulti.initial_se, CMulti.main_id in H0.
      rewrite <- bsim_skel. eauto. rewrite <- bsim_skel. eauto.
    Qed.


    Ltac unfoldC_in H := 
      unfold CMulti.initial_se, CMulti.main_id,
        CMulti.update_cur_thread, CMulti.update_thread,
        CMulti.get_cur_thread, CMulti.get_thread
        in H; simpl in H.

    Ltac unfoldA_in H :=
      unfold initial_se, AsmMulti.main_id,
        AsmMulti.get_cur_thread, AsmMulti.get_thread,
        AsmMulti.update_cur_thread, AsmMulti.update_thread
        in H; simpl in H.

    Ltac unfoldC := 
      unfold CMulti.initial_se, CMulti.main_id,
        CMulti.update_cur_thread, CMulti.update_thread,
        CMulti.get_cur_thread, CMulti.get_thread
        ; simpl.

    Ltac unfoldA H :=
      unfold initial_se, AsmMulti.main_id,
        AsmMulti.get_cur_thread, AsmMulti.get_thread,
        AsmMulti.update_cur_thread, AsmMulti.update_thread
        ; simpl.
    
    Lemma concur_initial_states :
      forall s1 s2, Closed.initial_state ConcurC s1 -> Closed.initial_state ConcurA s2 ->
               exists i s1', Closed.initial_state ConcurC s1' /\ match_states i s1' s2.
    Proof.
      intros s1 s2 INIC INIA. inv INIC. inv INIA.
      unfoldC_in H. unfoldA_in H2. rewrite <- bsim_skel in H2.
      rewrite H in H2. inv H2. rewrite <- bsim_skel in H3.
      rewrite H0 in H3. inv H3. rename m0' into tm1.
      exploit Genv.init_mem_genv_sup; eauto. intro SUP.
      set (w0 := init_w m1 main_b0 tm1 sb H0 H4). unfold init_w, wj0 in w0.
      generalize valid_se. intro VALID.
      assert (MSE': GS.match_senv cc_compcert w0 se tse).
      (* assert (MSE': injp_match_stbls (injp_w_compcert w0) se tse). *)
      { constructor. constructor. constructor.
        constructor. constructor. constructor.
        constructor.
        constructor.  rewrite <- SE_eq. apply match_se_initial; eauto.
        unfold se, CMulti.initial_se. rewrite SUP. eauto with mem. rewrite <- SE_eq.
        unfold se, CMulti.initial_se. rewrite SUP.
        apply Mem.support_alloc in H4 as SUPA. rewrite SUPA.
        simpl. eauto with mem.
        constructor. }
      specialize (bsim_lts se tse w0 MSE' VALID) as BSIM.
      set (rs0 := initial_regset (Vptr main_b0 Ptrofs.zero) (Vptr sb Ptrofs.zero)).
      set (q2 := (rs0,tm1)).
      set (q1 := {| cq_vf := Vptr main_b0 Ptrofs.zero; cq_sg := main_sig; cq_args := nil; cq_mem := m1 |}).
       assert (MQ: GS.match_query cc_compcert w0 q1 q2).
      { (* match initial query *)
        assert (NONEARG: Conventions1.loc_arguments main_sig = nil).
        unfold main_sig. unfold Conventions1.loc_arguments. destruct Archi.ptr64; simpl; eauto.
        destruct Archi.win64; simpl; eauto.
        (*ro*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        exploit sound_ro; eauto.
        (*wt*)
        econstructor. split. instantiate (1:= q1). constructor. constructor.
        reflexivity. simpl. constructor.
        (*CAinjp*)
        econstructor. split. instantiate (1:= q2).
        { econstructor.
        - rewrite NONEARG. simpl. constructor.
        - econstructor. unfold Mem.flat_inj. rewrite pred_dec_true.
          reflexivity.  rewrite <- SUP.
          eapply Genv.genv_symb_range; eauto. reflexivity.
        - intros. unfold Conventions.size_arguments in H2.
          rewrite NONEARG in H2. simpl in H2. inv H2. extlia.
        - simpl. unfold Tptr. replace Archi.ptr64 with true. reflexivity.
          eauto.
        - simpl. unfold initial_regset. rewrite Pregmap.gso.
          rewrite Pregmap.gss. unfold Vnullptr. replace Archi.ptr64 with true.
            econstructor. eauto. congruence.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hvalid; eauto.
        - unfold initial_regset. rewrite Pregmap.gss.
          eapply Hlocal; eauto.
        - econstructor. simpl. red.
          unfold Conventions.size_arguments. rewrite NONEARG.
          reflexivity.
        - congruence.
        - unfold initial_regset. rewrite Pregmap.gso. rewrite Pregmap.gss. unfold Vnullptr.
          destruct Archi.ptr64; congruence. congruence. }
        econstructor; eauto. intros. simpl. apply val_inject_id. eauto.
        split. unfold rs0. unfold initial_regset.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gso; try congruence.
        rewrite Pregmap.gss. congruence.
        constructor.
      }
      eapply GS.bsim_match_initial_states in BSIM as FINI; eauto.
      inv FINI. exploit bsim_match_cont_match; eauto.
      intros (ls1' & INI1' & [i Hm]).
      exists (initial_indexs i). eexists. split.
      econstructor; eauto.
      econstructor; eauto.
      instantiate (1:= initial_worlds (get w0)).
      econstructor; eauto.
      - intros. rewrite NatMap.gss. congruence.
      - instantiate (6:= initial_worlds w0). reflexivity.
      - intros. unfold initial_worlds in H3. rewrite NatMap.gso in H3. inv H3. eauto.
      - setoid_rewrite NatMap.gss. reflexivity.
      - split. simpl. unfold gw_tid. simpl. erewrite init_mem_tid; eauto.
        unfold gw_nexttid. simpl. erewrite init_mem_nexttid; eauto.
      - intros. setoid_rewrite NatMap.gsspec in H2. destr_in H2; inv H2.
        unfold gw_tid. split; eauto. simpl. erewrite init_mem_tid; eauto.
      - intros.   assert (n=1)%nat. lia. subst. instantiate (1:= empty_worlds).
        exists w0, None, (get w0), (CMulti.Local OpenC ls1'), (Local OpenA ls0), i.
        repeat apply conj; eauto. 
        constructor. unfold match_local_states. eauto.
        congruence.
    Qed.
   
    Lemma local_star_c : forall gs t sc1 sc2,
        Star (OpenC se) sc1 t sc2 ->
        fst (CMulti.threads OpenC gs) = None ->
        NatMap.get (CMulti.cur_tid OpenC gs) (CMulti.threads OpenC gs)  = Some (CMulti.Local OpenC sc1) ->
        star (CMulti.step OpenC) (CMulti.globalenv OpenC) gs t (CMulti.update_cur_thread OpenC gs (CMulti.Local OpenC sc2)).
    Proof.
      intros. generalize dependent gs.
      induction H; intros.
      - unfold CMulti.update_cur_thread, CMulti.update_thread.
        destruct gs. simpl.
        rewrite NatMap.set3. eapply star_refl. eauto.
        simpl in H0. congruence.
      - eapply star_step; eauto.
        eapply CMulti.step_local. eauto. eauto. eauto.
        set (gs' := (CMulti.update_thread OpenC gs (CMulti.cur_tid OpenC gs) (CMulti.Local OpenC s2))).
        assert (EQ: CMulti.update_cur_thread OpenC gs (CMulti.Local OpenC s3) = CMulti.update_cur_thread OpenC gs' (CMulti.Local OpenC s3)).
        unfold gs'. unfold CMulti.update_cur_thread. simpl. unfold CMulti.update_thread.
        simpl. rewrite NatMap.set2. reflexivity.
        rewrite EQ.
        eapply IHstar; eauto.
        unfold gs'. simpl. rewrite NatMap.gss. reflexivity.
    Qed.

    (*The hypothesis is required for this lemma, it is trivially satisfied by Clight semantics *)
    Hypothesis OpenC_final_int : forall s v m,
        Smallstep.final_state (OpenC se) s (cr v m) ->
        v <> Vundef.
    
    Lemma concur_final_states: forall i s1 s2 r,
        match_states i s1 s2 -> Closed.safe ConcurC s1 ->  Closed.final_state ConcurA s2 r ->
        exists s1', star (Closed.step ConcurC) (Closed.globalenv ConcurC) s1 E0 s1' /\ Closed.final_state ConcurC s1' r.
    Proof.
      intros i s1 s2 r Hm Safe1 F2.
      inv F2. inv Hm. inv H4.
      simpl in H. subst cur.
      unfoldA H0. 
      specialize (THREADS 1%nat CUR_VALID).
      destruct THREADS as (wB & owA & wP & lsc & lsa & i' & GETWB & GETi & MSEw & GETC & GETA & GETWA & MS & GETP & ACC).
      assert (lsa = AsmMulti.Local OpenA ls).
      eapply foo; eauto. subst lsa.
      specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
      assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
      eapply foo; eauto. subst wB.
      inv MS.
      unfold match_local_states in M_STATES.
      exploit @GS.bsim_match_final_states; eauto.
      {
        clear - GETC Safe1 THREADS_DEFAULTC.
        red. red in Safe1.
        intros.
        exploit Safe1. eapply local_star_c; eauto.
        intros [[r1 Hr]|[t [s Hs]]].
        - left. inv Hr. simpl in H0. unfoldC_in H1. rewrite NatMap.gss in H1. inv H1. eauto.
        - inv Hs; unfoldC_in H0; try rewrite NatMap.gss in H0; inv H0; eauto;
            unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C; eauto.
      } 
      intros [s1' [r1 [gw' [Star1 [FIN [ACCE [ACCI MR]]]]]]]. destruct r1.
      destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
      destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]].
      inv MRro. inv MRwt. inv MRp. inv MRe.
      simpl in H, H5. unfold proj_sig_res, main_sig in H5. simpl in H5.
      eexists. split.
      eapply local_star_c; eauto.
      unfoldC. econstructor; eauto. unfoldC.
      rewrite NatMap.gss. reflexivity.
      instantiate (1:= cr_mem).
      assert (cr_retval= Vint r).
      {
        apply OpenC_final_int in FIN as Rint.
        simpl in H6. generalize (H6 RAX). intro.
        assert (tres = rs' RAX).
        subst tres. reflexivity.
        assert (Val.inject j' cr_retval (Vint r)).
        rewrite <- H2.
        rewrite <- (compose_meminj_id_right j').
        eapply val_inject_compose; eauto.
        inv H10; eauto. congruence.
      }
      rewrite <- H8. eauto.
    Qed.

    Lemma safe_concur_single : forall s ls,
        Closed.safe ConcurC s ->
        fst (CMulti.threads OpenC s) = None ->
        CMulti.get_cur_thread OpenC s = Some (CMulti.Local OpenC ls) ->
        safe (OpenC se) ls.
    Proof.
      intros s ls Hsafe GET. red. red in Hsafe. intros. exploit Hsafe.
      eapply local_star_c; eauto. simpl.
      intros [[r1 F]| [t [s1'' S]]].
      - inv F. unfoldC_in H2. rewrite NatMap.gss in H2. inv H2. eauto.
      - inv S; unfoldC_in H1.
        + rewrite NatMap.gss in H1. inv H1. eauto.
        + rewrite NatMap.gss in H1. inv H1. eauto.
        + inv H1; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C; eauto.
    Qed.

    Hypothesis determinate_big_C : determinate_big OpenC.

    Lemma pthread_create_progress: forall q_ptc r_ptc q_str qa_ptc wA,
        query_is_pthread_create OpenC q_ptc r_ptc q_str ->
        GS.match_query cc_compcert wA q_ptc qa_ptc ->
        GS.match_senv cc_compcert wA se tse ->
        exists (gw: GS.gworld cc_compcert) ra_ptc qa_str,
          query_is_pthread_create_asm OpenA qa_ptc ra_ptc qa_str
          /\ (get wA) o-> gw
          /\ GS.match_reply cc_compcert (set wA gw) r_ptc ra_ptc.
    Proof.
      intros until wA. intros H H0 MSE.
     inv H. destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
     destruct H0 as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
     inv Hqr. inv Hqw. simpl in H. destruct H0. simpl in H0. inv H0. simpl in H1.
     inv Hqca. destruct qa_ptc as [trs ttm]. inv Hqe. destruct H2 as [PCN Hme].
     inv Hme. clear Hm4. rename Hm3 into Hme.
     subst tvf targs. rewrite pthread_create_locs in H5. simpl in H5.
     inv H5. inv H17. inv H18. inv H19.
     destruct MSE as [EQ1 [EQ2 [MSE EQ3]]].
     inv EQ1. inv EQ2. inv EQ3. inv H2. inv H3.
     (** prepare arguments *)
     assert (INJPTC: j b_ptc = Some (b_ptc, 0)).
     {
       inv MSE. inv H17.
       exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDPTC.
       intros (b3 & INJ).
       exploit mge_symb; eauto.
       intro HH. apply HH in FINDPTC as FINDPTC'.
       rewrite <- SE_eq in FINDPTC'. fold se in FINDPTC. setoid_rewrite FINDPTC in FINDPTC'.
       inv FINDPTC'. eauto.
     }
     assert (PCVAL: rs PC = Vptr b_ptc Ptrofs.zero).
     inv H6. rewrite H17 in INJPTC. inv INJPTC. reflexivity.
     assert (INJSTR: j b_start = Some (b_start, 0)).
     {
       inv MSE. inv H17.
       exploit mge_dom; eauto. eapply Genv.genv_symb_range. apply FINDSTR. eauto.
       intros (b3 & INJ).
       exploit mge_symb; eauto.
       intro HH. apply HH in FINDSTR as FINDSTR'.
       rewrite <- SE_eq in FINDSTR'. fold se in FINDSTR. setoid_rewrite FINDSTR in FINDSTR'.
       inv FINDSTR'. eauto.
     }
     assert (RSIVAL: rs RSI = Vptr b_start Ptrofs.zero).
     inv H5. rewrite H17 in INJSTR. inv INJSTR. reflexivity.
     case (Mem.thread_create tm) as [tm' id] eqn:MEM_CREATE'.
     exploit thread_create_inject; eauto. intros [Hm1' eqid]. subst id.
     assert (exists b_t' ofs_t', rs RDI = Vptr b_t' ofs_t').
     inv H11. eauto. destruct H2 as [b_t' [ofs_t' RDIVAL]].
     assert (exists b_arg' ofs_arg', rs RDX = Vptr b_arg' ofs_arg').
     inv H13. eauto. destruct H2 as [b_arg' [ofs_arg' RDXVAL]].

     (** prepare memories *)
     (** Here we allocate a dummy block on new thread for target memory.
         It's address is used as the initial value of RSP on this new procedure *)
     assert (TP1: Mem.range_prop tid (Mem.support tm')).
     {
       inv P1. constructor. auto. erewrite <- inject_next_tid; eauto.
     }
     set (tm'2 := Mem.yield tm' tid TP1).
     case (Mem.alloc tm'2 0 0 ) as [tm'3 sp0] eqn:DUMMY.
     assert (TP2: Mem.range_prop (Mem.tid (Mem.support tm)) (Mem.support tm'3)).
     {
       generalize (Mem.tid_valid (Mem.support tm)). intro.
       constructor; eauto. lia.
       apply Mem.support_alloc in DUMMY. rewrite DUMMY. simpl.
       unfold Mem.next_tid, sup_incr, Mem.sup_yield. simpl.
       rewrite Mem.update_list_length. inv MEM_CREATE'. simpl.
       rewrite app_length. simpl. lia.
     }
     set (tm'4 := Mem.yield tm'3 (Mem.tid (Mem.support tm)) TP2).
     
     set (m1' := Mem.yield m1 tid P1).
     assert (Hm'2 : Mem.inject j m1' tm'2).  unfold m1', tm'2.
     eapply yield_inject. eauto.
     assert (Hmq: Mem.inject j m1' tm'3).
     eapply Mem.alloc_right_inject; eauto.
     assert (Hmr: Mem.inject j m1 tm'4).
     {
       clear - Hm1 MEM_CREATE Hmq.
       inv Hmq. constructor; eauto.
       + inv mi_thread. constructor; eauto.
         inv Hms. constructor; eauto. simpl. inv MEM_CREATE.
         simpl. eapply inject_tid; eauto.
       + inv mi_inj. constructor; eauto.
     }
          

     (** similarly we need Mem.extends tm'4 ttm'4*)
     case (Mem.thread_create ttm) as [ttm' id] eqn:MEM_CREATE'2.
     assert (Hme1: Mem.extends tm' ttm').
     {
       clear - Hme MEM_CREATE' MEM_CREATE'2.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE'2. inv Hme.
       constructor; simpl; eauto. congruence.
       inv mext_inj. constructor; eauto.
     }
     assert (tid = id).
     {
       clear -Hme MEM_CREATE' MEM_CREATE'2.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE'2. inv Hme. rewrite mext_sup. reflexivity.
     }
     subst id.
     assert (TTP1: Mem.range_prop tid (Mem.support ttm')).
     {
       erewrite <- Mem.mext_sup; eauto.
     }
     set (ttm'2 := Mem.yield ttm' tid TTP1).
     assert (Hme2: Mem.extends tm'2 ttm'2).
     apply yield_extends; eauto.
     exploit Mem.alloc_extends. apply Hme2. eauto. reflexivity. reflexivity.
     intros (ttm'3 & DUMMY2 & Hmqe).
     assert (TTP2: Mem.range_prop (Mem.tid (Mem.support ttm)) (Mem.support ttm'3)).
     {
       erewrite <- Mem.mext_sup; eauto.
       erewrite <- (Mem.mext_sup tm'3 ttm'3); eauto.
     }
     set (ttm'4 := Mem.yield ttm'3 (Mem.tid (Mem.support ttm)) TTP2).
     assert (Hmre: Mem.extends tm'4 ttm'4).
     apply yield_extends; eauto. inv Hme. congruence.
     
     set (rs_q := rs # PC <- (rs RSI) # RDI <- (rs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (rs_r := rs # PC <- (rs RA) # RAX <- (Vint Int.one)).
     set (trs_q := trs # PC <- (trs RSI) # RDI <- (trs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (trs_r := trs # PC <- (trs RA) # RAX <- (Vint Int.one)).
     rename H0 into RSLD. simpl in RSLD.
     eapply lessdef_trans in PCVAL as PCVAL'; eauto.
     eapply lessdef_trans in RSIVAL as RSIVAL'; eauto; try congruence.
     eapply lessdef_trans in RDIVAL as RDIVAL'; eauto; try congruence.
     eapply lessdef_trans in RDXVAL as RDXVAL'; eauto; try congruence.
     inv H.
     exists (tt, (tt, (injpw j m1 tm'4 Hmr, extw tm'4 ttm'4 Hmre))).
     exists (trs_r, ttm'4). exists (trs_q, ttm'3).
     assert (UNC23: Mem.unchanged_on (fun _ _ => True) tm'2 tm'3). eapply Mem.alloc_unchanged_on. eauto.
     assert (UNC23': Mem.unchanged_on (fun _ _ => True) ttm'2 ttm'3). eapply Mem.alloc_unchanged_on. eauto.
     apply Mem.support_alloc in DUMMY as HSUP.
     apply Mem.support_alloc in DUMMY2 as HSUP2. simpl.
     assert (ROACCR1 : ro_acc m m1). eapply ro_acc_thread_create; eauto.
     assert (ROACCQ1: ro_acc m m1'). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ2: ro_acc tm tm'3).
     eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= tm'2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR2: ro_acc tm tm'4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ3: ro_acc ttm ttm'3).
      eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= ttm'2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR3: ro_acc ttm ttm'4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (SINC1: Mem.sup_include (Mem.support tm) (Mem.support tm'4)).
     { inv ROACCR2. eauto. }
     assert (SINC2: Mem.sup_include (Mem.support ttm) (Mem.support ttm'4)).
     { inv ROACCR3. eauto. } 
     repeat apply conj; eauto.
     - fold se in FINDPTC. rewrite SE_eq in FINDPTC.
       fold se in FINDSTR. rewrite SE_eq in FINDSTR.
       econstructor.
       eapply FINDPTC. eapply FINDSTR. eauto. eauto. eauto. eauto. reflexivity.
       unfold trs_q. instantiate (1:= sp0). rewrite RDXVAL'.
       rewrite RSIVAL'. reflexivity.
       eauto. eauto.
       instantiate (1:= TTP1). fold ttm'2. eauto. reflexivity.
     -  simpl. inv MEM_CREATE. inv MEM_CREATE'.
       constructor; simpl; eauto; try red; intros; simpl in *; try congruence; eauto.
       assert (Mem.loadbytes tm'3 b ofs n = Some bytes). eauto.
       erewrite Mem.loadbytes_unchanged_on_1 in H17. 2: eauto. eauto.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. simpl. reflexivity.
       assert (Mem.perm tm'3 b ofs Max p). eauto.
       exploit Mem.perm_unchanged_on_2; eauto. reflexivity.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       split. split; simpl; eauto. rewrite app_length. simpl. lia. constructor; simpl; eauto. 
       red. intros. rewrite <- Mem.sup_create_in. auto. intros. reflexivity.
       split. split; simpl; eauto. rewrite HSUP. simpl. rewrite Mem.update_list_length. rewrite app_length. simpl. lia.
       constructor; eauto.
       intros. unfold tm'4. transitivity (Mem.perm tm'2 b ofs k p). reflexivity.
       transitivity (Mem.perm tm'3 b ofs k p). 2: reflexivity.
       inv UNC23. apply unchanged_on_perm; eauto. red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. transitivity (  Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b (Mem.mem_contents tm'2))).
       2: reflexivity.
       inv UNC23. apply unchanged_on_contents; eauto.
     - simpl. constructor; eauto. inv ROACCR2. eauto. inv ROACCR3. eauto.
     - econstructor; eauto.
       split. econstructor; eauto. constructor. eauto.
       eexists. split. econstructor; eauto. 
       unfold pthread_create_sig. simpl. auto.
       exists (rs_r, tm'4). split. econstructor; eauto.
       unfold pthread_create_sig. simpl.
       unfold Conventions1.loc_result. replace Archi.ptr64 with true. simpl.
       unfold rs_r. rewrite Pregmap.gss. constructor. eauto.
       intros. unfold rs_r. rewrite !Pregmap.gso; eauto.
       destruct r; simpl in H1; simpl; congruence.
       destruct r; simpl in H; simpl; congruence.
       constructor; simpl; eauto.
       intros. unfold rs_r. unfold trs_r.
       setoid_rewrite Pregmap.gsspec. destr. constructor.
       setoid_rewrite Pregmap.gsspec. destr. eauto. eauto. constructor.
    Qed.
    
    Lemma concur_progress : forall i s1 s2,
        match_states i s1 s2 -> Closed.safe ConcurC s1 ->
        (exists r, Closed.final_state ConcurA s2 r) \/ (exists t s2', Closed.step ConcurA (Closed.globalenv ConcurA) s2 t s2').
    Proof.
      intros i s1 s2 Hm Hsafe. inv Hm. inv H.
      specialize (THREADS cur CUR_VALID) as THR_CUR. 
      destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
      specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
      generalize (determinate_big_C se). intro DetC.
      inv MS. (** going to enhence [match_states] stating that the current thread is always in [local] state*)
      - specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
        exploit @GS.bsim_progress; eauto. (* exploiting the progress of local state at target level *)
        intros [[r2 F]|[[q2 X]|[t [s2' S]]]].
        + inv BSIM. exploit bsim_match_final_states; eauto.
          intros (s1''' & r1' & gw' & Hstar' & Hf1 & ACO & ACI & MR).
          (** we know source current local state can only execute [final] here*)
          exploit Hsafe; eauto. eapply local_star_c; eauto.
          intros [[r1 Fc]|[tc [s1'' Sc]]].
          -- (* source global final - possible *)
            inv Fc. unfoldC_in H. unfoldC_in H1. subst. rewrite NatMap.gss in H1. inv H1.
            assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
            eapply foo; eauto. subst wB.  unfold CMulti.OpenLTS in H2. fold se in H2.
            inv DetC. exploit sd_big_final_determ. apply Hf1. apply H2. intro. subst.
            destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
            destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]]. destruct r2.
            inv MRro. inv MRwt. inv MRp. inv MRe. left.
            eexists. econstructor. 5: eauto. eauto. eauto.
            assert (rs' PC = Vnullptr). eauto. generalize (H3 PC). simpl. intro.
            rewrite H5 in H6. unfold Vnullptr in *. destr_in H6; inv H6; eauto.
            assert (rs' RAX = Vint r1). subst tres.
            unfold Conventions1.loc_result in H8. replace Archi.ptr64 with true in H8 by reflexivity.
            simpl in H8. inv H8. reflexivity.
            generalize (H3 RAX). simpl. intro.
            rewrite H5 in H6. inv H6. reflexivity.
          -- (* source global step *)
            inv Sc.
            ++ (* source local step - contradiction*)
              unfoldC_in H. rewrite NatMap.gss in H. inv H.
              inv DetC. exfalso. eapply sd_big_final_nostep; eauto.
            ++ (* source pthread - contradiction *)
              unfoldC_in H. rewrite NatMap.gss in H. inv H.
              inv DetC. exfalso. eapply sd_big_final_noext; eauto.
            ++ inv H; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
               inv DetC. exfalso. eapply sd_big_final_noext; eauto.
               inv DetC. exfalso. eapply sd_big_final_noext; eauto.
               unfoldC_in H1. inv H1. unfoldC_in GET_T.
               destruct (Nat.eq_dec cur target).
               (*ending thread can not switch to itself*)
               subst. exfalso. rewrite NatMap.gss in GET_T. inv GET_T.
               (*switch to [tatget] *)
               rewrite !NatMap.gso in GET_T; eauto.
               generalize (THREADS )
               (* a switch from ending state - possible *)
               admit.
        + inv BSIM. exploit bsim_match_external; eauto.
          intros (wA & s1''' & q1 & Hstar' & Hx1 & ACI & MQ & MS & MR).
          (** we know source current local state can only execute [final] here*)
          exploit Hsafe; eauto. eapply local_star_c; eauto.
          intros [[r1 Fc]|[tc [s1'' Sc]]].
          -- (* source global final - contradiction *)
            inv Fc. unfoldC_in H. subst. unfoldC_in H1. rewrite NatMap.gss in H1. inv H1.
            inv DetC. exfalso. eapply sd_big_final_noext; eauto.
          -- (* source global step *)
            inv Sc.
            ++ (* source local step - contradiction*)
              unfoldC_in H. rewrite NatMap.gss in H. inv H.
              inv DetC. exfalso. eapply sd_big_at_external_nostep; eauto.
            ++ (* source pthread - possible *)
              unfoldC_in H. rewrite NatMap.gss in H. inv H.
              inv DetC. exploit sd_big_at_external_determ. apply H1. apply Hx1.
              intros. subst.
              exploit pthread_create_progress; eauto.
              intros [gw [ra_ptc [qa_str [CREATEa [ACO Mr]]]]].
              exploit MR; eauto. intro Hrex. destruct Hrex as [Hy1 Hy2].
              exploit Hy1; eauto. intros [s2' AFTER2].
              exploit Hy2; eauto. intros [s1'1 [AFTER1 [i' Hm']]].
              right. do 2 eexists. eapply step_thread_create; eauto.
            ++ inv H; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
               (*a switch from X to yield - possible*) admit.
               (*a switch from X to join - possible*) admit.
               inv DetC. exfalso. eapply sd_big_final_noext; eauto.
        + right. do 2 eexists. econstructor; eauto.
      - admit.
      - admit.
      - admit.
      - admit.
    Admitted.

   (*



      
      intros i s1 s2 Hm Hsafe. inv Hm. inv H.
      specialize (THREADS cur CUR_VALID) as THR_CUR. 
      destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
      specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
      generalize (determinate_big_C se). intro DetC.
      (* start from ls2 progress, no enough info *)
      (*
        inv MS.
      - (*local*)
        specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
        exploit @GS.bsim_progress; eauto.
        intros [[r2 F]|[[q2 X]|[t [s2' S]]]].
        + left. eexists. econstructor; eauto. *)
      exploit Hsafe; eauto.
      eapply star_refl.  intros [[r1 F]| [t [s1'' S]]].
      - (*final*)
        inv F. unfoldC_in H. unfoldC_in H0.
        assert (lsc = CMulti.Local OpenC ls).
        eapply foo; eauto. subst lsc. inv MS.
        assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
        eapply foo; eauto. subst wB.
        specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
        exploit @GS.bsim_progress; eauto.
        intros [[r2 F]| [[q2 E]|[t [sa' S]]]].
        + inv BSIM. exploit bsim_match_final_states; eauto.
          intros (s1''' & r1' & gw' & Hstar' & Hf1 & ACO & ACI & MR).
          assert (s1''' = ls /\ r1' = (cr (Vint r1) m)).
          {
            inv Hstar'. split. reflexivity. inv DetC. exploit sd_big_final_determ. apply H1. apply Hf1.
            intro. eauto. inv DetC. exfalso. eapply sd_big_final_nostep. apply H1. apply H.
          }
          destruct H. subst.
          left.
          destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
          destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]]. destruct r2.
          inv MRro. inv MRwt. inv MRp. inv MRe.
          eexists. econstructor. 5: eauto. eauto. eauto.
          assert (rs' PC = Vnullptr). eauto. generalize (H3 PC). simpl. intro.
          rewrite H6 in H7. unfold Vnullptr in *. destr_in H7; inv H7; eauto.
          assert (rs' RAX = Vint r1). subst tres.
          unfold Conventions1.loc_result in H9. replace Archi.ptr64 with true in H9 by reflexivity.
          simpl in H9. inv H9. reflexivity.
          generalize (H3 RAX). simpl. intro.
          rewrite H6 in H7. inv H7. reflexivity.
        + inv BSIM. exploit bsim_match_external; eauto.
          intros (wA & s1' & q1 & Hstar & X & ACI & MQ & MS & MR).
          inv Hstar; inv DetC; exfalso.
          -- eapply sd_big_final_noext; eauto.
          -- eapply sd_big_final_nostep; eauto.
        + right. eexists. eexists. simpl. eapply step_local; eauto.
      - inv S; unfoldC_in H. unfoldC_in H0. simpl in H0.
        + (*local*)
        assert (lsc = CMulti.Local OpenC ls1).
        eapply foo; eauto. subst lsc. inv MS.
        (* assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
        eapply foo; eauto. subst wB. *)
        specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
        exploit @GS.bsim_progress; eauto.
        intros [[r2 F]| [[q2 E]|[t' [sa' S]]]].
        -- inv BSIM. exploit bsim_match_final_states; eauto.
           intros (s1''' & r1' & gw' & Hstar' & Hf1 & ACO & ACI & MR).
           exploit Hsafe. eapply local_star_c; eauto.
           intros [[r1'2 F']| [t'2 [s1'4 S']]].
           ++
           inv F'. unfoldC_in H1. unfoldC_in H2. rewrite NatMap.gss in H2. inv H2. subst.
           assert (wB = init_w m0 main_b tm0 sp0 INITMEM DUMMYSP).
           eapply foo; eauto. subst wB. unfold CMulti.OpenLTS in H4. fold se in H4.
           inv DetC. exploit sd_big_final_determ. apply Hf1. apply H4. intro. subst.
           left. 
           destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
           destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]]. destruct r2.
           inv MRro. inv MRwt. inv MRp. inv MRe.
           eexists. econstructor. 5: eauto. eauto. eauto.
           assert (rs' PC = Vnullptr). eauto. generalize (H5 PC). simpl. intro.
           rewrite H7 in H8. unfold Vnullptr in *. destr_in H8; inv H8; eauto.
           assert (rs' RAX = Vint r1'2). subst tres.
           unfold Conventions1.loc_result in H10. replace Archi.ptr64 with true in H10 by reflexivity.
           simpl in H10. inv H10. reflexivity.
           generalize (H5 RAX). simpl. intro.
           rewrite H7 in H8. inv H8. reflexivity.
           ++ (*kind of forward step_simulation *) admit.
        -- inv BSIM. exploit bsim_match_external; eauto.
           intros (wA & s1' & q1 & Hstar & X & ACI & MQ & MS & MR).
              exploit Hsafe. eapply local_star_c; eauto.
           intros [[r1'2 F']| [t'2 [s1'4 S']]].
           ++
             inv F'. unfoldC_in H1. unfoldC_in H2.
             rewrite NatMap.gss in H2. inv H2.
             inv DetC. exfalso. eapply sd_big_final_noext; eauto.
           ++ (*kind of forward step_simulation *) admit.
        -- right. do 2 eexists. econstructor; eauto.
        +
          assert (lsc = CMulti.Local OpenC ls).
          eapply foo; eauto. subst lsc. inv MS.
          specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
          exploit @GS.bsim_progress; eauto.
          intros [[r2 F]| [[q2 E]|[t [sa' S]]]].
          -- inv BSIM. exploit bsim_match_final_states; eauto.
             intros (s1''' & r1' & gw' & Hstar' & Hf1 & ACO & ACI & MR).
             
        + admit.

Admitted *)

   
   Lemma substep_switch_out : forall i s1 s2 s2' target m',
       match_states i s1 s2 ->
       AsmMulti.switch_out OpenA s2 s2' target m' ->
       exists s1' tm' ttm' worldsP wpc f Hme' Hmj',
         CMulti.switch_out OpenC s1 s1' target ttm' /\
           match_states' i worldsP s1' s2' /\
           let cur := CMulti.cur_tid OpenC s1' in
           (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
             NatMap.get cur worldsP = Some wpc /\
           gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme'))) /\
           Mem.tid (Mem.support m') = target.
   Proof.
     intros until m'. intros MS SWITCH.
     inv MS. inv H.
     inv SWITCH.
     - (* yield *)
       specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsa = AsmMulti.Local OpenA ls).
       eapply foo; eauto. subst lsa. inv MS.
       specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
       inversion BSIM.
       clear bsim_simulation bsim_match_initial_states
         bsim_match_final_states.
   Admitted.
  
   Lemma substep_switch_in : forall i s1' s2' s1'' target m' tm' ttm' f Hmj' Hme' worldsP wpc,
       (* sth more about gtmem'*)
       let cur := CMulti.cur_tid OpenC s1' in
       match_states' i worldsP s1' s2' ->
       NatMap.get cur worldsP = Some wpc -> (** the wpc here is a world at [X] *)
       (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) ->
       gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme'))) ->
       Mem.tid (Mem.support m') = target ->
       CMulti.switch_in OpenC s1' s1'' target m' -> exists s2'' i',
           AsmMulti.switch_in OpenA s2' s2'' target ttm' /\
             match_states i' s1'' s2''.
   Proof.
   Admitted.
    

       

   Lemma local_plus_c : forall gs t sc1 sc2,
        Plus (OpenC se) sc1 t sc2 ->
        fst (CMulti.threads OpenC gs) = None ->
        NatMap.get (CMulti.cur_tid OpenC gs) (CMulti.threads OpenC gs)  = Some (CMulti.Local OpenC sc1) ->
        plus (CMulti.step OpenC) (CMulti.globalenv OpenC) gs t (CMulti.update_cur_thread OpenC gs (CMulti.Local OpenC sc2)).
    Proof.
      intros. inv H.
      econstructor; eauto.
      econstructor. eauto. eauto. eauto.
      set (gs' := CMulti.update_thread OpenC gs (CMulti.cur_tid OpenC gs) (CMulti.Local OpenC s2)).
      assert (EQ: CMulti.update_cur_thread OpenC gs (CMulti.Local OpenC sc2) = CMulti.update_cur_thread OpenC gs' (CMulti.Local OpenC sc2)).
      unfold gs'. unfoldC. rewrite NatMap.set2.
      reflexivity.
      rewrite EQ.
      eapply local_star_c; eauto.
      unfold gs'. simpl. rewrite NatMap.gss. reflexivity.
    Qed.
(*
    Lemma local_plus : forall gs t sa1 sa2,
        lus (OpenA tse) sa1 t sa2 ->
        fst (threads OpenA gs) = None ->
        NatMap.get (cur_tid OpenA gs) (threads OpenA gs)  = Some (Local OpenA sa1) ->
        plus (step OpenA) (globalenv OpenA) gs t (update_cur_thread OpenA gs (Local OpenA sa2)).
    Proo
      intros. inv H.
      econstructor; eauto.
      econstructor. eauto. eauto. eauto.
      set (gs' := update_thread OpenA gs (cur_tid OpenA gs) (Local OpenA s2)).
      assert (EQ: update_cur_thread OpenA gs (Local OpenA sa2) = update_cur_thread OpenA gs' (Local OpenA sa2)).
      unfold gs', update_cur_thread, update_thread. simpl. rewrite NatMap.set2.
      reflexivity.
      rewrite EQ.
      eapply local_star; eauto.
      unfold gs'. simpl. rewrite NatMap.gss. reflexivity.
    Qed.
 *)
    Lemma trans_pthread_create__start_routine: forall q_ptc r_ptc q_str qc_ptc rc_ptc qc_str wA,
        query_is_pthread_create_asm OpenA q_ptc r_ptc q_str ->
        query_is_pthread_create OpenC qc_ptc rc_ptc qc_str ->
        GS.match_query cc_compcert wA qc_ptc q_ptc ->
        GS.match_senv cc_compcert wA se tse ->
        exists gw wA',
            gw_accg (get wA') gw /\
            (forall w, gw_accg w (get wA) -> gw_accg w gw) /\
            (get wA) o-> gw /\
            gw_nexttid gw = S (gw_nexttid (get wA)) /\
                           GS.match_reply cc_compcert (set wA gw) rc_ptc r_ptc /\
                           GS.match_query cc_compcert wA' qc_str q_str /\
                           GS.match_senv cc_compcert wA' se tse /\
                           worlds_ptc_str (cainjp_w_compcert wA) (cainjp_w_compcert wA').
    Proof.
      intros until wA. intros Hca Hcc MQ MSE.
      inv Hca. inv Hcc.
      destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
      destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
      inv Hqr. inv Hqw. simpl in H. destruct H0. simpl in H0. inv H0. simpl in H1.
      inv Hqca. inv Hqe. destruct H2 as [PCN Hme].
      inv Hme. clear Hm4. rename Hm3 into Hme.
      subst tvf targs. rewrite pthread_create_locs in H5. simpl in H5.
      inv H5. inv H17. inv H18. inv H19.
      destruct MSE as [EQ1 [EQ2 [MSE EQ3]]].
      inv EQ1. inv EQ2. inv EQ3. inv H2. inv H3. simpl in H0.
      rename m into ttm. rename m1 into ttm1.
      rename m0 into m. rename m2 into m1. rename m3 into ttm3.
      case (Mem.thread_create tm) as [tm1 id] eqn:MEM_CREATE'.
      exploit thread_create_inject; eauto. intros [Hm1' eqid]. subst id.
      assert (exists b_t' ofs_t', rs RDI = Vptr b_t' ofs_t').
      inv H11. eauto. destruct H2 as [b_t' [ofs_t' RDIVAL]].
      assert (exists b_arg' ofs_arg', rs RDX = Vptr b_arg' ofs_arg').
      inv H13. eauto. destruct H2 as [b_arg' [ofs_arg' RDXVAL]].
      assert (TP1: Mem.range_prop tid (Mem.support tm1)).
      {
        inv P0. constructor. auto. erewrite <- inject_next_tid; eauto.
      }
      set (tm2 := Mem.yield tm1 tid TP1).
      case (Mem.alloc tm2 0 0 ) as [tm3 sp0] eqn:DUMMY.
      assert (TP2: Mem.range_prop (Mem.tid (Mem.support tm)) (Mem.support tm3)).
      {
        generalize (Mem.tid_valid (Mem.support tm)). intro.
        constructor; eauto. lia.
        apply Mem.support_alloc in DUMMY. rewrite DUMMY. simpl.
        unfold Mem.next_tid, sup_incr, Mem.sup_yield. simpl.
        rewrite Mem.update_list_length. inv MEM_CREATE'. simpl.
        rewrite app_length. simpl. lia.
      }
     set (tm4 := Mem.yield tm3 (Mem.tid (Mem.support tm)) TP2).
     
     set (m2 := Mem.yield m1 tid P0).
     assert (Hm'2 : Mem.inject j m2 tm2).
     eapply yield_inject. eauto.
     assert (Hmq: Mem.inject j m2 tm3).
     eapply Mem.alloc_right_inject; eauto.
     assert (Hmr: Mem.inject j m1 tm4).
     {
       inv Hmq. constructor; eauto.
       + inv mi_thread. constructor; eauto.
         inv Hms. constructor; eauto. simpl. inv MEM_CREATE0.
         simpl. eapply inject_tid; eauto.
       + inv mi_inj. constructor; eauto.
     }
     (** similarly we need Mem.extends tm'4 ttm'4*)
     assert (Hme1: Mem.extends tm1 ttm1).
     {
       clear - Hme MEM_CREATE' MEM_CREATE.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE. inv Hme.
       constructor; simpl; eauto. congruence.
       inv mext_inj. constructor; eauto.
     }
     assert (tid = new_tid).
     {
       clear -Hme MEM_CREATE' MEM_CREATE.
       unfold Mem.thread_create in *. inv MEM_CREATE'.
       inv MEM_CREATE. inv Hme. rewrite mext_sup. reflexivity.
     }
     subst new_tid.
     set (ttm2 := Mem.yield ttm1 tid P1).
     assert (Hme2: Mem.extends tm2 ttm2).
     apply yield_extends; eauto.
     exploit Mem.alloc_extends. apply Hme2. eauto. reflexivity. reflexivity.
     intros (ttm3' & DUMMY2 & Hmqe). fold ttm2 in MEM_ALLOCSP.
     setoid_rewrite MEM_ALLOCSP in DUMMY2. inv DUMMY2. rename ttm3' into ttm3.
     set (ttm4 := Mem.yield ttm3 (Mem.tid (Mem.support ttm)) P2).
     assert (Hmre: Mem.extends tm4 ttm4).
     apply yield_extends; eauto. inv Hme. congruence.
     rename rs into trs. rename rs0 into rs.
     set (rs_q := rs # PC <- (rs RSI) # RDI <- (rs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (rs_r := rs # PC <- (rs RA) # RAX <- (Vint Int.one)).
     set (trs_q := trs # PC <- (trs RSI) # RDI <- (trs RDX) # RSP <- (Vptr sp0 Ptrofs.zero)).
     set (trs_r := trs # PC <- (trs RA) # RAX <- (Vint Int.one)).
     rename H0 into RSLD. simpl in RSLD.
     (* eapply lessdef_trans in PCVAL as PCVAL'; eauto.
     eapply lessdef_trans in RSIVAL as RSIVAL'; eauto.
     eapply lessdef_trans in RDIVAL as RDIVAL'; eauto.
     eapply lessdef_trans in RDXVAL as RDXVAL'; eauto. *)
     inv H.
     exists (tt, (tt, (injpw j m1 tm4 Hmr, extw tm4 ttm4 Hmre))).
     exists (se, ((row se m2), (se, (se, start_routine_sig, (tse,((cajw (injpw j m2 tm3 Hmq) start_routine_sig rs_q) , extw tm3 ttm3 Hmqe))) ))).
     assert (UNC23: Mem.unchanged_on (fun _ _ => True) tm2 tm3). eapply Mem.alloc_unchanged_on. eauto.
     assert (UNC23': Mem.unchanged_on (fun _ _ => True) ttm2 ttm3). eapply Mem.alloc_unchanged_on. eauto.
     apply Mem.support_alloc in DUMMY as HSUP. rename MEM_ALLOCSP into DUMMY2.
     apply Mem.support_alloc in DUMMY2 as HSUP2. simpl.
     assert (ROACCR1 : ro_acc m m1). eapply ro_acc_thread_create; eauto.
     assert (ROACCQ1: ro_acc m m2). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ2: ro_acc tm tm3).
     eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= tm2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR2: ro_acc tm tm4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (ROACCQ3: ro_acc ttm ttm3).
      eapply ro_acc_trans. eapply ro_acc_thread_create; eauto.
     eapply ro_acc_trans. eapply ro_acc_yield. 
     instantiate (1:= ttm2). reflexivity. eapply ro_acc_alloc; eauto.
     assert (ROACCR3: ro_acc ttm ttm4). eapply ro_acc_trans. eauto. eapply ro_acc_yield; eauto. reflexivity.
     assert (SINC1: Mem.sup_include (Mem.support tm) (Mem.support tm4)).
     { inv ROACCR2. eauto. }
     assert (SINC2: Mem.sup_include (Mem.support ttm) (Mem.support ttm4)).
     { inv ROACCR3. eauto. } 
     repeat apply conj.
     - (** accg *)
       simpl. econstructor.
       econstructor; eauto; try red; intros; try congruence; eauto.
       split. split; eauto. inv MEM_CREATE0. simpl. generalize (Mem.tid_valid (Mem.support m)). intro. unfold Mem.next_tid. simpl. lia.
       inv MEM_CREATE0. constructor; eauto. simpl. red. intros. eauto with mem.
       intros. reflexivity.
       split. split; eauto.
       simpl. erewrite Mem.support_alloc; eauto. simpl. inv MEM_CREATE'. simpl.
       generalize (Mem.tid_valid (Mem.support tm)). intro. unfold Mem.next_tid. lia.
       constructor; eauto. simpl. red. intros. eauto with mem. intros. reflexivity.
       {
         unfold tm4, ttm4.
         econstructor; simpl.
         erewrite Mem.support_alloc; eauto. simpl. inv MEM_CREATE'.
         generalize (Mem.tid_valid (Mem.support tm)). intro. unfold Mem.next_tid. lia.
         erewrite Mem.support_alloc; eauto. simpl. inv MEM_CREATE.
         generalize (Mem.tid_valid (Mem.support ttm)). intro. unfold Mem.next_tid. lia.
         red. intros. eauto with mem. red. intros. eauto with mem.
         red. intros. eauto with mem. red. intros. eauto with mem.
       }
     - intros. inv H. inv MEM_CREATE0. inv MEM_CREATE'. constructor. 
       unfold injp_gw_compcert.
       simpl. inv H17.
       assert (ROACC: ro_acc m3 tm4). { eapply ro_acc_trans. 2: eauto.
       destruct H28 as [_ [A _]]. constructor; eauto. }
       econstructor; eauto.
       + inv ROACC. eauto.
       + inv ROACC. eauto.
       + destruct H27 as [[A B] C]. constructor; simpl. split. unfold Mem.next_tid, Mem.sup_create in *. simpl. rewrite app_length. simpl. lia.
         lia. inv C. constructor; simpl. eapply Mem.sup_include_trans. eauto. red. intros. rewrite <- Mem.sup_create_in. auto.
         intros. etransitivity. eauto. reflexivity. intros. etransitivity. reflexivity. eauto.
       + destruct H28 as [[A B] C]. constructor; simpl. split. etransitivity. eauto.
         unfold Mem.next_tid, Mem.sup_yield. simpl.
         rewrite HSUP. simpl. rewrite Mem.update_list_length. rewrite app_length. simpl. lia. lia.
         inv C. constructor; simpl. eapply Mem.sup_include_trans. eauto. red. intros. rewrite <- Mem.sup_yield_in.
         rewrite HSUP. apply Mem.sup_incr_in2. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
         intros. etransitivity. eauto. transitivity (Mem.perm tm2 b ofs k p). reflexivity.
         transitivity (Mem.perm tm3 b ofs k p). 2: reflexivity. inv UNC23. apply unchanged_on_perm0; eauto.
         red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
         intros. inv UNC23. rewrite unchanged_on_contents0; eauto. apply unchanged_on_perm in H0; eauto with mem.
       + inv H21. inv ROACCR2. inv ROACCR3.
         constructor; simpl. eauto. eauto.
         eapply Mem.sup_include_trans; eauto.
         eapply Mem.sup_include_trans; eauto.
         eapply max_perm_decrease_trans. apply MPD1. eauto. eauto.
         eapply max_perm_decrease_trans. apply MPD2. eauto. eauto.
     - auto.
     - auto.
     - simpl. inv MEM_CREATE0. inv MEM_CREATE'.
       constructor; simpl; eauto; try red; intros; simpl in *; try congruence; eauto.
       assert (Mem.loadbytes tm3 b ofs n = Some bytes). eauto.
       erewrite Mem.loadbytes_unchanged_on_1 in H17. 2: eauto. eauto.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. simpl. reflexivity.
       assert (Mem.perm tm3 b ofs Max p). eauto.
       exploit Mem.perm_unchanged_on_2; eauto. reflexivity.
       red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       split. split; simpl; eauto. rewrite app_length. simpl. lia. constructor; simpl; eauto. 
       red. intros. rewrite <- Mem.sup_create_in. auto. intros. reflexivity.
       split. split; simpl; eauto. rewrite HSUP. simpl. rewrite Mem.update_list_length. rewrite app_length. simpl. lia.
       constructor; eauto.
       intros. unfold tm4. transitivity (Mem.perm tm2 b ofs k p). reflexivity.
       transitivity (Mem.perm tm3 b ofs k p). 2: reflexivity.
       inv UNC23. apply unchanged_on_perm; eauto. red. simpl. rewrite <- Mem.sup_yield_in, <- Mem.sup_create_in. eauto.
       intros. transitivity (  Maps.ZMap.get ofs (NMap.get (Maps.ZMap.t memval) b (Mem.mem_contents tm2))).
       2: reflexivity.
       inv UNC23. apply unchanged_on_contents; eauto.
     - simpl. constructor; eauto. inv ROACCR2. eauto. inv ROACCR3. eauto.
     - unfold gw_nexttid. simpl. inv MEM_CREATE0. simpl. unfold Mem.sup_create. unfold Mem.next_tid.
       simpl. rewrite app_length. simpl. lia.
     - econstructor; eauto.
       split. econstructor; eauto. constructor. eauto.
       eexists. split. econstructor; eauto. 
       unfold pthread_create_sig. simpl. auto.
       exists (rs_r, tm4). split. econstructor; eauto.
       unfold pthread_create_sig. simpl.
       unfold Conventions1.loc_result. replace Archi.ptr64 with true. simpl.
       unfold rs_r. rewrite Pregmap.gss. constructor. eauto.
       intros. unfold rs_r. rewrite !Pregmap.gso; eauto.
       destruct r; simpl in H1; simpl; congruence.
       destruct r; simpl in H; simpl; congruence.
       constructor; simpl; eauto.
       intros. unfold rs_r. unfold trs_r.
       setoid_rewrite Pregmap.gsspec. destr. constructor.
       setoid_rewrite Pregmap.gsspec. destr. eauto. eauto. fold ttm4. econstructor.
     - eexists. split. econstructor; eauto. econstructor.
       eapply ro_acc_sound; eauto.
       eexists. split. econstructor; eauto. simpl. intuition auto.
       exists (rs_q, tm3). split.
       econstructor; eauto. rewrite start_routine_loc. simpl.
       constructor. unfold rs_q. rewrite Pregmap.gso; try congruence.
       rewrite Pregmap.gss. eauto.
       constructor. unfold Conventions.size_arguments.
       rewrite start_routine_loc. simpl. intros. inv H. extlia.
       unfold rs_q. rewrite Pregmap.gss. constructor.
       eapply Hvalid; eauto. eapply Hlocal; eauto.
       econstructor. unfold Conventions.tailcall_possible, Conventions.size_arguments.
       rewrite start_routine_loc. simpl. reflexivity. congruence.
       constructor; eauto. simpl. unfold rs_q, trs_q. intros.
       setoid_rewrite Pregmap.gsspec. destr. apply val_inject_id. constructor.
       setoid_rewrite Pregmap.gsspec. destr. rewrite <- RS_RDX. eauto. eauto.
       setoid_rewrite Pregmap.gsspec. destr. rewrite <- RS_RSI. eauto. eauto.
       split. unfold rs_q. rewrite Pregmap.gso; try congruence.
       rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss. inv H5. congruence.
       constructor.
     - constructor. reflexivity.
     - constructor. reflexivity.
     - inv MSE. constructor; eauto. inv ROACCQ1. eapply Mem.sup_include_trans; eauto.
     - reflexivity.
     - econstructor; eauto. reflexivity.
   Qed.
    
   Lemma concur_step :
     forall (s2 : Closed.state ConcurA) (t : trace) (s2' : Closed.state ConcurA),
       Closed.step ConcurA (Closed.globalenv ConcurA) s2 t s2' ->
       forall (i : global_index) (s1 : Closed.state ConcurC),
         match_states i s1 s2 ->
         Closed.safe ConcurC s1 ->
         exists (i' : global_index) (s1' : Closed.state ConcurC),
           (plus (Closed.step ConcurC) (Closed.globalenv ConcurC) s1 t s1' \/
              star (Closed.step ConcurC) (Closed.globalenv ConcurC) s1 t s1' /\ global_order i' i) /\
             match_states i' s1' s2'.
   Proof.
      intros. inv H.
        + (* Local *)
          inv H0. inv H. unfoldA_in H2.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
          assert (lsa = AsmMulti.Local OpenA ls1).
          eapply foo; eauto. subst lsa. inv MS.
          specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
          inversion BSIM.
          clear bsim_match_initial_states
            bsim_match_final_states bsim_match_external.
          exploit bsim_simulation; eauto. eapply safe_concur_single; eauto.
          intros (li' & s2' & STEP & MATCH).
          specialize (get_nth_set (cur-1) i li li' GETi) as SETi.
          destruct SETi as (i' & SETi & Newi & OTHERi). exists i'.
          assert (wP = wPcur). congruence. subst.
          destruct STEP.
          -- eexists. split. left.
             eapply local_plus_c; eauto. unfold update_cur_thread.
             {
               simpl. econstructor. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto. eauto.
               eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto. eauto.
               instantiate (2:= worldsP). simpl. eauto.
               destruct CUR_INJP_TID. simpl. split; eauto.
               eauto. eauto. simpl. eauto.
               intros. instantiate (1:= worldsA).
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wPcur, (CMulti.Local OpenC s2'), (Local OpenA ls2), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
               - (* clear - THREADS H3 OTHERi n0. *)
                 simpl in *.
                 destruct (THREADS n H4) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
             }
          -- destruct H. eexists. split. right. split. eapply local_star_c; eauto.
             eapply global_order_decrease; eauto.
             {
               simpl. econstructor. econstructor. simpl; eauto. simpl.
               erewrite set_nth_error_length; eauto.
               eauto. eauto.
               intros. destruct (Nat.eq_dec 1 cur). subst.
               rewrite NatMap.gss. congruence.
               rewrite NatMap.gso; eauto.
               eauto. eauto. eauto. eauto. eauto. eauto. simpl. eauto.
               intros.
               destruct (Nat.eq_dec n cur).
               - subst.
                 exists wB, None, wPcur, (CMulti.Local OpenC s2'), (Local OpenA ls2), li'.
                 repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                 rewrite NatMap.gss. reflexivity. simpl. constructor. eauto.
               - (* clear - THREADS H3 OTHERi n0. *)
                 simpl in *.
                 destruct (THREADS n H5) as (wn & ownA & wp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                 exists wn, ownA, wp, lscn,lsan,lin. repeat apply conj; eauto. rewrite <- OTHERi; eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. lia.
                 rewrite NatMap.gso. simpl. eauto. simpl. lia.
             }
        + (* pthread_create *)
           inv H0. inv H. subst.
          specialize (THREADS cur CUR_VALID) as THR_CUR.
          destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA &GETWa & MS & GETWp & ACC).
          assert (lsa = AsmMulti.Local OpenA ls).
          eapply foo; eauto. subst lsa. inv MS.
          specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
          inversion BSIM.
          clear bsim_match_initial_states
            bsim_match_final_states bsim_simulation.
          exploit bsim_match_external. eauto. eapply safe_concur_single; eauto. eauto.
          intros (wA & s1' & qc_ptc & Hstar1 & AT_PTC & APP & MQ_PTC & MS & MR).
          
          (*exploit the safe property of ClosedC to get a after_external
            all steps except for pthread_create should be ruled out *)

          assert (exists rc_ptc qc_str s1'k,
                     query_is_pthread_create OpenC qc_ptc rc_ptc qc_str /\
                     after_external (OpenC se) s1' rc_ptc s1'k).
          { specialize (determinate_big_C se) as DetC.
            exploit H1. eapply local_star_c; eauto.
            intros [[r Hr]|[t [s'' S]]].
            - inv Hr. unfoldC_in H5. subst. unfoldC_in H6. rewrite NatMap.gss in H6.
              inv H6. inv DetC. exfalso. eauto. 
            - inv S; unfoldC_in H; try rewrite NatMap.gss in H.
              + inv H. inv DetC. exfalso. eapply sd_big_at_external_nostep; eauto.
              + inv H. inv DetC. exploit sd_big_at_external_determ. apply H6. apply AT_PTC.
                intro. subst. eauto.
                (* assert (rc_ptc = r_ptc0).
                { clear - H9 PTR_TO_STR_ASM.
                  inv H9. inv PTR_TO_STR_ASM.
                  rewrite MEM_CREATE in MEM_CREATE0. inv MEM_CREATE0. reflexivity.
                }
                subst. eauto. *)
              + inv H; unfoldC_in H6; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
                -- inv DetC.  exploit sd_big_at_external_determ. apply AT_PTC. apply AT_E.
                   intro. subst. exfalso. (* clear - Q_YIE H4 AT_E MQ_PTC MS bsim_order. *)
                   inv H4. inv Q_YIE. 
                   (* Lemma cc_compcert_mq_PCinj : forall b sg args m rs tm w,
                       GS.match_query cc_compcert (cq (Vptr b Ptrofs.zero sg args m)) (rs,tm) -> *)
                   destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
                   destruct MQ_PTC as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
                   inv Hqr. inv Hqw. simpl in H1. destruct H2.
                   inv Hqca. inv Hqe. destruct H9 as [PCN Hme].
                   inv Hme. clear Hm4. rename Hm3 into Hme.
                   subst tvf targs.
                   destruct MS as [EQ1 [EQ2 [MSE EQ3]]].
                   inv EQ1. inv EQ2. inv EQ3. inv H9. inv H10. simpl in H2.
                   inv MSE. inv H13. generalize (H2 PC). intro. rewrite <- H11 in H9. inv H9. inv H27.
                   rewrite RS_PC in H24. inv H24.
                   inv H18. exploit mge_symb; eauto. intro. apply H9 in FINDPTC.
                   apply Genv.find_invert_symbol in FINDPTC.
                   apply Genv.find_invert_symbol in H.
                   unfold se in FINDPTC.
                   setoid_rewrite FINDPTC in H. inv H.
                -- inv DetC.  exploit sd_big_at_external_determ. apply AT_PTC. apply AT_E.
                   intro. subst. exfalso. clear - Q_JOIN H4 AT_E MQ_PTC MS.
                   inv H4. inv Q_JOIN.
                   destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
                   destruct MQ_PTC as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
                   inv Hqr. inv Hqw. simpl in H0. destruct H0.
                   inv Hqca. inv Hqe. destruct H2 as [PCN Hme].
                   subst tvf targs.
                   destruct MS as [EQ1 [EQ2 [MSE EQ3]]].
                   inv EQ1. inv EQ2. inv EQ3. inv H2. inv H3. simpl in H0.
                   inv MSE. inv H7. generalize (H0 PC). intro. rewrite <- H4 in H2. inv H2. inv H20.
                   rewrite RS_PC in H14. inv H14.
                   inv H5. exploit mge_symb; eauto. intro. apply H2 in FINDPTC.
                   apply Genv.find_invert_symbol in FINDPTC.
                   apply Genv.find_invert_symbol in FINDPTJ.
                   unfold se in FINDPTC.
                   setoid_rewrite FINDPTC in FINDPTJ. inv FINDPTJ.
                -- inv DetC. exfalso. eapply sd_big_final_noext; eauto.
          }
          destruct H as [rc_ptc [qc_str [s1'k [CREATE AFTER]]]].
          exploit trans_pthread_create__start_routine; eauto.
          intros (gw & wA'c & ACCGTRANS & ACCG & ACCE &NTID & MR_PTC & MQ_STR &  MS_NT & WORLDS).
          inv WORLDS.
          set (wA'c_injp := {|
                        cajw_injp := injpw j (Mem.yield m' id P1) tm''' Hm2;
                        cajw_sg := start_routine_sig;
                        cajw_rs := ((rs # PC <- (rs RSI)) # RDI <- (rs RDX)) # RSP <- (Vptr sp Ptrofs.zero) |} ).
          assert (wP = wPcur). congruence. subst wP.
          exploit MR; eauto. intro Hrex. inv Hrex.
          exploit bsim_match_cont_match; eauto.
          intros [lsa' [AFTERc [li' MSlc]]].
          specialize (get_nth_set (cur-1) i li li' GETi).
          intros (i' & SETi' & GETi' & OTHERi).
          set (i'' := i' ++ (li::nil)).
          (** li for new thread is useless, also no effect? hopefully*)
          exists i''. eexists. split.
          -- left. eapply plus_right. eapply local_star_c; eauto.
             eapply CMulti.step_thread_create; eauto. unfoldC. apply NatMap.gss. eauto.
          -- (*match_states*)
             simpl.
             set (worlds' := NatMap.set next (Some wA'c) worldsB).
             set (worldsP' := NatMap.set next (Some (get wA'c)) (NatMap.set cur (Some gw) worldsP)).
             assert (LENGTHi'' :Datatypes.length i'' = next).
             unfold i''. rewrite app_length.
             simpl. erewrite set_nth_error_length; eauto. lia.
             econstructor. econstructor. simpl. lia.
             simpl. lia.
             eauto. eauto. simpl. unfold get_cqv. simpl.
             intros. destruct (Nat.eq_dec 1 cur). subst.
             rewrite NatMap.gss. congruence.
             rewrite NatMap.gso; eauto. 
             rewrite NatMap.gso. eauto. simpl.
             rewrite NatMap.gso. eauto. lia. lia.
             instantiate (6:= worlds'). unfold worlds'.
             rewrite NatMap.gso. eauto. lia.
             intros. unfold worlds' in H8. destruct (Nat.eq_dec n next).
             subst. rewrite NatMap.gss in H8. inv H8. simpl.
             erewrite w_compcert_sig_eq. rewrite <- H. simpl. split; reflexivity.
             eauto.
             rewrite NatMap.gso in H8. eauto. eauto.
             simpl. instantiate (2:= worldsP').
             unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
             simpl.
             destruct CUR_INJP_TID as [A B]. 
             simpl. split.

             erewrite gw_acce_tid. 2: eauto.
             erewrite gw_acci_tid; eauto. rewrite NTID.
             f_equal. erewrite gw_acci_nexttid; eauto.
             { (** thread id validity *)
               unfold worldsP'.
               exploit FIND_TID. eauto. intro TIDC.
               intros. destruct (Nat.eq_dec n next).
               - subst. rewrite NatMap.gss in H7.
                 assert (WEQ: get wA'c = wp). congruence.
                 unfold gw_tid. simpl. split.
                 rewrite <- WEQ. rewrite w_get_injp_eq. rewrite <- H. simpl.
                 destruct CUR_INJP_TID as [C D].
                 apply gw_acci_nexttid in APP. rewrite <- D in APP.
                 rewrite <- APP. unfold gw_nexttid. rewrite w_get_injp_eq. rewrite <- H6.
                 simpl. inv Htc1. reflexivity. lia.
               - destruct TIDC as [X Y]. rewrite NatMap.gso in H7. 2:lia.
                 destruct (Nat.eq_dec n cur).
                 +
                   subst. rewrite NatMap.gss in H7. inv H7.
                   split. apply gw_acce_tid in ACCE. rewrite ACCE.
                   apply gw_acci_tid in APP. rewrite APP. reflexivity.
                   simpl. lia.
                 + rewrite NatMap.gso in H7. inv H7.
                   assert (injp_tid (injp_gw_compcert wp) = n).
                   { eapply FIND_TID; eauto. }
                   split. eauto. simpl. rewrite <- H7.
                   exploit FIND_TID; eauto. intros [Z1 Z2]. lia. eauto.
             }
             simpl. eauto. simpl. eauto. simpl. intros. destruct (Nat.eq_dec n next).
             ++ (* the new thread *) subst.
                instantiate (1:= NatMap.set (Datatypes.length i'') None worldsA).
               exists wA'c. exists None. eexists. eexists. eexists. eexists. repeat apply conj.
                **
                  unfold worlds'. rewrite NatMap.gss. reflexivity.
                **
                  unfold i''.
                  rewrite nth_error_app2. rewrite app_length.
                  simpl.
                  replace (Datatypes.length i' + 1 - 1 - Datatypes.length i')%nat with 0%nat by lia.
                  reflexivity. rewrite app_length. simpl. lia.
                ** eauto.
               ** rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               ** rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
               ** rewrite NatMap.gss. reflexivity.
               ** destruct q_str, qc_str.
                  econstructor. 
                  unfold get_cqv, get_query. eauto. simpl. 
                  inv CREATE. reflexivity.
               **
               unfold worldsP'. rewrite NatMap.gss. reflexivity.
               ** intros. eauto.
             ++ destruct (Nat.eq_dec n cur).
          * (*the executing thread *) subst.
            exists wB, None, gw, (CMulti.Local OpenC lsa'),(Local OpenA ls'), li'.
            repeat apply conj; eauto.
            unfold worlds'. rewrite NatMap.gso. eauto. lia.
            unfold i''. rewrite nth_error_app1. eauto. unfold i'' in CUR_VALID.
            rewrite app_length in CUR_VALID. simpl in CUR_VALID. lia.
            rewrite NatMap.gss. reflexivity.
            rewrite NatMap.gss. reflexivity.
            rewrite NatMap.gso. eauto. congruence.
            constructor. eauto.
            unfold worldsP'. rewrite NatMap.gso. rewrite NatMap.gss. reflexivity. lia.
            congruence.
          * (* uneffected threads *)
            assert (Hr: (1 <= n < next)%nat). lia.
            destruct (THREADS n Hr) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
            exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
            unfold worlds'. rewrite NatMap.gso. eauto. lia.
            unfold i''. rewrite nth_error_app1.
            rewrite <- OTHERi; eauto. lia. erewrite set_nth_error_length; eauto. lia.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto.
            repeat rewrite NatMap.gso; eauto. congruence.
            unfold worldsP'. repeat rewrite NatMap.gso; eauto.
            intros. specialize (J H8).
            exploit gw_accg_acci_accg; eauto.
            eapply match_query_wt; eauto.
        + (* switch *)
          admit.
   Admitted.
   
   Lemma Concur_BSimP : Closed.bsim_properties ConcurC ConcurA global_index global_order match_states.
      constructor. auto.
      - eapply global_index_wf.
      - eapply concur_initial_states_exist; eauto.
      - eapply concur_initial_states.
      - eapply concur_final_states.
      - eapply concur_progress.
      - eapply concur_step.
      - intros. f_equal. simpl. unfold initial_se, CMulti.initial_se. congruence.
   Qed.

   Theorem Concur_Sim : Closed.backward_simulation ConcurC ConcurA.
   Proof. econstructor. eapply Concur_BSimP. Qed.

       
  End BSIM.

  Definition final_noundef (lts : semantics li_c li_c) : Prop :=
   forall s v m se,
        Smallstep.final_state (lts se) s (cr v m) ->
        v <> Vundef.
    
    
  Lemma BSIM : GS.backward_simulation cc_compcert OpenC OpenA ->
               final_noundef OpenC ->
               determinate_big OpenC ->
               Closed.backward_simulation ConcurC ConcurA.
  Proof.
    intros. inv H. inv X. eapply Concur_Sim; eauto.
  Qed.

End ConcurSim.

