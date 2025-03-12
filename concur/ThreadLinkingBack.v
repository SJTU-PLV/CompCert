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

   Definition injp_m (w: injp_world) : mem :=
     match w with injpw j m tm Hm => m end.
   
   Definition gw_m (gw: GS.gworld cc_compcert) : mem :=
     injp_m (injp_gw_compcert gw).
   
   Inductive match_thread_states : GS.ccworld cc_compcert -> (option (GS.ccworld cc_compcert)) -> GS.gworld cc_compcert -> bsim_index -> thread_state_C -> thread_state_A -> Prop :=
    |match_local : forall wB i sc sa wp
        (M_STATES: match_local_states wB wp i sc sa),
        match_thread_states wB None wp i (CMulti.Local OpenC sc) (Local OpenA sa)
    |match_initial : forall wB i cqv rs m tm 
        (M_QUERIES: GS.match_query cc_compcert wB (get_query cqv m) (rs,tm))
        (INIT_QUERY: exists s, Smallstep.initial_state (OpenC se) (get_query cqv m) s)
        (SG_STR: cqv_sg cqv = start_routine_sig),
        match_thread_states wB None (get wB) i (CMulti.Initial OpenC cqv) (Initial OpenA rs)
   |match_returny : forall wB wA i sc sa wp wp' rs q
        (AT_EXT: Smallstep.at_external (OpenC se) sc q)
        (WT_WA: wt_w_compcert wA)
        (WA_SIG : sig_w_compcert wA = yield_sig)
        (GET: get wA = wp')
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            bsim_match_cont (rex (match_local_states wB wp''))
              ((after_external (OpenC se)) sc r1) ((after_external (OpenA tse)) sa r2)),
          (*  (after_external (OpenC se)) sc r1 sc' ->
            exists i' sa', (after_external (OpenA tse)) sa r2 sa' /\
                        match_local_states wB wp'' i' sc' sa'), *)
        match_thread_states wB (Some wA) wp' i (CMulti.Returny OpenC sc) (Returny OpenA sa rs)
   |match_returnj : forall wB wA i sc sa wp wp' wait b ofs int rs q
        (AT_EXT: Smallstep.at_external (OpenC se) sc q)
        (RSLD: regset_lessdef (rs_w_compcert wA) rs)                     
        (WAIT: rs # RDI = Vint int /\ int_to_nat int = wait)
        (VPTR: Val.inject (injp_mi (injp_w_compcert wA)) (Vptr b ofs) (rs # RSI))
        (WT_WA: wt_w_compcert wA)
        (WA_SIG : sig_w_compcert wA = pthread_join_sig)
        (VPTR_LOCAL: fst b = gw_tid wp')
        (VPTR_PERM: Mem.valid_access (gw_m wp') Many64 b (Ptrofs.unsigned ofs) Writable)
        (GET: get wA = wp')
        (ACC1: wp *-> wp')
        (M_REPLIES: forall r1 r2 sc' wp'',
            get wA o-> wp'' ->
            GS.match_reply cc_compcert (set wA wp'') r1 r2 ->
            (after_external (OpenC se)) sc r1 sc' ->
            bsim_match_cont (rex (match_local_states wB wp''))
              ((after_external (OpenC se)) sc r1) ((after_external (OpenA tse)) sa r2)),
        match_thread_states wB (Some wA) wp' i (CMulti.Returnj OpenC sc wait (Vptr b ofs)) (Returnj OpenA sa rs)
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

    Ltac unfoldA :=
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

    Hypothesis determinate_big_C : determinate_big OpenC.

    Lemma concur_final_states: forall i s1 s2 r,
        match_states i s1 s2 -> Closed.safe ConcurC s1 ->  Closed.final_state ConcurA s2 r ->
        exists s1', star (Closed.step ConcurC) (Closed.globalenv ConcurC) s1 E0 s1' /\ Closed.final_state ConcurC s1' r.
    Proof.
      intros i s1 s2 r Hm Safe1 F2. specialize (determinate_big_C se) as DetC.
      inv F2. inv Hm. inv H4.
      simpl in H. subst cur.
      unfoldA_in H0. 
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
      intros [s1' [r1 [gw' [Star1 [FIN [ACCE [ACCI MR]]]]]]].
      (* destruct r1.
      destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
      destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]].
      inv MRro. inv MRwt. inv MRp. inv MRe.
      simpl in H, H5. unfold proj_sig_res, main_sig in H5. simpl in H5. *)
      exploit Safe1. eapply local_star_c; eauto. intros [[r1' Hr]| [t [s'' Hs]]].
      2: { unfoldC_in Hs. inv Hs; unfoldC_in H.
           - rewrite NatMap.gss in H. inv H. exfalso. inv DetC.
             eapply sd_big_final_nostep; eauto.
           - rewrite NatMap.gss in H. inv H. exfalso. inv DetC.
             eapply sd_big_final_noext; eauto.
           - inv H; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
             + exfalso. inv DetC. eapply sd_big_final_noext; eauto.
             + exfalso. inv DetC. eapply sd_big_final_noext; eauto.
             + unfoldC_in SUB_THREAD. extlia. }
      eexists. split. eapply local_star_c; eauto. inv Hr.
      unfoldC_in H. unfoldC_in H5. rewrite NatMap.gss in H5. inv H5.
      inv DetC. exploit sd_big_final_determ. apply H6. apply FIN.
      intro. subst. econstructor; unfoldC; eauto.
      rewrite NatMap.gss. reflexivity.
      assert (r = r1').
      { clear - MR H2.
        destruct gw' as [p [q [wp we]]]. simpl in p, q,wp,we.
        destruct MR as [q1' [MRro [q1'' [MRwt [q2' [MRp MRe]]]]]].
        inv MRro. inv MRwt. inv MRp. inv MRe. subst tres.
        unfold Conventions1.loc_result in H7. replace Archi.ptr64 with true in H7 by reflexivity.
        simpl in H7. simpl in H1. inv H7. generalize (H1 RAX).
        intro. rewrite <- H6 in H4. inv H4. congruence. } subst. eauto.
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
       inversion P1. constructor. auto. erewrite <- inject_next_tid; eauto.
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
       eapply FINDPTC. eapply FINDSTR.
        {
         destruct INITSTR as [sc INIc].
         set (wA'c_injp :=
                {|
                  cajw_injp := injpw j m1' tm'3 Hmq;
                  cajw_sg := start_routine_sig;
                  cajw_rs := rs_q |} ).
         set (wA'c := (se,(row se m1',(se,(se, start_routine_sig, (tse,(wA'c_injp,extw tm'3 ttm'3 Hmqe))))))).
         assert (MQ_str: GS.match_query cc_compcert wA'c (cq (Vptr b_start Ptrofs.zero) start_routine_sig
                                                            (Vptr b_arg ofs_arg :: nil) m1') (trs_q,ttm'3)).
         {
           inv ROACCR1.
           eexists. split. econstructor; eauto. simpl. constructor.
           eapply ro_acc_sound; eauto.
           eexists. split. econstructor. simpl. eauto.
           exists (rs_q,tm'3). split. econstructor; eauto. rewrite start_routine_loc.
           simpl. constructor; eauto. intros. unfold Conventions.size_arguments in H4.
           rewrite start_routine_loc in H4. simpl in H4. inv H4. extlia.
           unfold rs_q. rewrite Pregmap.gss. constructor.
           unfold rs_q. rewrite Pregmap.gss. constructor.
           eapply Mem.valid_new_block; eauto.
           unfold rs_q. rewrite Pregmap.gss. constructor.
           apply Mem.alloc_result in DUMMY as XX. subst sp0.
           erewrite Mem.support_alloc; eauto. reflexivity.
           econstructor. red. unfold Conventions.size_arguments. rewrite start_routine_loc. reflexivity.
           congruence.
           econstructor; eauto. simpl. unfold rs_q, trs_q.
           intros r. 
           destruct (Pregmap.elt_eq r RSP). subst. rewrite !Pregmap.gss. eapply val_inject_id. eauto.
           rewrite Pregmap.gso; eauto. rewrite Pregmap.gso with (j := RSP); eauto.
           destruct (Pregmap.elt_eq r RDI). subst. rewrite !Pregmap.gss. eauto.
           rewrite Pregmap.gso; eauto. rewrite Pregmap.gso with (j := RDI); eauto.
           destruct (Pregmap.elt_eq r PC). subst. rewrite !Pregmap.gss. eauto.
           rewrite Pregmap.gso; eauto. rewrite Pregmap.gso with (j := PC); eauto.
           split. unfold rs_q. rewrite Pregmap.gso; try congruence.
           rewrite Pregmap.gso; try congruence. rewrite Pregmap.gss. congruence.
           constructor.
         }
         assert (MSE_str: GS.match_senv cc_compcert wA'c se tse).
         split. simpl. constructor. reflexivity.
         split. constructor. reflexivity.
         split. inv MSE. constructor. eauto.
         unfold m1'.
         eapply Mem.sup_include_trans. eauto. red. intros. simpl. inv ROACCR1. erewrite <- Mem.sup_yield_in; eauto.
         eapply Mem.sup_include_trans; eauto. reflexivity.
         generalize valid_se. intro VALID.
         specialize (bsim_lts se tse wA'c MSE_str VALID) as BSIM.
         inv BSIM.
         exploit bsim_match_initial_states. eauto. intros [Hi1 Hi2].
         eauto.
       }
       
       eauto. eauto. eauto. eauto. reflexivity.
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

    Lemma match_r_ntid : forall w gw res m ar,
        GS.match_reply cc_compcert (set w gw) (cr res m) ar ->
        Mem.next_tid (Mem.support m) = gw_nexttid gw.
    Proof.
      intros.  destruct w as (a & b & c & d & e & f & g). simpl in g.
      destruct gw as (ga & gb & gc & gd). simpl in *.
      destruct H as (qc1 & H1 & qc2 & H2 & qa1 & H3 & H4). 
      inv H1. inv H2. inv H3. destruct ar. inv H4. simpl.
      destruct b. inv H. destruct d. destruct f. simpl in H1. inv H1.
      unfold gw_nexttid. simpl. reflexivity.
    Qed.

    Inductive local_star_c_safe_states : CMulti.state OpenC -> CMulti.state OpenC -> Prop :=
    |local_star_intro : forall sc sc' lsc lsc'
        (GETcur: CMulti.get_cur_thread OpenC sc = Some (CMulti.Local OpenC lsc))
        (Starl: Star (OpenC se) lsc E0 lsc')
        (Safe: safe (OpenC se) lsc)
        (SETcur: sc' = CMulti.update_cur_thread OpenC sc (CMulti.Local OpenC lsc')),
        local_star_c_safe_states sc sc'.

    Lemma substep_switch_in_progress : forall i s1' s2' s1'' target m' tm' ttm' f Hmj' Hme' worldsP wpc,
        (* sth more about gtmem'*)
        let cur := CMulti.cur_tid OpenC s1' in
        match_states' i worldsP s1' s2' ->
        NatMap.get cur worldsP = Some wpc -> (** the wpc here is a world at [X] *)
        (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) ->
        gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme'))) ->
        Mem.tid (Mem.support m') = target ->
        CMulti.switch_in OpenC s1' s1'' target m' -> exists s2'',
            AsmMulti.switch_in OpenA s2' s2'' target ttm'.
              (* match_states i' s1'' s2''. *)
    Proof.
  intros until wpc. intros cur MS' GETwpc NOTINIT ACCY TID_TARGET SWITCH.
     assert (RANGE: (1 <= target < CMulti.next_tid OpenC s1')%nat).
     {
       inv ACCY. simpl. inv MS'. simpl. simpl in cur. subst cur.
       assert ((tt,(tt,(injpw f m1 m2 Hmj,extw m2 m3 Hme0))) = wPcur).
       congruence.
       destruct CUR_INJP_TID. rewrite H1. rewrite <- H. simpl. unfold gw_nexttid. simpl.
       inv H2. eauto.
     }
     inv MS'. set (target := Mem.tid (Mem.support m')).
     simpl in cur. subst cur. rename cur0 into cur.
     destruct (Nat.eq_dec cur target).
     - (*switch to self*)
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (wpc = wP). congruence. subst wpc.
       inv SWITCH.
       + (*yield*)
         assert (lsc = CMulti.Returny OpenC ls1).
         eapply foo; eauto. subst lsc. inv MS. 
         assert (get wA = wPcur). clear -GETWp CUR_GWORLD.
         rewrite CUR_GWORLD in GETWp. inv GETWp. reflexivity.
         subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD.
         inv ACCY.
         assert (ACCEJ: injp_acce (get_injp wAca) (injpw f m' tm' Hmj')).
         { eapply injp_acc_yield_acce. eauto. rewrite <- H. inv H3.
           econstructor; eauto. eauto. }
         assert (ACCEE: ext_acce (extw m2 m3 Hme0) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (get_injp wAca) = injp_tid (injpw f m' tm' Hmj')).
           eauto. eapply ext_acc_yield_acce; eauto. inv H8. econstructor; eauto.
           simpl. rewrite <- H in BASE. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite BASE.
           erewrite inject_tid; eauto.
         }
         set (qc := cr Vundef m'). rename rs into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (trs' := Pregmap.set PC (trs RA) trs).
         set (r_a := (rs', tm')).
         set (tr_a := (trs', ttm')).
         exploit M_REPLIES; eauto. 
         instantiate (1:= (tt, (tt, (injpw f m' tm' Hmj', extw tm' ttm' Hme')))).
         repeat apply conj; simpl; eauto.
         instantiate (1:= tr_a). unfold tr_a.
         { 
           eexists. split. instantiate (1:= cr Vundef m').
           econstructor; eauto. constructor.
           inv WT_WA. simpl in ACCEJ. inv ACCEJ. constructor; eauto. destruct H14 as [_ [A _]]. auto.
           eexists. split. econstructor; eauto. constructor.
           exists r_a. split. unfold r_a. simpl. destruct wAca. simpl. destruct cajw_injp.
           econstructor; eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; simpl; eauto. unfold rs_w_compcert in RSLD. simpl in RSLD.
           unfold rs', trs'. intros. setoid_rewrite Pregmap.gsspec.
           destr; apply val_inject_id; eauto. constructor.
         }
         intros [Hy1 Hy2]. exploit Hy1; eauto. intros [sa' Hf].
         eexists.
         (*switch_in*)
         econstructor; eauto.
       + (*join*)
         assert (lsc = CMulti.Returnj OpenC ls1 tar' vptr).
         eapply foo; eauto. subst lsc. inv MS.
         assert (get wA = wPcur). clear -GETWp CUR_GWORLD.
         rewrite CUR_GWORLD in GETWp. inv GETWp. reflexivity. subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD. inv ACCY.
         assert (ACCEJ: injp_acce (get_injp wAca) (injpw f m' tm' Hmj')).
         { eapply injp_acc_yield_acce. rewrite <- H. inv H3.
           econstructor; eauto. eauto. }
         assert (ACCEE: ext_acce (extw m2 m3 Hme0) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (get_injp wAca) = injp_tid (injpw f m' tm' Hmj')).
           eauto. eapply ext_acc_yield_acce; eauto. inv H8. econstructor; eauto.
           simpl. rewrite <- H in BASE. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite BASE.
           erewrite inject_tid;eauto.
         }
         specialize (THREADS tar' RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsct = CMulti.Final OpenC res ).   eapply foo; eauto. subst lsct.
         inv MSt.
         exploit ACCt. congruence. intro ACCt'.
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m'). rename rs into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         set (trs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (trs RA) trs)).
         unfold injp_w_compcert in VPTR. simpl in VPTR.
         setoid_rewrite <- H in VPTR. simpl in VPTR.
         exploit Mem.storev_mapped_inject.
         2: eauto. eauto.
         eauto. simpl in ACCt'. unfold get_injp in ACCt'.
         unfold get_injp in H. rewrite <- H in ACCt'.
         eapply val_inject_incr. 2: eauto. inv ACCt'.
         inv H7. simpl. eauto.
         intros [tm''[MEM_RES' Hmj'']].
         set (r_a := (rs', tm'')).
         exploit Mem.storev_extends; eauto.
         intros [ttm'' [MEM_RES'' Hme'']].
         set (tr_a := (trs', ttm'')).
         set (wpj' := injpw f m'' tm'' Hmj'').
         set (wp' := (tt,(tt, (wpj', extw tm'' ttm'' Hme'')))).
         assert (ACCEJ2: injp_acce (get_injp wAca) wpj').
         {
           eapply injp_acce_storev; eauto.  
         }
         assert (ACCEE2: ext_acce (extw m2 m3 Hme0) (extw tm'' ttm'' Hme'')).
         { etransitivity. eauto.
         exploit ext_acci_storev. apply MEM_RES'. apply MEM_RES''. eauto. eauto. }
         exploit M_REPLIES; eauto.
         instantiate (1:= (tt,(tt,(injpw f m'' tm'' Hmj'', extw tm'' ttm'' Hme'')))).
         repeat eapply conj; simpl; eauto. 
         instantiate (1:= tr_a). unfold tr_a. simpl.
         { (* match_reply *)
           eexists. split. econstructor. constructor.
           inv WT_WA. simpl in ACCEJ2. unfold wpj' in ACCEJ2. inv ACCEJ2.
           destruct H15 as [_ [X _]]. constructor; eauto.
           eexists. split. econstructor. inv WT_WA. unfold sig_w_compcert in WA_SIG.
           simpl in WA_SIG. rewrite WA_SIG. simpl. auto.
           exists r_a. split. unfold r_a. simpl.
           destruct wAca. simpl in *.
           econstructor; eauto.  inv WT_WA. unfold sig_w_compcert in WA_SIG.
           simpl in WA_SIG. rewrite WA_SIG.
           unfold Conventions1.loc_result.
           replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
           intros. unfold rs'.
           destruct r; simpl in H0; inv H0; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           constructor. simpl. intros. unfold rs', trs'.
           setoid_rewrite Pregmap.gsspec. destr; eapply val_inject_id; eauto.
           setoid_rewrite Pregmap.gsspec. destr; eapply val_inject_id; eauto.
           eapply val_inject_id; eauto.
           eapply val_inject_id; eauto. constructor.
         }
         intros [Hy1 Hy2]. exploit Hy1; eauto. intros [sa' Hy].
         eexists.
         eapply switch_in_join; eauto.
       + (*initial, impossible*)
         simpl in *. exfalso. eapply NOTINIT. eauto.
     -  (*switch to others*)
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       exploit ACC. eauto. intro ACCG.
       inv SWITCH.
       + (*yield*)
         assert (lsc = CMulti.Returny OpenC ls1).
         eapply foo; eauto. subst lsc. inv MS. simpl in *.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD. inv ACCY.
         inv ACCG. rewrite <- H in *. rename m5 into m2'0. rename m6 into m3'0.
         rename m4 into m1'0.
         assert (ACCEJ: injp_acce (injpw j m1'0 m2'0 Hmj1) (injpw f m' tm' Hmj')).
         { eapply injp_accg_yield_acce; eauto. 
           inv H3. econstructor; eauto. }
         assert (ACCEE: ext_acce (extw m2'0 m3'0 Hme1) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (injpw j m1'0 m2'0 Hmj1) = injp_tid (injpw f m' tm' Hmj')). eauto.
           eapply ext_accg_yield_acce; eauto. inv H7. econstructor; eauto.
           simpl. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite <- BASE.
           erewrite inject_tid; eauto.
         }
         set (qc := cr Vundef m'). rename rs into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (trs' := Pregmap.set PC (trs RA) trs).
         set (r_a := (rs', tm')).
         set (tr_a := (trs', ttm')).
         exploit M_REPLIES; eauto.
         instantiate (1:= (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme')))).
         repeat apply conj; simpl; eauto.
         instantiate (1:= tr_a). unfold tr_a.
         { (*match_reply*)
           instantiate (1:= qc). unfold qc.
           eexists. split. econstructor; eauto. constructor.
           inv WT_WA. simpl in H. inv H. inv ACCEJ.
           destruct H16 as [_ [A _]].
           constructor; eauto.
           eexists. split. econstructor; eauto. inv WT_WA.
           unfold sig_w_compcert in WA_SIG. simpl in WA_SIG.
           rewrite WA_SIG. simpl. auto.
           exists (r_a). unfold r_a. split. destruct wAca.
           econstructor; eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; eauto. simpl.
           intros. unfold rs', trs'. setoid_rewrite Pregmap.gsspec.
           destr; eapply val_inject_id; eauto.
           constructor.
         }
         intros [Hy1 Hy2]. exploit Hy1; eauto. intros [sa' Hy].
         eexists.
         (*switch_in*)
         econstructor; eauto.
       + (*join*)
         assert (lsc = CMulti.Returnj OpenC ls1 tar' vptr).
         eapply foo; eauto. subst lsc. inv MS.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD, ACCG, VPTR.
         unfold injp_w_compcert in VPTR. simpl in VPTR.
         exploit gw_accg_yield_acce; eauto. constructor.
         intro ACCE. destruct ACCE as [_ [_ [ACCEJ ACCEE]]].
         simpl in ACCEJ, ACCEE. rename rs into trs.
         destruct wAca as [wAj sig rs]. simpl in VPTR.
         unfold sig_w_compcert in WA_SIG. simpl in WA_SIG, ACCEJ.
         (* get the waited thread state *)
         specialize (THREADS tar' RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsct = CMulti.Final OpenC res ).   eapply foo; eauto. subst lsct.         
         inv MSt.
         assert (ACCT: gw_accg wPt wPcur \/ wPcur = wPt).
         {
           destruct (Nat.eq_dec tar' cur). subst. right. congruence.
           left. eapply ACCt; eauto.
         }
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m').
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         set (trs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (trs RA) trs)).
         exploit Mem.storev_mapped_inject; eauto.
         inv ACCEJ. 
         eapply val_inject_incr. 2: eauto. simpl. eauto.
         eapply val_inject_incr. 2: eauto.
         {
           destruct ACCT. inv ACCY. inv H. simpl. inv H6. eauto.
           inv ACCY. eauto.
         }
         intros [tm''[MEM_RES' Hmj'']].
         set (r_a := (rs', tm'')).
         exploit Mem.storev_extends; eauto.
         intros [ttm'' [MEM_RES'' Hme'']].
         set (tr_a := (trs', ttm'')).
         set (wpj' := injpw f m'' tm'' Hmj'').
         set (wp' := (tt,(tt,(wpj', extw tm'' ttm'' Hme'')))).
         
         assert (ACCEJ': injp_acce (wAj) wpj').
         eapply injp_acce_storev; eauto. simpl in *. inv ACCEJ. eauto.
         assert (ACCEE' : ext_acce wAe (extw tm'' ttm'' Hme'')).
         etransitivity. eauto. exploit ext_acci_storev. apply MEM_RES'. eauto. eauto.
         eauto.
         simpl in H1. inv WT_WA. simpl in ACC1. unfold rs_w_compcert in RSLD. simpl in RSLD.
         simpl in HwaTid.
                  
         exploit M_REPLIES; eauto. simpl. instantiate (1:= wp').
         repeat apply conj; eauto.
         { instantiate (1:= tr_a). unfold tr_a.
           eexists. split. econstructor; eauto. constructor.
           eapply ro_acc_trans. instantiate (1:= m'). inv ACCEJ. destruct H11 as [_ [A _]].
           constructor; eauto. unfold Mem.storev in MEM_RES. destr_in MEM_RES.
           eapply ro_acc_store; eauto.
           eexists. split. econstructor; eauto. constructor.
           exists r_a. unfold r_a. split.
           econstructor; eauto. unfold Conventions1.loc_result.
           replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; eauto. simpl. intros. unfold rs', trs'.
           setoid_rewrite Pregmap.gsspec. destr; eauto. eapply val_inject_id; eauto.
           setoid_rewrite Pregmap.gsspec. destr; eauto. constructor. }
         intros [Hy1 Hy2]. exploit Hy1; eauto. intros [sa' Hy].
         eexists.
         (*switch_in*)
         eapply switch_in_join; eauto.
       + (* initial *)
         assert (lsc = CMulti.Initial OpenC cqv).
         eapply foo; eauto. subst lsc. inv MS.
         assert (wpc = wPcur). congruence. subst wpc.
         exploit ACC. eauto. intro ACCG_wB_wPcur.
         set (wpj' := injpw f m' tm' Hmj').
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
         exploit gw_accg_yield_acce. eauto. eauto.
         eauto. constructor. intro ACCG1.
         remember wB as wBi.
         destruct wBi as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & [wBj sig'' rsB] & wBe).
         simpl in ACCG, ACC, GETWp, HwaTid, ACCG_wB_wPcur, ACCG1.
         set (wB' := (se0,
           ({| ro_symtbl := se0'; ro_mem := m' |},
           (se1,
             (se1', sig', (se2, ({| cajw_injp := wpj'; cajw_sg := sig''; cajw_rs := rsB |}, extw tm' ttm' Hme'))))))).
         rename rs into trs.

         (*break the M_QUERIRES and MSEw*)
         destruct M_QUERIES as [qc' [Hq1 [qc'' [Hq2 [qa'' [Hq3 Hq4]]]]]].
         destruct cqv. inv Hq1. inv H. inv Hq2. inv H.
         simpl in *. inv Hq3. inv Hq4. destruct H0. inv H4. rename tm into ttm. rename tm1 into tm. rename rsB into rs. simpl in H.
         destruct ACCG1 as [_ [_ [ACCGJ ACCGE]]].
         simpl in ACCGJ, ACCGE.
         assert (MQ_CUR: GS.match_query cc_compcert wB'
                           (cq cqv_vf start_routine_sig cqv_args m') (trs, ttm')).
         {
           subst targs tsp0. 
           assert (Hincr :inject_incr j f).
           inv ACCGJ. eauto. 
           eexists. split. econstructor; eauto. constructor.
           eapply ro_acc_sound; eauto. inv ACCGJ.
           destruct H24 as [_ [? _]]. constructor; eauto.
           eexists. split. econstructor; simpl; eauto.
           exists (rs, tm'). split. simpl.
           econstructor; simpl; eauto.
           rewrite start_routine_loc in H9. simpl in H9. 
           rewrite start_routine_loc. simpl.
           eapply val_inject_list_incr; eauto.
           intros. unfold Conventions.size_arguments in H4.
           setoid_rewrite start_routine_loc in H4. simpl in H4. inv H4. extlia.
           inv ACCGJ. inv H15.
           econstructor. simpl. apply H25. eauto.
           inv ACCGJ. inv H16. econstructor. destruct H25 as [[_ B] _]. congruence.
           econstructor.  red. unfold Conventions.size_arguments.
           rewrite start_routine_loc. simpl. auto.
           constructor. simpl. eauto.
           split; eauto. constructor.
         }
         destruct MSEw as (A & B & C & D). inv A. inv B. inv C.
         assert (MSEw' : GS.match_senv cc_compcert wB' se tse).
         {
           split. constructor. reflexivity.
           split; constructor. reflexivity.
           inv ACCGJ. constructor. eapply Genv.match_stbls_incr_noglobal; eauto.
           destruct H27 as [P [Q R]]. eauto.
           destruct H28 as [P [Q R]]. eauto.
           reflexivity.
         }
         specialize (bsim_lts se tse wB' MSEw' valid_se) as BSIM.
         exploit @GS.bsim_match_initial_states. eauto. eauto.
         intros [Hi1 Hi2]. exploit Hi1; eauto. intros [sa Hi].
         eexists.
         (* switin_in_initial *)
         eapply switch_in_initial. eauto. eauto. eauto.
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
      inv MS. 
      - specialize (safe_concur_single _ _ Hsafe THREADS_DEFAULTC GETC). intro Hsafel.
        exploit @GS.bsim_progress; eauto. (* exploiting the progress of local state at target level *)
        intros [[r2 F]|[[q2 X]|[t [s2' S]]]].
        + (** target local LTS does [final_state] *)
          inv BSIM. exploit bsim_match_final_states; eauto.
          intros (s1''' & r1' & gw' & Hstar' & Hf1 & ACO & ACI & MR).
          (** we know source current local state can only execute [final] because of determinacy *)
          exploit Hsafe; eauto. eapply local_star_c; eauto.
          intros [[r1 Fc]|[tc [s1'' Sc]]].
          -- (* source global final - possible *)
            inv Fc. unfoldC_in H. subst cur. unfoldC_in H1. subst. rewrite NatMap.gss in H1. inv H1.
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
            ++ (** source switch - possible, but only the final-switch *)
              assert (wP = wPcur). congruence. subst wP.
              
              (** split the [switch_out], shall we ?  *)
               inv H; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
               * inv DetC; exfalso. eapply sd_big_final_noext; eauto.
               * inv DetC; exfalso. eapply sd_big_final_noext; eauto.
               * unfold CMulti.OpenLTS in FINAL. fold se in FINAL.
                 assert (r1' = cr res gmem).
                 inv DetC. eapply sd_big_final_determ; eauto. subst.                 

               (** split the replies from current ending thread *)
               destruct wB as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
               destruct gw' as [pp [qq [gwp' gwe']]]. simpl in MR.
               destruct MR as [r1' [Hrr [r1'' [Hrw [qa' [Hrca Hre]]]]]].
               assert (sig' = start_routine_sig).
               {
                 exploit SUB_THREAD_SIG; eauto. intros [A B].
                 eauto.
               }
               assert (SIG2: cajw_sg w_cap = start_routine_sig).
               { exploit SUB_THREAD_SIG; eauto. intros [A B]. eauto. }
               subst sig'.
               inv Hrr. inv Hrw. simpl in H1. inv H.
               inv Hrca. destruct r2 as [trs' ttm'].
               inv Hre. inv H5. clear Hm2. rename Hm1 into Hme. simpl in H3.
               destruct MSEw as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
               inv H5. inv H9. inv MSE.
               rename tm' into tm_r. rename ttm' into ttm_r.
               rename rs' into rs_r.
               rename trs' into trs_r.
               simpl in H2. simpl in gwp'.
               
               assert (tp : Mem.range_prop target (Mem.support(tm_r))).
               red. red in p. simpl in p. inversion Hm'0.
               inv mi_thread. inv Hms. setoid_rewrite <- H13. auto.
               set (tm' := Mem.yield tm_r target tp).
               set (m' := Mem.yield gmem target p).
               rename j' into j. rename Hme into Hme_r. rename Hm into Hme. rename Hm' into Hm.
               assert (Hmj' : Mem.inject j m' tm'). eapply yield_inject; eauto.
               
               assert (ttp: Mem.range_prop target (Mem.support (ttm_r))).
               erewrite <- Mem.mext_sup; eauto.
               set (ttm' := Mem.yield ttm_r target ttp).
               assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.

               set (wpj := injpw j gmem tm_r Hm).
               set (wpj' := injpw j m' tm' Hmj').
               set (wp:= (tt,(tt,(wpj, extw tm_r ttm_r Hme_r)))).
               set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
               set (gw' := (tt,(tt,(gwp', extw tm_r ttm_r Hme)))).
               set (wB := (se,( row se m0',(se,(se, start_routine_sig ,(tse,(w_cap,w_e))))))).

               unfoldC_in H1.
               set (s1' := {|
                            CMulti.threads := NatMap.set cur (Some (CMulti.Final OpenC res))
                                                (NatMap.set cur (Some (CMulti.Local OpenC ls)) threadsC);
                            CMulti.cur_tid := cur;
                            CMulti.next_tid := next |}).
               set (s2 := {| threads := threadsA; cur_tid := cur; next_tid := next |}).
               assert ( exists s2' tm' ttm' worldsP wpc f Hme' Hmj',
                          AsmMulti.switch_out OpenA s2 s2' target ttm' /\
                          match_states' i worldsP s1' s2' /\
                            let cur := CMulti.cur_tid OpenC s1' in
                            (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
                              NatMap.get cur worldsP = Some wpc /\
                              gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme')))).
               { eexists. exists tm', ttm'. exists (NatMap.set cur (Some gw') worldsP). exists gw',j, Hme', Hmj'.
                 repeat apply conj; try rewrite NatMap.gss; eauto.
                 - eapply switch_out_final; eauto. reflexivity.
                 -  econstructor.
                    8:{  rewrite NatMap.gss. reflexivity. }
                    all: simpl; eauto.
                    -- intros. rewrite NatMap.gsspec. destr.
                       rewrite NatMap.gso; eauto.
                    -- destruct CUR_INJP_TID as [X Y]. split.
                       apply gw_acci_tid in ACI. rewrite X. rewrite <- ACI. reflexivity.
                       apply gw_acci_nexttid in ACI. rewrite Y. rewrite <- ACI. reflexivity.
                    -- destruct   CUR_INJP_TID as [X Y].
                       intros. destruct (Nat.eq_dec n cur). subst. rewrite NatMap.gss in H13. inv H13.
                       split. apply gw_acci_tid in ACI. auto. lia.
                       rewrite NatMap.gso in H13. eauto. eauto.
                    -- intros.
                       instantiate (1:= worldsA). 
                       destruct (Nat.eq_dec n cur).
                       ++ subst n.
                          exists wB, None. eexists. eexists. eexists. exists li.
                          repeat apply conj; eauto. constructor. reflexivity.
                          constructor. reflexivity. destruct w_cap. rewrite <- H5. constructor; eauto.
                          rewrite NatMap.gss. reflexivity.
                          rewrite NatMap.gss. reflexivity.
                          eapply match_final_sub.
                          instantiate (1:= gw').
                          subst tres. unfold injp_gw_compcert. simpl. destruct w_cap.
                          inv H. simpl. simpl in SIG2. subst.
                          eapply Mem.val_inject_lessdef_compose. eauto. apply val_inject_id.
                          apply H3.
                          rewrite NatMap.gss. eauto. intros. extlia.
                       ++ (* clear - THREADS H3 OTHERi n0. *)
                         destruct (THREADS n H13) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F' & G & I & J).
                         exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
                         rewrite !NatMap.gso; eauto.
                         rewrite NatMap.gso; eauto.
                         rewrite NatMap.gso; eauto.
                         intros. specialize (J H14). eapply gw_accg_acci_accg; eauto.
                         unfold gw'. destruct w_cap. simpl in H. inv H. constructor.
                 - intros. unfoldC. rewrite NatMap.gss. congruence.
                 - unfold gw'. destruct w_cap. simpl in H. inv H. constructor; eauto; econstructor; eauto; reflexivity.
               }
               destruct H13 as (s2' & tm'1 & ttm'1 & worldsP1 & wpc & f1 & Hme'1 & Hmj'1 & A & B & C & D & E).
               exploit substep_switch_in_progress; eauto.
               intros (s2'' & X).
               right. do 2 eexists. eapply step_switch; eauto.
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
            ++ (*source switch - possible *)
              assert (wP = wPcur). congruence. subst wP.
              unfoldC_in H.
              inv H; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
              ** (*yield*)
                exploit @sd_big_at_external_determ. eauto. apply Hx1. apply AT_E. intro. subst q1. clear Hx1.
                destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
                destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
                inv Hqr. inv Hqw. simpl in H. destruct H2. simpl in H2. inv H2.
                inv Hqca. destruct q2 as [rs_q tm_q]. inv Hqe. destruct H14 as [PCN Hme].
                inv Hme. clear Hm3. rename Hm2 into Hme.
                destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
                inv H14. inv H15. simpl in H13.
                rename tm_q into ttm_q. rename rs_q into rrs_q. rename rs into rs_q. rename tm into tm_q.
                assert (tp : Mem.range_prop target (Mem.support(tm_q))).
                { red. red in p. simpl in p. inversion Hm.
                  inv mi_thread. inv Hms.
                  setoid_rewrite <- H14. auto. }
                set (tm' := Mem.yield tm_q target tp).
                simpl.
                set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := sg; cajw_rs := rs_q |}).
                set (m' := Mem.yield m target p).
                assert (Hm' : Mem.inject j m' tm').
                exploit yield_inject; eauto.
                assert (ttp : Mem.range_prop target (Mem.support (ttm_q))).
                { erewrite <- Mem.mext_sup; eauto. }
                set (ttm' := Mem.yield ttm_q target ttp).
                assert (Hme' : Mem.extends tm' ttm').
                eapply yield_extends; eauto.
                inv H.
                set (wpj := injpw j m tm_q Hm).
                set (wpj' := injpw j m' tm' Hm').
                set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
                set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
                set (wA := (se,(row se m,(se,(se, sg, (tse,(wAca,extw tm_q ttm_q Hm1))))))).

                unfoldC_in H1.
               set (s1' :=  {|
                            CMulti.threads := NatMap.set cur (Some (CMulti.Returny OpenC ls))
                                                (NatMap.set cur (Some (CMulti.Local OpenC ls)) threadsC);
                            CMulti.cur_tid := cur;
                            CMulti.next_tid := next |}).
               set (s2 := {| threads := threadsA; cur_tid := cur; next_tid := next |}).
               assert ( exists s2' tm' ttm' worldsP wpc f Hme' Hmj',
                          AsmMulti.switch_out OpenA s2 s2' target ttm' /\
                          match_states' i worldsP s1' s2' /\
                            let cur := CMulti.cur_tid OpenC s1' in
                            (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
                              NatMap.get cur worldsP = Some wpc /\
                              gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme')))).
               { 
               eexists. exists tm', ttm'.
               exists (NatMap.set cur (Some wp) worldsP), wp, j, Hme', Hm'.
               repeat apply conj.
               + (*step*)
                 eapply switch_out_yield. eauto. eauto.
                 { inv Q_YIE. inv MSE.
                   econstructor. fold tse. rewrite <- SE_eq. eauto.
                   subst tvf. inv H4.
                   rewrite <- SE_eq in H17.
                   exploit match_senv_id. eauto. apply H18. eauto. intros [X' Y'].
                   subst b delta. symmetry in H16. eapply lessdef_trans in H16; eauto.
                   simpl. simpl in H20. erewrite <- Mem.mext_sup. 2: eauto.
                   inv Hm3. inv mi_thread. inv Hms. unfold Mem.next_tid. auto.
                 }
                 reflexivity.
                 reflexivity.
               + (*match_states*)
                 apply gw_acci_nexttid in ACI as NTID. apply gw_acci_tid in ACI as TID.
                 econstructor.
                 8:{ rewrite NatMap.gss. reflexivity. }
                             all : simpl; eauto.
                 -- simpl. intros. rewrite NatMap.gsspec. destr.
                    rewrite NatMap.gso; eauto.
                 -- destruct CUR_INJP_TID as [X' Y']. split.
                    rewrite <- X' in TID. simpl in TID.
                    unfold gw_tid in TID. simpl in TID. unfold gw_tid. simpl. congruence.
                    rewrite <- Y' in NTID. simpl in NTID.
                    unfold gw_nexttid in NTID. simpl in NTID. unfold gw_nexttid. simpl. congruence.
                 -- destruct CUR_INJP_TID.  simpl in *.
                    intros. destruct (Nat.eq_dec n cur). subst.
                    rewrite NatMap.gss in H16. inv H16.
                    split. eauto. lia. 
                    rewrite NatMap.gso in H16.
                    exploit FIND_TID; eauto. eauto.
                 -- intros.
                    instantiate (1:= NatMap.set cur (Some wA) worldsA).
                    destruct (Nat.eq_dec n cur).
                    ++ subst n.
                       exists wB, (Some wA), wp. eexists. eexists. exists li.
                       repeat apply conj; eauto.
                       * rewrite NatMap.gss. reflexivity.
                       * rewrite NatMap.gss. reflexivity.
                       * rewrite NatMap.gss. reflexivity.
                       * simpl. simpl in wp'. assert (HRS: rs_q = cajw_rs wAca).  reflexivity.
                         eapply match_returny; eauto.
                         unfold wA. econstructor; eauto.
                         inversion Q_YIE. subst m1 args sg vf next0. eauto.
                         red. intros. apply val_inject_id. eauto.
                       * simpl in MR.
                         rewrite NatMap.gss. eauto.
                       * simpl. congruence.
                    ++ (* clear - THREADS H3 OTHERi n0. *)
                      destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                      exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
                      rewrite NatMap.gso; eauto.
                      rewrite NatMap.gso; eauto.
                      rewrite NatMap.gso; eauto.
                      rewrite NatMap.gso; eauto.
                      rewrite NatMap.gso; eauto.
                      simpl. intros. specialize (J H14).
                      eapply gw_accg_acci_accg; eauto. constructor.
               + intros. simpl. unfold CMulti.get_cur_thread, CMulti.update_cur_thread. simpl.
                 unfold CMulti.get_thread, CMulti.update_thread. simpl. rewrite NatMap.gss. congruence.
               + rewrite NatMap.gss. eauto.
               + econstructor; eauto. econstructor; eauto.
                 reflexivity. reflexivity. econstructor; eauto. reflexivity. reflexivity.
               }
               destruct H as (s2' & tm'1 & ttm'1 & worldsP1 & wpc & f1 & Hme'1 & Hmj'1 & A & B & C & D & E).
               exploit substep_switch_in_progress; eauto.
               intros (s2'' & X').
               right. do 2 eexists. eapply step_switch; eauto.
              ** (*join*)
                exploit @sd_big_at_external_determ. eauto. apply Hx1. apply AT_E. intro. subst q1. clear Hx1.
                destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
                destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
                inv Hqr. inv Hqw. simpl in H2. destruct H2. inv H2.
                inv Hqca. destruct q2 as [rs_q tm_q]. inv Hqe. destruct H14 as [PCN Hme].
                inv Hme. clear Hm3. rename Hm2 into Hme.
                destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
                inv H14. inv H15. inv MSE.
                rename tm_q into ttm_q. rename rs_q into rrs_q. rename rs into rs_q. rename tm into tm_q.
                inv Q_JOIN.
                subst targs tvf. simpl in H1. unfoldC_in H1.
                setoid_rewrite pthread_join_locs in H2. simpl in H2.
                inv H2. inv H18. inv H22.
                assert (HPC: rs_q PC = Vptr b_ptj Ptrofs.zero).
                inv H4. rewrite <- SE_eq in H17. exploit match_senv_id; eauto. intros [X' Y].
                subst b2 delta. reflexivity.
                assert (HRDI: rs_q RDI = Vint i0). inv H15. eauto.
                assert (HRSI: exists b_vptr' ofs_vptr', rs_q RSI = Vptr b_vptr' ofs_vptr').
                inv H18. eauto. destruct HRSI as [b_vptr' [ofs_vptr' HRSI]].
                eapply lessdef_trans in HPC as HPC'; eauto.
                eapply lessdef_trans in HRDI as HRDI'; eauto; try congruence.
                eapply lessdef_trans in HRSI as HRSI'; eauto; try congruence.
                assert (tp : Mem.range_prop target (Mem.support(tm_q))).
                red. red in p. simpl in p. inversion Hm.
                inv mi_thread. inv Hms. setoid_rewrite <- H2. auto.
                set (tm' := Mem.yield tm_q target tp).
                set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := pthread_join_sig; cajw_rs := rs_q |}).
                set (m' := Mem.yield m target p).
                assert (Hm': Mem.inject j m' tm'). eapply yield_inject; eauto.
                assert (ttp: Mem.range_prop target (Mem.support (ttm_q))).
                erewrite <- Mem.mext_sup; eauto.
                set (ttm' := Mem.yield ttm_q target ttp).
                assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.
                set (wpj := injpw j m tm_q Hm).
                set (wpj' := injpw j m' tm' Hm').
                set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
                set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
                inv H.
                set (wA := (se,(row se m,(se,(se, pthread_join_sig, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
                 unfoldC_in H1.
               set (s1' :=  {|
                            CMulti.threads := NatMap.set cur
                             (Some (CMulti.Returnj OpenC ls (int_to_nat i0) (Vptr b_vptr ofs_vptr)))
                             (NatMap.set cur (Some (CMulti.Local OpenC ls)) threadsC);
                            CMulti.cur_tid := cur;
                            CMulti.next_tid := next |}).
               set (s2 := {| threads := threadsA; cur_tid := cur; next_tid := next |}).
               assert ( exists s2' tm' ttm' worldsP wpc f Hme' Hmj',
                          AsmMulti.switch_out OpenA s2 s2' target ttm' /\
                          match_states' i worldsP s1' s2' /\
                            let cur := CMulti.cur_tid OpenC s1' in
                            (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
                              NatMap.get cur worldsP = Some wpc /\
                              gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme')))).
               { 
                eexists. exists tm', ttm'. exists (NatMap.set cur (Some wp) worldsP). exists wp,j,Hme', Hm'.
                repeat apply conj; try rewrite NatMap.gss; eauto.
                + (*step*)
                  eapply switch_out_join. eauto. eauto.
                  econstructor; eauto.
                  fold tse. rewrite <- SE_eq. eauto. eauto. reflexivity. reflexivity.
                + (*match_states*)
                  apply gw_acci_nexttid in ACI as NTID. apply gw_acci_tid in ACI as TID.
                  simpl in *.
                  econstructor. 8:{ rewrite NatMap.gss. reflexivity. }
                              all : simpl; eauto.
                  -- simpl. intros. rewrite NatMap.gsspec. destr.
                     rewrite NatMap.gso; eauto.
                  -- destruct CUR_INJP_TID as [X' Y]. split.
                     rewrite X'. rewrite <- TID. reflexivity.
                     rewrite Y. rewrite <- NTID. reflexivity.
                  -- destruct CUR_INJP_TID.
                     intros. destruct (Nat.eq_dec n cur). subst.
                     rewrite NatMap.gss in H16. inv H16.
                     split. eauto. lia. 
                     rewrite NatMap.gso in H16.
                     exploit FIND_TID; eauto. eauto.
                  -- intros.
                     instantiate (1:= NatMap.set cur (Some wA) worldsA).
                     destruct (Nat.eq_dec n cur).
                     ++ subst n.
                        exists wB, (Some wA), wp. eexists. eexists. exists li.
                        repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
                        rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
                        simpl. simpl in wp.
                        eapply match_returnj; eauto.
                        red. intros. eapply val_inject_id; eauto.
                        simpl. rewrite HRSI'. rewrite <- HRSI. eauto.
                        unfold wA. constructor.
                        rewrite NatMap.gss. eauto. simpl. congruence.
                     ++ (* clear - THREADS H3 OTHERi n0. *)
                       destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
                       exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto;
                         try rewrite !NatMap.gso; eauto.
                       simpl. intros. specialize (J H2).
                       eapply gw_accg_acci_accg; eauto. constructor.
                +  intros. unfoldC. rewrite NatMap.gss. congruence.
                + econstructor; eauto; econstructor; eauto; reflexivity.
               }
                destruct H as (s2' & tm'1 & ttm'1 & worldsP1 & wpc & f1 & Hme'1 & Hmj'1 & A & B & C & D & E).
               exploit substep_switch_in_progress; eauto.
               intros (s2'' & X').
               right. do 2 eexists. eapply step_switch; eauto.
              ** (*final*)
                exfalso. inv DetC. eapply sd_big_final_noext; eauto.
        + right. do 2 eexists. econstructor; eauto.
      - exploit Hsafe. eapply star_refl.
        intros [[r1 Fc]|[tc [s1'' Sc]]].
        + inv Fc. unfoldC_in H. unfoldC_in H1. congruence.
        + inv Sc; unfoldC_in H; try congruence.
          inv H; unfoldC_in GET_C; try congruence.
      - exploit Hsafe. eapply star_refl.
        intros [[r1 Fc]|[tc [s1'' Sc]]].
        + inv Fc. unfoldC_in H. unfoldC_in H1. congruence.
        + inv Sc; unfoldC_in H; try congruence.
          inv H; unfoldC_in GET_C; try congruence.
      - exploit Hsafe. eapply star_refl.
        intros [[r1 Fc]|[tc [s1'' Sc]]].
        + inv Fc. unfoldC_in H. unfoldC_in H1. congruence.
        + inv Sc; unfoldC_in H; try congruence.
          inv H; unfoldC_in GET_C; try congruence.
      - exploit Hsafe. eapply star_refl.
        intros [[r1 Fc]|[tc [s1'' Sc]]].
        + inv Fc. unfoldC_in H. unfoldC_in H1. congruence.
        + inv Sc; unfoldC_in H; try congruence.
          inv H; unfoldC_in GET_C; try congruence.
    Qed.

    Lemma match_senv_id_rev : forall j b b' d id, Genv.match_stbls j se se ->
                                         j b = Some (b',d) ->
                                        Genv.find_symbol tse id = Some b' ->
                                        b' = b /\ d = 0.
    Proof.
      intros. rewrite <- SE_eq in H1. inv H. split.
      exploit mge_symb; eauto.
      intro HH. apply HH in H1 as H2.
      setoid_rewrite H1 in H2. inv H2. eauto.
      exploit mge_img; eauto. eapply Genv.genv_symb_range; eauto.
      intros [b2 A].
      eapply mge_symb in A as HsA; eauto.
      eapply mge_symb in H0 as HsB; eauto.
      apply HsA in H1 as H1A. apply HsB in H1 as H1B.
      rewrite H1B in H1A. inv H1A. rewrite H0 in A. inv A. reflexivity.
    Qed.

    Lemma cc_compcert_mq_ms_id : forall b sg args m rs tm w id1 id2 b',
        GS.match_query cc_compcert w (cq (Vptr b Ptrofs.zero) sg args m) (rs,tm) ->
        GS.match_senv cc_compcert w se tse ->
        rs PC = Vptr b' Ptrofs.zero ->
        Genv.find_symbol se id1 = Some b ->
        Genv.find_symbol tse id2 = Some b' ->
        id1 = id2.
    Proof.
      intros until b'. intros MQ MS rsPC FIND1 FIND2.
      destruct w as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
      destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
      inv Hqr. inv Hqw. simpl in H. destruct H0. simpl in H1. inv H0.
      inv Hqca. inv Hqe. destruct H2 as [PCN Hme].
      inv Hme. clear Hm4. rename Hm3 into Hme.
      subst tvf targs.
      destruct MS as [EQ1 [EQ2 [MSE EQ3]]].
      inv EQ1. inv EQ2. inv EQ3. inv H2. inv H3. simpl in H0.
      inv MSE. inv H6. generalize (H0 PC). intro. rewrite <- H4 in H2. inv H2. inv H20.
      rewrite rsPC in H17. inv H17.
      inv H11. exploit mge_symb; eauto. intro. apply H2 in FIND1.
      apply Genv.find_invert_symbol in FIND1.
      apply Genv.find_invert_symbol in FIND2.
      unfold se in FIND2. congruence.
    Qed.

    Hypothesis OpenC_after_external_receptive : forall s q r,
        Smallstep.at_external (OpenC se) s q ->
        exists s', Smallstep.after_external (OpenC se) s r s'.
      
    Lemma substep_switch_out : forall i s1 s2 s2' target ttm',
       match_states i s1 s2 ->
       Closed.safe ConcurC s1 -> fst (CMulti.threads OpenC s1) = None ->
       AsmMulti.switch_out OpenA s2 s2' target ttm' ->
       exists s1s s1' m' tm' worldsP wpc f Hme' Hmj',
         star (Closed.step ConcurC) (Closed.globalenv ConcurC) s1 E0 s1s /\
           CMulti.switch_out OpenC s1s s1' target m' /\
           match_states' i worldsP s1' s2' /\
           let cur := CMulti.cur_tid OpenC s1' in
           (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) /\
             NatMap.get cur worldsP = Some wpc /\
           gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj', extw tm' ttm' Hme'))) /\
           Mem.tid (Mem.support m') = target.
   Proof.
     intros until ttm'. intros MS SAFE DEFAULT SWITCH.
     specialize (determinate_big_C se) as DetC.
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
       exploit bsim_match_external; eauto. eapply safe_concur_single; eauto.
       intros (wA & s1' & qc & Hstarc & HX & ACI & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.

       exploit SAFE. eapply local_star_c. eauto. eauto. unfoldC. eauto.
       intros [[r Hr]|[t [s'' S]]].
       (** rule out contradictions *)
       1: { (*contradiction*)
         unfoldC_in Hr. inv Hr. unfoldC_in H. subst. unfoldC_in H1. rewrite NatMap.gss in H1.
         inv H1.
         inv DetC. exfalso. eapply sd_big_final_noext; eauto. }
       inv S; unfoldC_in H; try rewrite NatMap.gss in H; inv H.
       1: { inv DetC. exfalso. eapply sd_big_at_external_nostep; eauto. }
       1: { exploit @sd_big_at_external_determ. eauto. apply HX. apply H1. intro. subst.
            inv H2. inv Q_YIE. exploit cc_compcert_mq_ms_id; eauto. intro. inv H. }
       2: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
            exploit @sd_big_at_external_determ. eauto. apply HX. apply AT_E0. intro. subst.
            inv Q_JOIN. inv Q_YIE. exploit cc_compcert_mq_ms_id; eauto. intro. inv H. }
       2: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0. exfalso.
            exploit @sd_big_final_noext; eauto. }
       (** main part *)
       unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
       exploit @sd_big_at_external_determ. eauto. apply HX. apply AT_E0. intro. subst.
       clear target0 p0 H1.
       rename m_q into ttm_q.
       destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
       inv Hqr. inv Hqw. simpl in H1. destruct H1. inv H1.
       inv Hqca. inv Hqe. destruct H13 as [PCN Hme].
       inv Hme. clear Hm3. rename Hm2 into Hme.
       destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H13. inv H14.
       rename tm into tm_q. rename rs_q into rrs_q. rename rs into rs_q.
        assert (tp : Mem.range_prop target (Mem.support(tm_q))).
       { red. red in p. simpl in p. inversion Hm.
         inv mi_thread. inv Hme. congruence. }
       set (tm' := Mem.yield tm_q target tp).
       simpl.
       set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := sg; cajw_rs := rs_q |}).
       rename p into ttp.
       assert (p: Mem.range_prop target (Mem.support m)).
       {
         red. erewrite inject_next_tid; eauto.
       }
       set (m' := Mem.yield m target p).
       assert (Hm' : Mem.inject j m' tm').
       exploit yield_inject; eauto.
       set (ttm' := Mem.yield ttm_q target ttp).
       assert (Hme' : Mem.extends tm' ttm').
       eapply yield_extends; eauto.
       inv H.
       exploit local_star_c; eauto. intro. unfoldC_in H.
       set (wpj := injpw j m tm_q Hm).
       set (wpj' := injpw j m' tm' Hm').
       set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
       set (wA := (se,(row se m,(se,(se, sg, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
       (** Use the safety and determinacy of source semantics to derive a source step *)
       eexists. eexists. exists m', tm'.
       exists (NatMap.set cur (Some wp) worldsP), wp, j, Hme', Hm'.
       simpl in H12.
       repeat apply conj.
       + (*star*) eauto.
       + (*step*)
         eapply CMulti.switch_out_yield. unfoldC. rewrite NatMap.gss. reflexivity.
         eauto. eauto. reflexivity. reflexivity.
       + (*match_states*)
         apply gw_acci_nexttid in ACI as NTID. apply gw_acci_tid in ACI as TID.
         econstructor. 8:{ rewrite NatMap.gss. reflexivity. }
         all : simpl; eauto.
         -- simpl. intros. rewrite NatMap.gsspec. destr.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID as [X Y]. split.
            rewrite <- X in TID. simpl in TID.
            unfold gw_tid in TID. simpl in TID. unfold gw_tid. simpl. congruence.
            rewrite <- Y in NTID. simpl in NTID.
            unfold gw_nexttid in NTID. simpl in NTID. unfold gw_nexttid. simpl. congruence.
         -- destruct CUR_INJP_TID.  simpl in *.
            intros. destruct (Nat.eq_dec n cur). subst.
            rewrite NatMap.gss in H16. inv H16.
            split. eauto. lia. 
            rewrite NatMap.gso in H16.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp'. assert (HRS: rs_q = cajw_rs wAca).  reflexivity.
               eapply match_returny; eauto.
               unfold wA. econstructor; eauto.
               inversion Q_YIE0. subst m1 args sg vf next0. eauto.
               red. intros. apply val_inject_id. eauto. simpl in MR.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H13) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto; try rewrite !NatMap.gso; eauto.
               simpl. intros. specialize (J H15).
               eapply gw_accg_acci_accg; eauto. constructor.
       + intros. simpl. unfold CMulti.get_cur_thread, CMulti.update_cur_thread. simpl.
         unfold CMulti.get_thread, CMulti.update_thread. simpl. rewrite NatMap.gss. congruence.
       + rewrite NatMap.gss. eauto.
       + econstructor; eauto. econstructor; eauto.
         reflexivity. reflexivity. econstructor; eauto. reflexivity. reflexivity.
       + eauto.
     -  specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsa = AsmMulti.Local OpenA ls).
       eapply foo; eauto. subst lsa. inv MS.
       specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
       inversion BSIM.
       clear bsim_simulation bsim_match_initial_states
         bsim_match_final_states.
       exploit bsim_match_external; eauto. eapply safe_concur_single; eauto.
       intros (wA & s1' & qc & Hstarc & HX & ACI & MQ & MS & MR).
       assert (wP = wPcur). congruence. subst wP.

       exploit SAFE. eapply local_star_c. eauto. eauto. unfoldC. eauto.
       intros [[r Hr]|[t [s'' S]]].
       (** rule out contradictions *)
       1: { (*contradiction*)
         unfoldC_in Hr. inv Hr. unfoldC_in H. subst. unfoldC_in H1. rewrite NatMap.gss in H1.
         inv H1.
         inv DetC. exfalso. eapply sd_big_final_noext; eauto. }
       inv S; unfoldC_in H; try rewrite NatMap.gss in H; inv H.
       1: { inv DetC. exfalso. eapply sd_big_at_external_nostep; eauto. }
       1: { exploit @sd_big_at_external_determ. eauto. apply HX. apply H1. intro. subst.
            inv H2. inv Q_JOIN. exploit cc_compcert_mq_ms_id; eauto. intro. inv H. }
       1: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
            exploit @sd_big_at_external_determ. eauto. apply HX. apply AT_E0. intro. subst.
            inv Q_JOIN. inv Q_YIE. exploit cc_compcert_mq_ms_id; eauto. intro. inv H3. }
       2: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0. exfalso.
            exploit @sd_big_final_noext; eauto. }
        unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
       exploit @sd_big_at_external_determ. eauto. apply HX. apply AT_E0. intro. subst.
       clear target0 p0 H1.  rename m_q into ttm_q.
       destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct MQ as [q1' [Hqr [q1'' [Hqw [qa' [Hqca Hqe]]]]]].
       inv Hqr. inv Hqw. simpl in H. destruct H1. simpl in H1. inv H1. simpl in H.
       inv Hqca. inv Hqe. destruct H13 as [PCN Hme].
       inv Hme. clear Hm3. rename Hm2 into Hme.
       destruct MS as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H13. inv H14. inv MSE.
       rename rs_q into rrs_q. rename rs into rs_q. rename tm into tm_q.
       inv Q_JOIN0.
       subst targs tvf.
       setoid_rewrite pthread_join_locs in H1. simpl in H1.
       inv H1. inv H21. inv H22.
       assert (HPC: rs_q PC = Vptr b_ptj Ptrofs.zero).
       inv H3. rewrite <- SE_eq in H16. exploit match_senv_id; eauto. intros [X Y].
       subst b2 delta. reflexivity.
       assert (HRDI: rs_q RDI = Vint i0). inv H17. eauto.
       assert (HRSI: exists b_vptr' ofs_vptr', rs_q RSI = Vptr b_vptr' ofs_vptr').
       inv H15. eauto. destruct HRSI as [b_vptr' [ofs_vptr' HRSI]].
       eapply lessdef_trans in HPC as HPC'; eauto.
       eapply lessdef_trans in HRDI as HRDI'; eauto; try congruence.
       eapply lessdef_trans in HRSI as HRSI'; eauto; try congruence.
       rename p into ttp.
       assert (tp : Mem.range_prop target (Mem.support(tm_q))).
       red. red in ttp. simpl in ttp. inversion Hm.
       inv mi_thread. inv Hme.  rewrite mext_sup. eauto.
       set (tm' := Mem.yield tm_q target tp).
       set (wAca := {| cajw_injp := injpw j m tm_q Hm; cajw_sg := pthread_join_sig; cajw_rs := rs_q |}).
       assert (p : Mem.range_prop target (Mem.support m)).
       red. red in ttp. simpl in ttp.
       erewrite inject_next_tid; eauto.
       set (m' := Mem.yield m target p).
       assert (Hm': Mem.inject j m' tm'). eapply yield_inject; eauto.
       set (ttm' := Mem.yield ttm_q target ttp).
       assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.
       set (wpj := injpw j m tm_q Hm).
       set (wpj' := injpw j m' tm' Hm').
       set (wp:= (tt,(tt,(wpj, extw tm_q ttm_q Hm1)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
       inv H.
       set (wA := (se,(row se m,(se,(se, pthread_join_sig, (tse,(wAca,extw tm_q ttm_q Hm1))))))).
       eexists. eexists. exists m', tm'. exists (NatMap.set cur (Some wp) worldsP). exists wp,j,Hme', Hm'.
       repeat apply conj; try rewrite NatMap.gss; eauto.
       + (*star*)
          eapply local_star_c; eauto.
       + (*step*)
         eapply CMulti.switch_out_join. unfoldC. rewrite NatMap.gss. reflexivity.
         eauto. 
         econstructor; eauto. reflexivity. reflexivity.
       + (*match_states*)
         apply gw_acci_nexttid in ACI as NTID. apply gw_acci_tid in ACI as TID.
         simpl in *.
         econstructor. 8:{ rewrite NatMap.gss. reflexivity. }
         all : simpl; eauto.
         -- simpl. intros. rewrite NatMap.gsspec. destr.
            rewrite NatMap.gso; eauto.
         -- destruct CUR_INJP_TID as [X Y]. split.
            rewrite X. rewrite <- TID. reflexivity.
            rewrite Y. rewrite <- NTID. reflexivity.
         -- destruct CUR_INJP_TID.
            intros. destruct (Nat.eq_dec n cur). subst.
            rewrite NatMap.gss in H14. inv H14.
            split. eauto. lia. 
            rewrite NatMap.gso in H14.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set cur (Some wA) worldsA).
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, (Some wA), wp. eexists. eexists. exists li.
               repeat apply conj; eauto. rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity. rewrite NatMap.gss. reflexivity.
               simpl. simpl in wp.
               eapply match_returnj; eauto.
               red. intros. eapply val_inject_id; eauto.
               simpl. rewrite HRSI'. rewrite <- HRSI. eauto.
               unfold wA. constructor.
               rewrite NatMap.gss. eauto. simpl. congruence.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto; try rewrite NatMap.gso; eauto.
               rewrite NatMap.gso; eauto.
               simpl. intros. specialize (J H1).
               eapply gw_accg_acci_accg; eauto. constructor.
       + intros. unfoldC. rewrite !NatMap.gss. congruence.
       + unfoldC. rewrite NatMap.gss. reflexivity.
       + econstructor; eauto; econstructor; eauto; reflexivity.
     -  specialize (THREADS cur CUR_VALID) as THR_CUR.
       destruct THR_CUR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (lsa = AsmMulti.Local OpenA ls).
       eapply foo; eauto. subst lsa. inv MS.
       specialize (bsim_lts se tse wB MSEw valid_se) as BSIM.
       inversion BSIM.
       clear bsim_simulation bsim_match_initial_states bsim_match_external.
       exploit bsim_match_final_states; eauto. eapply safe_concur_single; eauto.
       rename rs_r into trs_r.
       intros (s1' & [rs_r tm_r] & gw' & STAR & FINAL' & GW_ACC_IF & GW_ACC_BIG & MR).
       assert (wP = wPcur). congruence. subst wP.

       exploit SAFE. eapply local_star_c. eauto. eauto. unfoldC. eauto.
       intros [[r Hr]|[t [s'' S]]].
       (** rule out contradictions *)
       1: { (*contradiction*)
         unfoldC_in Hr. inv Hr. unfoldC_in H. subst.
         simpl in SUB_THREAD. extlia. }
       inv S; unfoldC_in H; try rewrite NatMap.gss in H; inv H.
       1: { inv DetC. exfalso. eapply sd_big_final_nostep; eauto. }
       1: { inv DetC. exfalso. eapply sd_big_final_noext; eauto. }
       1: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
            inv DetC. exfalso. eapply sd_big_final_noext; eauto. }
       1: { unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
            inv DetC. exfalso. eapply sd_big_final_noext; eauto. }
       unfoldC_in GET_C0. rewrite NatMap.gss in GET_C0. inv GET_C0.
       exploit @sd_big_final_determ. eauto. apply FINAL'. apply FINAL0. intro. inv H.
       clear target0 p0 H1.
        destruct wB as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & w_cap & w_e).
       destruct gw' as [pp [qq [gwp' gwe']]]. simpl in MR.
       destruct MR as [r1' [Hrr [r1'' [Hrw [qa' [Hrca Hre]]]]]].
       assert (sig' = start_routine_sig).
       {
         exploit SUB_THREAD_SIG; eauto. intros [A B].
         eauto.
       }
       assert (SIG2: cajw_sg w_cap = start_routine_sig).
       { exploit SUB_THREAD_SIG; eauto. intros [A B]. eauto. }
       subst sig'.
       inv Hrr. inv Hrw. simpl in H. inv H. simpl in H1.
       inv Hrca. inv Hre. inv H4. clear Hm2. rename Hm1 into Hme.
       destruct MSEw as [EQ1 [EQ2 [MSE EQ3]]]. inv EQ1. inv EQ2. inv EQ3.
       inv H4. inv H8. inv MSE.
       rename rs' into rs_r. rename tm' into tm_r.
       simpl in H2. simpl in gwp'.
       assert (tp : Mem.range_prop target (Mem.support(tm_r))).
       red. red in p. simpl in p. inversion Hm'0.
       inv mi_thread. inv Hme. setoid_rewrite mext_sup. auto.
       set (tm' := Mem.yield tm_r target tp).
       rename p into ttp. rename gmem into ttm_r. rename gmem0 into m_r.
       assert (p: Mem.range_prop target (Mem.support m_r)).
       red. red in ttp. simpl in ttp. erewrite inject_next_tid; eauto.
       set (m' := Mem.yield m_r target p).
       rename j' into j. rename Hme into Hme_r. rename Hm into Hme. rename Hm' into Hm.
       assert (Hmj' : Mem.inject j m' tm'). eapply yield_inject; eauto.
       set (ttm' := Mem.yield ttm_r target ttp).
       assert (Hme' : Mem.extends tm' ttm'). eapply yield_extends; eauto.

       set (wpj := injpw j m_r tm_r Hm).
       set (wpj' := injpw j m' tm' Hmj').
       set (wp:= (tt,(tt,(wpj, extw tm_r ttm_r Hme_r)))).
       set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
       set (gw' := (tt,(tt,(gwp', extw tm_r ttm_r Hme)))).
       set (wB := (se,( row se m0',(se,(se, start_routine_sig ,(tse,(w_cap,w_e))))))).
       eexists. eexists. exists m', tm'. exists (NatMap.set cur (Some gw') worldsP). exists gw',j, Hme', Hmj'.
       repeat apply conj; try rewrite NatMap.gss; eauto.
       + (*star*) eapply local_star_c; eauto.
       + (*step*)
         eapply CMulti.switch_out_final. unfoldC. eauto. unfoldC. rewrite NatMap.gss. reflexivity.
         eauto. reflexivity. unfoldC. reflexivity.
       + (*match_states*)
         simpl in *.
         econstructor.
         8:{  rewrite NatMap.gss. reflexivity. }
         all: simpl; eauto.
         -- intros. rewrite NatMap.gsspec. destr.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct   CUR_INJP_TID as [X Y]. split.
            apply gw_acci_tid in GW_ACC_BIG. rewrite X. rewrite <- GW_ACC_BIG. reflexivity.
            apply gw_acci_nexttid in GW_ACC_BIG. rewrite Y. rewrite <- GW_ACC_BIG. reflexivity.
         -- destruct   CUR_INJP_TID as [X Y].
            intros. destruct (Nat.eq_dec n cur). subst. rewrite NatMap.gss in H12. inv H12.
            split. apply gw_acci_tid in GW_ACC_BIG. auto. lia.
            rewrite NatMap.gso in H12. eauto. eauto.
         -- intros.
            instantiate (1:= worldsA). 
            destruct (Nat.eq_dec n cur).
            ++ subst n.
               exists wB, None. eexists. eexists. eexists. exists li.
               repeat apply conj; eauto. constructor. reflexivity.
               constructor. reflexivity. destruct w_cap. rewrite <- H4. constructor; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               eapply match_final_sub.
               instantiate (1:= gw').
               subst tres. unfold injp_gw_compcert. simpl. destruct w_cap.
               inv H. simpl. simpl in SIG2. subst.
               eapply Mem.val_inject_lessdef_compose. eauto. apply val_inject_id.
               apply H2.
               rewrite NatMap.gss. eauto. intros. extlia.
            ++ (* clear - THREADS H3 OTHERi n0. *)
               destruct (THREADS n H12) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; eauto.
               rewrite NatMap.gso; eauto.
               rewrite NatMap.gso; eauto.
               rewrite NatMap.gso; eauto.
               rewrite NatMap.gso; eauto.
               intros. specialize (J H13). eapply gw_accg_acci_accg; eauto.
               unfold gw'. destruct w_cap. simpl in H. inv H. constructor.
       + intros. unfoldC. rewrite !NatMap.gss. congruence.
       + unfoldC. rewrite NatMap.gss. reflexivity.
       + unfold gw'. destruct w_cap. simpl in H. inv H. constructor; eauto; econstructor; eauto; reflexivity.
   Qed.

   Hypothesis OpenC_initial_state_receptive : forall s vf sg args m m',
       Smallstep.initial_state (OpenC se) (cq vf sg args m) s ->
       Mem.sup_include (Mem.support m) (Mem.support m') ->
       exists s', Smallstep.initial_state (OpenC se) (cq vf sg args m') s'.
   
   Lemma substep_switch_in : forall i s1' s2' s2'' target m' tm' ttm' f Hmj' Hme' worldsP wpc,
       (* sth more about gtmem'*)
       let cur := CMulti.cur_tid OpenC s1' in
       match_states' i worldsP s1' s2' ->
       NatMap.get cur worldsP = Some wpc -> (** the wpc here is a world at [X] *)
       (forall cqv, CMulti.get_cur_thread OpenC s1' <> Some (CMulti.Initial OpenC cqv)) ->
       gw_acc_yield wpc (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme'))) ->
       Mem.tid (Mem.support m') = target ->
       AsmMulti.switch_in OpenA s2' s2'' target ttm' -> exists s1'' i',
           CMulti.switch_in OpenC s1' s1'' target m' /\
             match_states i' s1'' s2''.
   Proof.
     intros until wpc. intros cur MS' GETwpc NOTINIT ACCY TID_TARGET SWITCH.
     assert (RANGE: (1 <= target < CMulti.next_tid OpenC s1')%nat).
     {
       inv ACCY. simpl. inv MS'. simpl. simpl in cur. subst cur.
       assert ((tt,(tt,(injpw f m1 m2 Hmj,extw m2 m3 Hme0))) = wPcur).
       congruence.
       destruct CUR_INJP_TID. rewrite H1. rewrite <- H. simpl. unfold gw_nexttid. simpl.
       inv H2. eauto.
     }
     inv MS'. set (target := Mem.tid (Mem.support m')).
     simpl in cur. subst cur. rename cur0 into cur.
     destruct (Nat.eq_dec cur target).
     - (*switch to self*)
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       assert (wpc = wP). congruence. subst wpc.
       inv SWITCH.
       + (*yield*)
         assert (lsa = AsmMulti.Returny OpenA ls1 rs1).
         eapply foo; eauto. subst lsa. inv MS. 
         assert (get wA = wPcur). clear -GETWp CUR_GWORLD.
         rewrite CUR_GWORLD in GETWp. inv GETWp. reflexivity.
         subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD.
         inv ACCY.
         assert (ACCEJ: injp_acce (get_injp wAca) (injpw f m' tm' Hmj')).
         { eapply injp_acc_yield_acce. eauto. rewrite <- H. inv H3.
           econstructor; eauto. eauto. }
         assert (ACCEE: ext_acce (extw m2 m3 Hme0) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (get_injp wAca) = injp_tid (injpw f m' tm' Hmj')).
           eauto. eapply ext_acc_yield_acce; eauto. inv H8. econstructor; eauto.
           simpl. rewrite <- H in BASE. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite BASE.
           erewrite inject_tid; eauto.
         }
         set (qc := cr Vundef m'). rename rs1 into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (trs' := Pregmap.set PC (trs RA) trs).
         set (r_a := (rs', tm')).
         set (tr_a := (trs', ttm')).
         exploit M_REPLIES; eauto. 
         instantiate (1:= (tt, (tt, (injpw f m' tm' Hmj', extw tm' ttm' Hme')))).
         repeat apply conj; simpl; eauto.
         instantiate (1:= tr_a). unfold tr_a.
         { 
           eexists. split. instantiate (1:= cr Vundef m').
           econstructor; eauto. constructor.
           inv WT_WA. simpl in ACCEJ. inv ACCEJ. constructor; eauto. destruct H14 as [_ [A _]]. auto.
           eexists. split. econstructor; eauto. constructor.
           exists r_a. split. unfold r_a. simpl. destruct wAca. simpl. destruct cajw_injp.
           econstructor; eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; simpl; eauto. unfold rs_w_compcert in RSLD. simpl in RSLD.
           unfold rs', trs'. intros. setoid_rewrite Pregmap.gsspec.
           destr; apply val_inject_id; eauto. constructor.
         } 
         intros [Hy1 Hy2].
         assert (exists sc', after_external (OpenC se) sc (cr Vundef m') sc').
         eapply OpenC_after_external_receptive; eauto.
         destruct H0 as [sc'1 Hyc]. exploit Hy2; eauto.
         intros [sc' [AFT_E' [li' MLS']]]. clear Hy1 Hy2 sc'1 Hyc.
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         econstructor; eauto.
         (*match*)
         set (wpj' := injpw f m' tm' Hmj').
         set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor; simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y]. unfold wp'.
            split; eauto. 
            simpl. simpl. unfold wpj'. 
            inv H3. simpl. unfold gw_nexttid. simpl. rewrite <- H. reflexivity.
         -- intros. destruct (Nat.eq_dec n target).
            subst. rewrite NatMap.gss in H0. inv H0.
            split. reflexivity. lia.
            rewrite NatMap.gso in H0.
            exploit FIND_TID; eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               econstructor; eauto.
               rewrite !NatMap.gss. reflexivity.
               subst target. intros. congruence.
            ++ destruct (THREADS n H0) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n1. specialize (J n1). subst wp'.
               eapply gw_accg_yield_accg; eauto. simpl.
               rewrite <- H.
               econstructor; eauto. inv H3. econstructor; eauto.
               inv H8. econstructor; eauto.
               exploit FIND_TID. apply I. intros [X Y].
               unfold gw_tid. simpl. 
               setoid_rewrite X. lia.
       + (*join*)
         assert (lsa = Returnj OpenA ls1 rs1).
         eapply foo; eauto. subst lsa. inv MS.
         assert (get wA = wPcur). clear -GETWp CUR_GWORLD.
         rewrite CUR_GWORLD in GETWp. inv GETWp. reflexivity. subst wPcur.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD. inv ACCY.
         assert (ACCEJ: injp_acce (get_injp wAca) (injpw f m' tm' Hmj')).
         { eapply injp_acc_yield_acce. rewrite <- H. inv H3.
           econstructor; eauto. eauto. }
         assert (ACCEE: ext_acce (extw m2 m3 Hme0) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (get_injp wAca) = injp_tid (injpw f m' tm' Hmj')).
           eauto. eapply ext_acc_yield_acce; eauto. inv H8. econstructor; eauto.
           simpl. rewrite <- H in BASE. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite BASE.
           erewrite inject_tid;eauto.
         }

         specialize (THREADS wait RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsat = AsmMulti.Final OpenA res ).   eapply foo; eauto. subst lsat.
         inv MSt.
         exploit ACCt. congruence. intro ACCt'.
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m'). rename rs1 into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         set (trs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (trs RA) trs)).
         unfold injp_w_compcert in VPTR. simpl in VPTR.
         setoid_rewrite <- H in VPTR. simpl in VPTR.
         simpl in VPTR_LOCAL, VPTR_PERM.
         rewrite <- H in VPTR_LOCAL, VPTR_PERM.
         unfold gw_tid in VPTR_LOCAL. unfold gw_m in VPTR_PERM.
         unfold injp_gw_compcert in VPTR_LOCAL, VPTR_PERM.
         simpl in VPTR_LOCAL, VPTR_PERM.
         inv VPTR.
         exploit Mem.valid_access_inject. 3: eauto. 2: eauto. eauto.
         intros PERM2.
         assert (PERM1': Mem.valid_access m' Many64 b (Ptrofs.unsigned ofs) Writable).
         { clear -H3 VPTR_PERM. inv H3. inv VPTR_PERM. constructor; eauto. }
         assert (PERM2': Mem.valid_access tm' Many64 b2 (Ptrofs.unsigned ofs + delta) Writable).
         { clear -H8 PERM2. inv H8. inv PERM2. constructor; eauto. }
         exploit Mem.storev_extends_rev. eauto. eauto. rewrite <- H5. eauto.
         erewrite Mem.address_inject; eauto. eauto with mem. eapply Val.lessdef_refl.
         intros [tm'' [MEM_RES' Hme'']].
         exploit Mem.storev_mapped_inject_rev. eauto. eauto. econstructor; eauto.
         instantiate (1:= res0).
         simpl in ACCt'. unfold get_injp in ACCt'.
         unfold get_injp in H. rewrite <- H in ACCt'.
         eapply val_inject_incr. 2: eauto. inv ACCt'.
         inv H10. simpl. eauto. eauto.
         rename m'' into ttm''.
         intros [m'' [MEM_RES'' Hmj'']].
         set (r_a := (rs', tm'')).
         set (tr_a := (trs', ttm'')).
         set (wpj' := injpw f m'' tm'' Hmj'').
         set (wp' := (tt,(tt, (wpj', extw tm'' ttm'' Hme'')))).
         assert (ACCEJ2: injp_acce (get_injp wAca) wpj').
         { eapply injp_acce_storev; eauto. }
         assert (ACCEE2: ext_acce (extw m2 m3 Hme0) (extw tm'' ttm'' Hme'')).
         { etransitivity. eauto.
           exploit ext_acci_storev. apply MEM_RES'. apply MEM_RES. rewrite <- H5. eauto. eauto. }
         assert (exists sc', after_external (OpenC se) sc (cr (Vint Int.one) m'') sc').
         eapply OpenC_after_external_receptive; eauto.
         destruct H0 as [sc'1 AFT_E'1]. 
         exploit M_REPLIES; eauto.
         instantiate (1:= (tt,(tt,(injpw f m'' tm'' Hmj'', extw tm'' ttm'' Hme'')))).
         repeat eapply conj; simpl; eauto. 
         instantiate (1:= tr_a). unfold tr_a. simpl.
         { (* match_reply *)
           eexists. split. econstructor. constructor.
           inv WT_WA. simpl in ACCEJ2. unfold wpj' in ACCEJ2. inv ACCEJ2.
           destruct H17 as [_ [X _]]. constructor; eauto.
           eexists. split. econstructor. inv WT_WA. unfold sig_w_compcert in WA_SIG.
           simpl in WA_SIG. rewrite WA_SIG. simpl. auto.
           exists r_a. split. unfold r_a. simpl.
           destruct wAca. simpl in *.
           econstructor; eauto.  inv WT_WA. unfold sig_w_compcert in WA_SIG.
           simpl in WA_SIG. rewrite WA_SIG.
           unfold Conventions1.loc_result.
           replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
           intros. unfold rs'.
           destruct r; simpl in H0; inv H0; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           constructor. simpl. intros. unfold rs', trs'.
           setoid_rewrite Pregmap.gsspec. destr; eapply val_inject_id; eauto.
           setoid_rewrite Pregmap.gsspec. destr; eapply val_inject_id; eauto.
           eapply val_inject_id; eauto.
           eapply val_inject_id; eauto. constructor.
         }
         intros [Hy1 Hy2]. exploit Hy2; eauto.
         intros (sa' & AFT_E' & li' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         destruct WAIT as [WAIT1 WAIT2]. destruct WAIT_THE as [X' Y].
         rewrite X' in WAIT1. inv WAIT1.
         eexists. exists i'. split.
         (*switch_in*)
         eapply CMulti.switch_in_join; eauto.
         simpl.
         (*match*)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y].
            split.
            transitivity (Mem.tid (Mem.support m')). reflexivity. erewrite Mem.support_storev; eauto.
            reflexivity.
            inv H3. simpl.
            rewrite <- H. simpl. unfold gw_nexttid. simpl. 
            transitivity (Mem.next_tid (Mem.support ((Mem.yield m1 n p)))). reflexivity. erewrite Mem.support_storev; eauto.
         -- intros. destruct (Nat.eq_dec n target).
            subst. rewrite NatMap.gss in H0. inv H0. split.
            unfold wp'. unfold gw_tid. simpl. erewrite <- Mem.support_storev; eauto. reflexivity. simpl. lia.
            rewrite NatMap.gso in H0. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; try rewrite NatMap.gss; eauto.
               econstructor; eauto. simpl. subst target. congruence.
            ++ destruct (THREADS n H0) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n1. specialize (J n1). simpl in n1. subst wp'.
               eapply gw_accg_acci_accg. eauto.
               rewrite <- H in HwaTid.
               repeat apply conj; simpl; eauto. rewrite <- H.
               eapply injp_acci_storev; eauto. instantiate (1:= Hmj'1).
               eapply injp_acc_yield_acci; eauto.
               inv H3. econstructor; simpl; eauto.
               etransitivity. eapply ext_acc_yield_acci; simpl; eauto.
               simpl. 
               erewrite <- inject_tid. 2: eauto.
               inversion Hmj'. inv mi_thread. inv Hms. rewrite <- H9. eauto.
               eapply ext_acci_storev; eauto. rewrite <- H5. eauto.
               constructor. 
       + (*initial, impossible*)
         simpl in *. exfalso.
         unfoldA_in GET_T. subst target.
         assert (lsa = Initial OpenA rs0). eapply foo; eauto.
         subst lsa. inv MS.
         eapply NOTINIT; eauto.
     - 
       simpl in RANGE.
       specialize (THREADS target RANGE) as THR_TAR.
       destruct THR_TAR as (wB & owA & wP & lsc & lsa & li & GETW & GETi & MSEw & GETC & GETA & GETWa & MS & GETWp & ACC).
       exploit ACC. eauto. intro ACCG.
       inv SWITCH.
       + (*yield*)
         assert (lsa = AsmMulti.Returny OpenA ls1 rs1).
         eapply foo; eauto. subst lsa. inv MS. simpl in *.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD. inv ACCY.
         inv ACCG. rewrite <- H in *. rename m5 into m2'0. rename m6 into m3'0.
         rename m4 into m1'0.
         assert (ACCEJ: injp_acce (injpw j m1'0 m2'0 Hmj1) (injpw f m' tm' Hmj')).
         { eapply injp_accg_yield_acce; eauto. 
           inv H3. econstructor; eauto. }
         assert (ACCEE: ext_acce (extw m2'0 m3'0 Hme1) (extw tm' ttm' Hme')).
         {
           assert (BASE:injp_tid (injpw j m1'0 m2'0 Hmj1) = injp_tid (injpw f m' tm' Hmj')). eauto.
           eapply ext_accg_yield_acce; eauto. inv H7. econstructor; eauto.
           simpl. simpl in BASE.
           erewrite <- inject_tid. 2: eauto. rewrite <- BASE.
           erewrite inject_tid; eauto.
         }
         set (qc := cr Vundef m'). rename rs1 into trs.
         set (rs := cajw_rs wAca).
         set (rs' := Pregmap.set PC (rs RA) rs).
         set (trs' := Pregmap.set PC (trs RA) trs).
         set (r_a := (rs', tm')).
         set (tr_a := (trs', ttm')).
         exploit M_REPLIES; eauto.
         instantiate (1:= (tt,(tt,(injpw f m' tm' Hmj',extw tm' ttm' Hme')))).
         repeat apply conj; simpl; eauto.
         instantiate (1:= tr_a). unfold tr_a.
         { (*match_reply*)
           eexists. split. instantiate (1:= cr Vundef m').
           econstructor; eauto. constructor.
           inv WT_WA. simpl in H. inv H. inv ACCEJ.
           destruct H16 as [_ [A _]].
           constructor; eauto.
           eexists. split. econstructor; eauto. inv WT_WA.
           unfold sig_w_compcert in WA_SIG. simpl in WA_SIG.
           rewrite WA_SIG. simpl. auto.
           exists (r_a). unfold r_a. split. destruct wAca.
           econstructor; eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; eauto. simpl.
           intros. unfold rs', trs'. setoid_rewrite Pregmap.gsspec.
           destr; eapply val_inject_id; eauto.
           constructor.
         }
         intros [Hy1 Hy2].
         assert (exists sc', after_external (OpenC se) sc (cr Vundef m') sc').
         eapply OpenC_after_external_receptive; eauto.
         destruct H0 as [sc'1 AFT_E'1].
         exploit Hy2; eauto.
         intros (sa' & AFT_E' & li' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (*switch_in*)
         econstructor; eauto.
         (*match*)
         set (wpj' := injpw f m' tm' Hmj').
         set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor; simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y]. subst wp'.
            split. reflexivity. inv H3. reflexivity.
         -- intros. destruct (Nat.eq_dec n0 target).
            subst. rewrite NatMap.gss in H0. inv H0.
            split. reflexivity. lia.
            rewrite NatMap.gso in H0. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n0 target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; eauto.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               rewrite NatMap.gss. reflexivity.
               econstructor; eauto. rewrite NatMap.gss. reflexivity.
               intros. subst target. congruence.
            ++ destruct (THREADS n0 H0) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n2. destruct (Nat.eq_dec n0 cur).
               subst.
               replace wnp with  (tt, (tt, (injpw f m1 m2 Hmj, extw m2 m3 Hme0)))
                 by congruence.
               eapply gw_yield_acci_accg. 2: reflexivity. unfold wp', wpj'.
               econstructor; eauto. inv H3. econstructor; eauto.
               inv H7. econstructor; eauto.
               apply FIND_TID in GETwpc. destruct GETwpc as [X Y]. rewrite X.
               unfold wp', wpj', gw_tid. simpl. lia. constructor.
               specialize (J n3).
               eapply gw_accg_yield_accg. eauto.
               econstructor; eauto. inv H3. econstructor; eauto.
               inv H7. econstructor; eauto.
               apply FIND_TID in I. destruct I as [X Y]. rewrite X.
               unfold wp', wpj'. simpl. unfold gw_tid. simpl. lia.
       + (*join*)
         assert (lsa = AsmMulti.Returnj OpenA ls1 rs1).
         eapply foo; eauto. subst lsa. inv MS.
         assert (wpc = wPcur). congruence. subst wpc.
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         destruct wA as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & wAca & wAe).
         simpl in GETwpc, ACCY, ACC, GETWp, HwaTid, RSLD, ACCG, VPTR.
         unfold injp_w_compcert in VPTR. simpl in VPTR.
         exploit gw_accg_yield_acce; eauto. constructor.
         intro ACCE. destruct ACCE as [_ [_ [ACCEJ ACCEE]]].
         simpl in ACCEJ, ACCEE. rename rs1 into trs.
         destruct wAca as [wAj sig rs]. simpl in VPTR.
         unfold sig_w_compcert in WA_SIG. simpl in WA_SIG, ACCEJ.
         (* get the waited thread state *)
         specialize (THREADS wait RNG_WAIT) as THR_TAR'.
         destruct THR_TAR' as (wBt & owAt & wPt & lsct & lsat & lit & GETWt & GETit & MSEwt & GETCt & GETAt & GETWat & MSt & GETWpt & ACCt).         
         assert (lsat = AsmMulti.Final OpenA res).   eapply foo; eauto. subst lsat.         
         inv MSt.
         assert (ACCT: gw_accg wPt wPcur \/ wPcur = wPt).
         {
           destruct (Nat.eq_dec wait cur). subst. right. congruence.
           left. eapply ACCt; eauto.
         }
         rename gmem'' into m''.
         set (qc := cr (Vint Int.one) m').
         set (rs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (rs RA) rs)).
         set (trs' := Pregmap.set RAX (Vint Int.one)(Pregmap.set PC (trs RA) trs)).
         simpl in VPTR_LOCAL, VPTR_PERM.
         inv VPTR.
         assert (PERMs: Mem.valid_access m' Many64 b (Ptrofs.unsigned ofs) Writable /\
                          Mem.valid_access tm' Many64 b2 (Ptrofs.unsigned ofs + delta) Writable).
         { 
           clear - H3 H4 MEM_RES ACCG ACCY VPTR_LOCAL VPTR_PERM.
           inv ACCG. inv ACCY.  simpl in H4.
           unfold gw_tid in VPTR_LOCAL. unfold gw_m in VPTR_PERM.
           unfold injp_gw_compcert in VPTR_LOCAL, VPTR_PERM.
           simpl in VPTR_LOCAL, VPTR_PERM.
           rename VPTR_PERM into PERM1.
           assert (PERM3': Mem.valid_access ttm' Many64 b2 (Ptrofs.unsigned ofs + delta) Writable).
           { rewrite <- H3 in MEM_RES. simpl in MEM_RES.
           erewrite Mem.address_inject in MEM_RES.
           eapply Mem.store_valid_access_3. eauto. 3: eauto. eauto. eauto with mem.
           }
           exploit Mem.valid_access_inject. 3: eapply PERM1. eauto. eauto. intro PERM2.
           exploit Mem.valid_access_extends. 2: eapply PERM2. eauto. intro PERM3.
           assert (TID2: fst b2 = Mem.tid (Mem.support m2)).
           erewrite <- inject_block_tid. 3: eauto. 2: eauto. erewrite <- inject_tid; eauto.
           assert (PERM2':  Mem.valid_access tm' Many64 b2 (Ptrofs.unsigned ofs + delta) Writable).
           {
             inv PERM3'. split; eauto. red. intros.
             exploit H. instantiate (1:= ofs0). lia. intro Hp3'.
             inv Hme'4. exploit mext_perm_inv. apply Hp3'.
             intros [A | B].
             eauto. inv H5. inv H14.
             red in FREEP.
             exploit FREEP. eauto. 
             inv PERM2. instantiate (1:= ofs0). exploit H5. instantiate (1:= ofs0). lia.
             eauto with mem. intro. apply B. eauto. eauto with mem.
             intro. inv H5.
           }
           split; eauto.
           inv PERM2'. split; eauto. red. intros.
           exploit H. instantiate (1:= ofs0 + delta). lia. intro Hp2'.
           inv Hmj'4. exploit mi_perm_inv. inv H1. eauto. eauto.
           intros [A | B]. eauto.
           inv H1. inv H2. exploit H25. eauto. eauto. inv PERM1.
           instantiate (1:= ofs0). eauto with mem.
           intro. apply B. eauto with mem. eauto with mem. intro. inv H1. inv PERM1. eauto.
         }
         destruct PERMs as [PERM1' PERM2'].

         exploit Mem.storev_extends_rev. eauto. eauto. rewrite <- H3. eauto.
         erewrite Mem.address_inject; eauto. eauto with mem. inv ACCEJ. eauto.
         eapply Val.lessdef_refl.
         intros [tm'' [MEM_RES' Hme'']].
         exploit Mem.storev_mapped_inject_rev. 5: eauto. eauto. eauto.
         econstructor; eauto. inv ACCEJ. eauto.
         inv ACCEJ. eapply val_inject_incr. 2: eauto. simpl.
         destruct ACCT. inv ACCY. inv H. simpl. inv H17. eauto.
         inv ACCY. eauto.
         rename m'' into ttm''.
         intros [m'' [MEM_RES'' Hmj'']].
         set (r_a := (rs', tm'')).
         set (tr_a := (trs', ttm'')).
         set (wpj' := injpw f m'' tm'' Hmj'').
         set (wp' := (tt,(tt,(wpj', extw tm'' ttm'' Hme'')))).
         assert (ACCEJ': injp_acce (wAj) wpj').
         eapply injp_acce_storev; eauto. simpl in *. inv ACCEJ. eauto.
         assert (ACCEE' : ext_acce wAe (extw tm'' ttm'' Hme'')).
         { etransitivity. eauto. exploit ext_acci_storev. apply MEM_RES'.
           apply MEM_RES. rewrite <- H3. eauto. eauto. }
         simpl in H1. inv WT_WA. simpl in ACC1. unfold rs_w_compcert in RSLD. simpl in RSLD.
         simpl in HwaTid.
         assert (exists sc', after_external (OpenC se) sc (cr (Vint Int.one) m'') sc').
         eapply OpenC_after_external_receptive; eauto.
         destruct H as [sc'1 AFT_E'1]. 
         exploit M_REPLIES; eauto.
         simpl. instantiate (1:= wp').
         repeat apply conj; eauto.
         { instantiate (1:= tr_a). unfold tr_a.
           eexists. split. econstructor; eauto. constructor.
           eapply ro_acc_trans. instantiate (1:= m'). inv ACCEJ. destruct H13 as [_ [A _]].
           constructor; eauto. unfold Mem.storev in MEM_RES''. destr_in MEM_RES''.
           eapply ro_acc_store; eauto.
           eexists. split. econstructor; eauto. constructor.
           exists r_a. unfold r_a. split.
           econstructor; eauto. unfold Conventions1.loc_result.
           replace Archi.ptr64 with true. simpl. unfold rs'. rewrite Pregmap.gss. constructor. eauto.
           intros. unfold rs'.
           destruct r; simpl in H; inv H; repeat rewrite Pregmap.gso;
             simpl; try congruence; try reflexivity.
           econstructor; eauto. simpl. intros. unfold rs', trs'.
           setoid_rewrite Pregmap.gsspec. destr; eauto. eapply val_inject_id; eauto.
           setoid_rewrite Pregmap.gsspec. destr; eauto. constructor. }
         intros [Hy1 Hy2]. exploit Hy2; eauto.
         intros (sa' & AFT_E' & li' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         destruct WAIT as [WAIT1 WAIT2]. destruct WAIT_THE as [X' Y].
         rewrite X' in WAIT1. inv WAIT1.
         eexists. exists i'. split.
         (*switch_in*)
         eapply CMulti.switch_in_join; eauto.
         (*match*)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. simpl. 8:{  rewrite NatMap.gss. reflexivity. }
         all: simpl; eauto.
         -- erewrite set_nth_error_length; eauto.
         -- intros. fold target. destruct (Nat.eq_dec 1 target).
            subst target. rewrite e. rewrite NatMap.gss. congruence.
            rewrite NatMap.gso. eauto. eauto.
         -- destruct CUR_INJP_TID as [X Y].
            split.
            transitivity (Mem.tid (Mem.support m')). reflexivity. erewrite Mem.support_storev; eauto.
            unfold wp', wpj'. unfold gw_tid. simpl. reflexivity.
            inv ACCY. inv H6. unfold gw_nexttid. simpl.
            transitivity (Mem.next_tid (Mem.support ((Mem.yield m1 n0 p)))). reflexivity.
            erewrite Mem.support_storev; eauto.
         -- intros. destruct (Nat.eq_dec n0 target).
            subst. rewrite NatMap.gss in H. inv H. unfold gw_tid. simpl.
            erewrite <- Mem.support_storev; eauto. split. reflexivity. lia.
            rewrite NatMap.gso in H. eauto. eauto.
         -- intros.
            instantiate (1:= NatMap.set target None worldsA).
            destruct (Nat.eq_dec n0 target).
            ++ subst.
               exists wB, None, wp'. eexists. eexists. exists li'.
               repeat apply conj; try rewrite NatMap.gss; eauto.
               econstructor; eauto. simpl. intros. subst target. congruence.
            ++ destruct (THREADS n0 H) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
               exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
               rewrite <- OTHERi; eauto. lia.
               intros n2.
               assert (ACIJS: injp_acci (injpw f m' tm' Hmj') (injpw f m'' tm'' Hmj'')).
               apply injp_acc_tl_i.
               eapply injp_acc_tl_storev; eauto. inv ACCEJ. eauto.
               exploit ext_acci_storev. apply MEM_RES'. apply MEM_RES. rewrite <- H3.
               eauto. intro ACIES.
               destruct (Nat.eq_dec n0 cur).
               subst. replace wnp with wPcur by congruence.
               eapply gw_accg_acci_accg.
               eapply gw_acc_yield_accg. eauto.
               simpl in ACCG.
               apply gw_accg_neq in ACCG as NEQ.
               inv ACCEJ. destruct H14 as [[AA BB] _]. simpl.
               unfold gw_tid. simpl. rewrite <- BB.
               unfold gw_tid in NEQ. simpl in NEQ. eauto.
               repeat apply conj; simpl; eauto. constructor.
               specialize (J n3).
               eapply gw_accg_acci_accg.
               eapply gw_accg_yield_accg. eauto. eauto. simpl.
               apply FIND_TID in I. destruct I as [X Y]. rewrite X.
               unfold gw_tid. simpl. eauto.
               repeat apply conj; simpl; eauto. constructor.
       + (* initial *)
         assert (lsa = AsmMulti.Initial OpenA rs0).
         eapply foo; eauto. subst lsa. inv MS.
         assert (wpc = wPcur). congruence. subst wpc.
         exploit ACC. eauto. intro ACCG_wB_wPcur.
         set (wpj' := injpw f m' tm' Hmj').
         apply FIND_TID in GETWp as X. destruct X as [HwaTid RNGtarget].
         set (wp' := (tt,(tt,(wpj', extw tm' ttm' Hme')))).
         exploit gw_accg_yield_acce. eauto. eauto.
         eauto. constructor. intro ACCG1.
         remember wB as wBi.
         destruct wBi as (se0 & [se0' m0'] & se1 & [se1' sig'] & se2 & [wBj sig'' rsB] & wBe).
         simpl in ACCG, ACC, GETWp, HwaTid, ACCG_wB_wPcur, ACCG1.
         set (wB' := (se0,
           ({| ro_symtbl := se0'; ro_mem := m' |},
           (se1,
             (se1', sig', (se2, ({| cajw_injp := wpj'; cajw_sg := sig''; cajw_rs := rsB |}, extw tm' ttm' Hme'))))))).
         rename rs0 into trs.

         (*break the M_QUERIRES and MSEw*)
         destruct M_QUERIES as [qc' [Hq1 [qc'' [Hq2 [qa'' [Hq3 Hq4]]]]]].
         destruct cqv. inv Hq1. inv H. inv Hq2. inv H.
         simpl in *. inv Hq3. inv Hq4. destruct H0. inv H4. rename tm into ttm. rename tm1 into tm. rename rsB into rs. simpl in H.
         destruct ACCG1 as [_ [_ [ACCGJ ACCGE]]].
         simpl in ACCGJ, ACCGE.
         assert (MQ_CUR: GS.match_query cc_compcert wB'
                           (cq cqv_vf start_routine_sig cqv_args m') (trs, ttm')).
         {
           subst targs tsp0. 
           assert (Hincr :inject_incr j f).
           inv ACCGJ. eauto. 
           eexists. split. econstructor; eauto. constructor.
           eapply ro_acc_sound; eauto. inv ACCGJ.
           destruct H24 as [_ [? _]]. constructor; eauto.
           eexists. split. econstructor; simpl; eauto.
           exists (rs, tm'). split. simpl.
           econstructor; simpl; eauto.
           rewrite start_routine_loc in H9. simpl in H9. 
           rewrite start_routine_loc. simpl.
           eapply val_inject_list_incr; eauto.
           intros. unfold Conventions.size_arguments in H4.
           setoid_rewrite start_routine_loc in H4. simpl in H4. inv H4. extlia.
           inv ACCGJ. inv H15.
           econstructor. simpl. apply H25. eauto.
           inv ACCGJ. inv H16. econstructor. destruct H25 as [[_ B] _]. congruence.
           econstructor.  red. unfold Conventions.size_arguments.
           rewrite start_routine_loc. simpl. auto.
           constructor. simpl. eauto.
           split; eauto. constructor.
         }
         destruct MSEw as (A & B & C & D). inv A. inv B. inv C.
         assert (MSEw' : GS.match_senv cc_compcert wB' se tse).
         {
           split. constructor. reflexivity.
           split; constructor. reflexivity.
           inv ACCGJ. constructor. eapply Genv.match_stbls_incr_noglobal; eauto.
           destruct H27 as [P [Q R]]. eauto.
           destruct H28 as [P [Q R]]. eauto.
           reflexivity.
         }
         specialize (bsim_lts se tse wB' MSEw' valid_se) as BSIM.
         inversion BSIM.
         clear bsim_simulation bsim_match_final_states bsim_match_external.
         exploit bsim_match_initial_states.  eauto.
         intros [Hi1 Hi2].
         assert (exists s1'1, Smallstep.initial_state (OpenC se) (cq cqv_vf start_routine_sig cqv_args m') s1'1).
         destruct INIT_QUERY as [s' INIT1''].
         eapply OpenC_initial_state_receptive; eauto.
         inv ACCGJ. destruct H27 as [_ [? _]]. eauto.
         destruct H4 as [s1'1 INIT'1].
         exploit Hi2; eauto.
         intros (ls' & INIT & li' & MLS').
         specialize (get_nth_set (target-1) i li li' GETi) as SETi.
         destruct SETi as (i' & SETi & Newi & OTHERi).
         eexists. exists i'. split.
         (* switin_in_initial *)
         eapply CMulti.switch_in_initial. eauto. eauto. eauto.
     (* match_states *)
         econstructor. instantiate (1:= NatMap.set target (Some wp') worldsP).
         econstructor. 6:{ instantiate (2:= NatMap.set target (Some wB') worldsB).
         rewrite NatMap.gso. eauto. congruence. }
         all: simpl; eauto. erewrite set_nth_error_length; eauto.
         intros. destruct (Nat.eq_dec 1 target). subst. congruence.
         rewrite NatMap.gso. eauto. eauto.
         intros. destruct (Nat.eq_dec n0 target) in H0. subst.
         rewrite NatMap.gss in H5. inv H5.
         split; reflexivity. 
         rewrite NatMap.gso in H5. eauto. eauto.
         rewrite NatMap.gss. reflexivity.
         unfold wp'. simpl. split. eauto.
         destruct CUR_INJP_TID as [X Y]. inv ACCY.
         unfold gw_nexttid. simpl. inv H8. eauto.
         intros. destruct (Nat.eq_dec n0 target). subst.
         rewrite NatMap.gss in H4.
         inv H4. split. reflexivity. lia.
         rewrite NatMap.gso in H4. eauto. eauto.
         intros. instantiate (1:= worldsA).
         destruct (Nat.eq_dec n0 target). subst.
         exists wB', None, wp'. eexists. eexists. exists li'.

         destruct MSEw' as (AA & BB & CC & DD).
         repeat apply conj; try rewrite NatMap.gss; eauto.
         econstructor. red. eauto.
         intros. subst target. congruence.
         destruct (THREADS n0 H4) as (wn & owan & wnp & lscn & lsan & lin & A & B & C & D & E & F & G & I & J).
         exists wn, owan, wnp, lscn,lsan,lin. repeat apply conj; try rewrite NatMap.gso; eauto.
         rewrite <- OTHERi; eauto. lia.
         intros n2.
         apply gw_accg_neq in ACCG as GTID. unfold gw_tid in GTID. simpl in GTID.
         assert (TTID: Mem.tid (Mem.support m) = Mem.tid (Mem.support m')).
         inv ACCGJ. destruct H28 as [[AA BB] _]. eauto.
         destruct (Nat.eq_dec n0 cur).
         subst. replace wnp with wPcur by congruence.
         eapply gw_acc_yield_accg. eauto. simpl. 
         unfold gw_tid. simpl. rewrite <- TTID. lia.
         specialize (J n3).
         eapply gw_accg_yield_accg. eauto. eauto.
         apply FIND_TID in I. destruct I as [X Y]. rewrite X.
         unfold gw_tid. simpl. rewrite <- TTID. lia.
   Qed.

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
        inversion P0. constructor. auto. erewrite <- inject_next_tid; eauto.
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
         red. intros. eauto with mem.
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
       + red. intros.
         assert (~Mem.perm tm b2 (ofs1+ delta) Max Nonempty). eapply H32; eauto.
         intro.
         apply H18. assert (Mem.perm tm2 b2 (ofs1 + delta) Max Nonempty).
         eapply Mem.perm_alloc_4; eauto.
         intro. subst. apply Mem.fresh_block_alloc in DUMMY.
         apply H29 in H.
         apply DUMMY. eapply Mem.valid_block_inject_2; eauto.
         eauto with mem.
       + inv H21. inv ROACCR2. inv ROACCR3.
         constructor; simpl. eauto. eauto.
         eapply Mem.sup_include_trans; eauto.
         eapply Mem.sup_include_trans; eauto.
         eapply max_perm_decrease_trans. apply MPD1. eauto. eauto.
         eapply max_perm_decrease_trans. apply MPD2. eauto. eauto.
          red. intros.
         intro. eapply FREEP; eauto.
         intro. apply H24.
         assert (Mem.perm tm2 b ofs Max Nonempty). eauto with mem.
         eapply Mem.perm_alloc_1 in H27. 2: eauto. eauto with mem.
         assert (Mem.perm ttm3 b ofs Max Nonempty). eauto with mem.
         eapply Mem.perm_alloc_4 in H26. 2: eauto.
         assert (Mem.perm ttm1 b ofs Max Nonempty). eauto with mem.
         inv MEM_CREATE. eauto.
         intro. subst b.
         apply Mem.fresh_block_alloc in DUMMY.
         apply DUMMY.
         assert (Mem.valid_block tm sp0). apply SUP1. eapply Mem.perm_valid_block; eauto.
         unfold tm2. unfold Mem.valid_block. simpl. apply Mem.sup_yield_in. rewrite <- Mem.sup_create_in. eauto.
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
              + inv H; unfoldC_in H6; unfoldC_in GET_C; rewrite NatMap.gss in GET_C; inv GET_C.
                -- inv DetC.  exploit sd_big_at_external_determ. apply AT_PTC. apply AT_E.
                   intro. subst.
                   inv H4. inv Q_YIE. exploit cc_compcert_mq_ms_id; eauto. intro. inv H7.
                -- inv DetC.  exploit sd_big_at_external_determ. apply AT_PTC. apply AT_E.
                   intro. subst.
                   inv H4. inv Q_JOIN.  exploit cc_compcert_mq_ms_id; eauto. intro. inv H.
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
                  inv CREATE. eauto.
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
          rename s2' into s2''. rename s' into s2'.
          exploit substep_switch_out; eauto. inv H0. inv H. eauto.
          intros (s1s & s1' & tm' & ttm' & worldsP & wpc & f & Hme' & Hmj' & A & B & C & D & E& F & G).
          exploit substep_switch_in; eauto.
          intros (s1'' & i' & X & Y).
          exists i', s1''. split. left. eapply plus_right. eauto.
          eapply CMulti.step_switch; eauto. eauto. eauto.
   Qed.
   
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
    
  Definition after_external_receptive (lts : semantics li_c li_c) : Prop :=
    forall s q r se,
      Smallstep.at_external (lts se) s q ->
      exists s', Smallstep.after_external (lts se) s r s'.

  Definition initial_state_receptive (lts : semantics li_c li_c) : Prop :=
    forall s vf sg args se m m',
      Smallstep.initial_state (lts se) (cq vf sg args m) s ->
      Mem.sup_include (Mem.support m) (Mem.support m') ->
      exists s', Smallstep.initial_state (lts se) (cq vf sg args m') s'.

  Lemma BSIM : GS.backward_simulation cc_compcert OpenC OpenA ->
               determinate_big OpenC ->
               after_external_receptive OpenC ->
               initial_state_receptive OpenC ->
               Closed.backward_simulation ConcurC ConcurA.
  Proof.
    intros. inv H. inv X. eapply Concur_Sim; eauto.
  Qed.

End ConcurSim.


  Lemma Clight_determinate_big: forall p, determinate_big (Clight.semantics1 p).
  Proof.
    intros p se. constructor.
    - (*initial_determ*)
      intros. inv H; inv H0. reflexivity.
    - (*initial_nostep*)
      intros. red. intros. intro. inv H. inv H0. 
      setoid_rewrite H1 in FIND. inv FIND.
      setoid_rewrite H1 in FIND. inv FIND. inv H7.
    - (*ext_determ*)
      intros. inv H. inv H0. setoid_rewrite H1 in H6. inv H6. reflexivity.
    - (*after_determ*)
    intros. inv H. inv H0. reflexivity.
    - (*final_nostep*)
      intros. red. intros. intro. inv H. inv H0.
    - (*final_noext*)
      intros. inv H. inv H0.
    - (*final_determ*)
      intros. inv H. inv H0. reflexivity.
  Qed.

  Lemma Clight_after_external_receptive :
    forall (p: Clight.program), after_external_receptive (Clight.semantics1 p).
  Proof.
    intros p. red. intros. inv H. destruct r.
    eexists. econstructor; eauto.
  Qed.

  Lemma Clight_initial_state_receptive :
    forall (p: Clight.program), initial_state_receptive (Clight.semantics1 p).
  Proof.
    intros p. red. intros. inv H.
    eexists. econstructor; eauto.
  Qed.
  

