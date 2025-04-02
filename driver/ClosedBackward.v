Require Import Coqlib Errors Events Globalenvs Ctypes AST Memory Values Integers.
Require Import LanguageInterface Asm.
Require Import Smallstep SmallstepClosed Loading.
Require Import ValueAnalysis.
Require Import Inject InjectFootprint.
Require Import CA Compiler.

(** Instantiation of [close_sound_backward] for simulation using the simconv [cc_compcert] *)
Section CLOSE_BACKWARD.
  
Variable L_c : semantics li_c li_c.
Variable L_asm : semantics li_asm li_asm.

Hypothesis BSIM_CC : backward_simulation cc_compcert cc_compcert L_c L_asm.
Hypothesis det_big_C: determinate_big L_c.

Let skel_c := skel L_c.
Let main_id_c := prog_main skel_c.

Let skel_asm := skel L_asm.
Let main_id_asm := prog_main skel_asm.

Let se := Genv.symboltbl skel_c.
Let tse := Genv.symboltbl skel_asm.

Lemma skel_eq : skel_asm = skel_c.
Proof. inv BSIM_CC. inv X. eauto. Qed.

Lemma main_id_eq : main_id_asm = main_id_c.
Proof. pose proof skel_eq. unfold main_id_asm, main_id_c. congruence. Qed.

Lemma symtbl_eq : tse = se.
Proof. pose proof skel_eq. unfold se, tse. congruence. Qed.
  
Definition main_sg := AST.mksignature nil (AST.Tret AST.Tint) AST.cc_default.

Lemma main_sg_locs : Conventions1.loc_arguments main_sg = nil.
Proof. unfold Conventions1.loc_arguments. destr. destr. Qed.

Lemma main_sg_size: Conventions.size_arguments main_sg = 0.
Proof.
  unfold Conventions.size_arguments, Conventions1.loc_arguments. simpl.
  destruct Archi.ptr64, Archi.win64; simpl; auto.
Qed.

Inductive initial_c : query li_c -> Prop :=
|initial_c_intro: forall m main_b,
    Genv.init_mem skel_c = Some m ->
    Genv.find_symbol se main_id_c = Some main_b ->
    initial_c (cq (Vptr main_b Ptrofs.zero) main_sg nil m).

(** This definition is not deterministic. Will this becomes a problem? *)
Inductive final_c : int -> reply li_c -> Prop :=
|final_c_int : forall r m,
    final_c r (cr (Vint r) m).
(*|final_c_other : forall res r m,
    (forall i, res <> Vint i) ->
    final_c r (cr res m). *)


Definition initial_regset (pc : val) (sp: val):=
    (Pregmap.init Vundef) # PC <- pc
                          # RA <- Vnullptr
                          # RSP <- sp.

Inductive initial_asm : query li_asm -> Prop :=
|initial_asm_intro : forall m0 m main_b bsp rs,
    Genv.init_mem skel_asm = Some m0 ->
    Mem.alloc m0 0 0 = (m, bsp) ->
    Genv.find_symbol tse main_id_asm = Some main_b ->
    rs = initial_regset (Vptr main_b Ptrofs.zero) (Vptr bsp Ptrofs.zero) ->
    initial_asm (rs,m).

Inductive final_asm : int -> reply li_asm -> Prop :=
|final_asm_int : forall r (rs : regset) m,
     rs # RAX = Vint r ->
     final_asm r (rs,m).
(*|final_asm_other : forall r (rs: regset) m,
    (forall i, rs # RAX <> Vint i) ->
    final_asm r (rs,m). *)

Inductive valid_world_cc_compcert : ccworld cc_compcert -> Prop :=
|valid_w_intro: forall se j1 j2 m1 m2 m3 Hm1 Hm2 rs,
    valid_world_cc_compcert (se, row se m1,(se,(se,main_sg),(se,cajw (injpw j1 m1 m2 Hm1) main_sg rs,injpw j2 m2 m3 Hm2))).

Section Initial.
  
  Variable m0 : mem.
  Variable main_b : block.
  Variable tm : mem.
  Variable bsp : block.
  
  Hypothesis INITM: Genv.init_mem (skel_c) = Some m0.
  Hypothesis FINDMAIN: Genv.find_symbol se main_id_c = Some main_b.
  Hypothesis DUMMYSP: Mem.alloc m0 0 0 = (tm, bsp).
  
  Let j0 := Mem.flat_inj (Mem.support m0).
  Let Hm0_ := Genv.initmem_inject (skel_c) INITM.
  
  Lemma Hm0 : Mem.inject j0 m0 tm.
  Proof.
    eapply Mem.alloc_right_inject; eauto.
  Qed.
  
  Definition wj0 := injpw j0 m0 tm Hm0.
  
  Lemma Hvalid: Mach.valid_blockv (Mem.support tm) (Vptr bsp Ptrofs.zero).
  Proof.
    constructor. eapply Mem.valid_new_block. eauto.
  Qed.
  
  Definition rs0 := initial_regset (Vptr main_b Ptrofs.zero) (Vptr bsp Ptrofs.zero).

  Let j' := fun b => if eq_block b bsp then Some (bsp ,0) else j0 b.

  Lemma Hm1 : Mem.inject j' tm tm.
  Proof.
  generalize Hm0_. intro H.
  exploit Mem.alloc_parallel_inject. eauto. eauto.
  reflexivity. reflexivity.
  intros (j'1 & m2' & dsp' & A &B & C & D& E).
  rewrite DUMMYSP in A. inv A.
  replace j' with j'1. eauto.
  apply Axioms.functional_extensionality.
  intros. unfold j'. destr. subst. eauto. eapply E; eauto.
  Qed.

  Definition init_w_cainjp := cajw wj0 main_sg rs0.
 
  Definition init_w_injp := injpw j' tm tm Hm1.

  Definition init_w : ccworld cc_compcert.
  unfold cc_compcert, cc_c_asm_injp. simpl.
  (* ro *)
  split. split. exact se. split. exact se. exact m0.
  (* wt_c *)
  split. split. exact se. split. exact se. exact main_sg.
  (* cc_c_asm_injp *)
  split. split. exact se. exact init_w_cainjp. exact init_w_injp.
  Defined.  

  Theorem valid_init_w : valid_world_cc_compcert init_w.
  Proof. constructor. Qed.
    
  Theorem sound_ro : sound_memory_ro se m0.
  Proof.
    eapply initial_ro_sound; eauto.
  Qed.

  Lemma m0_se_support : Genv.genv_sup se = Mem.support m0.
  Proof. eapply Genv.init_mem_genv_sup; eauto. Qed.

  Lemma main_sp_neq : main_b <> bsp.
  Proof.
    simpl. apply Mem.fresh_block_alloc in DUMMYSP.
    apply Genv.genv_symb_range in FINDMAIN. rewrite m0_se_support in FINDMAIN.
    intro. subst. eauto.
  Qed.

  Lemma j_main : j0 main_b = Some (main_b, 0).
  Proof.
    apply Genv.genv_symb_range in FINDMAIN.  rewrite m0_se_support in FINDMAIN.
    unfold j0, Mem.flat_inj. rewrite pred_dec_true; eauto.
  Qed.
         
  (** match_senv *)
  
  Lemma match_se_initial : Genv.match_stbls (Mem.flat_inj (Mem.support m0)) se se.
  Proof.
    pose proof m0_se_support as SUP.
    constructor; intros; eauto.
    - rewrite <- SUP. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
    - rewrite <- SUP. exists b2. unfold Mem.flat_inj. rewrite pred_dec_true; eauto.
    - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
    - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
    - unfold Mem.flat_inj in H. destruct Mem.sup_dec in H; inv H. reflexivity.
  Qed.
    
  Lemma Hmatch_senv : match_senv cc_compcert init_w se se.
  Proof.
    pose proof m0_se_support as SUP.
    apply Mem.fresh_block_alloc in DUMMYSP as FRESH; eauto.
    assert (SUPINCL: Mem.sup_include (Mem.support m0) (Mem.support tm)).
    apply Mem.support_alloc in DUMMYSP. rewrite DUMMYSP. red.
    intros. apply Mem.sup_incr_in2; eauto.
    unfold cc_compcert. simpl.
    split; [|split; [|split]].
    constructor. auto.
    constructor. auto.
    econstructor. apply match_se_initial; eauto.
    rewrite SUP. eauto.
    rewrite SUP. eauto.
    constructor.
    eapply Genv.match_stbls_incr. apply match_se_initial.
    red. intros. unfold j'. destr. subst b. unfold Mem.flat_inj in H. destr_in H.
    { intros. rewrite SUP. unfold j', j0 in H0. destr_in H0. inv H. unfold Mem.flat_inj in H2. destr_in H2; eauto. }
    rewrite SUP. eauto.
    rewrite SUP. eauto.
  Qed.

  Lemma Hmatch_query : match_query cc_compcert init_w
    {| cq_vf := Vptr main_b Ptrofs.zero; cq_sg := main_sg; cq_args := nil; cq_mem := m0 |}
    (initial_regset (Vptr main_b Ptrofs.zero) (Vptr bsp Ptrofs.zero), tm).
  Proof.
    set (rs := initial_regset (Vptr main_b Ptrofs.zero) (Vptr bsp Ptrofs.zero)).
    assert (rsPC : rs # PC = Vptr main_b Ptrofs.zero).
    unfold rs,rs0, initial_regset.
    rewrite Pregmap.gso; try congruence.
    rewrite Pregmap.gso; try congruence.
    rewrite Pregmap.gss. reflexivity.
    assert (rsRA : rs # RA = Vnullptr).
    unfold rs,rs0, initial_regset.
    rewrite Pregmap.gso; try congruence.
    rewrite Pregmap.gss. reflexivity.
    econstructor. split. constructor. simpl. constructor. apply sound_ro. eauto.
    econstructor. split. constructor. simpl. eauto.
    exists (rs,tm). split.
    +
    econstructor; simpl; eauto. rewrite main_sg_locs. simpl. constructor.
    rewrite rsPC. econstructor; eauto. apply j_main; eauto.  rewrite Ptrofs.add_zero. reflexivity.
    rewrite main_sg_size. intros. inv H. extlia.
    unfold Tptr. replace Archi.ptr64 with true. reflexivity. eauto.
    rewrite rsRA. unfold Vnullptr. replace Archi.ptr64 with true.
    econstructor. eauto. eapply Hvalid; eauto. constructor. red. apply main_sg_size; eauto. congruence.
    rewrite rsRA. unfold Vnullptr. destr.
    +
    econstructor; simpl; eauto. intros.
    unfold rs, rs0, initial_regset.
    setoid_rewrite Pregmap.gsspec. destr; eauto.
    econstructor.  unfold j'. rewrite pred_dec_true; eauto.
    rewrite Ptrofs.add_zero. reflexivity.
    setoid_rewrite Pregmap.gsspec. destr; eauto. constructor.
    setoid_rewrite Pregmap.gsspec. destr; eauto. 
    econstructor. unfold j'. rewrite pred_dec_false; eauto.
    apply j_main; eauto. eapply main_sp_neq; eauto.
    rewrite Ptrofs.add_zero. reflexivity.
    split. unfold rs, rs0, initial_regset.
    rewrite Pregmap.gso; try congruence. rewrite Pregmap.gso; try congruence.
    rewrite Pregmap.gss. congruence. constructor.
  Qed.
    
End Initial.

Let LTS_asm := L_asm tse.


Lemma match_initial_backward_ca1 : forall q1,
    initial_c q1 -> exists wB q2,
      match_query cc_compcert wB q1 q2 /\
        match_senv cc_compcert wB se tse /\
        initial_asm q2 /\ valid_world_cc_compcert wB.
Proof.
  intros. inv H. rename m into m0.
  caseEq (Mem.alloc m0 0 0). intros m bsp Hdummy.
  set (wB:= init_w m0 main_b m bsp H0 Hdummy).
  set (rs := rs0 main_b bsp).
  exists wB. exists (rs,m). repeat apply conj.
  - eapply Hmatch_query; eauto.
  - (*ms*)
    rewrite symtbl_eq. eapply Hmatch_senv.
  - (*init_asm*)
    econstructor; eauto. rewrite skel_eq; eauto.
    rewrite main_id_eq, symtbl_eq; eauto. reflexivity.
  - constructor.
Qed.

(** seems to be correct *)
Lemma match_initial_backward_ca2 : forall q1 q2,
    initial_c q1 -> initial_asm q2 -> exists wB,
        match_query cc_compcert wB q1 q2 /\ match_senv cc_compcert wB se tse /\ valid_world_cc_compcert wB.
Proof.
  intros. inv H. inv H0. rewrite skel_eq in H.
  rewrite H1 in H. inv H.
  rewrite main_id_eq in H4. rewrite symtbl_eq in H4. rewrite H2 in H4. inv H4.
  set (wB:= init_w m0 main_b0 m1 bsp H1 H3).
  exists wB. split.
  eapply Hmatch_query; eauto. split.
  rewrite symtbl_eq.
  eapply Hmatch_senv; eauto. constructor.
Qed.

Lemma match_final_backward_ca : forall rv1 rv2 r1 r2 wB,
    match_reply cc_compcert wB r1 r2 -> valid_world_cc_compcert wB ->
    final_asm rv2 r2 -> final_c rv1 r1 -> rv1 = rv2.
Proof.
  intros. inv H0. destruct H as [rx [Hr1 [ry [Hr2 [rz [Hr3 Hr4]]]]]].
  inv Hr1. inv Hr2. inv H. simpl in H0. inv Hr3. inv Hr4. destruct H as [Hw Hj].
  destruct r2. inv Hj. inv H3. rename m into ttm'.
  simpl in H.
  subst tres. unfold main_sg in H10. simpl in H10. unfold Conventions1.loc_result in H10.
  replace Archi.ptr64 with true in H10 by reflexivity. simpl in H10.
  specialize (H RAX). 
  inv H1. inv H2. inv H10. rewrite <- H3 in H. inv H. congruence.
Qed.

Lemma match_final_forward_ca : forall rv r1 r2 wB,
    match_reply cc_compcert wB r1 r2 -> valid_world_cc_compcert wB ->
     final_c rv r1 -> final_asm rv r2.
Proof.
  intros. inv H0. destruct H as [rx [Hr1 [ry [Hr2 [rz [Hr3 Hr4]]]]]].
  inv Hr1. inv Hr2. inv H. simpl in H0. inv Hr3. inv Hr4. destruct H as [Hw Hj].
  destruct r2. inv Hj. inv H3. rename m into ttm'.
  simpl in H.
  subst tres. unfold main_sg in H9. simpl in H9. unfold Conventions1.loc_result in H9.
  replace Archi.ptr64 with true in H9 by reflexivity. simpl in H9.
  specialize (H RAX). 
  inv H1. inv H2. inv H9. constructor. rewrite <- H6 in H. inv H. congruence.
Qed.

Definition close_c := close_semantics L_c initial_c final_c.
Definition close_asm := close_semantics L_asm initial_asm final_asm.

Hypothesis closed_Lasm : forall s2 q, ~ at_external LTS_asm s2 q.
Theorem closed_backward_simulation_cc_compcert :
  Closed.backward_simulation close_c close_asm.
Proof.
  eapply close_sound_backward.
  intros. eapply closed_Lasm.
  exact match_initial_backward_ca1.
  exact match_initial_backward_ca2.
  exact det_big_C.
  intros. symmetry. eapply match_final_backward_ca; eauto.
  exact match_final_forward_ca.
  exact BSIM_CC.
Qed.
  
End CLOSE_BACKWARD.

(* Checking whether the defs and lemmas from are typed as we want in the outside of the Section. *)
(* Check close_c.
Check close_asm.
Check closed_backward_simulation_cc_compcert. *)

Definition closed_program_asm (p: Asm.program): Prop :=
  forall i f ef, Maps.PTree.get i (prog_defmap p) = Some (Gfun f) -> f <> External ef.

Definition closed_semantics_asm (L : semantics li_asm li_asm ) : Prop :=
  forall s q, ~ at_external (L ((Genv.symboltbl (skel L)))) s q.

Lemma closed_program_asm_LTS: forall p, 
    closed_program_asm p ->
    closed_semantics_asm (Asm.semantics p).
Proof.
  intros. red. red in H. intros. intro.
  red in H0. simpl in H0. destruct s. inv H0.
  unfold Genv.find_funct in H1. destr_in H1. destr_in H1.
  rewrite Genv.find_funct_ptr_iff in H1.
  setoid_rewrite Genv.find_def_spec in H1. destr_in H1.
  eapply H; eauto.
Qed.

Corollary transf_bsim_single_clight : forall p tp,
    transf_clight_program p = OK tp ->
    closed_program_asm tp ->
    Closed.backward_simulation (close_c (Clight.semantics1 p)) (close_asm (Asm.semantics tp)).
Proof.
  intros.
  eapply closed_backward_simulation_cc_compcert.
  apply clight_semantic_preservation.
  apply transf_clight_program_match; auto.
  eapply Clight_determinate_big.
  eapply closed_program_asm_LTS; eauto.  
Qed.

Corollary transf_bsim_single_c : forall p tp,
    transf_c_program p = OK tp ->
    closed_program_asm tp ->
    Closed.backward_simulation (close_c (Csem.semantics p)) (close_asm (Asm.semantics tp)).
Proof.
  intros.
  eapply closed_backward_simulation_cc_compcert.
  apply transf_c_program_correct; auto.
  eapply Csem_determinate_big.
  eapply closed_program_asm_LTS; eauto.  
Qed.

Require Import Linking SmallstepLinking.
Require Import AsmLinking.

Corollary transf_bsim_link_clight :
  forall p1 p2 spec tp1 tp2 tp,
    compose (Clight.semantics1 p1) (Clight.semantics1 p2) = Some spec ->
    transf_clight_program p1 = OK tp1 ->
    transf_clight_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    closed_program_asm tp ->
    Closed.backward_simulation (close_c spec) (close_asm (Asm.semantics tp)).
Proof.
  intros.
  eapply closed_backward_simulation_cc_compcert; eauto.
  apply forward_to_backward_simulation.
  eapply compose_transf_clight_program_correct; eauto.
  - unfold compose in H. unfold option_map in H. destr_in H. inv H.
    eapply semantics_receptive. destruct i; eapply Clight.semantics_receptive; eauto.
  - eapply Asm.semantics_determinate.
  - eapply compose_determinate_big; eauto; eapply Clight_determinate_big.
  - eapply closed_program_asm_LTS; eauto.
Qed.

Require Import SmallstepLinkingBack.

Corollary transf_bsim_link_c :
  forall p1 p2 spec tp1 tp2 tp,
    compose (Csem.semantics p1) (Csem.semantics p2) = Some spec ->
    transf_c_program p1 = OK tp1 ->
    transf_c_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    closed_program_asm tp ->
    Closed.backward_simulation (close_c spec) (close_asm (Asm.semantics tp)).
Proof.
  intros.
  eapply closed_backward_simulation_cc_compcert; eauto.
  3: { eapply closed_program_asm_LTS; eauto. }
  eapply compose_transf_c_program_correct; eauto.
  eapply compose_determinate_big; eauto; eapply Csem_determinate_big.
Qed.

Require Import Behaviors.

Theorem separate_transf_c_program_preservation:
    forall p1 p2 spec tp1 tp2 tp,
    compose (Csem.semantics p1) (Csem.semantics p2) = Some spec ->
    transf_c_program p1 = OK tp1 ->
    transf_c_program p2 = OK tp2 ->
    link tp1 tp2 = Some tp ->
    closed_program_asm tp ->
    forall beh,
      program_behaves (close_asm (Asm.semantics tp)) beh ->
      exists beh', program_behaves (close_c spec) beh' /\ behavior_improves beh' beh.
Proof.
  intros.
  eapply backward_simulation_behavior_improves; eauto.
  eapply transf_bsim_link_c; eauto.
Qed.
