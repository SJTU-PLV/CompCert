Require Import Coqlib Errors.
Require Import AST Linking Smallstep SmallstepClosed Invariant CallconvAlgebra.

Require Import Conventions Mach.
Require Import Locations.
Require Import LanguageInterface.

Require Import Integers.
Require Import Values Memory.

Require Import CallconvBig InjectFootprint Injp.
Require Import CAnew.
Require Import Asm Asmrel.
Require Import Asmgenproof0 Asmgenproof1.
Require Import Encrypt EncryptSpec Encryptproof.
Require Import Client Server.

Require Import SmallstepLinking VCompBig HCompBig CallConvLibs.
Require Import Composition Clight Asm CMulti AsmMulti ThreadLinking ThreadLinkingBack Compiler.


Import GS.

(** 1st step : module linking *)

Section LINKING.
  Variable client_s server_s : Asm.program.
  
  Hypothesis compile_client : transf_clight_program client = OK client_s.
  Hypothesis compile_server : transf_clight_program server = OK server_s.

  Variable c_spec c_server_spec : Smallstep.semantics li_c li_c.
  
  Hypothesis compose_c1 : compose L_E (Clight.semantics1 server) = Some c_server_spec.
  Hypothesis compose_c2 : compose (Clight.semantics1 client) c_server_spec = Some c_spec.

  Variable asm_prog asm_server_prog : Asm.program.

  Hypothesis compose_asm1 : link encrypt_s server_s = Some asm_server_prog.
  Hypothesis compose_asm2 : link client_s asm_server_prog = Some asm_prog.

  Lemma client_sim : forward_simulation cc_compcert (Clight.semantics1 client) (Asm.semantics client_s).
  Proof.
    eapply clight_semantic_preservation. eapply transf_clight_program_match.
    apply compile_client.
  Qed.

  Lemma server_sim : forward_simulation cc_compcert (Clight.semantics1 server) (Asm.semantics server_s).
  Proof.
    eapply clight_semantic_preservation. eapply transf_clight_program_match.
    apply compile_server.
  Qed.

  Lemma module_linking_correct1 :
    forward_simulation cc_compcert c_server_spec (Asm.semantics asm_server_prog).
  Proof.
    rewrite <- cctrans_id_2.
    eapply st_fsim_vcomp; eauto.
    2: eapply asm_linking; eauto.
    eapply compose_simulation.
    apply correctness_L_E. apply server_sim. eauto.
    unfold compose. cbn.
    apply link_erase_program in compose_asm1. rewrite compose_asm1. cbn. f_equal. f_equal.
    apply Axioms.functional_extensionality. intros [|]; auto.
  Qed.

  Theorem module_linking_correct :
    forward_simulation cc_compcert c_spec (Asm.semantics asm_prog).
  Proof.
    rewrite <- cctrans_id_2.
    eapply st_fsim_vcomp; eauto.
    2: eapply asm_linking; eauto.
    eapply compose_simulation.
    apply client_sim. apply module_linking_correct1. eauto.
    unfold compose. cbn.
    apply link_erase_program in compose_asm2. rewrite compose_asm2. cbn. f_equal. f_equal.
    apply Axioms.functional_extensionality. intros [|]; auto.
  Qed.

  Theorem thread_linking_correct :
    Closed.forward_simulation (Concur_sem_c c_spec) (Concur_sem_asm (Asm.semantics asm_prog)).
  Proof.
    apply Opensim_to_Globalsim; eauto. apply module_linking_correct.
  Qed.

  Lemma c_spec_receptive : receptive c_spec.
  Proof.
    unfold compose in compose_c2. unfold option_map in compose_c2.
    destruct link in compose_c2; inv compose_c2.
    eapply HCompBig.semantics_receptive. intros. destruct i.
    eapply Clight.semantics_receptive.
    unfold compose in compose_c1. unfold option_map in compose_c1.
    destruct link in compose_c1; inv compose_c1.
    eapply HCompBig.semantics_receptive. intros. destruct i.
    { red. intros. constructor.
      intros. inv H. eexists. simpl. inv H0. econstructor; eauto.
      red. intros. inv H. simpl. lia. }
    eapply Clight.semantics_receptive.
  Qed.
                     
  Lemma L_E_determinate_big : determinate_big L_E.
  Proof.
    red. intros. constructor; intros; inv H.
    - inv H0. reflexivity.
    - red. intros. intro. inv H.
    - inv H0.
    - inv H0. reflexivity.
  Qed.

  Lemma valid_query_neq1 : forall se q,
      Smallstep.valid_query (semantics1 server se) q = true ->
      Smallstep.valid_query (L_E se) q = true -> False .
  Proof.
    intros. inv H. inv H0.
    unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr in *.
    repeat destr_in H1. repeat destr_in Heqo. simpl.
    destr_in H2. repeat destr_in Heqo.
    rewrite Genv.find_def_spec in Heqo0, Heqo1.
    destr_in Heqo0.
    exfalso. clear - Heqo0  Heqo1.
    unfold encrypt_s in Heqo0.
    apply in_prog_defmap in Heqo0.
    unfold server in Heqo1.
    apply in_prog_defmap in Heqo1. simpl in *.
    destruct Heqo0 as [H|[H|H]]; inv H.
    destruct Heqo1 as [H|H]; inv H.
  Qed.

  Lemma valid_query_neq2 : forall se q,
      Smallstep.valid_query (semantics1 client se) q = true ->
      Smallstep.valid_query (L_E se) q = true -> False.
  Proof.
    intros. inv H. inv H0.
    unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr in *.
    repeat destr_in H1. repeat destr_in Heqo. simpl.
    destr_in H2. repeat destr_in Heqo.
    rewrite Genv.find_def_spec in Heqo0, Heqo1.
    destr_in Heqo0.
    exfalso. clear - Heqo0  Heqo1.
    apply in_prog_defmap in Heqo0.
    apply in_prog_defmap in Heqo1. simpl in *.
    destruct Heqo0 as [H|[H|H]]; inv H.
    destruct Heqo1 as [H|[H|[H|[H|[H|H]]]]]; inv H.
  Qed.

  Lemma valid_query_neq3 : forall se q,
      Smallstep.valid_query (semantics1 client se) q = true ->
      Smallstep.valid_query (semantics1 server se) q = true -> False.
  Proof.
    intros. inv H. inv H0.
    unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr in *.
    repeat destr_in H1. repeat destr_in Heqo. simpl.
    destr_in H2. repeat destr_in Heqo.
    rewrite Genv.find_def_spec in Heqo0, Heqo1.
    destr_in Heqo0.
    exfalso.  clear - H2 H0 Heqo0  Heqo1.
    apply in_prog_defmap in Heqo0.
    apply in_prog_defmap in Heqo1. simpl in *.
    destruct Heqo0 as [H|H]; inv H;
      destruct Heqo1 as [H|[H|[H|[H|[H|H]]]]]; inv H.
    inv H2.
  Qed.
  
  Lemma c_spec_determinate_big : determinate_big c_spec.
  Proof.
    unfold compose in compose_c2. unfold option_map in compose_c2.
    destruct link eqn:Hl in compose_c2;  inv compose_c2.
    eapply HCompBig.semantics_determinate_big.
    {
      intros. destruct i; destruct j; eauto.
      - unfold compose in compose_c1. unfold option_map in compose_c1.
        destruct link eqn:Hl1 in compose_c1; inv compose_c1. inv H0.
        unfold valid_query in H2. exfalso.
        destruct (Smallstep.valid_query (L_E se) q) eqn:HLE;
          destruct ( Smallstep.valid_query (semantics1 server se) q) eqn:Hs;
          eauto using valid_query_neq1,valid_query_neq2,valid_query_neq3.
      - unfold compose in compose_c1. unfold option_map in compose_c1.
        destruct link eqn:Hl1 in compose_c1; inv compose_c1. inv H.
        unfold valid_query in H2. exfalso.
        destruct (Smallstep.valid_query (L_E se) q) eqn:HLE;
          destruct ( Smallstep.valid_query (semantics1 server se) q) eqn:Hs;
          eauto using valid_query_neq1,valid_query_neq2,valid_query_neq3.
    }
    destruct i. eapply Clight_determinate_big.
    unfold compose in compose_c1. unfold option_map in compose_c1.
    destruct link eqn:Hl1 in compose_c1; inv compose_c1.
    eapply HCompBig.semantics_determinate_big.
    {
      intros. destruct i; destruct j; eauto using valid_query_neq1.
      exfalso. eapply valid_query_neq1; eauto.
    }
    intros. destruct i. eapply L_E_determinate_big.
    eapply Clight_determinate_big.
  Qed.

  Lemma compose_after_receptive : forall (Lc1 Lc2 Lc : Smallstep.semantics li_c li_c),
      compose Lc1 Lc2 = Some Lc ->
      after_external_receptive Lc1 ->
      after_external_receptive Lc2 ->
      after_external_receptive Lc.
  Proof.
    intros Lc1 Lc2 Lc Hc Hr1 Hr2.
    unfold compose in Hc. unfold option_map in Hc.
    destruct link in Hc; inv Hc.    red. intros. inv H. destruct i.
    - red in Hr1.
      exploit Hr1; eauto. instantiate (1:= r).
      intros [s' Hy].
      eexists. econstructor; eauto.
    - exploit Hr2; eauto. instantiate (1:= r).
      intros [s' Hy]. eexists. econstructor; eauto.
  Qed.

  Lemma compose_initial_receptive : forall (Lc1 Lc2 Lc : Smallstep.semantics li_c li_c),
      compose Lc1 Lc2 = Some Lc ->
      initial_state_receptive Lc1 ->
      valid_query_receptive Lc1 ->
      initial_state_receptive Lc2 ->
      valid_query_receptive Lc2 ->
      initial_state_receptive Lc.
  Proof.
    intros Lc1 Lc2 Lc Hc Hi1 Hv1 Hi2 Hv2.
    unfold compose in Hc. unfold option_map in Hc.
    destruct link in Hc; inv Hc.
    red. intros. inv H. destruct i.
    - exploit Hi1; eauto.
      intros [s' Hi].
      eexists. econstructor. instantiate (1:=true). simpl.
      eauto. eauto.
    - exploit Hi2; eauto. intros [s' Hi]. eexists. econstructor.
      instantiate (1:= false). eauto. eauto.
  Qed.
  
  Lemma c_spec_receptive_after_external : after_external_receptive c_spec.
  Proof.
    eapply compose_after_receptive; eauto.
    eapply Clight_after_external_receptive.
    eapply compose_after_receptive; eauto.
    red. intros. inv H.
    eapply Clight_after_external_receptive.
  Qed.

  Lemma c_spec_receptive_initial_state : initial_state_receptive c_spec.
    eapply compose_initial_receptive. eauto.
    apply Clight_initial_state_receptive. apply Clight_valid_query_receptive.
    eapply compose_initial_receptive. eauto.
    red. intros. inv H. eexists. econstructor; eauto.
    red. intros. reflexivity.
    apply Clight_initial_state_receptive. apply Clight_valid_query_receptive.
    red. intros.
    unfold compose in compose_c1. unfold option_map in compose_c1.
    destruct link in compose_c1; inv compose_c1. reflexivity.
  Qed.
  
  Theorem module_linking_back :
    backward_simulation cc_compcert c_spec (Asm.semantics asm_prog).
  Proof.
    eapply GS.forward_to_backward_simulation. eapply module_linking_correct.
    apply c_spec_receptive.
    eapply Asm.semantics_determinate.
  Qed.

  Theorem thread_linking_back :
    Closed.backward_simulation (Concur_sem_c c_spec) (Concur_sem_asm (Asm.semantics asm_prog)).
    apply BSIM; eauto. eapply module_linking_back.
    apply c_spec_determinate_big.
    apply c_spec_receptive_after_external.
    apply c_spec_receptive_initial_state.
  Qed.     

End LINKING.
