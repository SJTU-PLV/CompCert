Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Values Globalenvs Memory.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import LinkedList HashMap.
Require Import HashMapCommon LinkedListSafe HashMapSafe.
Require Import MoveCheckingDomain.
Require Import Rusttypes.
Require Import InvariantAlgebra Compiler.

Local Open Scope error_monad_scope.
Local Open Scope inv_scope.
Import ListNotations.

(* The linked_list module (implemented in Rustlight) is totally safe
after the compilation. The safety interface for the compiled module is

⟦list.s⟧ ⊩ {process ↦ ⊤, hmap_process ↦ ⊥} ⋅ I_rs⋅R_ra
        ↠ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_ra
 *)
Lemma compiled_linked_list_safe: forall linked_list_asm,
  transf_rustlight_program linked_list_mod = OK linked_list_asm ->
  module_type_safe ((list_ext_inv @@ rs_own) @! cc_rust_compcert) ((hmap_ext_inv @@ rs_own) @! cc_rust_compcert) (Asm.semantics linked_list_asm) SIF.
Proof.
  intros.
  eapply transf_rustlight_partial_safe_to_total_safe; eauto.
  eapply linked_list_module_safe.
Qed.

Definition hmap_size : nat := 10%nat.

(* The hash_map module is totally safe after the compilation.

⟦hmap.s⟧ ⊩ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc⋅R_ca
             ↠ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} ⋅ R_ca
 *)
Lemma compiled_hash_map_safe: forall hash_map_asm,
  transf_clight_program hash_map_prog = OK hash_map_asm ->
  module_type_safe
    (((hmap_ext_inv @@ rs_own) @! cc_rust_c) @! cc_compcert)
    ((hmap_int_inv hmap_size) @! cc_compcert)
    (Asm.semantics hash_map_asm) SIF.
Proof.
  intros.
  eapply transf_clight_total_safety_preservation. eauto.
  eapply hash_map_module_safe.
Qed.

(*   eapply open_safety_inv_ref. *)
(*   3: { eapply transf_clight_total_safety_preservation. eauto. *)
(*        eapply hash_map_module_safe. } *)
(*   rewrite invcc_compose_assoc. *)
(*   eapply cc_inv_ref. reflexivity. *)
(*   eapply cc_rust_compcert_eqv. *)
(*   red. *)
(*   rewrite invcc_compose_assoc. *)
(*   eapply cc_inv_ref. reflexivity. *)
(*   eapply cc_rust_compcert_eqv. *)
(* Qed. *)

(** The syntactic linked assembly module (linked_list_asm +
hash_map_asm) is totally safe with the following safety interfaces.

 ⟦hmap.s + list.s⟧ ⊩ ({find_process ↦ ⊤⋅I_rs⋅R_rc, hash ↦ P⋅I_rs⋅R_rc}
                    ⊎ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q}) ⋅ R_ca
                    ↠ 
                    ({find_process ↦ ⊤⋅I_rs⋅R_rc, hash ↦ P⋅I_rs⋅R_rc}
                    ⊎ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q}) ⋅ R_ca

We want to separate the hmap_process from functions those have rust
interfaces.

 ⟦hmap.s + list.s⟧ ⊩ {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q}⋅ R_ca
                     ↠ 
                     {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q}⋅ R_ca

 *)

(* {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤}. *)
Definition hmap_rs_cond :=
  hmap_ext_inv ⊎ list_ext_inv.

(* {hmap_process ↦ Q} *)
Definition cq_hmap_process N (w: hmap_world_int) (q: c_query) (fid: ident) : Prop :=
  if ident_eq fid hmap_process then
    vq_hmap_process N w q
  else False.

Definition cr_hmap_process N (w: hmap_world_int) (r: c_reply) (fid: ident) : Prop :=
  if ident_eq fid hmap_process then
    vr_hmap_process N w r
  else False.


(* {hmap_process ↦ Q} *)
Definition hmap_process_cond N : invariant li_c :=
  {| inv_world := hmap_world_int;
    symtbl_inv w se := (list_senv_ext (hmap_list_ext w)) = se
                       (* wf_xx_senv is used to ensure the safety of
                       function call (see eval_Eglobal) *)
                       /\ wf_senv se;
    query_inv w q := cq_inv w q (list_senv_ext (hmap_list_ext w)) (cq_hmap_process N);
    reply_inv w r := cr_inv w r (list_callee_ext (hmap_list_ext w)) (cr_hmap_process N)|}.


Lemma invcc_id1 {liA: language_interface} (P: invariant liA):
    invref (P@!1) P.
Proof.
  red. intros. destruct w1. inv H. inv H1. inv H0. inv H1.
  inv H2. inv H3. 
  exists i. repeat apply conj; auto.
  intros. simpl.
  exists r. split; auto.
Qed.

Lemma invcc_id2 {liA: language_interface} (P: invariant liA):
    invref P (P@!1).
Proof.
  red. intros. exists (w1, tt).
  repeat apply conj; try simpl; auto.
  exists se. auto. exists q. eauto.
  intros. destruct H1. destruct H1. subst. auto.
Qed.


Lemma module_type_safe_compose_id {liA liB: language_interface} P Q (L: semantics liA liB):
      module_type_safe (P @! 1) (Q @! 1) L SIF ->
      module_type_safe P Q L SIF.
Proof.
  intros.
  eapply open_safety_inv_ref; eauto.
  eapply invcc_id1. eapply invcc_id2.
Qed.


Lemma hmap_ext_inv_hmap_fun_disjoint: forall w vf sg args m,
    query_inv hmap_ext_inv w (rsq vf sg args m) ->
    Genv.is_internal (Genv.globalenv (hmap_senv_ext w) (Ctypes.program_of_program hash_map_prog)) vf = false.
Proof.
  intros. destruct w. simpl in H. red in H. simpl in H.
  destruct vf; try contradiction.
  destruct Ptrofs.eq_dec in H; try contradiction. subst.
  destruct Genv.invert_symbol eqn: SYM in H; try contradiction.
  red in H.
  unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
  rewrite dec_eq_true. rewrite Genv.find_def_spec. setoid_rewrite SYM.
  repeat destruct ident_eq in H; try contradiction; subst; reflexivity.
Qed.

Lemma hmap_int_inv_valid_query: forall w vf sg args m N,
    query_inv (hmap_int_inv N) w (cq vf sg args m) ->
    Genv.is_internal (Genv.globalenv (list_senv_ext (hmap_list_ext w)) (Ctypes.program_of_program hash_map_prog)) vf = true.
Proof.
  intros. simpl in H. red in H. simpl in H.
  destruct vf; try contradiction.
  destruct Ptrofs.eq_dec in H; try contradiction. subst.
  destruct Genv.invert_symbol eqn: SYM in H; try contradiction.
  red in H.
  unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
  rewrite dec_eq_true. rewrite Genv.find_def_spec. setoid_rewrite SYM.
  repeat destruct ident_eq in H; try contradiction; subst; reflexivity.
Qed.


Theorem link_linked_list_hash_map_safe: forall linked_list_asm hash_map_asm linked_mod,
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    Linking.link hash_map_asm linked_list_asm = Some linked_mod ->
    module_type_safe
      (* {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra *)
      (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
         (* ⊎ {hmap_process ↦ Q}⋅ R_ca *)
         ⊎ (hmap_process_cond hmap_size @! cc_compcert))
      (* The same as above *)
      (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert) ⊎ (hmap_process_cond hmap_size @! cc_compcert))
      (Asm.semantics linked_mod) SIF.
Proof.
  intros.
  (* 1. safety preservation under syntactic linking *)
  assert (SAFE: module_type_safe
    ((((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
     ⊎ hmap_process_cond hmap_size @! cc_compcert) @! 1)
    ((((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
       ⊎ hmap_process_cond hmap_size @! cc_compcert) @! 1)
    (Asm.semantics linked_mod) SIF).
  { eapply module_type_safe_preservation.
    2: { eapply AsmLinking.asm_linking_backward. eauto. }
    (* 2. refinement of safety interfaces *)
    eapply open_safety_inv_ref.
    (* 2.1 prove safety composition *)
    3: {
      (** TODO: the senv must be valid  *)
      eapply compose_total_type_safety_general.
      (* 2.1.1 safety of hmap.s *)
      4: { eapply compiled_hash_map_safe. eauto. }
      (* 2.1.2 safety of list.s. It requires refienment *)
      4: { eapply open_safety_inv_ref.
           3: { eapply compiled_linked_list_safe. eauto. }
           admit. admit. }
      (* 2.1.3 disjointness of the safety interfaces for composition *)
      { intros w q se SINV VQ QINV. destruct w as ((w1 & w2) & w3 & w4).
        destruct QINV as (?q & Q1 & Q2).
        destruct SINV as (?se & S1 & S2).           
        (* use fsim to rewrite the valid_query *)
        exploit clight_semantic_preservation.
        eapply transf_clight_program_match. eauto. intros ([FSIM] & [BSIM]).
        erewrite fsim_match_valid_query. 3: eapply Q2.
        2: { eapply FSIM. eauto.
             erewrite fsim_skel; eauto.
             eapply match_senv_valid_for; eauto.
             eapply (VQ true). }
        (* destruct query_inv to show that valid query is false *)
        destruct w1 as (w1' & w1'').
        destruct Q1 as (?q & (Q11 & Q12) & Q13).
        destruct S1 as (?se & (S11 & S12) & S13).           
        inv S13. inv S11.
        inv Q13. simpl. 
        eapply hmap_ext_inv_hmap_fun_disjoint. eauto. }
      (* 2.1.3 valid_query q is false if q satisfies the invariant
         of the compiled hash_map. The proof here is different from
         the above cases as we cannot construct a rust query to use
         fsim_match_valid_query. We prove that if q satisfies the
         hash_map invariant, it must satisfy the valid_query of the
         hash_map_asm. We can use the property of syntactic linking
         (link_prog, link_fundef) to show that if q points to an
         internal function of hash_map_asm, then it must not point to
         an internal function of linked_list_asm.  *)
      { intros w q se SINV VQ QINV. destruct w as (w1 & w2).
        destruct QINV as (?q & Q1 & Q2).
        destruct SINV as (?se & S1 & S2).
        (* use fsim to rewrite the valid_query *)
        exploit clight_semantic_preservation.
        eapply transf_clight_program_match. eauto.
        intros ([FSIM] & [BSIM]).
        assert (VQ1: valid_query (Asm.semantics hash_map_asm se) q = true).
        { erewrite fsim_match_valid_query. 3: eapply Q2.
          2: { eapply FSIM. eauto.
               erewrite fsim_skel; eauto.
               eapply match_senv_valid_for; eauto. 
               eapply (VQ true). }
          (* property of hmap_int_inv *)
          simpl.
          destruct S1. rewrite <- H2.
          destruct q0.
          eapply hmap_int_inv_valid_query.  eauto. }
        simpl. simpl in VQ1.
        (* simplify *)
        destruct q. simpl. simpl in VQ1.
        unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr in *.
        destruct (r Asm.PC) eqn: PC; auto.           
        destruct Ptrofs.eq_dec; auto. subst.
        erewrite Genv.find_def_spec in *.
        destruct (Genv.invert_symbol se b) eqn: SYM; try congruence.
        destruct ((prog_defmap hash_map_asm) ! i) eqn: FIND1 in VQ1; try congruence.
        destruct ((prog_defmap linked_list_asm) ! i) eqn: FIND2; auto.
        eapply Linking.link_prog_inv in H1. destruct H1 as (A1 & A2 & A3).
        exploit A2. eauto. eauto. intros (IN1 & IN2 & (gd & LINK)).
        destruct g; destruct g0; simpl in LINK; try congruence; auto.
        change Linking.link with (@Linking.link_def Asm.fundef unit _ _) in LINK.
        simpl in LINK.
        change Linking.link with (@Linking.link_fundef Asm.function) in LINK.
        destruct f; destruct f0; simpl in VQ1, LINK; try congruence; simpl; auto. }
      { (* external calls are not valid incoming call *)
        intros. destruct i.
        simpl. destruct s. inv H2.
        unfold Genv.is_internal. simpl. rewrite H3. reflexivity.
        simpl. destruct s. inv H2.
        unfold Genv.is_internal. simpl. rewrite H3. reflexivity. }
      { (* 2.1.4 semantic compose *)
        unfold SmallstepLinking.compose. simpl.
        erewrite Linking.link_erase_program; eauto. simpl.
        f_equal. f_equal.
        apply Axioms.functional_extensionality. intros [|]; auto.  }
    } 
    (* 2.2 refinement of invariant *)
    admit.
    (* 2.3 refinement of invariant *)
    admit. }
  (* 3. refienment of the interface of Lowering *)
  eapply module_type_safe_compose_id.
  eauto.
Qed.

