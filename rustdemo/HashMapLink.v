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
Require Import InvariantAlgebra Compiler.

Local Open Scope error_monad_scope.
Local Open Scope inv_scope.
Import ListNotations.

(* The linked_list module (implemented in Rustlight) is totally safe
after the compilation *)
Lemma compiled_linked_list_safe: forall linked_list_asm,
  transf_rustlight_program linked_list_mod = OK linked_list_asm ->
  module_type_safe ((hmap_inv @@ rs_own) @! cc_rust_compcert) ((hmap_inv @@ rs_own) @! cc_rust_compcert) (Asm.semantics linked_list_asm) SIF.
Proof.
  intros.
  eapply transf_rustlight_partial_safe_to_total_safe; eauto.
  eapply linked_list_module_safe.
Qed.

(* The hash_map module is totally safe after the compilation *)
Lemma compiled_hash_map_safe: forall hash_map_asm,
  transf_clight_program hash_map_prog = OK hash_map_asm ->
  module_type_safe ((hmap_inv @@ rs_own) @! cc_rust_compcert) ((hmap_inv @@ rs_own) @! cc_rust_compcert) (Asm.semantics hash_map_asm) SIF.
Proof.
  intros.
  eapply open_safety_inv_ref.
  3: { eapply transf_clight_total_safety_preservation. eauto.
       eapply hash_map_module_safe. }
  rewrite invcc_compose_assoc.
  eapply cc_inv_ref. reflexivity.
  eapply cc_rust_compcert_eqv.
  red.
  rewrite invcc_compose_assoc.
  eapply cc_inv_ref. reflexivity.
  eapply cc_rust_compcert_eqv.
Qed.

(** The syntactic linked assembly module (linked_list_asm +
hash_map_asm) is totally safe under the invariant ((hmap_inv @@
rs_own) @! cc_rust_compcert). *)
Theorem link_linked_list_hash_map_safe: forall linked_list_asm hash_map_asm linked_mod,
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    Linking.link linked_list_asm hash_map_asm = Some linked_mod ->
    module_type_safe ((hmap_inv @@ rs_own) @! cc_rust_compcert) ((hmap_inv @@ rs_own) @! cc_rust_compcert) (Asm.semantics linked_mod) SIF.
Proof.
  intros.
  assert (SAFE: module_type_safe (((hmap_inv @@ rs_own) @! cc_rust_compcert) @! 1)
                  (((hmap_inv @@ rs_own) @! cc_rust_compcert) @! 1) (Asm.semantics linked_mod) SIF).
  { eapply module_type_safe_preservation.
    2: { eapply AsmLinking.asm_linking_backward. eauto. }
    eapply compose_total_type_safety; eauto.
    eapply compiled_linked_list_safe; eauto.
    eapply compiled_hash_map_safe; eauto.
    unfold SmallstepLinking.compose. simpl.
    erewrite Linking.link_erase_program; eauto. simpl.
    f_equal. f_equal.
    apply Axioms.functional_extensionality. intros [|]; auto. }      
  eapply open_safety_inv_ref.
  eapply cc_inv_ref. reflexivity.
  eapply CallconvAlgebra.cc_compose_id_right.
  red. eapply cc_inv_ref. reflexivity.
  eapply CallconvAlgebra.cc_compose_id_right.
  eapply open_safety_inv_ref; eauto.
  rewrite invcc_compose_assoc. reflexivity.
  rewrite invcc_compose_assoc. reflexivity.
Qed.

