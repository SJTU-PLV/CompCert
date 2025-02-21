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

(** The semantically linked assembly module (linked_list_asm +
hash_map_asm) is totally safe under the invariant ((hmap_inv @@
rs_own) @! cc_rust_compcert). For now, the adequacy of Asm linking
cannot be used to prove the safety of the syntactic linked module
because it is a forward_simulation. *)
Theorem link_linked_list_hash_map_safe: forall linked_list_asm hash_map_asm composed_sem,
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    SmallstepLinking.compose (Asm.semantics linked_list_asm) (Asm.semantics hash_map_asm) = Some composed_sem ->
    module_type_safe ((hmap_inv @@ rs_own) @! cc_rust_compcert) ((hmap_inv @@ rs_own) @! cc_rust_compcert) composed_sem SIF.
Proof.
  intros.
  eapply compose_total_type_safety; eauto.
  eapply compiled_linked_list_safe; auto.
  eapply compiled_hash_map_safe; auto.
Qed.

