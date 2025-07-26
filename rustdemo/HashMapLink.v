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

⟦list.s⟧ ⊩ {process ↦ ⊤, hmap_process ↦ ⊥, hmap_set ↦ ⊤} ⋅ I_rs⋅R_ra
        ↠ {find_process ↦ ⊤, hash ↦ P, empty_list ↦ ⊤, insert ↦ ⊤} ⋅ I_rs⋅R_ra
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

⟦hmap.s⟧ ⊩ {find_process/empty_list/insert ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc⋅R_ca
             ↠ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q, main/hmap_set/hmap_init ↦ ⊤} ⋅ R_ca
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


(** The syntactic linked assembly module (linked_list_asm +
hash_map_asm) is totally safe with the following safety interfaces.

 ⟦hmap.s + list.s⟧ ⊩ ({find_process/empty_list/insert ↦ ⊤⋅I_rs⋅R_rc, hash ↦ P⋅I_rs⋅R_rc}
                    ⊎ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q, main/hmap_set/hmap_init ↦ ⊤}) ⋅ R_ca
                    ↠ 
                    ({find_process/empty_list/insert ↦ ⊤⋅I_rs⋅R_rc, hash ↦ P⋅I_rs⋅R_rc}
                    ⊎ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q, main/hmap_set/hmap_init ↦ ⊤}) ⋅ R_ca

We want to separate the hmap_process and main from functions those have rust
interfaces.

 ⟦hmap.s + list.s⟧ ⊩ { find_process/empty_list/insert ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q, main ↦ ⊤}⋅ R_ca
                     ↠ 
                     {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q, main/hmap_set/hmap_init ↦ ⊤}⋅ R_ca

 *)

(* {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤}. *)
Definition hmap_rs_cond :=
  hmap_ext_inv ⊎ list_ext_inv.

(** TODO: we may also need to add hmap_init and hmap_set here  *)
(* {hmap_process ↦ Q, main ↦ ⊤} *)
Definition cq_hmap_process N (w: hmap_world_int) (q: c_query) (fid: ident) : Prop :=
  if ident_eq fid hmap_process then
    vq_hmap_process N w q
  else if ident_eq fid main then
         list_callee_ext (hmap_list_ext w) = main /\
           cq_args q = nil /\
           cq_sg q = signature_main   
  else False.

Definition cr_hmap_process N (w: hmap_world_int) (r: c_reply) (fid: ident) : Prop :=
  if ident_eq fid hmap_process then
    vr_hmap_process N w r
  else if ident_eq fid main then
         (* The return value of the main function is zero *)
         cr_retval r = Vint Int.zero
  else False.


(* {hmap_process ↦ Q, main ↦ ⊤} *)
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

Lemma hmap_process_cond_valid_query: forall w vf sg args m,
    query_inv (hmap_process_cond hmap_size) w (cq vf sg args m) ->
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


Lemma list_ext_inv_valid_query: forall w vf sg args m,
    query_inv list_ext_inv w (rsq vf sg args m) ->
    Genv.is_internal (Genv.globalenv (list_senv_ext w) (Ctypes.program_of_program hash_map_prog)) vf = true.
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

Lemma hmap_ext_inv_valid_query: forall w vf sg args m,
    query_inv hmap_ext_inv w (rsq vf sg args m) ->
    Genv.is_internal (Genv.globalenv (hmap_senv_ext w) (program_of_program linked_list_mod)) vf = true.
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


Lemma hmap_inv_inv_ref: invref ((list_ext_inv @@ rs_own) @! cc_rust_c) (hmap_int_inv hmap_size).
  red. intros ((w1 & w2) & w3) se q (se1 & (S11 & S12) & S2) (q1 & (Q11 & Q12) & Q2).
  inv S2.
  destruct w2 as (se' & w2). inv S12. inv S11.
  simpl in Q11. red in Q11. inv Q2. simpl in *.
  destruct vf; try contradiction.
  destruct Ptrofs.eq_dec; try contradiction; subst.
  destruct (Genv.invert_symbol) eqn: SYM; try contradiction.
  red in Q11. 
  exists (Build_hmap_world_int w1 (Some w2) None).
  split. auto.
  repeat apply conj; auto.
  + simpl. red. simpl. rewrite dec_eq_true.
    rewrite SYM. red.
    destruct (ident_eq i process); subst; try contradiction.
    * simpl. exists (rsq (Vptr b Ptrofs.zero) sg vargs m).
      repeat apply conj; auto. red. simpl. rewrite dec_eq_true. rewrite SYM. auto.
      econstructor.
    * destruct ident_eq; try contradiction.
  + intros r R. simpl in R. red in R. red in R.
    repeat destruct ident_eq; try contradiction.
    * simpl in R. destruct R as (r1 & (R1 & (w' & ACC & ROWN)) & R2).
      simpl. exists r1. repeat apply conj; eauto.
    (* impossible *)
    * subst. inv Q11. congruence.
    * subst. inv Q11. congruence.
Qed.        

(* Used in the refienment of safety interfaces in the linked module *)
Lemma hmap_cc_compcert_eqv: 
  inveqv
    ((((hmap_ext_inv @@ rs_own) @! cc_rust_c) @! cc_compcert)
     ⊎ hmap_int_inv hmap_size @! cc_compcert)
    ((((hmap_rs_cond @@ rs_own) @! cc_rust_c) @! cc_compcert)
       ⊎ hmap_process_cond hmap_size @! cc_compcert).
Proof.
  split.
  - red. intros [w1 | w1].
    + destruct w1 as (((w1 & w2) & w3) & w4).
      intros se q (se1 & (se2 & ((S1 & S2) & S3)) & S4) (q1 & (q2 & ((Q1 & Q2) & Q3)) & Q4).
      inv S3.
      (* case analysis of Q1 *)
      simpl in Q1. red in Q1. destruct q2. simpl in Q1.
      destruct rsq_vf; try contradiction.
      destruct Ptrofs.eq_dec in Q1; try contradiction. subst.
      destruct Genv.invert_symbol eqn: SYM in Q1; try contradiction.
      red in Q1. destruct w3. inv Q3.
      repeat destruct ident_eq in Q1; try contradiction; subst.
      (* call find *)
      * exists (inl ((((inl w1), w2), tt), w4)). repeat apply conj.
        -- econstructor. split; eauto.
           econstructor. split; eauto.
           2: { simpl. eauto. }
           simpl in S1. 
           econstructor. simpl. eauto.
           auto.
        -- econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
        -- intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
           econstructor. split; eauto.
           econstructor. split; eauto.
           econstructor; auto.
      (* call hash, the same as above *)
      * exists (inl ((((inl w1), w2), tt), w4)). repeat apply conj.
        -- econstructor. split; eauto.
           econstructor. split; eauto.
           2: { simpl. eauto. }
           simpl in S1. 
           econstructor. simpl. eauto.
           auto.
        -- econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
        -- intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
           econstructor. split; eauto.
           econstructor. split; eauto.
           econstructor; auto.
      (* call empty_list, the same as above *)
      * exists (inl ((((inl w1), w2), tt), w4)). repeat apply conj.
        -- econstructor. split; eauto.
           econstructor. split; eauto.
           2: { simpl. eauto. }
           simpl in S1. 
           econstructor. simpl. eauto.
           auto.
        -- econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
        -- intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
           econstructor. split; eauto.
           econstructor. split; eauto.
           econstructor; auto.
      (* call insert, same as above *)
      * exists (inl ((((inl w1), w2), tt), w4)). repeat apply conj.
        -- econstructor. split; eauto.
           econstructor. split; eauto.
           2: { simpl. eauto. }
           simpl in S1. 
           econstructor. simpl. eauto.
           auto.
        -- econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
        -- intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
           econstructor. split; eauto.
           econstructor. split; eauto.
           econstructor; auto.
    + destruct w1 as (w1 & w2).
      intros se q (se1 & (S1 & S2)) (q1 & (Q1 & Q2)).
      (* case analysis of Q1 *)
      simpl in Q1. red in Q1. destruct q1. simpl in Q1.
      destruct cq_vf; try contradiction.
      destruct Ptrofs.eq_dec in Q1; try contradiction. subst.
      destruct Genv.invert_symbol eqn: SYM in Q1; try contradiction.
      red in Q1. 
      repeat destruct ident_eq in Q1; try contradiction; subst.
      (* call process *)
      * destruct (hmap_rs_own w1) eqn: ROWN; try contradiction.
        exists (inl ((((inr (hmap_list_ext w1)), (se1, r)), tt), w2)).
        repeat apply conj.
        -- econstructor. split; eauto.
           econstructor. split; eauto.
           2: econstructor.
           econstructor. eauto. reflexivity.
        -- econstructor. split; eauto.
           inv Q1. inv H. inv H1. inv H0. 
           econstructor. split.
           2: econstructor.
           econstructor. eauto. eauto.
        -- intros r0 (r1 & (R1 & R2)).
           inv Q1. inv H. inv H1. inv H0.
           simpl in H. red in H. simpl in H.
           rewrite dec_eq_true in H. rewrite SYM in H.
           red in H. rewrite dec_eq_true in H. inv H.
           inv R1. inv H. inv H0. inv H2.
           econstructor. split; eauto.
           simpl. red. red. rewrite CALLEE in *.
           rewrite dec_eq_true. rewrite ROWN.
           econstructor; eauto. split.
           2: econstructor.
           econstructor; eauto.
      (* call hmap_process *)
      * exists (inr (w1, w2)). repeat apply conj.
        -- econstructor. split; eauto.
        -- econstructor. split; eauto.
           simpl. red. simpl. 
           rewrite dec_eq_true. rewrite SYM. auto.
        -- intros r (r1 & (R1 & R2)).
           simpl in R1. red in R1.
           econstructor. split; eauto.
           inv Q1.
           simpl. red. red. rewrite CALLEE in *.
           rewrite dec_eq_false; auto.
      (* call main *)
      * destruct Q1 as (Q11 & Q12 & Q13).
        exists (inr (w1, w2)). repeat apply conj.
        -- econstructor. split; eauto.
        -- econstructor. split; eauto.
           simpl. red. simpl. 
           rewrite dec_eq_true. rewrite SYM.
           red. simpl. auto.
        -- intros r (r1 & (R1 & R2)).
           simpl in R1. red in R1. red in R1.
           rewrite Q11 in *. simpl in R1.
           red. red. econstructor.
           split; eauto.
           simpl. red. red. rewrite Q11. simpl. auto.           
  - red. intros [w1 | w1].
    + destruct w1 as (((w1 & w2) & w3) & w4).
      intros se q (se1 & (se2 & ((S1 & S2) & S3)) & S4) (q1 & (q2 & ((Q1 & Q2) & Q3)) & Q4).
      inv S3.
      (* case analysis of Q1 *)
      simpl in Q1.
      destruct w1 as [w1 | w1].
      * red in Q1. destruct q2. simpl in Q1.
        destruct rsq_vf; try contradiction.
        destruct Ptrofs.eq_dec in Q1; try contradiction. subst.
        destruct Genv.invert_symbol eqn: SYM in Q1; try contradiction.
        red in Q1. destruct w3. inv Q3.
        repeat destruct ident_eq in Q1; try contradiction; subst.
        (* call find *)
        -- exists (inl (((w1, w2), tt), w4)). repeat apply conj.
           ++ econstructor. split; eauto.
              econstructor. split; eauto.
              2: econstructor. 
              econstructor; eauto.
           ++  econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
           ++ intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
              econstructor. split; eauto.
              econstructor. split; eauto.
              econstructor; auto.
        (* call hashs *)
        -- exists (inl (((w1, w2), tt), w4)). repeat apply conj.
           ++ econstructor. split; eauto.
              econstructor. split; eauto.
              2: econstructor. 
              econstructor; eauto.
           ++  econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
           ++ intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
              econstructor. split; eauto.
              econstructor. split; eauto.
              econstructor; auto.
        (* call empty_list *)
        -- exists (inl (((w1, w2), tt), w4)). repeat apply conj.
           ++ econstructor. split; eauto.
              econstructor. split; eauto.
              2: econstructor. 
              econstructor; eauto.
           ++  econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
           ++ intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
              econstructor. split; eauto.
              econstructor. split; eauto.
              econstructor; auto.
        (* call insert *)
        -- exists (inl (((w1, w2), tt), w4)). repeat apply conj.
           ++ econstructor. split; eauto.
              econstructor. split; eauto.
              2: econstructor. 
              econstructor; eauto.
           ++  econstructor. split; eauto.
           econstructor. split.
           2: econstructor. 
           econstructor. simpl. red. simpl.
           rewrite dec_eq_true. rewrite SYM. auto.
           auto.
           ++ intros r (r1 & (r2 & ((R1 & R2) & R3)) & R4).
              econstructor. split; eauto.
              econstructor. split; eauto.
              econstructor; auto.

      * red in Q1. destruct q2. simpl in Q1.
        destruct rsq_vf; try contradiction.
        destruct Ptrofs.eq_dec in Q1; try contradiction. subst.
        destruct Genv.invert_symbol eqn: SYM in Q1; try contradiction.
        red in Q1. destruct w3. inv Q3.
        repeat destruct ident_eq in Q1; try contradiction; subst.
        (* call process *)
        exists (inr ((Build_hmap_world_int w1 (Some (snd w2)) None), w4)). repeat apply conj.
        -- econstructor. split; eauto. auto.
        -- econstructor. split; eauto.
           simpl. red. simpl. rewrite dec_eq_true. rewrite SYM.
           red. rewrite dec_eq_true. simpl.
           eexists. split.
           2: econstructor. split.
           red. simpl. rewrite dec_eq_true. rewrite SYM. auto.
           destruct w2; auto.
        -- intros r R. inv R. inv H.
           simpl in H0. red in H0.
           inv Q1.
           red in H0. rewrite CALLEE in *. rewrite dec_eq_true in H0.
           simpl in H0. destruct H0 as (r1 & ((R1 & R2) & R3)).
           econstructor. split; eauto.
           econstructor. split; eauto.
           econstructor; auto.
           destruct w2; eauto.
    + destruct w1 as (w1 & w2).
      intros se q (se1 & (S1 & S2)) (q1 & (Q1 & Q2)).
      (* case analysis of Q1 *)
      simpl in Q1. red in Q1. destruct q1. simpl in Q1.
      destruct cq_vf; try contradiction.
      destruct Ptrofs.eq_dec in Q1; try contradiction. subst.
      destruct Genv.invert_symbol eqn: SYM in Q1; try contradiction.
      red in Q1. 
      repeat destruct ident_eq in Q1; try contradiction; subst.
      (* call hmap_process or call main*)
      * exists (inr (w1, w2)). repeat apply conj.
        -- econstructor. split; eauto.
        -- econstructor. split; eauto.
           simpl. red. simpl. 
           rewrite dec_eq_true. rewrite SYM. auto.
        -- intros r (r1 & (R1 & R2)).
           simpl in R1. red in R1.
           econstructor. split; eauto.
           inv Q1.
           simpl. red. red. rewrite CALLEE in *.
           rewrite dec_eq_true; auto.
      * exists (inr (w1, w2)). repeat apply conj.
        -- econstructor. split; eauto.
        -- econstructor. split; eauto.
           simpl. red. simpl. 
           rewrite dec_eq_true. rewrite SYM. auto.
        -- intros r (r1 & (R1 & R2)).
           simpl in R1. red in R1.
           econstructor. split; eauto.
           inv Q1.
           simpl. red. red. rewrite H in *.
           rewrite dec_eq_true; auto.           
Qed.

              
(*  ⟦hmap.s + list.s⟧ ⊩ {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q, main ↦ ⊤}⋅ R_ca
                     ↠ 
                     {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q, main ↦ ⊤}⋅ R_ca
 *)
Theorem compose_linked_list_hash_map_safe: forall linked_list_asm hash_map_asm composed_mod linked_mod,
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    SmallstepLinking.compose
      (Asm.semantics hash_map_asm)
      (Asm.semantics linked_list_asm) = Some composed_mod ->
    (* it is required for the premised of safety composition *)
    Linking.link hash_map_asm linked_list_asm = Some linked_mod ->
    module_type_safe
      (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
         ⊎ hmap_process_cond hmap_size @! cc_compcert)
      (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
         ⊎ hmap_process_cond hmap_size @! cc_compcert)
      composed_mod SIF.
Proof.
  intros until linked_mod. intros T1 T2 COMP LINK.
  (* 1. safety preservation under syntactic linking *)
  assert (SAFE: module_type_safe
                  ((((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
                      ⊎ hmap_process_cond hmap_size @! cc_compcert))
                  ((((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
                      ⊎ hmap_process_cond hmap_size @! cc_compcert))
                  composed_mod SIF).
  { (* 2. refinement of safety interfaces *)
    eapply open_safety_inv_ref.
    (* 2.1 safety composition *)
    3: { eapply compose_total_type_safety_general.
         (* 2.1.1 safety of hmap.s *)
         4: { eapply compiled_hash_map_safe. eauto. }
         (* 2.1.2 safety of list.s. It requires refienment *)
         4: { eapply open_safety_inv_ref.
              3: { eapply compiled_linked_list_safe. eauto. }
              { etransitivity. 
                eapply cc_inv_ref. reflexivity.
                eapply cc_rust_compcert_eqv.
                erewrite <- invcc_compose_assoc.
                eapply cc_inv_ref. 2: reflexivity.
                (* ((list_ext_inv @@ rs_own) @! cc_rust_c) ≤ (hmap_int_inv hmap_size) *)
                eapply hmap_inv_inv_ref. }
              { etransitivity. 
                eapply cc_inv_ref. reflexivity.
                eapply cc_rust_compcert_eqv.
                red. erewrite <- invcc_compose_assoc.
                eapply cc_inv_ref. 2: reflexivity.
                reflexivity. }
         }
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
             destruct S1. rewrite <- H.
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
           eapply Linking.link_prog_inv in LINK. destruct LINK as (A1 & A2 & A3).
           exploit A2. eauto. eauto. intros (IN1 & IN2 & (gd & LINK)).
           destruct g; destruct g0; simpl in LINK; try congruence; auto.
           change Linking.link with (@Linking.link_def Asm.fundef unit _ _) in LINK.
           simpl in LINK.
           change Linking.link with (@Linking.link_fundef Asm.function) in LINK.
           destruct f; destruct f0; simpl in VQ1, LINK; try congruence; simpl; auto. }
         { (* external calls are not valid incoming call *)
           intros. destruct i.
           simpl. destruct s. inv H.
           unfold Genv.is_internal. simpl. rewrite H0. reflexivity.
           simpl. destruct s.  inv H.
           unfold Genv.is_internal. simpl. rewrite H0. reflexivity. }
         auto. }
    (* 2.2 refinement of invariant *)
    { eapply inv_sum_ref2.
      2: { etransitivity.
           2: { eapply cc_inv_ref. reflexivity.
                eapply cc_rust_compcert_eqv. }
           erewrite <- invcc_compose_assoc. reflexivity. }
      2: reflexivity.
      eapply hmap_cc_compcert_eqv. }
    (* 2.3 refinement of invariant *)
    red.
    eapply inv_sum_ref1.
    2: { etransitivity.
         eapply cc_inv_ref. reflexivity.
         eapply cc_rust_compcert_eqv.
         erewrite <- invcc_compose_assoc. reflexivity. }
    2: reflexivity.
    eapply hmap_cc_compcert_eqv. }
  auto.
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
    (* 2. safety of the composed semantics *)
    eapply compose_linked_list_hash_map_safe; eauto.
    (* 2.1 prove safety composition *)
    { (* semantic compose *)
      unfold SmallstepLinking.compose. simpl.
      erewrite Linking.link_erase_program; eauto. simpl.
      f_equal. f_equal.
      apply Axioms.functional_extensionality. intros [|]; auto.  } }  
  (* 3. refienment of the interface I @! id *)
  eapply module_type_safe_compose_id.
  eauto.
Qed.

(*  ⟦hmap.s + list.s⟧ ⊩ ⊥
                     ↠ 
                     {find_process ↦ ⊤, hash ↦ P, process ↦ ⊤} ⋅I_rs⋅R_ra
                     ⊎ {hmap_process ↦ Q}⋅ R_ca

Since the linked module must not perform external calls, so we can set the external interfaces to be ⊥
 *)

Theorem link_linked_list_hash_map_safe_1: forall linked_list_asm hash_map_asm linked_mod,
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    Linking.link hash_map_asm linked_list_asm = Some linked_mod ->
    module_type_safe
      inv_bot
      (* The same as above *)
      (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert) ⊎ (hmap_process_cond hmap_size @! cc_compcert))
      (Asm.semantics linked_mod) SIF.
Proof.
  intros until linked_mod. intros T1 T2 LINK.
  assert (SAFE: module_type_safe
    (inv_bot @! 1)
    ((((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
       ⊎ hmap_process_cond hmap_size @! cc_compcert) @! 1)
    (Asm.semantics linked_mod) SIF).
  { eapply module_type_safe_preservation.    
    2: { eapply AsmLinking.asm_linking_backward. eauto. }
    (* 2. safety implication  *)
    exploit compose_linked_list_hash_map_safe; eauto.
    { unfold SmallstepLinking.compose. simpl.
      erewrite Linking.link_erase_program; eauto. simpl.
      instantiate (1 := (SmallstepLinking.semantics
       (fun i : bool => Asm.semantics (if i then hash_map_asm else linked_list_asm))
       (erase_program linked_mod))).
      f_equal. f_equal.
      apply Axioms.functional_extensionality. intros [|]; auto.  } 
    intros [SAFE].
    destruct SAFE as (inv & SAFE).
    constructor.
    eapply (Module_type_safe_components Asm.li_asm Asm.li_asm _ _ _ _ inv).
    intros se w SYM VSE.
    econstructor; eauto.
    1-3, 5: intros; eapply SAFE; eauto.
    (* at_external *)
    intros s q SINV ATEXT.
    exploit @external_preserves_progress; eauto.
    intros (w1 & SYM1 & QINV1 & RINV1).
    inv ATEXT.
    assert (VQ: valid_query (Asm.semantics hash_map_asm se) q = false
                /\ valid_query (Asm.semantics linked_list_asm se) q = false).
    { split.
      eapply (H0 true); eauto.
      eapply (H0 false); eauto. }
    exploit clight_semantic_preservation.
    eapply transf_clight_program_match. eauto.
    intros ([FSIM1] & [BSIM1]).
    exploit rustlight_semantic_preservation.
    eapply transf_rustlight_program_match. eauto.
    intros ([FSIM2] & [BSIM2]).
    eapply Linking.link_erase_program in LINK.
    destruct VQ as (VQ1 & VQ2).      
    destruct w1 as [w1 | w1].
    - destruct w1 as ((w1 & w2) & w3).
      destruct QINV1 as (q1 & (Q11 & Q12) & Q2).
      destruct SYM1 as (se1 & (S11 & S12) & S2).
      destruct w1 as [w1 | w1].
      (* call list *)
      + erewrite fsim_match_valid_query in VQ2.
        2: { eapply FSIM2. eauto.           
             erewrite fsim_skel; eauto.
             eapply match_senv_valid_for; eauto.
             eapply Genv.valid_for_linkorder; eauto.
            simpl. eapply Linking.link_linkorder. eauto. }
        2: eauto.
        simpl in Q11. destruct q1. 
        exploit hmap_ext_inv_valid_query; eauto.
        simpl. eauto. intros VQ2'.
        simpl in VQ2. inv S11. setoid_rewrite VQ2 in VQ2'. inv VQ2'.
      (* call process *)
      + (* match_senv. We need to construct the match_senv cc_compcert
      from match_senv cc_rust_compcert *)
        generalize cc_rust_compcert_eqv. intros (A1 & A2).
        exploit @A1; eauto. intros (((se1' & w11') & w12') & (S11' & S12') & (q1' & Q11' & Q12') & R1').
        inv S11'.
        erewrite fsim_match_valid_query in VQ1.
        2: { eapply FSIM1. eauto.
             eauto.
             erewrite fsim_skel; eauto.
             eapply match_senv_valid_for; eauto.
             eapply Genv.valid_for_linkorder; eauto.
             simpl. eapply (proj1 (Linking.link_linkorder _ _ _ LINK)). }
        2: eauto.
        (* simplify the query_inv *)
        simpl in Q11. destruct q1. 
        exploit list_ext_inv_valid_query; eauto.
        simpl. eauto. intros VQ1'.
        inv S11. inv Q11'. simpl in VQ1. setoid_rewrite VQ1 in VQ1'. inv VQ1'.
    (* call hmap_process *)
    - destruct w1 as (w1 & w2).
      destruct QINV1 as (q1 & Q1 & Q2).
      destruct SYM1 as (se1 & S1 & S2).
      erewrite fsim_match_valid_query in VQ1.
      2: { eapply FSIM1. eauto.
           erewrite fsim_skel; eauto.
             eapply match_senv_valid_for; eauto.
             eapply Genv.valid_for_linkorder; eauto.
             simpl. eapply (proj1 (Linking.link_linkorder _ _ _ LINK)). }
      2: eauto.
      simpl in Q1. destruct q1.
      exploit hmap_process_cond_valid_query; eauto.
      simpl. eauto.
      inv S1.
      intros VQ1'. simpl in VQ1. setoid_rewrite VQ1 in VQ1'. inv VQ1'. }
  eapply module_type_safe_compose_id.
  eauto.
Qed.

(** Closed safety for the hash map *)
Require Import SmallstepClosed.

(* We try to give a common pattern for closing an assembly program
(which is compiled from C) and proving its closed safety. We require
the source language for the main function (not the source language of
M_asm) is C language as we want to use the source safety condition to
prove that its initialization satisfies the valid_query and
pre-condition of the main function, which is language-specific. If the
main function is written in other language (e.g., Rust), we need to
write a new proof pattern but it should be similar to the following
code. *)
Section CLOSED_ASM_SAFE.

Variable M_asm : Asm.program.
Variable incoming_cond : invariant li_c.


Let L_asm := Asm.semantics M_asm.
Let se := Asm.initial_se (erase_program M_asm).

Hypothesis M_open_safe: module_type_safe inv_bot (incoming_cond @! cc_compcert) L_asm SIF.

Lemma asm_valid_se : Genv.valid_for (skel L_asm) se.
Proof.
  unfold se. unfold Asm.initial_se. red.
  intros.
  apply Genv.find_info_symbol in H. destruct H as [b [A B]].
  exists b,g. split. auto. split. auto.
  apply Linking.linkorder_refl.
Qed.


Section Initial.
     
  Variable m m1: mem.
  Variable b : block.           (* main block *)
  Variable sb : block.           (* asm dummy stack block *)
  
  Let main_id := AST.prog_main (skel L_asm).
                               
  Hypothesis INITM: Genv.init_mem (skel L_asm) = Some m.
  Hypothesis FINDMAIN: Genv.find_symbol se main_id = Some b.
  Hypothesis DUMMYSP: Mem.alloc m 0 0 = (m1, sb).
  
  Lemma INJ1 : Mem.inject (Mem.flat_inj (Mem.support m)) m m.
  Proof.
    eapply Genv.initmem_inject. eauto. Qed.

  Lemma INJ2 : Mem.inject (Mem.flat_inj (Mem.support m)) m m1.
  Proof.
    eapply Mem.alloc_right_inject; eauto. eapply INJ1. Qed.

  Let rs0 := Asm.initial_regset (Vptr b Ptrofs.zero) (Vptr sb Ptrofs.zero).
  Let caw := CA.cajw (InjectFootprint.injpw (Mem.flat_inj (Mem.support m)) m m1 INJ2) signature_main rs0.
  (* (Genv.symtbl * ValueAnalysis.ro_world * (Genv.symtbl * (Genv.symtbl * signature) * (Genv.symtbl * CA.cc_cainjp_world * unit))) *)
  Definition rca_w := ((se, ValueAnalysis.row se m), (se, (se, signature_main), (se, caw, tt))).
  Let q0 := (cq (Vptr b Ptrofs.zero) signature_main nil m).
  
  Lemma SUP : (Genv.genv_sup (Asm.initial_se (erase_program M_asm))) = Mem.support m.
  Proof.
    eapply Genv.init_mem_genv_sup. eauto.
  Qed.  

  Lemma MQ: match_query cc_compcert
              rca_w
              q0
              (Asm.initial_regset (Vptr b Ptrofs.zero) (Vptr sb Ptrofs.zero), m1).
  Proof.
    simpl. exists q0. split.
    - econstructor. econstructor. red. split.
      (* ro memory *)
      + eapply ValueAnalysis.initial_romatch; eauto.
      + unfold se. rewrite SUP. eapply Mem.sup_include_refl.
    - exists q0. split.
      econstructor. split. eauto. constructor.
      exists (Asm.initial_regset (Vptr b Ptrofs.zero) (Vptr sb Ptrofs.zero), m1).        
      split.
      (* cainjp (important) *)
      + exploit Genv.find_symbol_not_fresh; eauto. intros BV.
        econstructor.
        * rewrite Conventions1.loc_arguments_main. econstructor.
        * econstructor.
          unfold Mem.flat_inj. unfold Mem.valid_block in BV.
          destruct Mem.sup_dec; try congruence.
          eauto. reflexivity.
        * intros. unfold Conventions.size_arguments in H.
          rewrite Conventions1.loc_arguments_main in H. simpl in H.
          inv H. lia.
        * econstructor.
        * econstructor.
        * econstructor. eapply Mem.valid_new_block. eauto.
        * econstructor. red. unfold Conventions.size_arguments.
          rewrite Conventions1.loc_arguments_main. reflexivity.
        * congruence.
        * vm_compute. congruence.            
      + red. repeat apply conj.
        * intros. simpl. eapply Valuesrel.val_inject_refl.
        * vm_compute. congruence.
        * simpl. eapply Mem.extends_refl.
  Qed.
  
  
    (* Prove [match_senv cc_compcert rca_w se0 se0] which is useful for the following proof*)
    Lemma MSENV: match_senv cc_compcert rca_w se se.
    Proof.
      econstructor. econstructor. simpl. auto.
      econstructor. simpl. econstructor. auto.
      econstructor. simpl. econstructor.
      (* match_stbls_flat_id in Globalenv *)
      + rewrite <- SUP. eapply Genv.match_stbls_flat_id.
      + unfold se. setoid_rewrite SUP. eapply Mem.sup_include_refl.
      + unfold se. setoid_rewrite SUP.
        erewrite Mem.support_alloc with (m2 := m1).
        eapply Mem.sup_incr_in2. eauto.
      + simpl. auto. 
    Qed.

    Variable incoming_w : inv_world incoming_cond.
      (** This hypothesis is specific to the definition of programs *)
    Hypothesis VQ0: query_inv incoming_cond incoming_w q0.
    Hypothesis SYMINV: symtbl_inv incoming_cond incoming_w se.

    (* Lemma asm_query_inv: query_inv (incoming_cond @! cc_compcert) (incoming_w, rca_w) (rs0, m1). *)
    (* Proof. *)
    (*   econstructor. split; eauto. *)
    (*   eapply MQ. *)
    (* Qed. *)

    (* Lemma asm_symtbl_inv: symtbl_inv (incoming_cond @! cc_compcert) (incoming_w, rca_w) se. *)
    (* Proof. *)
    (*   econstructor. instantiate (1:=se). split. auto. *)
    (*   eapply MSENV. *)
    (* Qed. *)

    Hypothesis incoming_cond_retval:
      forall r, reply_inv incoming_cond incoming_w r ->
           exists retval, cr_retval r = Vint retval.
    
    Lemma asm_reply_inv: forall r,
        reply_inv (incoming_cond @! cc_compcert) (incoming_w, rca_w) r ->
        exists retval : int, Asm.final_reply r = Vint retval.
    Proof.
      (* post-condition can guarantee that the return value is an integer *)
      intros r RINV.
      inv RINV. destruct H.
      exploit incoming_cond_retval. eauto. intros (retval & RV).
      inv H0. destruct H1. inv H0. inv H2. inv H1.
      destruct H2. inv H1. inv H2. destruct H1. inv H2. inv H1.
      destruct r. 
      unfold Asm.final_reply.
      vm_compute in tres. unfold tres in *.
      simpl in RV. subst.
      inv H12. destruct H4. inv H2.
      simpl in H4. specialize (H4 (Asm.IR Asm.RAX)). rewrite <- H5 in H4.
      inv H4. eauto.
    Qed.

End Initial.

End CLOSED_ASM_SAFE.
    
(** The final theorem of the hash map example --- the linked assembly
module is reachable safe *)
Theorem hash_map_closed_safety: forall linked_list_asm hash_map_asm linked_mod,
    (* Compilation for the two modules *)
    transf_rustlight_program linked_list_mod = OK linked_list_asm ->
    transf_clight_program hash_map_prog = OK hash_map_asm ->
    (* Linking of the two modules *)
    Linking.link hash_map_asm linked_list_asm = Some linked_mod ->
    closed_safety (Asm.closed_semantics linked_mod).
Proof.
  intros ? ? ? C1 C2 LINK. exploit link_linked_list_hash_map_safe_1; eauto.
  intros OPEN_SAFE.
  exploit link_linked_list_hash_map_safe_1; eauto. intros SAFE.
  eapply closed_open_safety_adequacy with
    (IB := (((hmap_rs_cond @@ rs_own) @! cc_rust_compcert)
              ⊎ hmap_process_cond hmap_size @! cc_compcert)); auto. 
  eapply asm_valid_se; auto.
  (* Safety of intitialization *)
  intros q IQ. unfold Asm.init_query in IQ.
  destruct Genv.find_symbol eqn: FSYM in IQ; try congruence.
  destruct Genv.init_mem eqn: INITM in IQ; try congruence.
  destruct Mem.alloc as [m1 sb] eqn: ALLOCSB in IQ. inv IQ.
  exploit Genv.initmem_inject. eauto. intros INJ1.
  exploit Mem.alloc_right_inject; eauto. intros INJ2.
  exploit Genv.init_mem_genv_sup. eauto. intros SUP.
  set (se0 := (Asm.initial_se (skel (Asm.semantics linked_mod)))) in *.
  set (main_id := Asm.main_id (skel (Asm.semantics linked_mod))) in *.
  set (rs0 := (Asm.initial_regset (Vptr b Ptrofs.zero) (Vptr sb Ptrofs.zero))) in *.
  (* q0 is a valid pre-condition for hmap_process_cond *)
  set (hmap_w := Build_hmap_world_int (Build_list_world_ext main_id se0) None None).
  set (q0 := (cq (Vptr b Ptrofs.zero) signature_main nil m)).
  (* To prove valid_query and valid_for (skel hash_map/linked_list)
  se0, we need to following code *)
  exploit AsmLinking.asm_linking. eauto.
  intros [FSIM].
  erewrite fsim_match_valid_query with (ccA := cc_id).
  2: { eapply fsim_lts with (ccB:= cc_id) (wB := tt) (se2:= se0) (f:= FSIM).
       simpl. auto. unfold se0. eapply asm_valid_se. }
  instantiate (1 := (rs0, m1)).
  2: econstructor.
  exploit clight_semantic_preservation.
  eapply transf_clight_program_match. eauto.
  intros ([FSIM1] & [BSIM1]).
  exploit rustlight_semantic_preservation.
  eapply transf_rustlight_program_match. eauto.
  intros ([FSIM2] & [BSIM2]).
  assert (SK1: skel (Clight.semantics1 hash_map_prog) = skel (Asm.semantics hash_map_asm)).
  { eapply fsim_skel; eauto. }
  assert (SK2: skel (Rustlightown.semantics linked_list_mod) = skel (Asm.semantics linked_list_asm)).
  { eapply fsim_skel; eauto. }
  assert (MAIN_EQ: main_id = main).
  { unfold main_id. eapply Linking.link_prog_inv in LINK. destruct LINK as (A1 & A2 & A3).
    subst. simpl.
    simpl in SK1. unfold erase_program in SK1. inv SK1.
    reflexivity. }
  split.
  (* valid_query: The proof of valid_query: use fsim_match_valid_query and show
    that hmap.c has an internal main function. *)
  - simpl. unfold SmallstepLinking.valid_query. eapply orb_true_iff.
    left.
    (* The left proof goal is: valid_query (Asm.semantics
      hash_map_asm se0) (rs0, m1) = true. It is proved by the
      fsim_match_valid_query of the CompCertO compiler *)    
    erewrite fsim_match_valid_query.
    2: { eapply fsim_lts with (ccB := cc_compcert) (wB := rca_w linked_mod m m1 b sb INITM ALLOCSB) (se1 := se0) (L1 := (Clight.semantics1 hash_map_prog)) (f:= FSIM1).
         (* match_senv cc_compcert rca_w se0 se0 *)
         - eapply MSENV.
         - erewrite fsim_skel. 2: eapply FSIM1.
           eapply Genv.valid_for_linkorder. 2: eapply asm_valid_se.
           eapply Linking.link_erase_program in LINK. 
           eapply Linking.link_linkorder in LINK as (A1 & A2). auto. }
    2: { eapply MQ. eauto. }
    (* The left proof goal is to prove q0 is valid in hash_map_prog
      which is specific to the definition of hash_map_prog which we
      can expand *)
    simpl. unfold Genv.is_internal, Genv.find_funct, Genv.find_funct_ptr.
    rewrite dec_eq_true.
    rewrite Genv.find_def_spec. erewrite Genv.find_invert_symbol.
    2: eauto.
    (* Use (main_id, main_func) in the hash_map_prog *)
    rewrite MAIN_EQ. reflexivity.
  - assert (VQ0: query_inv (hmap_process_cond hmap_size) hmap_w q0).
    { simpl. red. unfold q0. simpl. rewrite dec_eq_true.
      erewrite Genv.find_invert_symbol. 2: eauto.
      red.
      (* use the pre-condition of main function in cq_hmap_process *)
      rewrite MAIN_EQ. simpl. auto. }
    assert (SYMINV: symtbl_inv (hmap_process_cond hmap_size) hmap_w se0).
    { econstructor. 
      econstructor.  unfold wf_senv.
      (* wf_senv can be proved by Genv.valid_for *)
      eapply Linking.link_erase_program in LINK.
      eapply Linking.link_linkorder in LINK as (A1 & A2).
      split.
      eapply Genv.valid_for_linkorder. 2: eapply asm_valid_se.
      rewrite SK1. auto.
      eapply Genv.valid_for_linkorder. 2: eapply asm_valid_se.
      rewrite SK2. auto. }
    exists (inr (hmap_w, (rca_w linked_mod m m1 b sb INITM ALLOCSB))).
    repeat apply conj.
    + exists q0. split. eauto.
      eapply MQ. auto.
    + exists se0. split; auto.
      eapply MSENV.
    + intros. inv H. eapply asm_reply_inv; eauto.
      2: { econstructor. eauto. }
      intros rc RINV. simpl in RINV. do 2 red in RINV.
      (* use the post-condition for the main function in hash_map program *)
      rewrite MAIN_EQ in *. simpl in RINV. eauto.
Qed.
