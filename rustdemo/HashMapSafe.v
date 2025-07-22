Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Rusttypes.
Require Import Cop Ctypes Ctypesdefs.
Require Import Values Globalenvs Memory.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import Clight HashMap LinkedList HashMapCommon.
Require Import Separation.
Require Import MoveCheckingFootprint MoveCheckingDomain.
Require Import MoveCheckingSafe LanguageInterface.
Require Import Clightgenproof.

Local Open Scope error_monad_scope.
Local Open Scope sep_scope.
Import ListNotations.

Lemma max_uint:
  Int.max_unsigned = 4294967295.
Proof.
  reflexivity.
Qed.

Lemma ptr_modulus:
  Ptrofs.modulus = 18446744073709551616.
Proof.
  reflexivity.
Qed.

  
Fixpoint num_frames_cont (k: cont) : nat :=
  match k with
  | Kstop => O
  | Kcall _ _ _ _ k' =>
      S (num_frames_cont k')
  | Kseq _ k
  | Kloop1 _ _ k
  | Kloop2 _ _ k
  | Kswitch k => num_frames_cont k
  end.

Definition num_frames (s: state) : nat :=
  match s with
  | State _ _ k _ _ _
  | Callstate _ _ k _
  | Returnstate _ k _ => num_frames_cont k
  end.


Definition not_call_return_state s :=
  match s with
  | Callstate _ _ _ _
  | Returnstate _ _ _ => False
  | _ => True
  end.


Definition hash_map_sem := semantics1 hash_map_prog.

Definition int_to_nat (i: int) : nat :=
  Z.to_nat (Int.unsigned i).

Definition nat_to_int (n: nat) : int :=
  Int.repr (Z.of_nat n).

Lemma free_rule: forall chunk m b ofs (spec: Values.val -> Prop) P,
    m |= contains chunk b ofs spec ** P ->
    exists m', Mem.free m b ofs (ofs + size_chunk chunk) = Some m'
          /\ m' |= P.
Proof.
  intros until P. intros MP.
  edestruct Mem.range_perm_free as (m1 & FREE1).
  eapply MP. exists m1. split; auto.
  eapply m_invar. eapply MP.
  eapply Mem.free_unchanged_on. eauto.
  intros. intro.
  eapply MP; eauto.
  simpl. auto.
Qed.

Lemma deref_loc_det: forall ty m b ofs bf v1 v2,
    deref_loc ty m b ofs bf v1 ->
    deref_loc ty m b ofs bf v2 ->
    v1 = v2.
Proof.
  destruct ty; intros.
  all: try (inv H; inv H0; simpl in *; try congruence).
  all: try inv H1; inv H6. 
  congruence.
Qed.


(* Clight evaluation of expression is deterministic *)
Lemma eval_expr_lvalue_det: forall ge e le m,
    (forall a v1 ,
        eval_expr ge e le m a v1 ->
        forall v2, eval_expr ge e le m a v2 ->
              v1 = v2)
    /\ (forall a b1 ofs1 bf1,
          eval_lvalue ge e le m a b1 ofs1 bf1 ->
          forall b2 ofs2 bf2, eval_lvalue ge e le m a b2 ofs2 bf2 ->
                         Vptr b1 ofs1 = Vptr b2 ofs2 /\ bf1 = bf2).
Proof.
  intros ge e le m.
  apply eval_expr_lvalue_ind; intros.
  1-4: inv H; auto; inv H0.
  (* tmepvar *)
  inv H0. congruence. inv H1. inv H1.
  eapply H0; eauto. inv H2.
  (* unary operation *)
  inv H2. exploit H0; eauto. intros; subst. congruence. inv H3.
  (* binary op *)
  inv H4.
  exploit H0; eauto. intros; subst.
  exploit H2; eauto. intros; subst. congruence. inv H5.
  (* cast *)
  inv H2. exploit H0; eauto. intros; subst. congruence. inv H3.
  (* sizeof *)
  inv H. eauto. inv H0.
  (* alignof *)
  inv H. auto. inv H0.
  (* deref *)
  { inv H.
    - inv H2. exploit H0. eapply H. intros (A1 & A2). inv A1.
      eapply deref_loc_det; eauto.
    - inv H2. exploit H0. eapply H. intros (A1 & A2). inv A1.
      eapply deref_loc_det; eauto.
    - inv H2. exploit H0. eapply H. intros (A1 & A2). inv A1.
      eapply deref_loc_det; eauto.
    - inv H2. exploit H0. eapply H. intros (A1 & A2). inv A1.
      eapply deref_loc_det; eauto.
    - inv H2. exploit H0. eapply H. intros (A1 & A2). inv A1.
      eapply deref_loc_det; eauto. }
  inv H0; eauto.
  split; congruence.
  split; congruence.
  inv H1; eauto.
  split; congruence.
  split; congruence.
  inv H1. exploit H0. eapply H7. intros. inv H1. auto.
  inv H4. exploit H0. eapply H8. intros. inv H4.
  split; congruence.
  exploit H0. eapply H8. intros. inv H4.
  split; congruence.
  inv H4. exploit H0. eapply H8. intros. inv H4.
  split; congruence.
  exploit H0. eapply H8. intros. inv H4.
  split; congruence.
Qed.

Lemma eval_expr_det: forall ge e le m a v1 v2,
    eval_expr ge e le m a v1 ->
    eval_expr ge e le m a v2 ->
    v1 = v2.
Proof.       
  intros. eapply eval_expr_lvalue_det; eauto.
Qed.

  
Lemma eval_lvalue_det: forall ge e a le m b1 ofs1 bf1,
    eval_lvalue ge e le m a b1 ofs1 bf1 ->
    forall b2 ofs2 bf2, eval_lvalue ge e le m a b2 ofs2 bf2 ->
                   Vptr b1 ofs1 = Vptr b2 ofs2 /\ bf1 = bf2.
Proof.
  intros. eapply eval_expr_lvalue_det; eauto.
Qed.

Lemma eval_exprlist_det: forall ge e le m al tyl vl1,
    eval_exprlist ge e le m al tyl vl1 ->
    forall vl2, eval_exprlist ge e le m al tyl vl2 ->
    vl1 = vl2.
Proof.
  induction 1; intros.
  inv H. auto. inv H2.
  f_equal.
  exploit eval_expr_det. eapply H. eauto. intros. congruence.
  eauto.
Qed.

Lemma assign_loc_det ce : forall ty m b ofs bf v m1 m2,
    assign_loc ce ty m b ofs bf v m1 ->
    assign_loc ce ty m b ofs bf v m2 ->
    m1 = m2.
Proof.
  intros. inv H; inv H0; auto; try congruence.
  inv H1. inv H7. congruence.
Qed.

Lemma alloc_variables_det ce: forall l e1 m1 e2 m2 e3 m3,
    alloc_variables ce e1 m1 l e2 m2 ->
    alloc_variables ce e1 m1 l e3 m3 ->
    e2 = e3 /\ m2 = m3.
Proof.
  induction l; intros until m3; intros A1 A2; inv A1; inv A2; auto.
  rewrite H3 in H8. inv H8. eauto.
Qed.

Lemma bind_parameters_det ce: forall l vl e m m1 m2,
    bind_parameters ce e m l vl m1 ->
    bind_parameters ce e m l vl m2 ->
    m1 = m2.
Proof.
  induction l; intros until m2; intros B1 B2; inv B1; inv B2; auto.
  rewrite H1 in H9. inv H9.
  exploit assign_loc_det. eapply H3. eauto. intros. subst.
  eapply IHl; eauto.
Qed.

Lemma function_entry1_det: forall ge f vl m m1 m2 e1 le1 e2 le2,
    function_entry1 ge f vl m e1 le1 m1 ->
    function_entry1 ge f vl m e2 le2 m2 ->
    e1 = e2 /\ le1 = le2 /\ m1 = m2.
Proof.
  intros. inv H. inv H0.
  exploit alloc_variables_det. eapply H2. eauto. intros (A1 & A2). subst.
  repeat apply conj; auto.
  eapply bind_parameters_det; eauto.
Qed.

(* Separation predicate of bucket *)

(* similar definition for parameter of process *)
Inductive process_val_spec m fp : Values.val -> Prop :=
| process_val_spec_intro: forall v
    (WTVAL: sem_wt_val ll_ce m fp v)
    (WTFP: wt_footprint ll_ce Tbox_int fp)
    (NOREP: list_norepet (footprint_flat fp))
    (CASTED: RustOp.val_casted v Tbox_int),
    process_val_spec m fp v.

Lemma process_val_spec_inv: forall m fp v,
    process_val_spec m fp v ->
    exists b, v = Vptr b Ptrofs.zero.
Proof.
  intros. inv H. inv WTFP.
  inv WTVAL. simpl in WF. congruence.
  inv WTVAL.
  eauto.
Qed.

Lemma process_val_spec_unchanged_on: forall m1 m2 fp v,
    Mem.unchanged_on (fun b _ => In b (footprint_flat fp)) m1 m2 ->
    process_val_spec m1 fp v ->
    process_val_spec m2 fp v.
Proof.
  intros until v. intros UNC PRED.  
  inv PRED. econstructor; eauto.
  eapply sem_wt_val_unchanged_blocks. eauto.
  eapply Mem.unchanged_on_implies. eauto.
  intros. simpl.
  inv WTFP. inv WTVAL. simpl in WF. congruence.
  inv WTVAL.
  simpl in H. simpl. destruct H; try contradiction; eauto.
  destruct H; try contradiction; eauto.
Qed.  


Program Definition process_val_pred (b: block) (pos: Z) (fp: footprint) : massert :=
  {| m_pred m := m |= contains Mptr b pos (process_val_spec m fp)
                   /\ ~ In b (footprint_flat fp);
    m_footprint b1 ofs1 := (b = b1 /\ pos <= ofs1 < pos + size_chunk Mptr)
                           \/ In b1 (footprint_flat fp); |}.
Next Obligation.
  destruct H2.
  repeat apply conj; auto.
  - red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. left. auto.
    eapply Mem.perm_valid_block with (ofs := pos). eapply H2.
    lia.
  - exists H3. split.
    + eapply Mem.load_unchanged_on; eauto.
      intros. simpl. left; auto.
    + eapply process_val_spec_unchanged_on.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. right. auto. auto.
Defined.
Next Obligation.
  destruct H0.
  - destruct H0; subst.
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies. eauto. constructor.
  - inv H6.
    eapply sem_wt_val_footprint_valid_block with (ce := ll_ce) (v:=H3); eauto.
    eapply ll_ce_composite_members_norepet.
Defined.


Lemma bucket_val_spec_inv: forall m fp v,
    bucket_val_spec m fp v ->
    exists b, v = Vptr b Ptrofs.zero.
Proof.
  intros. inv H. inv WTFP.
  inv WTVAL. simpl in WF. congruence.
  rewrite sizeof_List_ty in *. inv WTVAL.
  eauto.
Qed.

Lemma bucket_pred_elim: forall m b ofs fp P,
    m |= bucket_pred b ofs fp ** P ->
    exists v, m |= contains Mptr b ofs (eq v) ** P
         /\ bucket_val_pred m fp v
         /\ ~ In b (footprint_flat fp)
         /\ (forall b1 ofs1, m_footprint (contains Mptr b ofs (eq v) ** P) b1 ofs1 ->
                       In b1 (footprint_flat fp) ->
                       False).
Proof.
  intros until P. intros MPRED.
  simpl in MPRED.
  destruct MPRED as (((A1 & A2 & (v & LOAD & SPEC)) & A4) & A5 & A6).
  exists v. split.
  - simpl. split. split. auto.
    split. auto. eauto. split; auto.
    red. intros. eapply A6; eauto.
    simpl. simpl in H. destruct H; subst. auto.
  - repeat apply conj; auto.
    intros. simpl in H. destruct H.
    + destruct H; subst. eauto.
    + eapply A6; eauto.
      simpl. eauto.
Qed.

Lemma bucket_pred_intro: forall m b ofs v fp P,
    m |= contains Mptr b ofs (eq v) ** P ->
    bucket_val_pred m fp v ->
    ~ In b (footprint_flat fp) ->
    (forall b1 ofs1, m_footprint (contains Mptr b ofs (eq v) ** P) b1 ofs1 ->
                In b1 (footprint_flat fp) -> False) ->
    m |= bucket_pred b ofs fp ** P.
Proof.
  intros until P. intros MPRED BUK NIN SEP.
  simpl. simpl in MPRED.
  destruct MPRED as ((A1 & A2 & A3) & A4 & A5).
  destruct A3 as (v1 & LOAD & SPEC). subst.
  repeat apply conj; try lia; eauto.
  eapply A2. eapply A2.
  red. intros. simpl in H. destruct H.
  - eapply A5; eauto. simpl.
    destruct H; subst. auto.
  - eapply SEP; eauto.
    simpl. right. eauto.
Qed.

(* This predicate is used to prove accessibility of rs_own for the
guarantee condition. It describes the properties of the footprint
owned by the environment. *)
Program Definition rs_own_acc_pred (m: mem) (fp: footprint) (Hm: Mem.sup_include (footprint_flat fp) (Mem.support m)) : massert :=
  {| m_pred m' := Mem.unchanged_on (fun b _ => ~ In b (footprint_flat fp)) m m';
    m_footprint b ofs := In b (Mem.support m) /\ ~ In b (footprint_flat fp) |}.
Next Obligation.
  econstructor.
  - eapply Mem.sup_include_trans. eapply H. eapply H0.
  - intros. split.
    + intros. eapply H in H3; eauto.
      eapply H0. split; eauto.
      eapply Mem.perm_valid_block. eauto. auto.
    + intros. eapply H; eauto.
      eapply H0; eauto. eapply Mem.unchanged_on_support. eauto. auto.
  - intros.
    etransitivity.
    erewrite Mem.unchanged_on_contents; eauto.
    simpl. split; auto. eapply Mem.perm_valid_block. eauto.
    erewrite <- Mem.unchanged_on_perm; eauto. eapply Mem.perm_valid_block. eauto.
    erewrite Mem.unchanged_on_contents; eauto.
Defined.
Next Obligation.
  eapply H. eauto.
Defined.

Section SOUNDNESS.

Variable N : nat.

Context (se : Genv.symtbl).
Context (w: hmap_world_int).


Let ge := globalenv se hash_map_prog.

Let Ni := nat_to_int N.

Hypothesis Neq10: N = 10%nat.

Lemma Nieq : Ni = Int.repr 10.
Proof.
  unfold Ni. rewrite Neq10.
  reflexivity.
Qed.

Lemma Nzeq: Z.of_nat N = 10.
  rewrite Neq10. reflexivity.
Qed.

Lemma N_in_range:
  0 <= 10 <= Int.max_unsigned.
Proof.
  assert (10 < Int.max_unsigned) by reflexivity. lia.
Qed.

Let rw := hmap_rs_own w.

Definition rw_mem : option mem :=
  match rw with
  | Some (rsw _ _ m _)  => Some m
  | None => None
  end.

Definition rw_fp : option flat_footprint :=
  match rw with
  | Some (rsw _ fp _ _) => Some fp
  | None => None                
  end.

Definition rw_sg : option rust_signature :=
  match rw with
  | Some (rsw sg _ _ _) => Some sg
  | None => None                
  end.


(** Combine it with the wf_senv in LinkedListSafe *)
Hypothesis wf_senv: wf_senv se.

Remark hmap_ce: genv_cenv ge = PTree.empty composite.
  reflexivity. Qed.

Lemma massert_eqv_pure_l: forall P,
    massert_eqv P (pure True ** P).
Proof.
  intros. split.
  red; split; [intros; eapply sep_pure; auto|simpl; intros; destruct H; try contradiction; auto].
  red. split. intros. eapply sep_pure in H. destruct H; auto.
  intros. simpl. auto.
Qed.

Lemma hmap_pred_rec_split: forall k n,
    (k < n)%nat ->
    forall fpl b pos,
      length fpl = n ->
      massert_eqv (hmap_pred_rec n fpl b pos)
        (hmap_pred_rec k (firstn k fpl) b pos
           ** bucket_pred b (pos + (size_chunk Mptr * (Z.of_nat k))) (nth k fpl fp_emp)
           ** hmap_pred_rec (n - 1 - k) (skipn (S k) fpl) b (pos + size_chunk Mptr * (Z.of_nat k) + size_chunk Mptr)).
Proof.
  induction k.
  - intros. destruct n; try lia.
    simpl. destruct fpl; inv H0. simpl.
    etransitivity. eapply sepconj_morph_2.
    instantiate (1 := pure True ** bucket_pred b pos f).
    eapply massert_eqv_pure_l.
    reflexivity.
    replace (pos + size_chunk Mptr * 0) with pos by lia.
    rewrite !Nat.sub_0_r. 
    eapply sep_assoc.
  - intros n KLT fpl b pos LEN.
    cbn [hmap_pred_rec firstn].
    destruct fpl. simpl in LEN. destruct n; try lia.
    destruct n; try lia. inv LEN.
    cbn [hmap_pred_rec firstn].
    etransitivity.
    eapply sepconj_morph_2. reflexivity.
    eapply IHk. lia. auto.
    rewrite !skipn_cons.
    replace (S (Datatypes.length fpl) - 1 - S k)%nat with (length fpl - 1 - k)%nat.
    replace ((pos + size_chunk Mptr * Z.of_nat (S k))) with ((pos + size_chunk Mptr + size_chunk Mptr * Z.of_nat k)).
    replace (nth (S k) (f :: fpl) fp_emp) with (nth k fpl fp_emp) by auto.
    symmetry. eapply sep_assoc.
    lia. lia.
Qed.    

Lemma firstn_app_3 {A: Type}: forall (l1 l2 : list A),
    firstn (Datatypes.length l1) (l1 ++ l2) = l1.
Proof.
  intros. rewrite <- (Nat.add_0_r (length l1)).
  rewrite firstn_app_2. rewrite firstn_O.
  eapply app_nil_r.
Qed.

Lemma hmap_pred_rec_append_one:
    forall n fpl b pos fp,
      length fpl = n ->
      massert_eqv (hmap_pred_rec (n + 1)%nat (fpl ++ [fp]) b pos)
        (hmap_pred_rec n fpl b pos
           ** bucket_pred b (pos + (size_chunk Mptr * (Z.of_nat n))) fp).
Proof.
  intros. etransitivity.
  eapply hmap_pred_rec_split with (k:=n). lia.
  rewrite app_length. auto.
  rewrite <- H.
  rewrite firstn_app_3.
  rewrite app_nth2. rewrite Nat.sub_diag.
  replace (S (Datatypes.length fpl)) with (length (fpl ++ [fp])).
  rewrite skipn_all. simpl.
  replace (Datatypes.length fpl + 1 - 1 - Datatypes.length fpl)%nat with 0%nat by lia.
  simpl.
  etransitivity.
  rewrite <- sep_assoc.
  eapply sep_comm. symmetry.
  eapply massert_eqv_pure_l.
  rewrite app_length. simpl. lia.
  lia.
Qed.

Lemma hmap_pred_rec_fpl_length: forall n fpl m b ofs,
    m |= hmap_pred_rec n fpl b ofs ->
    length fpl = n.
Proof.
  induction n; intros until ofs; intros PRED; simpl in PRED.
  - destruct fpl; inv PRED. auto.
  - destruct fpl; inv PRED.
    destruct H0. simpl. f_equal. eauto.
Qed.    

Let hmap_pred := hmap_pred N.

Lemma hmap_pred_fpl_length: forall m b fpl,
    m |= hmap_pred b fpl ->
    length fpl = N.
Proof.
  intros. simpl in H.
  destruct H as (A1 & A2 & A3).
  eapply hmap_pred_rec_fpl_length; eauto.
Qed.


Lemma bucket_pred_emp_eqv: forall b ofs,
    massert_eqv (contains Mptr b ofs (eq Vnullptr))
      (bucket_pred b ofs fp_emp).
Proof.
  intros. red. split.
  - red. split.
    + intros. simpl in *.
      destruct H as (A1 & (A2 & A3) & A4).
      repeat apply conj; auto; try lia.
      destruct A4 as (v & B1 & B2).
      exists v. split; eauto.
      red. subst. rewrite dec_eq_true. auto.
    + intros. simpl in *. destruct H; try contradiction.
      lia.
  - red. split.
    + intros. simpl in *.
      destruct H as ((A1 & (A2 & A3) & A4) & A5); try contradiction.
      repeat apply conj; auto; try lia.
      destruct A4 as (v & B1 & B2).
      exists v. split; eauto.
      red in B2. destruct Val.eq in B2. auto. inv B2. inv WTVAL.
    + intros. simpl in *. destruct H; try contradiction.
      lia.
Qed.

Lemma sep_assoc5: forall A1 A2 A3 A4 A5 m,    
    m |= (A1 ** A2 ** A3 ** A4) ** A5 ->
    m |= A1 ** A2 ** A3 ** A4 ** A5.
Proof.
  intros. rewrite !sep_assoc in H. auto.
Qed.

(** TODO: property of splitting hmap_pred_rec  *)

(* Pre-condition of hmap_process function *)
(** We should not make hmap_process an external function because
its pre-condition of the hmap argument is not compatible with rs_own.
It cannot be called from Rust side. The rust module cannot
instantiate a value with type hmap_ty. One way to resolve this problem
is that prove manually {I'}M[..] refining {I@@rs_own}M[..] where I' is
a more dedicated condition that distinguish the call to
hmap_process or process and then use different conditions. *)


(* state invariant *)

Definition return_find_bucket_cont k :=
  (Kseq
     (Sifthenelse
        (Ebinop Oeq (Ederef (Etempvar buk List_box_ptr) List_ptr)
           (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint) 
        (Sreturn None)
        (Ssequence
           (Scall (Some tmp)
              (Evar find
                 (Tfunction (Tcons List_ptr (Tcons tint Tnil)) List_ptr cc_default))
              [Ederef (Etempvar buk List_box_ptr) List_ptr; Evar key tint])
           (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)))) k).

(* We call hmap_operate_on from the main function. [b_hmap] is used to
record the value of the hmap in main *)
Inductive hmap_operate_on_cont b_hmap : cont -> Prop :=
(* from main function *)
| hmap_operate_on_cont_intro1: forall le
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero))
    (FUNID: list_callee_ext (hmap_list_ext w) = main),    
    hmap_operate_on_cont b_hmap (Kcall None main_func empty_env le (Kseq (Sreturn (Some (Econst_int Int.zero tint))) Kstop))
(* from environment *)
| hmap_operate_on_cont_intro2: forall
  (HMLOC: hmap_location w = Some b_hmap)
  (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process),
    hmap_operate_on_cont b_hmap Kstop.

(* The continuation (that inside Kcall) of calling find_bucket. The
caller can be hmap_process, hmap_set, hmap_remove. It outputs a
predicate which describe the contents of hmap_process. [b] is the
block storing the hash_map *)
Inductive call_find_bucket_from_operate_on (b: block) : cont -> massert -> Prop :=
| call_find_bucket_from_operate_on_intro: forall k e le b_hmap b_key ki
    (ENV: e = PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
    (LENV: le = create_undef_temps (fn_temps hmap_operate_on_func))
    (CONT: hmap_operate_on_cont b k),
    call_find_bucket_from_operate_on b (Kcall (Some buk) hmap_operate_on_func e le (return_find_bucket_cont k))
                                     (contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
                                        ** contains Mint32 b_key 0 (eq (Vint ki)))
.

Definition find_bucket_return_to_hmap_set_cont k :=
  (Kseq
     (Ssequence
        hmap_set_cond
        (* *buk = insert(tmp, key, val) *)
        hmap_set_after_cond)
     k).

Inductive hmap_set_cont b_hmap : cont -> Prop :=
| hmap_set_cont_intro: forall le
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero)),
    hmap_set_cont b_hmap (Kcall None main_func empty_env le (Kseq main_after_insertion Kstop)).

Inductive call_find_bucket_from_hmap_set (b_hmap: block) : cont -> massert -> Prop :=
| call_find_bucket_from_hmap_set_intro: forall k e le sb_hmap sb_key sb_v kv fp
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (LENV: le = create_undef_temps (fn_temps hmap_set_func))
    (CONT: hmap_set_cont b_hmap k),
    call_find_bucket_from_hmap_set b_hmap (Kcall (Some buk) hmap_set_func e le (find_bucket_return_to_hmap_set_cont k))
      (contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
         ** contains Mint32 sb_key 0 (eq (Vint kv))
         ** process_val_pred sb_v 0 fp)
.


Inductive call_find_bucket_cont (b: block) : cont -> massert -> Prop :=
(* from hmap_process *)
| call_find_bucket_cont_intro1: forall k MP
    (CONT: call_find_bucket_from_operate_on b k MP),
    call_find_bucket_cont b k MP
| call_find_bucket_cont_intro2: forall k MP
    (CONT: call_find_bucket_from_hmap_set b k MP),
    call_find_bucket_cont b k MP
.

Lemma call_find_bucket_cont_eq_call_cont: forall b k MP,
    call_find_bucket_cont b k MP ->
    k = call_cont k.
Proof.
  intros. inv H; inv CONT; simpl; f_equal.
Qed.

  
(* [b] is the block storing the hash map. The returned massert
specifies the stack contents in find_bucket and the contents in the
caller of find_bucket *)
Inductive call_hash_cont : cont -> massert -> Prop :=
| call_hash_cont_intro: forall k MP b_key b_hmap ki b fpl
    (* (HMLOC: forall b', hmap_location w = Some b' -> b' = b) *)
    (CONT: call_find_bucket_cont b k MP),
    call_hash_cont (Kcall (Some index) find_bucket_func
                      (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                      (PTree.set index Vundef (PTree.empty Values.val))
                      (Kseq
                         (Sreturn
                            (Some (Ebinop Oadd (Evar hmap List_box_ptr) (Etempvar index tuint) List_box_ptr))) k))
      (contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
         ** contains Mint32 b_key 0 (eq (Vint ki))
         (* find_bucket owns the predicate of the hash map *)
         ** hmap_pred b fpl
         ** MP)
.

Inductive call_find_cont : cont -> massert -> Prop :=
| call_find_cont_intro: forall k idx fpl1 fpl2 b b_hmap b_key ki vspec
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N)
    (CONT: hmap_operate_on_cont b k),
    (* (HMLOC: hmap_location w = Some b), *)
    call_find_cont (Kcall (Some tmp) hmap_operate_on_func
       (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
       (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
          (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val))))
       (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr))
          k))
      (* The bucket location we load *)
      (contains Mptr b ((size_chunk Mptr) * (Int.unsigned idx)) vspec
        ** contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
         ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
         ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
         (* stack frame *)
         ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
         ** contains Mint32 b_key 0 (eq (Vint ki))).

Inductive call_hmap_operate_on: state -> Prop :=
| call_hmap_operate_on_intro: forall b1 b2 kv m fpl k
    (SYM: Genv.invert_symbol se b1 = Some hmap_process)
    (** specify the cont *)
    (* b2 must be the hmap_location of the world, if hmap_location is
    None, it means that hmap_operate is called from internal function
    instead of environment *)
    (* (HMLOC: forall b, hmap_location w = Some b -> b = b2) *)
    (HMAP: m |= hmap_pred b2 fpl),    
    call_hmap_operate_on (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m).
    
Inductive call_find_bucket: state -> Prop :=
| call_find_bucket_intro: forall b1 b2 kv k m fpl MP
    (SYM: Genv.invert_symbol se b1 = Some find_bucket)
    (CONT: call_find_bucket_cont b2 k MP)
    (* (HMLOC: hmap_location w = Some b2) *)
    (* MP is the predicate for the stack frames *)
    (HMAP: m |= hmap_pred b2 fpl ** MP),
    call_find_bucket (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m).

(* The continuation of init_hmap *)
Inductive init_hmap_cont: cont -> Prop :=
| init_hmap_cont_intro: forall le
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (GETHMAP: PTree.get hmap le = Some Vundef)
    (GETVAL: PTree.get val le = Some Vundef),
    init_hmap_cont (Kcall (Some hmap) main_func empty_env le (Kseq main_after_init_hmap Kstop)).


Inductive sound_state_init : state -> Prop :=
  (* Invariants for the main function *)
| hmap_call_main: forall bf m
    (SYMB: Genv.invert_symbol se bf = Some main)
    (FUNID: list_callee_ext (hmap_list_ext w) = main),
    sound_state_init (Callstate (Vptr bf Ptrofs.zero) nil Kstop m)
(* Before calling init_hmap *)
| hmap_main_internal1: forall t s n m
    (STAR: starNf step1 num_frames ge n (State main_func (fn_body main_func) Kstop empty_env (create_undef_temps (fn_temps main_func)) m) t s)
    (NOTCALLRET: not_call_return_state s)
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (RAN: (0<= n <=1)%nat),
    sound_state_init s
(* After calling init_map and before calling malloc for creating a value *)
| hmap_main_internal2: forall t s n m le b fpl
    (STAR: starNf step1 num_frames ge n (State main_func Sskip (Kseq main_after_init_hmap Kstop) empty_env le m) t s)
    (GETHMAP: PTree.get hmap le = Some (Vptr b Ptrofs.zero))
    (GETVAL: PTree.get val le = Some Vundef)
    (MPRED : m |= hmap_pred b fpl)
    (NOTCALLRET: not_call_return_state s)
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (RAN: (0<= n <=3)%nat),
    sound_state_init s
(* Before calling malloc for creating the value *)
| hmap_main_insert_call_malloc: forall m bf sz le b_hmap fpl
    (FINDF: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some Clightgen.malloc_decl)
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero))
    (GETVAL: PTree.get val le = Some Vundef)
    (MPRED : m |= hmap_pred b_hmap fpl)
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (SZEQ: sz = Vlong (Int64.repr 4)),
    sound_state_init (Callstate (Vptr bf Ptrofs.zero) [sz]
                   (Kcall (Some val) main_func empty_env le
                      (Kseq (Ssequence main_assign_value main_call_hmap_set) (Kseq main_after_insertion Kstop))) m)
(* After returning from malloc of allocating the value *)
| hmap_main_insert_return_malloc: forall m b_v b_hmap le fpl
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero))
    (GETVAL: PTree.get val le = Some Vundef)
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (DIS_BV: forall ofs, ~ (m_footprint (hmap_pred b_hmap fpl) b_v ofs))
    (MPRED: m |= contains_neg Mptr b_v (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr 4)))
              ** range b_v 0 4
              ** hmap_pred b_hmap fpl),
    sound_state_init (Returnstate (Vptr b_v Ptrofs.zero)
                   (Kcall (Some val) main_func empty_env le
                      (Kseq (Ssequence main_assign_value main_call_hmap_set) (Kseq main_after_insertion Kstop))) m)
(* Before calling hmap_set, that is, assigning 23 into the *val *)
| hmap_main_insert_assign_val: forall m b_v b_hmap le fpl t s n
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero))
    (GETVAL: PTree.get val le = Some (Vptr b_v Ptrofs.zero))
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (DIS_BV: forall ofs, ~ (m_footprint (hmap_pred b_hmap fpl) b_v ofs))
    (MPRED: m |= contains_neg Mptr b_v (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr 4)))
              ** range b_v 0 4
              ** hmap_pred b_hmap fpl)
    (STAR: starNf step1 num_frames ge n (State main_func Sskip (Kseq (Ssequence main_assign_value main_call_hmap_set) (Kseq main_after_insertion Kstop)) empty_env le m) t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0<= n <=4)%nat),
    sound_state_init s
(* After returning from hmap_set, and next is to call hmap_process *)
| hmap_main_before_hmap_process: forall m b_hmap le fpl t s n
    (GETHMAP: PTree.get hmap le = Some (Vptr b_hmap Ptrofs.zero))
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (MPRED: m |= hmap_pred b_hmap fpl)
    (STAR: starNf step1 num_frames ge n (State main_func Sskip (Kseq main_after_insertion Kstop) empty_env le m) t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0<= n <=2)%nat),
    sound_state_init s                     

(* After calling hmap_operate and before returning *)
| hmap_main_internal3: forall t s n m le b fpl
    (STAR: starNf step1 num_frames ge n (State main_func Sskip (Kseq (Sreturn (Some (Econst_int Int.zero tint))) Kstop) empty_env le m) t s)
    (GETHMAP: PTree.get hmap le = Some (Vptr b Ptrofs.zero))
    (MPRED : m |= hmap_pred b fpl)
    (NOTCALLRET: not_call_return_state s)
    (FUNID: list_callee_ext (hmap_list_ext w) = main)
    (RAN: (0<= n <=1)%nat),
    sound_state_init s
| hmap_return_main: forall m
    (FUNID: list_callee_ext (hmap_list_ext w) = main),
    sound_state_init (Returnstate (Vint Int.zero) Kstop m)
                
(* Invariant for the init_hmap function *)
| hmap_call_init_hmap: forall bf m k
    (CONT: init_hmap_cont k)
    (SYMB: Genv.invert_symbol se bf = Some init_hmap),
    sound_state_init (Callstate (Vptr bf Ptrofs.zero) nil k m)
(* Before the loop in init_hmap (i.e., it executes the [malloc] and *)
(* the [tmp = 0] of the loop initialization *)
| hmap_init_hmap_internal1: forall t s n m k
    (STAR: starNf step1 num_frames ge n (State init_hmap_func (fn_body init_hmap_func) k empty_env (create_undef_temps (fn_temps init_hmap_func)) m) t s)
    (CONT: init_hmap_cont k)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0<= n <= 1)%nat),
    sound_state_init s
(* Before calling malloc in init_hmap *)
| hmap_init_hmap_call_malloc: forall m k bf sz
    (CONT: init_hmap_cont k)
    (FINDF: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some Clightgen.malloc_decl)
    (SZEQ: sz = Vlong (Int64.repr (Z.of_nat N * (size_chunk Mptr)))),
    sound_state_init (Callstate (Vptr bf Ptrofs.zero) [sz]
                   (Kcall (Some hmap) init_hmap_func empty_env
                      (PTree.set hmap Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))
                      (Kseq
                         (Ssequence (Ssequence (Sset tmp (Econst_int Int.zero tuint)) init_hmap_loop)
                            (Sreturn (Some (Etempvar hmap hmap_ty)))) k))
                   m)
| hmap_init_hmap_return_malloc: forall m k b
    (CONT: init_hmap_cont k)
    (MPRED: m |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** range b 0 (Z_of_nat N * size_chunk Mptr)),
    sound_state_init (Returnstate (Vptr b Ptrofs.zero)
                   (Kcall (Some hmap) init_hmap_func empty_env
                      (PTree.set hmap Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))
                      (Kseq
                         (Ssequence (Ssequence (Sset tmp (Econst_int Int.zero tuint)) init_hmap_loop)
                            (Sreturn (Some (Etempvar hmap hmap_ty)))) k)) m)
(* Before entering the loop of init_hmap *)
| hmap_init_hmap_before_loop: forall t s n m k b le
    (CONT: init_hmap_cont k)
    (STAR: starNf step1 num_frames ge n
             (State init_hmap_func Sskip
                (Kseq (Ssequence (Ssequence (Sset tmp (Econst_int Int.zero tuint)) init_hmap_loop)
                         (Sreturn (Some (Etempvar hmap hmap_ty)))) k) empty_env
                le m) t s)
    (RAN: (0<= n <= 4)%nat)
    (GETHMAP: PTree.get hmap le = Some (Vptr b Ptrofs.zero))
    (MPRED: m |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              (* The rest memory location *)
              ** range b 0 (Z_of_nat N * size_chunk Mptr))
    (NOTCALLRET: not_call_return_state s),
    sound_state_init s
(* Invariant for the loop *)
| hmap_init_hmap_loop: forall t s n m fpl idx k b le
    (CONT: init_hmap_cont k)
    (STAR: starNf step1 num_frames ge n
             (State init_hmap_func init_hmap_loop
                         (Kseq (Sreturn (Some (Etempvar hmap hmap_ty))) k) empty_env
                le m) t s)
    (* The loop body have 3 steps of execution before entering the next loop *)
    (RAN: if Int.ltu idx (Int.repr buk_size) then (0 <= n <= 7)%nat else (0<= n <= 5)%nat)
    (** loop invariants: the location hmap points to *)
(*     partially satisfies the hmap_pred *)
    (GETTMP2: PTree.get tmp le = Some (Vint idx))
    (GETHMAP: PTree.get hmap le = Some (Vptr b Ptrofs.zero))
    (IDXVAL: if Int.ltu idx (Int.repr buk_size) then True else Int.eq idx (Int.repr buk_size) = true)
    (MPRED: m |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              (* The location of b from 0 to idx is initialized *)
              ** hmap_pred_rec (int_to_nat idx) fpl b 0
              (* The rest memory location *)
              ** range b (Int.unsigned idx * size_chunk Mptr) (Z_of_nat N * size_chunk Mptr))
    (NOTCALLRET: not_call_return_state s),
    sound_state_init s
| hmap_init_hmap_after_loop: forall m fpl k b le
    (CONT: init_hmap_cont k)
    (GETHMAP: PTree.get hmap le = Some (Vptr b Ptrofs.zero))
    (MPRED: m |= hmap_pred b fpl),
    sound_state_init (State init_hmap_func (Sreturn (Some (Etempvar hmap hmap_ty))) k empty_env le m)
| hmap_init_hmap_return: forall m fpl k b
    (CONT: init_hmap_cont k)
    (MPRED: m |= hmap_pred b fpl),
    sound_state_init (Returnstate (Vptr b Ptrofs.zero) k m).

Inductive sound_state_set : state -> Prop :=
(* callstate of hmap_set *)
| hmap_set_call: forall bf b_hmap b_v kv k m v_fp fpl
    (SYMB: Genv.invert_symbol se bf = Some hmap_set)
    (CONT: hmap_set_cont b_hmap k)
    (BVSPEC: process_val_spec m v_fp (Vptr b_v Ptrofs.zero))
    (MPRED: m |= hmap_pred b_hmap fpl)
    (DISJOINT: forall b ofs, m_footprint (hmap_pred b_hmap fpl) b ofs ->
                        In b (footprint_flat v_fp) -> False),
    sound_state_set (Callstate (Vptr bf Ptrofs.zero) [Vptr b_hmap Ptrofs.zero; Vint kv; Vptr b_v Ptrofs.zero] k m)
(* Before calling find_bucket *)
| hmap_set_internal1: forall k n m t s fpl b_hmap sb_hmap sb_key sb_v e kv v_fp
    (STAR: starNf step1 num_frames ge n (State hmap_set_func (fn_body hmap_set_func) k e (create_undef_temps (fn_temps hmap_set_func)) m) t s)
    (CONT: hmap_set_cont b_hmap k)    
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (NOTCALLRET: not_call_return_state s)
    (MPRED: m |= contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** process_val_pred sb_v 0 v_fp
              ** hmap_pred b_hmap fpl)
    (RAN: (0<= n <=1)%nat),
    sound_state_set s
(* Invariant of callstate of find_bucket is defined by
find_bucket_callstate *)                    
(* After returning from find_bucket *)
| hmap_set_internal2: forall k n m t s fp fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le v_fp
    (STAR: starNf step1 num_frames ge n
             (State hmap_set_func Sskip
                (Kseq (Ssequence hmap_set_cond hmap_set_after_cond) k)
                e le m) t s)
    (CONT: hmap_set_cont b_hmap k)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (LENV: le = (set_opttemp (Some buk)
                     (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx))))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))))
    (NOTCALLRET: not_call_return_state s)
    (MPRED: m |= contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** process_val_pred sb_v 0 v_fp)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: length (fpl1 ++ fp :: fpl2) = N)
    (RAN: (0<= n <= 3)%nat),
    sound_state_set s
(* Before calling empty_list *)
| hmap_set_call_empty_list: forall k bf m fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le v_fp
    (SYMB: Genv.invert_symbol se bf = Some empty_list)
    (CONT: hmap_set_cont b_hmap k)
    (* copy from hmap_set_internal2 *)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (LENV: le = (set_opttemp (Some buk)
                     (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx))))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))))
    (* As we want to replace (b_hmap, idx*8) with the return value of
    [empty_list], we just set its memory predicate as contain True *)
    (MPRED: m |= contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** process_val_pred sb_v 0 v_fp)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N),
    sound_state_set (Callstate (Vptr bf Ptrofs.zero) nil (Kcall (Some tmp) hmap_set_func e le (Kseq hmap_set_after_cond k)) m)
(* After returning from empty_list *)
| hmap_set_return_empty_list: forall k m fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le MP  v_fp l_fp b_l
    (CONT: hmap_set_cont b_hmap k)
    (* copy from hmap_set_internal2 *)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (LENV: le = (set_opttemp (Some buk)
                     (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx))))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))))
    (MPEQ: MP = contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** process_val_pred sb_v 0 v_fp)
    (MPRED: m |= MP)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: length (fpl1 ++ l_fp :: fpl2) = N)
    (* l_fp is the footprint of the empty list *)
    (RETV_SPEC: bucket_val_spec m l_fp (Vptr b_l Ptrofs.zero))
    (* disjointness is used to prove bucket_pred_intro which embeds
    the return value into the MP *)
    (DISJOINT: forall b1 ofs1, m_footprint MP b1 ofs1 ->
                In b1 (footprint_flat l_fp) -> False),
    sound_state_set (Returnstate (Vptr b_l Ptrofs.zero) (Kcall (Some tmp) hmap_set_func e le (Kseq hmap_set_after_cond k)) m)
(* Execution of hmap_set_after_cond before calling insert *)
| hmap_set_internal3: forall k n m t s fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le b_l MP v_fp l_fp
    (STAR: starNf step1 num_frames ge n
             (State hmap_set_func Sskip
                (Kseq hmap_set_after_cond k) e le m) t s)
    (CONT: hmap_set_cont b_hmap k)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (GETBUK: le ! buk = Some (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx)))))
    (GETTMP: le ! tmp = Some (Vptr b_l Ptrofs.zero))
    (MPEQ: MP = contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** process_val_pred sb_v 0 v_fp)
    (MPRED: m |= MP)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N)
    (RETV_SPEC: bucket_val_spec m l_fp (Vptr b_l Ptrofs.zero))
    (DISJOINT: forall b1 ofs1, m_footprint MP b1 ofs1 ->
                In b1 (footprint_flat l_fp) -> False)
    (DISJOINT2: ~ In b_hmap (footprint_flat l_fp))
    (NOTCALLRET: not_call_return_state s),
    sound_state_set s
(* Call insert function *)
| hmap_set_call_insert: forall k m fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le b_l MP l_fp bf b_v bv_fp
    (SYMB: Genv.invert_symbol se bf = Some insert)
    (CONT: hmap_set_cont b_hmap k)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (GETBUK: le ! buk = Some (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx)))))
    (GETTMP: le ! tmp = Some (Vptr b_l Ptrofs.zero))
    (MPEQ: MP = contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** contains Mptr sb_v 0 (fun _ => True))
    (MPRED: m |= MP)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N)        
    (RETV_SPEC: bucket_val_spec m l_fp (Vptr b_l Ptrofs.zero))
    (BV_SPEC: process_val_spec m bv_fp (Vptr b_v Ptrofs.zero))
    (DISJOINT: forall b1 ofs1, m_footprint MP b1 ofs1 ->
                (In b1 (footprint_flat l_fp) \/ In b1 (footprint_flat bv_fp)) -> False)
    (DISJOINT2: ~ In b_hmap (footprint_flat l_fp))
    (NOREPET: list_norepet ((footprint_flat l_fp) ++ (footprint_flat bv_fp))),
    sound_state_set (Callstate (Vptr bf Ptrofs.zero) [Vptr b_l Ptrofs.zero; Vint kv; Vptr b_v Ptrofs.zero] (Kcall (Some tmp) hmap_set_func e le (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k)) m)
(* return from insert *)
| hmap_set_return_insert: forall k m fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le b_l MP l_fp b_v
    (CONT: hmap_set_cont b_hmap k)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (GETBUK: le ! buk = Some (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx)))))
    (GETTMP: le ! tmp = Some (Vptr b_l Ptrofs.zero))
    (MPEQ: MP = contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** contains Mptr sb_v 0 (eq (Vptr b_v Ptrofs.zero)))
    (MPRED: m |= MP)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N)
    (RETV_SPEC: bucket_val_spec m l_fp (Vptr b_l Ptrofs.zero))
    (DISJOINT: forall b1 ofs1, m_footprint MP b1 ofs1 ->
                          In b1 (footprint_flat l_fp) -> False)
    (DISJOINT2: ~ In b_hmap (footprint_flat l_fp)),
    sound_state_set (Returnstate (Vptr b_l Ptrofs.zero) (Kcall (Some tmp) hmap_set_func e le (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k)) m)
(* after returning from insert and steps to return set *)
| hmap_set_internal4: forall n t k m fpl1 fpl2 b_hmap sb_hmap sb_key sb_v e kv idx le b_l MP l_fp b_v s (* stmt1 k1 m1 *)
    (STAR: starNf step1 num_frames ge n
             (State hmap_set_func Sskip
                (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k) e le m) t 
             s)
    (* (SEQ: s = (State hmap_set_func stmt1 k1 e le m1)) *)
    (CONT: hmap_set_cont b_hmap k)
    (ENV: e = PTree.set val (sb_v, val_ty)
                (PTree.set key (sb_key, tint)
                   (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (GETBUK: le ! buk = Some (Vptr b_hmap (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx)))))
    (GETTMP: le ! tmp = Some (Vptr b_l Ptrofs.zero))
    (* (BUKEQ: if (n <=? 1)%nat then BUKPRED = fun _ => True else BUKPRED = (eq (Vptr b_l Ptrofs.zero))) *)
    (MPEQ: MP = contains Mptr b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) (fun _ => True)
              ** contains_neg Mptr b_hmap (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0
              (* ** bucket_pred b_hmap ((size_chunk Mptr) * (Int.unsigned idx)) fp *)
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b_hmap (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* local stack of hmap_set *)
              ** contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))
              ** contains Mint32 sb_key 0 (eq (Vint kv))
              ** contains Mptr sb_v 0 (eq (Vptr b_v Ptrofs.zero)))
    (MPRED: m |= MP)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: S (length (fpl1 ++ fpl2)) = N)
    (RETV_SPEC: bucket_val_spec m l_fp (Vptr b_l Ptrofs.zero))
    (DISJOINT: forall b1 ofs1, m_footprint MP b1 ofs1 ->
                          In b1 (footprint_flat l_fp) -> False)
    (DISJOINT2: ~ In b_hmap (footprint_flat l_fp))
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0<= n <= 2)%nat),
    sound_state_set s
(* return state of set function *)
| hmap_set_returnstate: forall k m b_hmap fpl
    (CONT: hmap_set_cont b_hmap k)
    (MPRED: m |= hmap_pred b_hmap fpl),
    sound_state_set (Returnstate Vundef k m)
.


Inductive sound_state : state -> Prop :=
(* Invariant for the initialization of the hash_map *)
| hmap_init_inv: forall s
    (SINV_INIT: sound_state_init s),
    sound_state s
(* Invariant for inserting key-value pairs into the hash_map *)
| hmap_set_inv: forall s
    (SINV_SET: sound_state_set s),
    sound_state s
                
(* callstate in process function *)
| hmap_call_process: forall bf b rwm rwfp
    (SYMB: Genv.invert_symbol se bf = Some process)
    (RWMEM: rw_mem = Some rwm)
    (RWFP: rw_fp = Some rwfp)
    (WTVAL: sem_wt_val ll_ce rwm (fp_box b 4 (fp_scalar Rusttypes.type_int32s)) (Vptr b Ptrofs.zero))
    (FPEQ: list_equiv rwfp (footprint_flat (fp_box b 4 (fp_scalar Rusttypes.type_int32s))))
    (FUNID: (list_callee_ext (hmap_list_ext w)) = process)
    (SGEQ: rw_sg = Some process_sig),
    sound_state (Callstate (Vptr bf Ptrofs.zero) [Vptr b Ptrofs.zero] Kstop rwm)
| hmap_process_internal: forall b_val m e s t n fp rwm Hm rwfp
    (MPRED: m |= process_val_pred b_val 0 fp
              ** rs_own_acc_pred rwm fp Hm)
    (RWMEM: rw_mem = Some rwm)
    (RWFP: rw_fp = Some rwfp)
    (FPEQ: list_equiv rwfp (footprint_flat fp))
    (STAR: starNf step1 num_frames ge n (State process_func (fn_body process_func) Kstop e (PTree.empty Values.val) m) t s)
    (ENV: e = PTree.set val (b_val, tptr tint) empty_env)
    (NOTCALLRET: not_call_return_state s)
    (FUNID: (list_callee_ext (hmap_list_ext w)) = process)
    (SGEQ: rw_sg = Some process_sig)
    (RAN: (0 <= n <= 5)%nat),
    sound_state s
| hmap_return_process: forall b fp m rwm rwfp Hm
    (MPRED: m |= rs_own_acc_pred rwm fp Hm)
    (RWMEM: rw_mem = Some rwm)
    (RWFP: rw_fp = Some rwfp)
    (WTVAL: sem_wt_val ll_ce m fp (Vptr b Ptrofs.zero))
    (WTFP: wt_footprint ll_ce (Tbox Rusttypes.type_int32s) fp)
    (NOREP: list_norepet (footprint_flat fp))
    (CAST: RustOp.val_casted (Vptr b Ptrofs.zero) (rs_sig_res process_sig)) 
    (FPEQ: list_equiv rwfp (footprint_flat fp))
    (FUNID: (list_callee_ext (hmap_list_ext w)) = process)
    (SGEQ: rw_sg = Some process_sig),
    sound_state (Returnstate (Vptr b Ptrofs.zero) Kstop m)

(* We need to maintain an invariant that hmap_operate_on is an internal function *) 
| hmap_operate_on_callstate: forall b1 b2 kv k m
    (CALL: call_hmap_operate_on (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m))
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (CONT: hmap_operate_on_cont b2 k),
    sound_state (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)
| hmap_operate_on_internal1: forall t s b_hmap b_key fpl ki b m e le k n
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl)
    (* (HMLOC: forall b', hmap_location w = Some b' -> b' = b) *)
    (ENV: e = PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
    (LENV: le = create_undef_temps (fn_temps hmap_operate_on_func))
    (STAR: starNf step1 num_frames ge n (State hmap_operate_on_func (fn_body hmap_operate_on_func) k e le m) t s)
    (CONT: hmap_operate_on_cont b k)
    (NOTCALLRET: not_call_return_state s)
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (RAN: (0<= n <=1)%nat),
    sound_state s
(* return from find_bucket *)
| hmap_operate_on_internal2: forall t s1 s2 n idx fpl1 fpl2 b fp m k b_hmap b_key ki
    (SEQ: s1 = (State hmap_operate_on_func Sskip (return_find_bucket_cont k)
                  (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (set_opttemp (Some buk)
                     (Vptr b (Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned idx))))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m))    
    (STAR: starNf step1 num_frames ge n s1 t s2)
    (MPRED: m |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b ((size_chunk Mptr) * (Int.unsigned idx)) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* stack frame *)
              ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki)))
    (* (HMLOC: forall b', hmap_location w = Some b' -> b' = b) *)
    (CONT: hmap_operate_on_cont b k)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: length (fpl1 ++ fp :: fpl2) = N)
    (NOTCALLRET: not_call_return_state s2)
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (RAN: (0 <= n <= 10)%nat),
    sound_state s2
| hmap_operate_on_call_find: forall m k MP fp ki bf v
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (FINDSYM: Genv.invert_symbol se bf = Some find)
    (CONT: call_find_cont k MP)
    (SUP: Mem.sup_include (footprint_flat fp) (Mem.support m)),
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    (** TODO: specify the query_inv of (I @@ rs_own) *)
    sound_state (Callstate (Vptr bf Ptrofs.zero) [v; Vint ki] k m)
| hmap_operate_on_return_find: forall m k MP fp v
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (CONT: call_find_cont k MP),
    sound_state (Returnstate v k m)
(* execution after returning from find *)
| hmap_operate_on_internal3: forall k idx fpl1 fpl2 b b_hmap b_key ki vspec s0 t s m fp MP n v
    (SEQ: s0 = (State hmap_operate_on_func Sskip
                  (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k) (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (set_opttemp (Some tmp) v (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx))) (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))))
                  m))
    (CONT: hmap_operate_on_cont b k)
    (MPEQ: MP = contains Mptr b (size_chunk Mptr * Int.unsigned idx) vspec **
              contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) **
              hmap_pred_rec (int_to_nat idx) fpl1 b 0 **
              hmap_pred_rec (N - 1 - int_to_nat idx) fpl2 b (size_chunk Mptr * Int.unsigned idx + size_chunk Mptr) **
              contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero)) **
              contains Mint32 b_key 0 (eq (Vint ki)))
    (* (HMLOC: forall b', hmap_location w = Some b' -> b' = b) *)
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0 <= n <= 2)%nat)
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (FPLEN: length (fpl1 ++ fp :: fpl2) = N),
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state s
(*     sound_state s *)
| hmap_operate_on_returnstate: forall k m b fpl
    (** TODO: specify the cont *)
    (CONT: hmap_operate_on_cont b k)
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (* (HMLOC: forall b', hmap_location w = Some b' -> b' = b) *)
    (MPRED: m |= hmap_pred b fpl),
    sound_state (Returnstate Vundef k m)
| find_bucket_callstate: forall b1 b2 kv k m
    (CALL: call_find_bucket (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)) ,
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)
| find_bucket_internal1: forall s0 t s n b_key b_hmap m k b fpl ki MP
    (SEQ: s0 = (State find_bucket_func (fn_body find_bucket_func) k
                  (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (create_undef_temps (fn_temps find_bucket_func)) m))
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl
              ** MP)
    (* (HMLOC: forall b, hmap_location w = Some b -> b = b2) *)
    (CONT: call_find_bucket_cont b k MP)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0 <= n <= 1)%nat),
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state s
(* at_external state calling hash function in the Rust side *)
| find_bucket_call_hash: forall ki b k m MP
    (COND: hash_pre_cond_args Ni [Vint ki; Vint Ni])
    (FINDSYM: Genv.invert_symbol se b = Some hash)
    (CONT: call_hash_cont k MP)
    (MPRED: m |= MP),
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state (Callstate (Vptr b Ptrofs.zero) [Vint ki; Vint Ni] k m)
| find_bucket_return_hash: forall v k m MP
    (COND: hash_post_cond_retv Ni v)
    (CONT: call_hash_cont k MP)
    (MPRED: m |= MP), 
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state (Returnstate v k m)
| find_bucket_internal2: forall s0 t s n b_key b_hmap m k b fpl ki MP r
    (SEQ: s0 = (State find_bucket_func Sskip
                  (Kseq (Sreturn (Some (Ebinop Oadd (Evar hmap List_box_ptr) (Etempvar index tuint) List_box_ptr))) k) (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env)) (set_opttemp (Some index) (Vint r) (PTree.set index Vundef (PTree.empty Values.val))) m))
    (INRAN: Int.ltu r Ni = true)
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl
              ** MP)
    (* (HMLOC: forall b, hmap_location w = Some b -> b = b2) *)
    (CONT: call_find_bucket_cont b k MP)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process) *)
    (RAN: (0 <= n <= 1)%nat),
    sound_state s
| find_bucket_returnstate: forall idx fpl1 fpl2 b fp m k MP
    (MPRED: m |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b (size_chunk Mptr * Int.unsigned idx) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b ((size_chunk Mptr * Int.unsigned idx) + size_chunk Mptr)
              ** MP)
    (* (HMLOC: forall b, hmap_location w = Some b -> b = b2) *)
    (MAXRAN: Int.unsigned idx < Z.of_nat N)
    (FPLEN: length (fpl1 ++ fp :: fpl2) = N)
    (CONT: call_find_bucket_cont b k MP),
    (* (FUNID: list_callee_ext (hmap_list_ext w) = hmap_process), *)
    sound_state (Returnstate (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx))) k m)
.

(* maybe we can have a general function_entry_rule *)
Lemma function_entry_hmap_operate_on: forall m P b ofs ki,
    m |= P ->
    exists b1 b2 m', 
      function_entry1 ge hmap_operate_on_func [Vptr b ofs; Vint ki] m (PTree.set key (b2, tint) (PTree.set hmap (b1, hmap_ty) empty_env)) (create_undef_temps (fn_temps hmap_operate_on_func)) m'
      /\ m' |= contains Mptr b1 0 (eq (Vptr b ofs))
          ** contains Mint32 b2 0 (eq (Vint ki))
          ** P.
Proof.
  intros until ki. intros MP.
  destruct (Mem.alloc m 0 (size_chunk Mptr)) eqn: ALLOC1.
  destruct (Mem.alloc m0 0 (size_chunk Mint32)) eqn: ALLOC2.
  exploit alloc_rule. eapply ALLOC1. lia. vm_compute. congruence.
  eapply MP. intros MP1.
  exploit alloc_rule. eapply ALLOC2. lia. vm_compute. congruence.
  eapply MP1. intros MP2.
  eapply sep_swap12 in MP2.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mptr). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vptr b ofs). instantiate (1 := eq (Vptr b ofs)). auto.
  intros (m2 & STORE1 & MP3).
  eapply sep_swap12 in MP3.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mint32). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vint ki). instantiate (1 := eq (Vint ki)). auto.
  intros (m3 & STORE2 & MP4).
  eapply sep_swap12 in MP4.
  exists p, p0, m3. split.
  econstructor.
  eapply proj_sumbool_true with (a:= list_norepet_dec ident_eq [hmap; key]); eauto.
  econstructor; eauto.
  econstructor; eauto. econstructor.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  auto.
Qed.  

(* The same as hmap_opearate_on because they have the same types of arguments *)
Lemma function_entry_find_bucket: forall m P b ofs ki,
    m |= P ->
    exists b1 b2 m', 
      function_entry1 ge find_bucket_func [Vptr b ofs; Vint ki] m (PTree.set key (b2, tint) (PTree.set hmap (b1, hmap_ty) empty_env)) (create_undef_temps (fn_temps find_bucket_func)) m'
      /\ m' |= contains Mptr b1 0 (eq (Vptr b ofs))
          ** contains Mint32 b2 0 (eq (Vint ki))
          ** P.
Proof.
  intros until ki. intros MP.
  destruct (Mem.alloc m 0 (size_chunk Mptr)) eqn: ALLOC1.
  destruct (Mem.alloc m0 0 (size_chunk Mint32)) eqn: ALLOC2.
  exploit alloc_rule. eapply ALLOC1. lia. vm_compute. congruence.
  eapply MP. intros MP1.
  exploit alloc_rule. eapply ALLOC2. lia. vm_compute. congruence.
  eapply MP1. intros MP2.
  eapply sep_swap12 in MP2.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mptr). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vptr b ofs). instantiate (1 := eq (Vptr b ofs)). auto.
  intros (m2 & STORE1 & MP3).
  eapply sep_swap12 in MP3.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mint32). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vint ki). instantiate (1 := eq (Vint ki)). auto.
  intros (m3 & STORE2 & MP4).
  eapply sep_swap12 in MP4.
  exists p, p0, m3. split.
  econstructor.
  eapply proj_sumbool_true with (a:= list_norepet_dec ident_eq [hmap; key]); eauto.
  econstructor; eauto.
  econstructor; eauto. econstructor.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  auto.
Qed.  


Lemma function_entry_process: forall m b ofs fp Hm,
    process_val_spec m fp (Vptr b ofs) ->
    exists b1 m', 
      function_entry1 ge process_func [Vptr b ofs] m (PTree.set LinkedList.val (b1, tptr tint) empty_env) (PTree.empty Values.val) m'
      /\ m' |= process_val_pred b1 0 fp ** rs_own_acc_pred m fp Hm.
Proof.
  intros until Hm. intros WTVAL.
  destruct (Mem.alloc m 0 (size_chunk Mptr)) eqn: ALLOC1.
  exploit alloc_rule. eapply ALLOC1. lia. vm_compute. congruence.
  instantiate (1 := rs_own_acc_pred m fp Hm). simpl. eapply Mem.unchanged_on_refl.
  intros MP1.
  exploit process_val_spec_unchanged_on.
  eapply Mem.alloc_unchanged_on. eauto. eauto. intros SPEC1.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mptr). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vptr b ofs). instantiate (1 := eq (Vptr b ofs)).
  reflexivity.
  intros (m2 & STORE1 & MP3).
  exists p, m2. split.
  - econstructor.
    + eapply proj_sumbool_true with (a:= list_norepet_dec ident_eq [LinkedList.val]); eauto.
    + econstructor. eauto. simpl. 
      econstructor.
    + econstructor. reflexivity.
      econstructor. reflexivity. eauto.
      econstructor.
    + reflexivity.
  - simpl. simpl in MP3.
    destruct MP3 as ((A1 & A2 & (v & A3 & A4)) & A5 & A6).
    subst.
    assert (NIN: ~ In p (footprint_flat fp)).
    { intro. eapply Mem.fresh_block_alloc. eauto.
      eapply Hm. eauto. }    
    repeat apply conj; eauto. lia. lia.
    eapply A2. apply Z.divide_0_r.
    exists (Vptr b ofs). split; auto.
    (* process_val_spec *)
    eapply process_val_spec_unchanged_on; eauto.
    eapply Mem.store_unchanged_on. eauto. 
    intros. auto.
    red in A6. simpl in A6.
    red. simpl. intros. destruct H.
    + destruct H; subst. eapply A6; eauto.
    + destruct H0. congruence.
Qed.


Lemma function_entry_hmap_set: forall m b_hmap kv b_v fp P,
    process_val_spec m fp (Vptr b_v Ptrofs.zero) ->
    m |= P ->
    (forall b ofs, m_footprint P b ofs -> In b (footprint_flat fp) -> False) ->
    exists b1 b2 b3 m', 
      function_entry1 ge hmap_set_func [Vptr b_hmap Ptrofs.zero; Vint kv; Vptr b_v Ptrofs.zero] m
        (PTree.set val (b3, val_ty) (PTree.set key (b2, tint) (PTree.set hmap (b1, hmap_ty) empty_env)))
        (create_undef_temps (fn_temps hmap_set_func)) m'
      /\ m'
          |= contains Mptr b1 0 (eq (Vptr b_hmap Ptrofs.zero)) **
          contains Mint32 b2 0 (eq (Vint kv)) **
          process_val_pred b3 0 fp ** P.
Proof.
  intros until P. intros SPEC MP DIS.
  destruct (Mem.alloc m 0 (size_chunk Mptr)) eqn: ALLOC1.
  destruct (Mem.alloc m0 0 (size_chunk Mint32)) eqn: ALLOC2.
  destruct (Mem.alloc m1 0 (size_chunk Mptr)) eqn: ALLOC3.  
  exploit alloc_rule. eapply ALLOC1. lia. vm_compute. congruence.
  eapply MP. intros MP1.
  exploit alloc_rule. eapply ALLOC2. lia. vm_compute. congruence.
  eapply MP1. intros MP2.
  eapply sep_swap12 in MP2.
  exploit alloc_rule. eapply ALLOC3. lia. vm_compute. congruence.
  eapply MP2. intros MP3.
  erewrite sep_swap12, sep_swap23 in MP3.  
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mptr). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vptr b_hmap Ptrofs.zero). instantiate (1 := eq (Vptr b_hmap Ptrofs.zero)). auto.
  intros (m3 & STORE1 & MP4). 
  eapply sep_swap12 in MP4.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mint32). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vint kv). instantiate (1 := eq (Vint kv)). auto.
  intros (m4 & STORE2 & MP5).
  eapply sep_swap12 in MP5.
  eapply sep_swap3 in MP5.
  exploit storev_rule. eapply range_contains with (ofs:=0) (chunk:= Mptr). eauto.
  eapply Z.divide_0_r.
  instantiate (1 := Vptr b_v Ptrofs.zero). instantiate (1 := eq (Vptr b_v Ptrofs.zero)). auto.
  intros (m5 & STORE3 & MP6).
  (* val_spec in m5 *)
  assert (FPVALID: forall b, In b (footprint_flat fp) -> Mem.valid_block m b).
  { inv SPEC. inv WTFP.
    inv WTVAL. inv WTVAL. inv WT. inv WTVAL. inv WTLOC. simpl.
    intros. destruct H; try contradiction. subst.
    eapply sem_wt_val_valid_block. eauto. inv WTVAL. simpl. eauto. }   
  exploit process_val_spec_unchanged_on.
  2: eapply SPEC. instantiate (1 := m5). (* inv SPEC. inv WTFP. *)
  (* inv WTVAL. inv WTVAL. inv WT. inv WTVAL. inv WTLOC. *)
  (* simpl. *)
  eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
  eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
  eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
  (* exploit sem_wt_val_valid_block. eauto. simpl. eauto. intros VB. *)
  (* inv WTVAL.   *)
  eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
  intros. intro. eapply Mem.fresh_block_alloc. eapply ALLOC1. eapply FPVALID. auto.
  eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
  intros. intro. eapply Mem.fresh_block_alloc. eapply ALLOC2. 
  eapply Mem.valid_block_alloc; eauto. 
  eapply Mem.unchanged_on_trans. eapply Mem.store_unchanged_on. eauto.
  intros. intro. eapply Mem.fresh_block_alloc. eapply ALLOC3.
  eapply Mem.valid_block_alloc; eauto.
  eapply Mem.valid_block_alloc; eauto.
  eapply Mem.unchanged_on_refl.
  intros SPEC1. 
  eapply sep_swap3 in MP6.
  exists p, p0, p1, m5. split.
  econstructor.
  eapply proj_sumbool_true with (a:= list_norepet_dec ident_eq [hmap; key; val]); eauto.
  (* alloc_variables *)
  econstructor; eauto.
  econstructor; eauto. econstructor; eauto.
  simpl. econstructor. 
  (* bind_parameters *)  
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. reflexivity.
  econstructor. reflexivity. eauto.
  econstructor. auto.
  (* memory predicate *)
  erewrite <- sep_assoc. erewrite <- sep_assoc in MP6.
  set ( mp:=(contains Mptr p 0 (eq (Vptr b_hmap Ptrofs.zero)) **
               contains Mint32 p0 0 (eq (Vint kv)))) in *.
  erewrite sep_swap12. erewrite sep_swap12 in MP6.
  red. red. do 2 red in MP6.
  destruct MP6 as (A1 & A2 & A3).
  split.
  + simpl. simpl in A1.
    destruct A1 as (B1 & B2 & (v & B3 & B4)).
    assert (NIN: ~ In p1 (footprint_flat fp)).
    { intro. eapply Mem.fresh_block_alloc. eapply ALLOC3.
      eapply Mem.valid_block_alloc; eauto.
      eapply Mem.valid_block_alloc; eauto. }    
    repeat apply conj; eauto. lia. lia.
    eapply B2. eapply Z.divide_0_r.
    subst. exists (Vptr b_v Ptrofs.zero). split; eauto.
  + split; auto.
    red. intros. eapply A3; eauto. simpl. simpl in H.
    destruct H; auto. destruct H. auto.
    simpl in H0. destruct H0.
    * destruct H0.
      -- destruct H0; subst.
         exfalso. eapply Mem.fresh_block_alloc. eapply ALLOC1. auto.
      -- destruct H0; subst.
         exfalso. eapply Mem.fresh_block_alloc. eapply ALLOC2.
         eapply Mem.valid_block_alloc; eauto.
    * exfalso. eapply DIS; eauto. 
Qed.  

Lemma function_entry_main: forall m,
    function_entry1 ge main_func nil m empty_env (create_undef_temps (fn_temps main_func)) m.
      (* /\ m' |= process_val_pred b1 0 fp ** rs_own_acc_pred m fp Hm. *)
Proof.
  intros. econstructor. simpl. constructor.
  econstructor. econstructor. reflexivity.
Qed.

Lemma function_entry_init_hmap: forall m,
    function_entry1 ge init_hmap_func nil m empty_env (create_undef_temps (fn_temps init_hmap_func)) m.
Proof.
  intros. econstructor. simpl. constructor.
  econstructor. econstructor. reflexivity.
Qed.


(* Soundness of at_external, using (I @@ rs_own @! cc_rust_c) as the interface *)

Definition find_rs_sig :=
  mksignature nil nil [List_box; Rusttypes.type_int32s] List_box cc_default ll_ce.

Definition hash_rs_sig :=
  mksignature nil nil [Rusttypes.type_int32s; type_int32u] type_int32u cc_default ll_ce.

Definition empty_list_rs_sig := 
  mksignature nil nil nil List_box cc_default ll_ce.

Definition insert_rs_sig := 
  mksignature nil nil [List_box; Rusttypes.type_int32s; Tbox_int] List_box cc_default ll_ce.

(* External interface: {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc *)
Lemma hash_map_external: forall s q,
    sound_state s ->
    at_external ge s q ->
    exists wI w_rs q_rs,
      cc_rust_c_mq q_rs q
      /\ query_inv hmap_ext_inv wI q_rs
      /\ rs_own_query w_rs q_rs
      /\ wI.(hmap_senv_ext) = se
      /\ forall r_rs r_c,
        reply_inv hmap_ext_inv wI r_rs ->
        (* kripke relation *)
        (exists w_rs', rsw_acc w_rs w_rs' /\ rs_own_reply w_rs' r_rs) ->
        cc_rust_c_mr r_rs r_c ->
        (exists s', after_external s r_c s'
               /\ (forall s', after_external s r_c s' -> sound_state s')).
Proof.
  intros s q_c SINV ATEXT. inv ATEXT. unfold f in *.
  inv SINV; try inv SINV_INIT; try inv SINV_SET; try simpl in NOTCALLRET; try contradiction.
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal main_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      reflexivity. }
    rewrite H in FIND. inv FIND.
  (* call malloc *)
  - rewrite FINDF in H. inv H.
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal init_hmap_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      reflexivity. }
    rewrite H in FIND. inv FIND.
  - rewrite H in FINDF. inv FINDF.
  (* call hmap_set *)
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal hmap_set_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      reflexivity. }
    rewrite H in FIND. inv FIND.
  (** call empty_list in hmap_set *)
   - assert (SUP: Mem.sup_include nil (Mem.support m)).
     { red. intros. inv H0. }
     exists (Build_hmap_world_ext empty_list se (nat_to_int N)),
      (rsw empty_list_rs_sig [] m SUP),
      (rsq (Vptr bf Ptrofs.zero) empty_list_rs_sig nil m).
    assert (FINDFUN1: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some empty_list_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite SYMB. reflexivity. }
    assert (FINDFUN2: Genv.find_funct (Genv.globalenv se linked_list_mod) (Vptr bf Ptrofs.zero) = Some (Rusttypes.Internal empty_list_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite SYMB. reflexivity. }
    rewrite FINDFUN1 in H. inv H.
    replace {| sig_args := [];
              sig_res := AST.Tlong;
              sig_cc := cc_default |} with (signature_of_rust_signature empty_list_rs_sig) by reflexivity.
    repeat apply conj.
    + econstructor.
    + unfold empty_list_rs_sig.
      simpl. red. simpl. rewrite dec_eq_true. rewrite SYMB.
      red. simpl. 
      replace (@nil Rusttypes.type) with (type_list_of_typelist Rusttypes.Tnil).
      econstructor; eauto.
      (* casted *)
      econstructor. reflexivity.
    + eapply rs_own_query_intro with (fpl := []).
      * simpl. econstructor.
      * econstructor. 
      * econstructor. 
      * simpl. 
        red; split; auto.
    + reflexivity.
    (* reply *)
    + intros ? ? A1 A2 A3.
      simpl in A1. red in A1. red in A1. simpl in A1. 
      destruct A2 as (w_rs' & ACC & A2). inv A2.
      inv A3.
      eexists. split.
      econstructor.
      intros s' AFEXT. inv AFEXT.
      inv CONT.
      inv ACC.
      (* return from empty_list *)
      inv WTFP. inv SEMWT. inv SEMWT.
      replace (Rusttypes.sizeof (rs_sig_comp_env empty_list_rs_sig) List_ty) with 32 in SEMWT by reflexivity. 
      inv SEMWT.
      eapply hmap_set_inv. eapply hmap_set_return_empty_list with (l_fp := fp_box b 32 fp0) (b_hmap := b_hmap).
      econstructor. all: eauto. 
      * reflexivity. 
      * eapply m_invar. eauto. eapply Mem.unchanged_on_implies. eapply UNC.
        simpl. intros. auto.
      * rewrite app_length in *. simpl. lia.
      * econstructor. econstructor; eauto.
        econstructor; auto. auto. auto.
      * intros. eapply SEP with (b:=b1).  intro. inv H1.
        eapply INCL. simpl. eauto. eapply m_valid; eauto.

  (** TODO: call insert in hmap_set *)
  - admit.
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal process_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      reflexivity. }
    rewrite H in FIND. inv FIND.    
  - inv CALL. 
    assert (FIND: Genv.find_funct ge (Vptr b1 Ptrofs.zero) = Some (Internal hmap_operate_on_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    rewrite H in FIND. inv FIND.
  (* call find *)
  - exists (Build_hmap_world_ext find se (nat_to_int N)),
      (rsw find_rs_sig (footprint_flat fp) m SUP),
      (rsq (Vptr bf Ptrofs.zero) find_rs_sig [v; Vint ki] m).
    assert (FINDFUN1: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some find_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite FINDSYM. reflexivity. }
    assert (FINDFUN2: Genv.find_funct (Genv.globalenv se linked_list_mod) (Vptr bf Ptrofs.zero) = Some (Rusttypes.Internal find_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite FINDSYM. reflexivity. }
    rewrite FINDFUN1 in H. inv H.
    replace {| sig_args := [AST.Tlong; AST.Tint];
              sig_res := AST.Tlong;
              sig_cc := cc_default |} with (signature_of_rust_signature find_rs_sig) by reflexivity.
    repeat apply conj.
    + econstructor.
    + unfold find_rs_sig.
      replace [List_box; Rusttypes.type_int32s] with (type_list_of_typelist (Rusttypes.Tcons List_box (Rusttypes.Tcons Rusttypes.type_int32s Rusttypes.Tnil))).
      simpl. red. simpl. rewrite dec_eq_true. rewrite FINDSYM.
      red. rewrite dec_eq_true.
      replace ([List_box; Rusttypes.type_int32s]) with (type_list_of_typelist (Rusttypes.Tcons List_box (Rusttypes.Tcons Rusttypes.type_int32s Rusttypes.Tnil))) by reflexivity.
      econstructor. eauto.
      (* casted *)
      econstructor.
      inv VSPEC. auto.
      econstructor. econstructor. auto.
      econstructor.
      eauto.
      (* pre-cond *)
      econstructor. 
      reflexivity. reflexivity. 
    + inv VSPEC.
      eapply rs_own_query_intro with (fpl := [fp; fp_scalar Rusttypes.type_int32s]).
      * simpl. rewrite app_nil_r. auto.
      * econstructor. eauto.
        econstructor. econstructor.
        econstructor.
      * econstructor. eauto.
        econstructor; econstructor. auto.
      * simpl. rewrite app_nil_r.
        red; split; auto.
    + reflexivity.
    (* reply *)
    + intros ? ? A1 A2 A3.
      simpl in A1. red in A1. red in A1. rewrite dec_eq_true in A1.
      destruct A2 as (w_rs' & ACC & A2). inv A2.
      inv A3.
      eexists. split.
      econstructor.
      intros s' AFEXT. inv AFEXT.
      inv CONT.
      inv ACC.
      eapply hmap_operate_on_return_find with (fp:= rfp).
      (* memory predicate *)
      eapply m_invar. eapply MPRED.
      eapply Mem.unchanged_on_implies. eapply UNC.
      intros. simpl. eauto.
      (** disjoint footprint *)
      intros. eapply INCL in H0.
      (* prove b0 is a valid block *)
      exploit m_valid. eapply MPRED. eapply H. intros VALID.
      (* b0 is in fp or not *)
      destruct (in_dec eq_block b0 (footprint_flat fp)).
      eapply DISJOINT; eauto. 
      eapply SEP; eauto.       
      (* spec *)
      econstructor; eauto. auto.
      econstructor; eauto.
  - inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b1 Ptrofs.zero) = Some (Internal find_bucket_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    rewrite H in FIND. inv FIND.
  (* call hash *)
  - assert (SUP: Mem.sup_include nil (Mem.support m)).
    { eapply incl_nil_l. }
    exists (Build_hmap_world_ext hash se (nat_to_int N)),
      (rsw hash_rs_sig nil m SUP),
      (rsq (Vptr b Ptrofs.zero) hash_rs_sig [Vint ki; Vint Ni] m).
    assert (FINDFUN1: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some hash_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite FINDSYM. reflexivity. }
    assert (FINDFUN2: Genv.find_funct (Genv.globalenv se linked_list_mod) (Vptr b Ptrofs.zero) = Some (Rusttypes.Internal hash_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite FINDSYM. reflexivity. }
    rewrite FINDFUN1 in H. inv H.
    replace {| sig_args := [AST.Tint; AST.Tint];
              sig_res := AST.Tint;
              sig_cc := cc_default |} with (signature_of_rust_signature hash_rs_sig) by reflexivity.
    repeat apply conj.
    + econstructor.
    + unfold hash_rs_sig.      
      simpl. red. simpl. rewrite dec_eq_true. rewrite FINDSYM.
      red. rewrite dec_eq_false; try congruence.
      2: { vm_compute. congruence. }
      rewrite dec_eq_true.
      replace [Rusttypes.type_int32s; type_int32u] with (type_list_of_typelist (Rusttypes.Tcons Rusttypes.type_int32s (Rusttypes.Tcons type_int32u Rusttypes.Tnil))) by reflexivity.
      econstructor. eauto.
      (* casted *)
      econstructor.
      econstructor. auto.
      econstructor. econstructor. auto.
      econstructor.
      eauto.
      (* pre-cond *)
      econstructor. unfold Ni. rewrite Neq10. reflexivity.
      econstructor. auto.
      econstructor. auto.
      reflexivity. 
    + eapply rs_own_query_intro with (fpl := [fp_scalar Rusttypes.type_int32s; fp_scalar type_int32u]).
      * simpl. econstructor.
      * econstructor.
        econstructor. econstructor.
        econstructor. econstructor.
      * econstructor. econstructor. auto.
        econstructor. econstructor. auto. econstructor.
      * simpl. 
        red; split; auto.
    + reflexivity.
    (* reply *)
    + intros ? ? A1 A2 A3.
      simpl in A1. red in A1. red in A1. rewrite dec_eq_false in A1.
      rewrite dec_eq_true in A1. inv A1.
      destruct A2 as (w_rs' & ACC & A2). inv A2.
      inv A3.
      eexists. split.
      econstructor.
      intros s' AFEXT. inv AFEXT.
      inv CONT.
      inv ACC.
      eapply find_bucket_return_hash.
      (* post conditions *)
      eauto. 
      (* cont *)
      econstructor. eauto. eauto.
      eapply m_invar. eauto.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. auto. auto.
      intro. inv H.
(* Qed. *)
Admitted.

(* Incoming safety interface: {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} *)
Lemma initial_preservation_progress: forall q_c,
    valid_query (hash_map_sem se) q_c = true ->
    (list_senv_ext (hmap_list_ext w)) = se ->
    query_inv (hmap_int_inv N) w q_c ->
    (* cc_rust_c_mq q_rs q_c -> *)
    (* rs_own_query rw q_rs -> *)
    (* vq_hash_map w q_rs -> *)
    exists s, initial_state ge q_c s
         /\ (forall s, initial_state ge q_c s -> sound_state s).
Proof.
  intros q_c VQ SEEQ HQ.
  simpl in HQ. red in HQ.
  destruct q_c. simpl in HQ. destruct cq_vf; try contradiction.
  destruct Ptrofs.eq_dec in HQ; try contradiction. subst.
  destruct Genv.invert_symbol eqn: SYM in HQ; try contradiction.
  red in HQ.
  (* Three cases of i *)  
  repeat destruct ident_eq in HQ; try contradiction; subst.   
  Strategy opaque [linked_list_mod].
  (* call process *)
  - simpl in HQ.
    destruct (hmap_rs_own w) eqn: RSOWN in HQ; try contradiction.
    destruct HQ as (q_rs & (QINV1 & QINV2) & QINV3).
    inv QINV3. inv QINV2.    
    red in QINV1. simpl in QINV1.
    rewrite dec_eq_true in QINV1. rewrite SYM in QINV1. red in QINV1.
    rewrite dec_eq_true in QINV1. inv QINV1.
    assert (MEQ: rw_mem = Some cq_mem).
    { unfold rw_mem, rw. rewrite RSOWN. auto. }
    assert (RWFPEQ: rw_fp = Some fp).
    { unfold rw_fp, rw. rewrite RSOWN. auto. }
    unfold signature_of_rust_signature. simpl.
    assert (RWSGEQ: rw_sg = Some process_sig).
    { unfold rw_sg, rw. rewrite RSOWN. auto. }    
    (* assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal process_func)). *)
    (* { simpl. destruct Ptrofs.eq_dec; try congruence. *)
    (*   eapply Genv.find_funct_ptr_iff. *)
    (*   rewrite Genv.find_def_spec. *)
    (*   rewrite <- SEEQ. *)
    (*   rewrite SYM. *)
    (*   reflexivity. } *)
    (* generalize FIND. intros FIND1. *)
    (* simpl in FIND. rewrite dec_eq_true in FIND. *)
    rewrite SEEQ in FINDF.
    eexists. split.
    + replace {| sig_args := [Tptr]; sig_res := Tptr; sig_cc := cc_default |} with (signature_of_type (to_ctypelist (Rusttypes.Tcons (Tbox Rusttypes.type_int32s) Rusttypes.Tnil)) (to_ctype (Tbox Rusttypes.type_int32s)) cc_default).
      (* inv TYF. *)
      econstructor; eauto.
      eapply RustOp.val_casted_list_to_ctype. eauto.
      reflexivity.
    + intros. inv H.
      unfold ge in H7. setoid_rewrite FINDF in H7. inv H7.
      inv WTFP. inv H5.
      inv SEMWT. inv H6. inv H3; simpl in *; try congruence.
      inv H4.
      inv H4.
      inv WT. inv WTLOC.
      inv WTLOC.
      inv WT. inv MODE.
      eapply hmap_call_process; eauto.
      rewrite <- SEEQ. eauto.
      econstructor. econstructor. reflexivity. eauto.
      econstructor. eauto. eauto. auto.
  (* call hmap_process *)
  - inv HQ.
    rewrite SEEQ in *.
    eexists. split.
    + econstructor; eauto.
    + intros. inv H.
      eapply hmap_operate_on_callstate; eauto.
      econstructor; eauto. econstructor. auto. auto.
  (* call main function *)
  - simpl in HQ. destruct HQ as (A1 & A2 & A3). subst.
    exploit Genv.find_def_spec. erewrite SYM. instantiate (1 := hash_map_prog).
    intros FINDF. rewrite SEEQ in *.
    eexists. split.
    + replace signature_main with (signature_of_type Tnil tint cc_default) by reflexivity.
      econstructor. simpl. rewrite dec_eq_true. eapply Genv.find_funct_ptr_iff.
      instantiate (1 := main_func). eauto. reflexivity.
      econstructor.
    + intros s INIT. inv INIT.
      eapply hmap_init_inv.
      eapply hmap_call_main. auto. auto.
Qed.

Lemma final_progress: forall s r,
    sound_state s ->
    final_state s r ->
    reply_inv (hmap_int_inv N) w r.
Proof.
  intros. inv H0. inv H; try inv SINV_INIT; try inv SINV_SET; try (simpl in NOTCALLRET; contradiction).
  (* return from main *)
  + simpl. red. red. rewrite FUNID.
    reflexivity.
  (* return from init_hmap: impossible *)
  + inv CONT.
  (* return from hmap_set: impossible *)
  + inv CONT.
  (* return from process *)
  + simpl. red. red.
    rewrite FUNID. rewrite dec_eq_true. 
    unfold rw_mem, rw_fp, rw_sg in *. unfold rw in *.
    destruct (hmap_rs_own w) eqn: RSOWN; try congruence.
    exists (rsr (Vptr b Ptrofs.zero) m).
    repeat apply conj.
    * simpl. red. red. rewrite FUNID. rewrite dec_eq_true. auto.
    * destruct r. inv RWMEM. inv RWFP. inv SGEQ.
      assert (SUP: Mem.sup_include rwfp (Mem.support m)).
      { eapply Mem.sup_include_trans. eapply Hm0.
        eapply Mem.unchanged_on_support. eapply MPRED. }
      exists (rsw process_sig rwfp m SUP). split.
      -- econstructor.
         eapply Mem.unchanged_on_implies. eapply MPRED.
         intros. simpl. intro. eapply H. eapply FPEQ. eauto.
         eapply flat_footprint_separated_refl.
      -- eapply rs_own_reply_intro with (rfp:= fp); eauto.
         red. intros. eapply FPEQ. eauto.
    * simpl. econstructor.
  + inv CONT.
  (** How to prevent returning from hmap_operate_on  *)
  (* return from hmap_process *)
  + simpl. red. red. inv CONT.
    rewrite FUNID. rewrite dec_eq_false. rewrite dec_eq_true.
    econstructor; eauto.
    intro. inv H.    
  + inv CONT.
  (* return from find_bucket: impossible *)
  + inv CONT; inv CONT0.
Qed.


Lemma extcall_malloc_sem_inv: forall se vptr_sz m t vres m',
    extcall_malloc_sem se [vptr_sz] m t vres m' ->
    exists m0 b sz,
      vptr_sz = Vptrofs sz
      /\ Mem.alloc m (-size_chunk Mptr) (Ptrofs.unsigned sz) = (m0, b)
      /\ Mem.store Mptr m0 b (- size_chunk Mptr) (Vptrofs sz) = Some m'
      /\ vres = Vptr b Ptrofs.zero.
Proof.
  intros. inv H.
  do 3 eexists. repeat apply conj; eauto.
Qed.

Lemma add_one_lt: forall idx sz,
    Int.unsigned idx < Int.max_unsigned ->
    Int.ltu idx sz = true ->
    Int.ltu (Int.add idx Int.one) sz = false ->
    Int.eq (Int.add idx Int.one) sz = true.
Proof.                       
  intros idx sz RAN LT1 LT2.  
  eapply negb_true_iff in LT2.
  unfold Int.ltu in LT2. destruct zlt in LT2; simpl in LT2; try congruence.
  eapply Int.ltu_inv in LT1.
  unfold Int.eq, Int.add in *.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr in g.
  rewrite Int.unsigned_one in *.
  eapply Z.ge_le in g. apply Z.le_lteq in g.
  destruct g. lia. rewrite H. rewrite zeq_true. auto.
  rewrite Int.unsigned_one. lia.
  rewrite Int.unsigned_one. lia.
Qed.


(* progress and invariant preservation in hmap_set *)

Lemma step_hmap_set_preservation_progress: forall s,
    sound_state_set s ->
    (not_stuck (hash_map_sem se) s
    /\ (forall s' t, step1 ge s t s' ->
               sound_state s')).
Proof.
  intros s INV. inv INV.
  (* call hmap_set *)
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal hmap_set_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      auto. }
    generalize (function_entry_hmap_set m b_hmap kv b_v _ _ BVSPEC MPRED DISJOINT). intros (sb_hmap & sb_kv & sb_bv & m1 & (ENTRY & MPRED1)).
    split.
    + red. do 2 right.
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply hmap_set_inv.
      eapply hmap_set_internal1. 
      econstructor. eauto. reflexivity. simpl. auto.
      eauto. lia.

  (* step to call find_bucket *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_set_inv. eapply hmap_set_internal1 with (n:=1%nat).
        eapply starNf_step_right; eauto. 
        1,4: inv H; simpl; auto. eauto. reflexivity. eauto. lia. }
    inv STEP.
    2-3: destruct H7; inv H.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    2: lia.
    generalize ((proj1 wf_senv) find_bucket). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some (Internal find_bucket_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    assert (EVALF: eval_expr (Smallstep.globalenv (hash_map_sem se))
                     (PTree.set val (sb_v, val_ty)
                        (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val))) m
                     (Evar find_bucket find_bucket_ty) (Vptr b Ptrofs.zero)).
    { econstructor. eapply eval_Evar_global. reflexivity. eauto.
      eapply deref_loc_reference. reflexivity. }
    exploit load_rule. eapply sep_proj1. eapply MPRED. 
    intros (v1 & LOAD1 & SPEC1). subst.
    exploit load_rule. eapply sep_proj1. eapply sep_proj2. eapply MPRED.
    intros (v2 & LOAD2 & SPEC2). subst.    
    assert (EVALARGS: eval_exprlist (Smallstep.globalenv (hash_map_sem se))
                        (PTree.set val (sb_v, val_ty)
                           (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
                        (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val))) m
                        [Evar hmap hmap_ty; Evar key tint] (Tcons hmap_ty (Tcons tint Tnil)) 
                        [Vptr b_hmap Ptrofs.zero; Vint kv]).
    { econstructor. econstructor. eapply eval_Evar_local. reflexivity. 
      econstructor. reflexivity. eauto. reflexivity.
      econstructor. econstructor. econstructor. reflexivity. 
      econstructor. reflexivity. eauto. reflexivity.
      econstructor. }
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. eauto. 
      + intros. inv H.
        exploit eval_expr_det. eapply EVALF. eauto. intros A. subst.
        unfold ge in H13. setoid_rewrite FINDFUN in H13. inv H13.
        inv H14. 
        exploit eval_exprlist_det. eapply EVALARGS. unfold ge in H12. 
        simpl. eapply H12. intros A. inv A.
        eapply find_bucket_callstate. econstructor; eauto.
        eapply Genv.find_invert_symbol. eauto.
        eapply call_find_bucket_cont_intro2. econstructor. reflexivity.
        reflexivity. eauto. rewrite <- !sep_assoc, sep_comm, -> !sep_assoc in MPRED.
        eauto. }
  (* evaluate conditional checking of NULL *)
  - generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    { rewrite Ptrofs.unsigned_repr. auto.
      rewrite Nzeq in *. rewrite maxv. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros R.
      destruct Archi.ptr64; lia. } 
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_set_inv. eapply hmap_set_internal2 with (n:=1%nat).
        eapply starNf_step_right; eauto. 
        1,5: inv H; simpl; auto. eauto. reflexivity. eauto. eauto. auto. 
        auto. lia. }
    inv STEP.
    2: inv H6.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_set_inv. eapply hmap_set_internal2 with (n:=2%nat).
        eapply starNf_step_right; eauto. 
        1,5: inv H; simpl; auto. eauto. reflexivity. eauto. eauto. auto. 
        auto. lia. }
    inv STEP.
    2-3: destruct H7; inv H. 
    (* load *buk from memory *)
    exploit (load_rule (bucket_val_pred m fp)). eapply MPRED.
    intros (v1 & LOAD1 & SPEC1).  unfold bucket_val_pred in SPEC1.
    (* load key from memory *)
    exploit (load_rule (eq (Vint kv))). eapply MPRED.
    intros (v2 & LOAD2 & SPEC2). subst. 
    (* evaluate the conditional expression *)
    assert (EVALB: eval_expr (Smallstep.globalenv (hash_map_sem se))
    (PTree.set val (sb_v, val_ty)
       (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
    (PTree.set buk (Vptr b_hmap (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
       (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
    (Ebinop Oeq (Ederef (Etempvar buk List_box_ptr) List_ptr)
       (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint) 
                     (Val.of_bool (if Val.eq v1 Vnullptr then true else false))).
    { econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. reflexivity. simpl. rewrite OFSEQ. eauto.
      econstructor. econstructor. reflexivity.
      simpl. unfold sem_cmp, cmp_ptr. simpl.
      (* we should show that the pointer (if not NULL) is a valid pointer *)
      destruct Val.eq in SPEC1. subst.
      reflexivity.
      inv SPEC1. inv WTFP. inv WTVAL. simpl in WF. congruence.
      replace (Rusttypes.sizeof ll_ce List_ty) with 32 in WTVAL by reflexivity.
      inv WTVAL.
      simpl. rewrite Int64.eq_true. simpl.
      setoid_rewrite (proj2 (Mem.valid_pointer_nonempty_perm m b 0)).
      reflexivity.
      eapply Mem.perm_implies. eapply VALID. rewrite size_chunk_Mptr.
      destruct Archi.ptr64; lia. econstructor. }
    assert (BVAL: bool_val (Val.of_bool (if Val.eq v1 Vnullptr then true else false)) tint m = Some (if Val.eq v1 Vnullptr then true else false)).
    { destruct Val.eq; reflexivity. }    
    inv STAR1; cbn [num_frames num_frames_cont] in *.    
    (* evaluate Sifthenelse *)
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        (* evaluate (buk == NULL) *)
        eauto. eauto.
      - intros. eapply hmap_set_inv. eapply hmap_set_internal2 with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    exploit eval_expr_det. eapply H9. eapply EVALB.
    intros. subst. setoid_rewrite BVAL in H10. inv H10. clear H9.
    destruct Val.eq.
    (* evaluate the true branch (i.e., buk == NULL) until calling empty_list *)
    { inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate to call empty_list *)
      generalize ((proj1 wf_senv) empty_list). intros FINDF.
      exploit FINDF. reflexivity. clear FINDF.
      intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
      assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some empty_list_ext).
      { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
        rewrite Genv.find_def_spec.
        erewrite Genv.find_invert_symbol; eauto.
        reflexivity. }    
      assert (EVALF: eval_expr (Smallstep.globalenv (hash_map_sem se))
                       (PTree.set val (sb_v, val_ty)
                          (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
                       (PTree.set buk (Vptr b_hmap (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
                          (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
                       (Evar empty_list empty_list_ty) (Vptr b Ptrofs.zero)).
      { econstructor. eapply eval_Evar_global. reflexivity. eauto.
        eapply deref_loc_reference. reflexivity. }
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor.
          reflexivity. eauto. econstructor. eauto. reflexivity.
        - intros. inv H.
          exploit eval_expr_det. eapply H11. eapply EVALF. intros A. subst.
          unfold ge in H13. setoid_rewrite FINDFUN in H13. inv H13. inv H14. inv H12.
          eapply hmap_set_inv. eapply hmap_set_call_empty_list; eauto.
          eapply Genv.find_invert_symbol. auto.
          reflexivity. 
          (* memory predicate *)
          rewrite sep_swap3, sep_swap23 in MPRED. eapply sep_imp.
          eapply MPRED. 2: eauto.
          { red. split. 
            - simpl. intros m1 ((A1 & A2 & (v & A3 & A4)) & A5). 
              split; auto. split; eauto.
            - simpl. intros b1 ofs1 (A1 & A2). auto. }
          rewrite app_length in FPLEN. simpl in FPLEN.
          rewrite app_length. lia. }
      inv STEP. simpl in FEQ2. lia. }
    (* evaluate false branch *)
    { assert (EVALE: eval_expr (Smallstep.globalenv (hash_map_sem se))
                       (PTree.set val (sb_v, val_ty)
                          (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
                       (PTree.set buk (Vptr b_hmap (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
                          (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
                       (Ederef (Etempvar buk List_box_ptr) List_ptr) v1).
      { econstructor. econstructor. econstructor. reflexivity. econstructor.
        reflexivity. simpl. rewrite OFSEQ. auto. }     
      rewrite sep_swap3, sep_swap23 in MPRED. 
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sset *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor. eauto.
        - intros. 
          exploit bucket_val_spec_inv. eauto. intros (b1 & A). subst.
          inv H.
          exploit eval_expr_det. eapply H9. unfold ge. eapply EVALE. intros A. subst.
          eapply hmap_set_inv. eapply hmap_set_internal3 with (n:=0%nat); eauto.
          econstructor. reflexivity. reflexivity.          
          eapply sep_imp. eapply MPRED.
          2: reflexivity.
          { red. split. 
            - simpl. intros m1 ((A11 & A12 & (v & (A13 & A14))) & A2).
              split; auto.
              split; eauto.
            - simpl. intros b ofs (A1 & A2). auto. }
          rewrite app_length in *. simpl in FPLEN. lia.
          { intros. destruct H. 
            - simpl in H. destruct H. subst. 
              eapply sep_proj1 in MPRED. eapply MPRED. auto.
            - eapply MPRED. simpl. eauto. eauto. }
          intro. eapply sep_proj1 in MPRED. eapply MPRED. auto. }
      lia. }
  (* call empty_list *)
  - assert (FINDFUN: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some empty_list_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite SYMB. reflexivity. }
    split.
    + red. right. left.
      eexists. econstructor. eauto.
    + intros. inv H. rewrite FINDFUN in FIND. inv FIND. 
      rewrite FINDFUN in FIND. inv FIND. inv H6.
  (* return from empty_list *)
  - split.
    + red. do 2 right.
      do 2 eexists. econstructor. 
    + intros. inv H.
      eapply hmap_set_inv. eapply hmap_set_internal3 with (n:=0%nat); eauto.
      econstructor. reflexivity. reflexivity.
      rewrite app_length in *. simpl in FPLEN. lia.
      intro. eapply (DISJOINT b_hmap (size_chunk Mptr * Int.unsigned idx)); eauto. 
      simpl. left. split; eauto. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros. destruct Archi.ptr64; lia.
      simpl. auto.
  (* before calling insert *)
  - generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    { rewrite Ptrofs.unsigned_repr. auto.
      rewrite Nzeq in *. rewrite maxv. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros R.
      destruct Archi.ptr64; lia. } 
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_set_inv. eapply hmap_set_internal3 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    2: inv H6.
    (* evaluate Ssequence *)
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_set_inv. eapply hmap_set_internal3 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }    
    inv STEP.
    2-3:  destruct H7 as [A|A]; inv A.
    (* evaluate Scall (insert) *)
    generalize ((proj1 wf_senv) insert). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some insert_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }
    assert (EVALF: eval_expr (Smallstep.globalenv (hash_map_sem se))
                     (PTree.set val (sb_v, val_ty)
                        (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env))) le m
                     (Evar insert insert_ty) (Vptr b Ptrofs.zero)).
    { econstructor. eapply eval_Evar_global. reflexivity. eauto.
      eapply deref_loc_reference. reflexivity. }    
    exploit (load_rule (eq (Vint kv))). eapply MPRED. 
    intros (v1 & LOAD1 & SPEC1). subst.
    (* extract b_v from MPRED *)
    rewrite <- !sep_assoc in MPRED.
    set (MP := (((((contains Mptr b_hmap (size_chunk Mptr * Int.unsigned idx)
                    (fun _ : Values.val => True) **
                  contains_neg Mptr b_hmap (- size_chunk Mptr)
                    (eq (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr))))) **
                 hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0) **
                hmap_pred_rec (N - 1 - int_to_nat idx) fpl2 b_hmap
                  (size_chunk Mptr * Int.unsigned idx + size_chunk Mptr)) **
               contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero))) **
              contains Mint32 sb_key 0 (eq (Vint kv)))) in *.
    assert (MPRED1: m |= MP ** contains Mptr sb_v 0 (process_val_spec m v_fp)).
    { do 2 red in MPRED. destruct MPRED as (A1 & A2 & A3).
      do 2 red. split. eapply A1. split. 
      eapply contains_imp; eauto. eapply A2.
      (* footprint disjoint *)
      red. intros. eapply A3; eauto. simpl in H0. simpl. destruct H0. left; auto. }
    exploit load_rule. 
    eapply sep_proj2 with (P:= MP). eauto.
    intros (v2 & LOAD2 & SPEC2). exploit process_val_spec_inv. eauto.
    intros (b_v & A). subst.
    assert (EVALARGS: eval_exprlist (Smallstep.globalenv (hash_map_sem se))
                        (PTree.set val (sb_v, val_ty)
                           (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env))) le m
                        [Etempvar tmp List_ptr; Evar key tint; Evar val val_ty]
                        (Tcons List_ptr (Tcons tint (Tcons val_ty Tnil)))
                        [Vptr b_l Ptrofs.zero; Vint kv; Vptr b_v Ptrofs.zero]).
    { econstructor. econstructor. eauto.  reflexivity. 
      econstructor. econstructor. eapply eval_Evar_local. reflexivity. 
      econstructor. reflexivity. eauto. reflexivity.
      econstructor. econstructor. econstructor. reflexivity. 
      econstructor. reflexivity. eauto. reflexivity.
      econstructor. } 
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    2: { inv STEP. simpl in FEQ1. lia. }
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. reflexivity.
      + intros. inv H.
        exploit eval_expr_det. eapply EVALF. eauto. intros A. subst.
        unfold ge in H13. setoid_rewrite FINDFUN in H13. inv H13.
        inv H14. 
        exploit eval_exprlist_det. eapply EVALARGS. unfold ge in H12. 
        simpl. eapply H12. intros A. inv A.
        eapply hmap_set_inv. eapply hmap_set_call_insert; eauto.
        eapply Genv.find_invert_symbol; auto.
        rewrite <- !sep_assoc. eapply sep_imp; eauto. 
        eapply contains_imp. auto.
        (* disjoint footprint *)
        { intros b1 ofs1 A1 A2. 
          destruct A2.          
          - eapply DISJOINT; eauto. instantiate (1 := ofs1).
            simpl. rewrite <- !or_assoc. 
            simpl in A1. rewrite <- !or_assoc in A1. destruct A1.
            + left. eauto.
            + left. right. destruct H0. auto.
          - eapply MPRED; eauto. 
            2: { simpl. eauto. }            
            instantiate (1 := ofs1).
            simpl. simpl in A1. rewrite <- !or_assoc in A1. destruct A1; auto.
            destruct H0. subst.            
            exfalso. destruct MPRED as (A1 & A2 & A3). eapply A2. auto. }
        (* norepet (l_fp ++ v_fp) *)
        { eapply list_norepet_app. repeat apply conj.
          - inv RETV_SPEC. eauto.
          - inv SPEC2. auto.
          - red. intros. intro. subst. eapply DISJOINT; eauto.
            instantiate (1 := 0). simpl. rewrite <- !or_assoc. right. auto. } }
  (* call insert state *)
  -  assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr bf Ptrofs.zero) = Some insert_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite SYMB. reflexivity. }
    split.
    + red. right. left. eexists.
      econstructor; eauto.
    + intros. inv H.
      unfold ge in FIND. setoid_rewrite FINDFUN in FIND. inv FIND.
      unfold ge in FIND. setoid_rewrite FINDFUN in FIND. inv FIND. inv H6.
  (* return insert state *)
  - split.
    + red. do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H.
      eapply hmap_set_inv. eapply hmap_set_internal4 with (n:=0%nat).      
      econstructor.  eauto. reflexivity.
      simpl. rewrite PTree.gso. eauto. vm_compute. congruence.
      simpl. rewrite PTree.gss. eauto. reflexivity.
      all: eauto. 
      simpl. auto.
  (* Before returning from hmap_set *)
  - assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    { rewrite Ptrofs.unsigned_repr. auto.
      rewrite Nzeq in *. rewrite maxv. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros R.
      destruct Archi.ptr64; lia. } 
    generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. inv H.
        2: inv H7. 
        eapply hmap_set_inv. eapply hmap_set_internal4 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. econstructor. }
    inv STEP. 2: inv H6.
    assert (EVALL: eval_lvalue (Smallstep.globalenv (hash_map_sem se))
                     (PTree.set val (sb_v, val_ty)
                        (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env))) le m
                     (Ederef (Etempvar buk List_box_ptr) List_ptr) b_hmap (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) Full).
    { econstructor. econstructor. eauto. }
    assert (EVALE: eval_expr (Smallstep.globalenv (hash_map_sem se))
                     (PTree.set val (sb_v, val_ty)
                        (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env))) le m 
                     (Etempvar tmp List_ptr) (Vptr b_l Ptrofs.zero)).
    { econstructor. auto. }
    exploit store_rule. eapply MPRED.
    instantiate (1 := Vptr b_l Ptrofs.zero). instantiate (1 := eq (Vptr b_l Ptrofs.zero)).
    eauto. intros (m2 & STORE1 & MPRED2).    
    assert (STEP_DET: forall s' t1, step1 ge (State hmap_set_func (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k
              (PTree.set val (sb_v, val_ty)
                 (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
              le m) t1 s' -> s' = State hmap_set_func Sskip k
              (PTree.set val (sb_v, val_ty)
                 (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))
              le m2).
    { intros. inv H.
      2-3: destruct H8; try congruence. 
      exploit eval_lvalue_det. eapply H9. eapply EVALL. intros (A1 & A2). inv A1.
      exploit eval_expr_det. eapply H10. eapply EVALE. intros A. inv A.
      inv H12; inv H.
      simpl in H0. rewrite OFSEQ in H0. inv H11. setoid_rewrite STORE1 in H0. inv H0.
      reflexivity. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign *)
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. econstructor. reflexivity. simpl. rewrite OFSEQ. eauto.
      - intros. generalize H as A. intros. 
        specialize (STEP_DET s' t A). subst.
        eapply hmap_set_inv. eapply hmap_set_internal4 with (n:=2%nat).
        eapply starNf_step_right; eauto.         
        all: eauto. }
    inv STAR1.
    2: lia.
    specialize (STEP_DET s t1 STEP). subst.
    (* We first combine l_fp into memory predicate and then free blocks *)
    exploit bucket_val_spec_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto. intros SPEC1.
    set (MP := contains_neg Mptr b_hmap (- size_chunk Mptr)
                (eq (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) **
              hmap_pred_rec (int_to_nat idx) fpl1 b_hmap 0 **
              hmap_pred_rec (N - 1 - int_to_nat idx) fpl2 b_hmap
                (size_chunk Mptr * Int.unsigned idx + size_chunk Mptr) **
              contains Mptr sb_hmap 0 (eq (Vptr b_hmap Ptrofs.zero)) **
              contains Mint32 sb_key 0 (eq (Vint kv)) **
              contains Mptr sb_v 0 (eq (Vptr b_v Ptrofs.zero))) in *.
    assert (MPRED3: m2 |= bucket_pred b_hmap (size_chunk Mptr * Int.unsigned idx) l_fp ** MP).
    { do 2 red. 
      generalize MPRED2 as MPRED2'. intros.
      do 2 red in MPRED2. destruct MPRED2 as (A1 & A2 & A3).
      split. 
      + simpl. simpl in A1.
        destruct A1 as (B1 & B2 & (v & B3 & B4)). subst.
        split; auto. split; auto. split; eauto.
      + split; auto.
        (* footprint disjoint *)
        red. intros. destruct H. 
        * eapply MPRED2'; eauto. simpl. intuition.
        * eapply DISJOINT. do 2 red. eauto. auto. }
    unfold MP in *.    
    (* freelist *)
    do 3 rewrite <- sep_assoc in MPRED3.    
    rewrite sep_swap12, sep_swap23 in MPRED3.
    exploit free_rule. eapply sep_comm. 
    rewrite <- !sep_assoc in MPRED3. eapply MPRED3.
    intros (m3 & FREE1 & MP1).
    rewrite !sep_assoc in MP1.
    exploit free_rule. eapply MP1.
    intros (m4 & FREE2 & MP2).
    exploit free_rule. eapply MP2.
    intros (m5 & FREE3 & MP3).
    simpl in FREE1, FREE2, FREE3.
    inv CONT.
    assert (FREELIST: Mem.free_list m2
                        (blocks_of_env (Smallstep.globalenv (hash_map_sem se))
                           (PTree.set val (sb_v, val_ty)
                              (PTree.set key (sb_key, tint) (PTree.set hmap (sb_hmap, hmap_ty) empty_env)))) = Some m5).
    { simpl. setoid_rewrite FREE1. setoid_rewrite FREE2. 
      setoid_rewrite FREE3. reflexivity. }
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor; eauto. 
      - intros. inv H. setoid_rewrite FREELIST in H8. inv H8.
        eapply hmap_set_inv. eapply hmap_set_returnstate; eauto.
        econstructor; auto.
        eauto. 
        (* hmap_pred *)
        instantiate (1 := fpl1 ++ l_fp :: fpl2).
        rewrite sep_swap12, sep_swap23 in MP3. 
        unfold hmap_pred, HashMapCommon.hmap_pred.
        eapply sep_imp. eapply MP3. reflexivity.       
        etransitivity. 
        2: { eapply hmap_pred_rec_split with (k:=(int_to_nat idx)); eauto. 
             unfold int_to_nat. lia.
             rewrite !app_length in *. simpl. lia. }
      exploit (hmap_pred_rec_fpl_length (int_to_nat idx) fpl1). eapply MPRED2.
      intros L1. rewrite <- L1 in *.
      rewrite firstn_app_3.
      rewrite <- (Nat.add_0_r (length fpl1)). 
      rewrite app_nth2_plus. cbn [nth]. rewrite Z.add_0_l.
      rewrite skipn_app. rewrite skipn_all2; try lia.
      replace ((S (length fpl1 + 0) - length fpl1))%nat with 1%nat by lia.
      cbn [skipn]. rewrite !app_nil_l. rewrite !Nat.add_0_r.
      replace (Z.of_nat (length fpl1)) with (Int.unsigned idx).
      reflexivity.
      rewrite L1. unfold int_to_nat. rewrite Z2Nat.id. reflexivity.
      eapply Int.unsigned_range. }    
  (* returnstate of hmap_set *)
  - split.
    + red. inv CONT. do 2 right.
      do 2 eexists. econstructor; eauto.
    + intros. inv H. inv CONT.
      eapply hmap_init_inv.
      eapply hmap_main_before_hmap_process with (n:=0%nat); eauto.
      econstructor. simpl. auto.
Qed.             

Lemma step_hmap_init_preservation_progress: forall s,
    sound_state_init s ->
    (not_stuck (hash_map_sem se) s
    /\ (forall s' t, step1 ge s t s' ->
               sound_state s')).
  intros s INV. inv INV.
  (* call main *)
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal main_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      auto. }
    generalize (function_entry_main m). intros ENTRY.
    split.
    + red. do 2 right.
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply hmap_init_inv.
      eapply hmap_main_internal1.
      econstructor. reflexivity. auto. lia.
  (* Internal steps of main: before calling init_hmap *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_init_inv. eapply hmap_main_internal1 with (n:=1%nat).
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. eauto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    generalize ((proj1 wf_senv) init_hmap). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some (Internal init_hmap_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    (* evaluate Scall *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity.
        econstructor. eapply eval_Evar_global. reflexivity.
        eauto. eapply deref_loc_reference. reflexivity.
        econstructor. reflexivity.
      + intros. inv H.
        inv H10. inv H12. inv H11. inv H. inv H6.
        inv H0; inv H.
        eapply hmap_init_inv.
        eapply hmap_call_init_hmap.
        econstructor. auto. reflexivity. reflexivity.
        eapply Genv.find_invert_symbol. auto. }
    lia.
  (* main: after returning from init_hmap *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_internal2 with (n:=1%nat).
        eapply starNf_step_right; eauto. 
        1, 5: inv H; simpl; auto. all: eauto. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluete Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_internal2 with (n:=2%nat).
        eapply starNf_step_right; eauto. 
        1, 5: inv H; simpl; auto. all: eauto. }
    inv STEP.
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluete Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_internal2 with (n:=3%nat).
        eapply starNf_step_right; eauto. 
        1, 5: inv H; simpl; auto. all: eauto. }
    inv STEP.
    (* find malloc symbol and malloc function *)
    generalize ((proj1 wf_senv) malloc). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (bf & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr bf Ptrofs.zero) = Some Clightgen.malloc_decl).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    assert (EVALE: eval_expr (Smallstep.globalenv (hash_map_sem se)) empty_env le m 
                     (Evar malloc malloc_ty) (Vptr bf Ptrofs.zero)).
    { econstructor. eapply eval_Evar_global. reflexivity. eauto.
      eapply deref_loc_reference. reflexivity. }
    assert (EVALARGS: eval_exprlist (Smallstep.globalenv (hash_map_sem se)) empty_env le m [
                          Esizeof tint tlong] (Tcons Ctyping.size_t Tnil) [Vlong (Int64.repr 4)]).
    {  econstructor. econstructor. reflexivity. econstructor. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Scall *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. reflexivity.       
      + intros. inv H.
        inv H10. exploit eval_expr_det. eauto. eapply EVALE. intros A. inv A.
        simpl in H13. setoid_rewrite FINDFUN in H13. inv H13.
        inv H14.
        exploit eval_exprlist_det. eauto. eapply EVALARGS. intros A. inv A.
        eapply hmap_init_inv. eapply hmap_main_insert_call_malloc; eauto. }
    lia.
  (* execution of malloc before insertion *)
  - destruct (Mem.alloc m (- size_chunk Mptr) 4) as [m1 b] eqn: ALLOC.
    destruct (Mem.valid_access_store m1 Mptr b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr 4))) as [m2].
    { eapply Mem.valid_access_implies.
      eapply Mem.valid_access_alloc_same. eauto. lia. lia.
      eapply Z.divide_opp_r. rewrite align_chunk_Mptr. rewrite size_chunk_Mptr.
      eapply Z.divide_refl. constructor. }
    (* As alloc_rule does not support negative position, we prove it manually *)
    eapply m_invar in MPRED as MPRED'. 
    2: { eapply Mem.unchanged_on_trans. eapply Mem.alloc_unchanged_on. eauto.
         eapply Mem.store_unchanged_on. eauto. intros. simpl. intro.
         eapply Mem.fresh_block_alloc. eauto. eapply m_valid. eapply MPRED.
         simpl. eauto. }    
    assert (MPRED1: m2 |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr 4))) ** range b 0 4).
    { simpl. repeat apply conj.
      - red. intros. eapply Mem.perm_store_1. eauto.
        eapply Mem.perm_alloc_2. eauto. lia.
      - eapply Z.divide_opp_r. rewrite align_chunk_Mptr. rewrite size_chunk_Mptr.
        eapply Z.divide_refl.
      - eexists. split; eauto.
        erewrite Mem.load_store_same; eauto.
        reflexivity.
      - lia.
      - rewrite ptr_modulus. lia.
      - intros. eapply Mem.perm_store_1. eauto.
        eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto.
        rewrite size_chunk_Mptr. destruct Archi.ptr64; lia.
        constructor.
      - red. simpl. intros. destruct H. destruct H0. subst. lia. }
    assert (MPRED2: m2 |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr 4))) ** range b 0 4 ** hmap_pred b_hmap fpl).
    { rewrite <- sep_assoc. do 2 red. split; eauto. split; auto.
      red. intros. simpl in H. destruct H.
      - destruct H; subst. 
        eapply Mem.fresh_block_alloc. eauto.
        eapply m_valid. eapply MPRED. eauto.
      - destruct H; subst.
        eapply Mem.fresh_block_alloc. eauto.
        eapply m_valid. eapply MPRED. eauto. }    
    split.
    + red. do 2 right.
      do 2 eexists. eapply step_external_function; eauto.
      simpl.
      change (Vlong (Int64.repr 4)) with (Vptrofs (Ptrofs.repr 4)).
      econstructor. eauto. eauto.
    + intros. inv H. setoid_rewrite FINDF in FIND. inv FIND.
      setoid_rewrite FINDF in FIND. inv FIND.
      eapply extcall_malloc_sem_inv in H6 as (m1' & b1 & sz1 & A1 & A2 & A3 & A4).
      change (Vlong (Int64.repr 4)) with (Vptrofs (Ptrofs.repr 4)) in *.
      eapply Rustlightown.Vptrofs_det in A1. subst.
      rewrite Ptrofs.unsigned_repr in *.
      rewrite ALLOC in A2. inv A2.
      rewrite e in A3. inv A3.
      eapply hmap_init_inv. eapply hmap_main_insert_return_malloc; eauto.
      (* disjoint footprint *)
      intros. intro. eapply Mem.fresh_block_alloc. eauto.
      eapply m_valid; eauto.
      rewrite maxv. lia.
  (* return from malloc before insertion *)
  - split.
    + red. do 2 right.
      do 2 eexists. econstructor.
    + intros. inv H.
      eapply hmap_init_inv. eapply hmap_main_insert_assign_val with (n:=0%nat).
      6: econstructor.
      simpl. rewrite PTree.gso; eauto. congruence.
      simpl. rewrite PTree.gss; eauto. 
      all: eauto. simpl. auto. lia.
  (* assign val before insertion  *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_insert_assign_val with (n:=1%nat).
        6: eapply starNf_step_right; eauto. 
        6, 7: inv H; simpl; auto. all: eauto. lia. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_insert_assign_val with (n:=2%nat).
        6: eapply starNf_step_right; eauto. 
        6, 7: inv H; simpl; auto. all: eauto. lia. }
    inv STEP.
    assert (EVALL: eval_lvalue (Smallstep.globalenv (hash_map_sem se)) empty_env le m
                     (Ederef (Etempvar val val_ty) tint) b_v Ptrofs.zero Full).
    { econstructor. econstructor. eauto. }
    assert (EVALE: eval_expr (Smallstep.globalenv (hash_map_sem se)) empty_env le m
                 (Econst_int (Int.repr 23) tint) (Vint (Int.repr 23))).
    { econstructor. }
    eapply sep_swap12 in MPRED as MPRED1.
    exploit storev_rule. eapply range_contains with (ofs:= 0) (chunk:= Mint32). 
    eapply MPRED1. eapply Z.divide_0_r.
    instantiate (1 := Vint (Int.repr 23)). instantiate (1 := eq (Vint (Int.repr 23))). 
    reflexivity.
    intros (m1 & STORE1 & MPRED2). rewrite sep_swap12 in MPRED2.
    assert (ASS: assign_loc (Smallstep.globalenv (hash_map_sem se))
                   (typeof (Ederef (Etempvar val val_ty) tint)) m b_v Ptrofs.zero Full
                   (Vint (cast_int_int I32 Signed (Int.repr 23))) m1).
    { econstructor. reflexivity. eauto. }
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. 
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_insert_assign_val with (n:=3%nat).
        6: eapply starNf_step_right; eauto. 
        6, 7: inv H; simpl; auto. all: eauto. lia. }
    inv STEP.
    exploit eval_lvalue_det. eauto. eapply EVALL. intros (A1 & A2). inv A1.
    exploit eval_expr_det. eauto. eapply EVALE. intros A. inv A. inv H10.
    exploit assign_loc_det. eauto. eapply ASS. intros A. inv A.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_insert_assign_val with (n:=4%nat).
        6: eapply starNf_step_right; eauto. 
        6, 7: inv H; simpl; auto. all: eauto. lia. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    (* call hmap_set *)
    generalize ((proj1 wf_senv) hmap_set). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some (Internal hmap_set_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    assert (EVALF: eval_expr (Smallstep.globalenv (hash_map_sem se)) empty_env le m1
                     (Evar hmap_set hmap_set_ty) (Vptr b Ptrofs.zero)).
    { econstructor. eapply eval_Evar_global; eauto.
      eapply deref_loc_reference. reflexivity. }
    assert (EVALARGS: eval_exprlist (Smallstep.globalenv (hash_map_sem se)) empty_env le m1
                        [Etempvar hmap hmap_ty; Econst_int (Int.repr 42) tint; Etempvar val val_ty]
                        (Tcons hmap_ty (Tcons tint (Tcons val_ty Tnil))) 
                        [Vptr b_hmap Ptrofs.zero; Vint (Int.repr 42); Vptr b_v Ptrofs.zero]).
    { econstructor. 
      econstructor; eauto. reflexivity.
      econstructor. econstructor. reflexivity.
      econstructor. econstructor. eauto. reflexivity. econstructor. }
    assert (SPEC: process_val_spec m1 (fp_box b_v 4 (fp_scalar Rusttypes.type_int32s))
                    (Vptr b_v Ptrofs.zero)).
    { exploit load_rule. eapply MPRED2. intros (v & A1 & A2). subst.
      exploit load_rule_neg. eapply sep_pick1. eapply MPRED2. intros (v & A3 & A4). subst.
      econstructor; eauto. econstructor; eauto. econstructor; eauto. reflexivity.
      econstructor. 
      - red. intros. 
        destruct (Z.lt_decidable ofs 0).
        + eapply sep_pick1 in MPRED2. eapply MPRED2. lia.
        + eapply MPRED2. simpl. lia.
      - rewrite maxv. lia.
      - econstructor. econstructor. reflexivity.
      - econstructor. intro. inv H. econstructor.
      - econstructor. }
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity. reflexivity.
      + intros. inv H.
        inv H13.
        exploit eval_expr_det. eapply EVALF. eauto. intros. subst.
        exploit eval_exprlist_det. eapply EVALARGS. eauto. intros. subst.
        simpl in H16. setoid_rewrite FINDFUN in H16. inv H16. inv H17.
        eapply hmap_set_inv. eapply hmap_set_call with (v_fp := fp_box b_v 4 (fp_scalar Rusttypes.type_int32s)).
        eapply Genv.find_invert_symbol; eauto.
        econstructor. auto. auto. auto.
        eapply MPRED2.
        (* footprint disjoint *)
        intros. simpl in H0. destruct H0; try contradiction. subst.
        eapply DIS_BV; eauto. }
    lia.

  (* before calling hmap_process *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_before_hmap_process with (n:=1%nat).
        4: eapply starNf_step_right; eauto. 
        4, 5: inv H; simpl; auto. all: eauto. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluete Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_before_hmap_process with (n:=2%nat).
        4: eapply starNf_step_right; eauto. 
        4, 5: inv H; simpl; auto. all: eauto. }
    inv STEP.
    (* call hmap_process *)
    generalize ((proj1 wf_senv) hmap_process). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some (Internal hmap_operate_on_func)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate Scall *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity.
        econstructor. eapply eval_Evar_global. reflexivity.
        eauto. eapply deref_loc_reference. reflexivity.       
        econstructor. econstructor. eauto. reflexivity.
        econstructor. econstructor. reflexivity.
        econstructor. reflexivity.                                             
      + intros. inv H.        
        inv H10. inv H11. inv H. inv H6.
        inv H0; try inv H. simpl in H7. rewrite FINDF in H7. inv H7.
        simpl in H13. setoid_rewrite FINDFUN in H13. inv H13.
        inv H12. inv H4. 2: inv H. rewrite GETHMAP in H2. inv H2.
        inv H6. inv H7. inv H4. 2: inv H. inv H6. inv H8.        
        eapply hmap_operate_on_callstate.
        econstructor. eapply Genv.find_invert_symbol. auto.
        eauto. 
        econstructor. auto. auto.  }
    lia.
  (* after returning from hmap_operate_on  *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_main_internal3 with (n:=1%nat).        
        eapply starNf_step_right; eauto. 
        1, 4: inv H; simpl; auto. eauto. eauto. auto. lia. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sreturn *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        econstructor. reflexivity. reflexivity.
      + intros. inv H. inv H8. 2: inv H. inv H9.
        eapply hmap_init_inv.
        eapply hmap_return_main; eauto. }
    inv STEP.
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    inv NOTCALLRET. lia.
  (* return from main *)
  - split.
    + red. left. eexists. econstructor.
    + intros. inv H.

  (* call init_hmap *)
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal init_hmap_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      auto. }
    generalize (function_entry_init_hmap m).
    intros ENTRY.
    split.
    + red. do 2 right.
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply hmap_init_inv.
      eapply hmap_init_hmap_internal1 with (n:=0%nat).
      econstructor. auto. econstructor. lia.

  (* In init_hmap: allocate the hash map array using malloc *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_init_hmap_internal1 with (n:=1%nat).
        eapply starNf_step_right; eauto. 
        1-3: inv H; simpl; auto. lia. }
    inv STEP.
    2: { destruct H7; try congruence. }
    2: { destruct H7; try congruence. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* find malloc symbol and malloc function *)
    generalize ((proj1 wf_senv) malloc). intros FINDF.
    exploit FINDF. reflexivity. clear FINDF.
    intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
    assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b Ptrofs.zero) = Some Clightgen.malloc_decl).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      erewrite Genv.find_invert_symbol; eauto.
      reflexivity. }    
    (* evaluate Scall *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        reflexivity.
        econstructor. eapply eval_Evar_global. reflexivity.
        eauto. eapply deref_loc_reference. reflexivity.
        (* evaluate sizeof(ptr) * N *)
        econstructor. econstructor. econstructor. econstructor.
        reflexivity. reflexivity. econstructor. reflexivity.
      + intros. inv H.
        inv H10. inv H12. inv H6. inv H3.
        2: inv H. inv H6.
        2: inv H. inv H7. 2: inv H.
        vm_compute in H8. inv H8. vm_compute in H5. inv H5.
        inv H11. inv H. inv H6.
        inv H0; inv H.
        eapply hmap_init_inv.
        eapply hmap_init_hmap_call_malloc. auto.
        simpl in H7. setoid_rewrite FINDF in H7. inv H7. auto.
        rewrite Neq10. reflexivity. }
    lia.
  (* Execution of calling malloc *)

  - (* allocation of malloc and storing the block size *)
    replace (Vlong (Int64.repr (Z.of_nat N * size_chunk Mptr))) with (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr))).
    2: { rewrite Neq10. reflexivity. }
    destruct (Mem.alloc m (- size_chunk Mptr)
                (Ptrofs.unsigned (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) as [m0 b] eqn: ALLOC.
    assert (SZRAN: 0 <= Z.of_nat 10 * size_chunk Mptr <= Ptrofs.max_unsigned).
    { rewrite maxv. vm_compute. split; intros; congruence. }
    destruct (Mem.valid_access_store m0 Mptr b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) as [m1].
    { eapply Mem.valid_access_implies.
      eapply Mem.valid_access_alloc_same. eauto. lia. rewrite Neq10.
      rewrite Ptrofs.unsigned_repr.  lia. auto.
      eapply Z.divide_opp_r. rewrite align_chunk_Mptr. rewrite size_chunk_Mptr.
      eapply Z.divide_refl. constructor. }
    (* As alloc_rule does not support negative position, we prove it manually *)
    assert (MPRED: m1 |= contains_neg Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) ** range b 0 (Z.of_nat N * size_chunk Mptr)).
    { simpl. repeat apply conj.
      - red. intros. eapply Mem.perm_store_1. eauto.
        eapply Mem.perm_alloc_2. eauto. rewrite Ptrofs.unsigned_repr. lia.
        lia.
      - eapply Z.divide_opp_r. rewrite align_chunk_Mptr. rewrite size_chunk_Mptr.
        eapply Z.divide_refl.
      - eexists. split; eauto.
        erewrite Mem.load_store_same; eauto.
        reflexivity.
      - lia.
      - rewrite ptr_modulus. rewrite Neq10. rewrite size_chunk_Mptr.
        destruct Archi.ptr64; lia.
      - intros. eapply Mem.perm_store_1. eauto.
        eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto.
        rewrite Ptrofs.unsigned_repr. lia. lia.
        constructor.
      - red. simpl. intros. destruct H. destruct H0. subst. lia. }
    split.
    (* evaluate calling malloc *)
    { red. do 2 right.
      do 2 eexists. eapply step_external_function.
      eauto. simpl.
      econstructor. eauto. eauto. }
    intros. inv H. rewrite FINDF in FIND. inv FIND.
    rewrite FINDF in FIND. inv FIND.
    simpl in H6.
    eapply extcall_malloc_sem_inv in H6 as (m1' & b1 & sz1 & A1 & A2 & A3 & A4).
    eapply Rustlightown.Vptrofs_det in A1. subst.
    rewrite ALLOC in A2. inv A2.
    rewrite e in A3. inv A3.
    (* sound_state *)
    eapply hmap_init_inv.
    eapply hmap_init_hmap_return_malloc; auto.
    
  (* Execution after returning from malloc *)
  - split.
    + red. do 2 right.
      do 2 eexists. econstructor.
    + intros. inv H.
      eapply hmap_init_inv.
      eapply hmap_init_hmap_before_loop with (n:= 0%nat); eauto.
      econstructor. lia. reflexivity.
      simpl. auto.
  (* Execution before loop *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros.
        eapply hmap_init_inv.
        eapply hmap_init_hmap_before_loop with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. lia. }
    inv STEP.
    2: { simpl in H6; try contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_init_inv.
        eapply hmap_init_hmap_before_loop with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. lia. }
    inv STEP.
    2: { destruct H7; try congruence. }
    2: { destruct H7; try congruence. }
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_init_inv.
        eapply hmap_init_hmap_before_loop with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sset *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        econstructor.
      + intros. eapply hmap_init_inv. eapply hmap_init_hmap_before_loop with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. lia. }
    inv STEP. inv H8.
    2: inv H.
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate Kseq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. inv H. eapply hmap_init_inv. eapply hmap_init_hmap_loop with (n:=0%nat) (idx:= Int.zero). eauto.
        econstructor.
        vm_compute.  lia. eapply PTree.gss.
        rewrite PTree.gso. eauto. vm_compute. congruence.
        vm_compute. auto.
        instantiate (1 := nil). 
        replace (hmap_pred_rec (int_to_nat Int.zero) [] b 0) with (pure True) by reflexivity.
        eapply sep_swap2. eapply sep_pure. split; auto.
        simpl. auto.
        simpl in H7. contradiction. }
    lia.
  (* Execution of the loop in init_hmap *)
  - generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Sloop *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_init_inv. eapply hmap_init_hmap_loop with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto.  
        1, 3: inv H; simpl; auto.
        destruct Int.ltu; lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_init_inv. eapply hmap_init_hmap_loop with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. destruct Int.ltu; lia. }    
    inv STEP.
    2: { destruct H9; try congruence. }
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sifthenelse *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        econstructor. econstructor. eauto. econstructor.
        reflexivity. simpl. instantiate (1 := (Int.ltu idx (Int.repr buk_size))).
        { destruct Int.ltu; reflexivity. }
      + intros.
        eapply hmap_init_inv.
        eapply hmap_init_hmap_loop with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 3: inv H; simpl; auto. destruct Int.ltu; lia. }
    (* evaluate the ifthenelse *)
    inv STEP.
    inv H10; try inv H. inv H9; try inv H.
    inv H5. 2: inv H. rewrite GETTMP2 in H3. inv H3.
    simpl in H7. unfold sem_cmp, sem_binarith in H7. simpl in H7.
    replace (sem_cast (Vint idx) tuint (Tint I32 Unsigned noattr) m) with (Some (Vint idx)) in H7 by reflexivity.
    inv H6. 2: inv H.
    replace (sem_cast (Vint (Int.repr buk_size)) tuint (Tint I32 Unsigned noattr) m) with (Some (Vint (Int.repr buk_size))) in H7 by reflexivity.
    inv H7.
    assert (BEQ: b0 = Int.ltu idx (Int.repr buk_size)).
    { destruct Int.ltu; inv H0; reflexivity. }
    destruct b0; symmetry in BEQ; rewrite BEQ in *.
    (* idx < buk_size *)
    { inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sskip *)
      { split.
        + red. do 2 right.
          do 2 eexists. econstructor; eauto.
        + intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          1,4: inv H; simpl; auto. 1-2: rewrite BEQ; auto; lia. }
      inv STEP.
      2: { simpl in H7. contradiction. }
      (* store NULL in the location of (b, (idx* size ptr)) *)
      generalize BEQ as BEQ1. intros.
      eapply Int.ltu_inv in BEQ.
      replace (Int.unsigned (Int.repr buk_size)) with 10 in BEQ by reflexivity.
      generalize MPRED as MPRED1. intros.
      rewrite <- sep_assoc in MPRED.
      erewrite sep_comm in MPRED.
      assert (ADDEQ: (Int.unsigned (Int.add idx Int.one) * size_chunk Mptr) = 
                       Int.unsigned idx * size_chunk Mptr + size_chunk Mptr).
      { unfold Int.add. rewrite Int.unsigned_repr.
        rewrite Z.mul_add_distr_r. rewrite Int.unsigned_one.
        lia. rewrite Int.unsigned_one.  rewrite max_uint. lia. }
      eapply range_split with (mid := (Int.unsigned (Int.add idx Int.one) * size_chunk Mptr)) in MPRED.
      2: { unfold Int.add. rewrite Int.unsigned_repr.
           generalize (Int.unsigned_range idx).
           generalize (size_chunk_pos Mptr).
           intros R1 R2. 
           rewrite Neq10. split. rewrite Z.mul_add_distr_r.
           rewrite Int.unsigned_one. lia.
           erewrite <- Z.mul_le_mono_pos_r. rewrite Int.unsigned_one.  
           lia. lia. rewrite Int.unsigned_one.  rewrite max_uint. lia. }
      exploit storev_rule. eapply range_contains with (ofs:= (Int.unsigned idx * size_chunk Mptr)) (chunk:= Mptr). rewrite ADDEQ in MPRED at 1. eapply MPRED.
      rewrite align_chunk_Mptr, size_chunk_Mptr.
      eapply Z.divide_mul_r. eapply Z.divide_refl.
      instantiate (1 := Vnullptr). instantiate (1 := eq Vnullptr). auto.
      intros (m2 & STORE1 & MP3).
      assert (MULEQ: ((Ptrofs.mul (Ptrofs.repr (sizeof (Smallstep.globalenv (hash_map_sem se)) (to_ctype List_box))) (ptrofs_of_int Unsigned idx))) = (Ptrofs.repr (Int.unsigned idx * size_chunk Mptr))).
      { unfold Ptrofs.mul. f_equal.
        unfold ptrofs_of_int, Ptrofs.of_intu, Ptrofs.of_int.
        rewrite !Ptrofs.unsigned_repr. rewrite Z.mul_comm. reflexivity.
        rewrite maxv.
        lia.
        vm_compute. split; congruence. }      
      inv STAR1; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sassign *)
      { split.
        + red. do 2 right.
          do 2 eexists. econstructor; eauto.
          econstructor. econstructor. econstructor. eauto.
          econstructor. eauto.
          econstructor. econstructor. econstructor. reflexivity.
          reflexivity. econstructor. reflexivity.
          rewrite Ptrofs.add_zero_l. rewrite MULEQ.
          eauto.
        + intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto. 
        1, 4: inv H; simpl; auto. rewrite BEQ1; lia.
        rewrite BEQ1. auto. }
      (* inversion of assignment *)
      inv STEP.
      2: { destruct H10; inv H. }
      inv H9. inv H5. inv H6. 2: inv H.
      inv H7. 2-3: inv H.
      rewrite GETTMP2 in H4. inv H4.
      rewrite GETHMAP in H3. inv H3.
      inv H10. 2: inv H.
      inv H2. 2: inv H. inv H4. inv H11.
      inv H8. inv H12.
      rewrite Ptrofs.add_zero_l in H1.
      simpl in MULEQ. rewrite MULEQ in H1.
      inv H. setoid_rewrite STORE1 in H1. inv H1.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Kloop1: to add idx with 1 *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor; eauto.
        - intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=6%nat); eauto.
          eapply starNf_step_right; eauto. 
          1, 4: inv H; simpl; auto. rewrite BEQ1; lia.
          rewrite BEQ1. auto. }
      inv STEP.
      2: { simpl in H7. contradiction. }
      inv STAR1; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sset *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor; eauto.
          econstructor. econstructor. eauto.
          econstructor. reflexivity.
        - intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=7%nat); eauto.
          eapply starNf_step_right; eauto. 
          1, 4: inv H; simpl; auto. rewrite BEQ1; lia.
          rewrite BEQ1. auto. }
      inv STEP.
      inv H9. 2: inv H. inv H5. 2: inv H.
      rewrite GETTMP2 in H3. inv H3.
      inv H6. 2: inv H. inv H7.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Kloop2 *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor; eauto.
        - intros. inv H.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=0%nat) (idx := Int.add idx Int.one).
          eauto. econstructor.
          destruct (Int.ltu (Int.add idx Int.one) (Int.repr buk_size)); lia.
          rewrite PTree.gss. reflexivity.
          rewrite PTree.gso. eauto. congruence.
          destruct (Int.ltu (Int.add idx Int.one) (Int.repr buk_size)) eqn: BEQ2; auto.   
          eapply add_one_lt; auto. rewrite max_uint. lia.
          instantiate (1 := fpl ++ [fp_emp]).
          rewrite <- sep_assoc in MP3. rewrite sep_comm in MP3.
          rewrite sep_assoc in MP3.          
          rewrite <- (sep_assoc (hmap_pred_rec (int_to_nat idx) fpl loc 0)) in MP3.
          eapply sep_swap12 in MP3. eapply sep_swap12.
          eapply sep_imp. eapply MP3. 2: reflexivity.
          replace (int_to_nat (Int.add idx Int.one)) with ( (int_to_nat idx)+ 1)%nat.
          etransitivity. 2: eapply hmap_pred_rec_append_one.
          simpl.
          {
            eapply sepconj_morph_2. reflexivity.
            replace (size_chunk Mptr * Z.of_nat (int_to_nat idx)) with (Int.unsigned idx * size_chunk Mptr).
            2: { unfold int_to_nat. rewrite Z2Nat.id. lia. lia. }
            symmetry.
            eapply bucket_pred_emp_eqv. }
          eapply hmap_pred_rec_fpl_length. eapply MP3.
          unfold int_to_nat.
          unfold Int.add. rewrite Int.unsigned_repr. rewrite Z2Nat.inj_add.
          reflexivity. lia. rewrite Int.unsigned_one. lia.
          rewrite Int.unsigned_one. rewrite max_uint. lia.
          auto.
          simpl in H8. contradiction. }
      inv STEP.
      2: { simpl in H7. contradiction. }
      lia. }
      (* replace (sem_add (PTree.empty composite) (Vint idx) tuint (Vint Int.one) tuint m') with *)
      (*   (Some (Vint (Int.add idx Int.one))) in * by reflexivity. *)

    (* idx >= buk_size *)
    { inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sbreak *)
      { split.
        + red. do 2 right.
          do 2 eexists. econstructor; eauto.
        + intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          1,4: inv H; simpl; auto. 1-2: rewrite BEQ; auto; lia. }
      inv STEP.
      inv STAR1; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sbreak *)
      { split.
        + red. do 2 right.
          do 2 eexists. eapply step_break_loop1.
        + intros.
          eapply hmap_init_inv.
          eapply hmap_init_hmap_loop with (n:=5%nat); eauto.
          eapply starNf_step_right; eauto. 
          1,4: inv H; simpl; auto. 1-2: rewrite BEQ; auto; lia.  }
      inv STEP. destruct H10; congruence.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Kseq *)
      { split.
        + red. do 2 right.
          do 2 eexists. econstructor.
        + intros. inv H.
          2: { simpl in H8. contradiction. }
          eapply hmap_init_inv.
          eapply hmap_init_hmap_after_loop; eauto.
          instantiate (1 := fpl).
          unfold hmap_pred, HashMapCommon.hmap_pred.
          assert (IDXEQ: int_to_nat idx = N).
          { exploit Int.eq_spec. rewrite IDXVAL. intros. subst.
            reflexivity. }
          rewrite IDXEQ in *. 
          rewrite <- sep_assoc in MPRED. eapply MPRED. }
      lia. }

  (* init_hmap: after the loop *)
  - split.
    + red. do 2 right.
      do 2 eexists. econstructor.
      econstructor. eauto. reflexivity. reflexivity.
    + intros. inv H.
      1,3 : destruct H8; try congruence.
      inv H8. 2: inv H. rewrite GETHMAP in H2. inv H2. inv H9. 
      inv H10. eapply hmap_init_inv. eapply hmap_init_hmap_return; eauto.
      inv CONT. simpl. econstructor; auto.
  (* init_hmap: return init_hmap *)
  - inv CONT. split.
    + red. do 2 right.
      do 2 eexists. econstructor.
    + intros. inv H.
      eapply hmap_init_inv.
      eapply hmap_main_internal2 with (n:=0%nat).
      econstructor. 
      simpl. eapply PTree.gss.
      simpl. rewrite PTree.gso; auto. vm_compute. congruence.
      eauto. simpl. auto. auto. lia.
Qed.

Lemma step_preservation_progress: forall s,
    sound_state s ->
    not_stuck (hash_map_sem se) s
    /\ (forall s' t, step1 ge s t s' ->
               sound_state s').
Proof.
  intros s INV. inv INV.
  (* Initilization of hash map *)
  - eapply step_hmap_init_preservation_progress. auto.
  (* Insertion of key-value pair *)
  - eapply step_hmap_set_preservation_progress. auto.

  (* call process *)
  - assert (FIND: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some (Internal process_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYMB.
      auto. }
    assert (Hm': Mem.sup_include (footprint_flat (fp_box b 4 (fp_scalar Rusttypes.type_int32s))) (Mem.support rwm)).
    { unfold rw_mem, rw_fp in *. destruct rw; try congruence.
      destruct r. inv RWMEM. inv RWFP.
      eapply Mem.sup_include_trans. 2: eauto. red. intros.
      inv H. 
      eapply FPEQ. simpl. eauto. inv H0. }
    exploit function_entry_process.
    econstructor; eauto. econstructor. econstructor. reflexivity.
    econstructor. intro. inv H. econstructor.
    econstructor.
    instantiate (1 := Hm').
    intros (b_val & m1 & ENTRY & MPRED1).
    split.
    + red. do 2 right.
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply hmap_process_internal.
      eauto. eauto. eauto. eauto. econstructor.
      reflexivity. reflexivity. eauto. eauto.
      lia.
      
  (* process internal *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR1.
    (* evaluate Ssequence *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_process_internal with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    exploit loadv_rule. eapply MPRED1.      
    intros (v & LOAD1 & SPEC1). inv SPEC1.
    inv WTFP. inv WTVAL. simpl in WF; try congruence.
    inv WTVAL.
    inv WT. inv WTLOC.
    inv WTLOC. inv MODE. inv WT.
    (** store xor value to *val. For now, we just prove it here and
      does not write a separate lemma. *)
    edestruct Mem.valid_access_store with (chunk:= Mint32) (v:= (Vint (Int.xor n (Int.repr 42)))) as (m2 & STORE1). eapply Mem.valid_access_implies.
    split. rewrite Z.add_0_l.
    red. intros. eapply VALID. rewrite size_chunk_Mptr in *.
    simpl in H.
    destruct Archi.ptr64; lia. eapply Z.divide_0_r. econstructor.
    (* use sep_preserved *)
    exploit (sep_preserved m m2). eapply MPRED1.
    { simpl. intros ((A1 & A2 & (v1 & A3 & A4)) & A5).
      (* unchanged on *)
      exploit Mem.store_unchanged_on. eauto.
      instantiate (1 := fun b _ => b = b_val).
      intros. intro. eapply A5. auto. intros UNC.
      assert (VB1: Mem.valid_block m b_val).
      { eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies. eauto. constructor. }
      assert (VB2: Mem.valid_block m b).
      { eapply Mem.valid_access_valid_block.          
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access; eauto. constructor. }
      repeat apply conj; auto. lia. lia.
      red. intros. erewrite <- Mem.unchanged_on_perm.
      eapply A2. auto. eauto. reflexivity. auto.
      eapply Z.divide_0_r.
      (* load and sem_wt_val *)
      exists (Vptr b Ptrofs.zero). split.
      erewrite Mem.load_unchanged_on_1; eauto.
      reflexivity.
      econstructor; eauto.
      econstructor. econstructor. reflexivity.
      eapply Mem.load_store_same; eauto.
      econstructor; eauto.
      red. intros. eapply Mem.perm_store_1; eauto.
      erewrite Mem.load_unchanged_on_1. eauto.
      eapply Mem.store_unchanged_on. eauto.
      instantiate (1 := fun b1 ofs1 => b1 <> b \/ ofs1 < 0).
      red. intros. destruct H0; try congruence. lia.
      auto. 
      simpl. intros. lia. auto.
      econstructor. econstructor. reflexivity. }
    { intros MP. eapply m_invar. eapply MP.
      simpl. eapply Mem.store_unchanged_on. eauto.
      simpl. intros. intro. destruct H0. eapply H1. auto. }
    intros MPRED2.
    inv STAR0; cbn [num_frames num_frames_cont] in *.  
    (* evaluate Sassign *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        econstructor. econstructor. econstructor. reflexivity.
        econstructor. reflexivity. eauto.
        econstructor. econstructor. econstructor. econstructor.
        econstructor. reflexivity. econstructor. reflexivity.
        eauto. econstructor. reflexivity.
        eauto.
        econstructor. reflexivity. reflexivity.
        econstructor. reflexivity.
        replace (Vint (cast_int_int I32 Signed (Int.xor (cast_int_int I32 Signed n) (cast_int_int I32 Signed (Int.repr 42))))) with (Vint (Int.xor n (Int.repr 42))).
        eauto. reflexivity.
      + intros. eapply hmap_process_internal with (n:=2%nat). eapply MPRED1. eauto.
        eauto. eauto.
        2: eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. eauto. auto. lia. }
    inv STEP.
    (* inversion of assignment *)
    inv H8. inv H4. inv H.
    2: { inv H3. }
    inv H6. inv H0; try inv H2. inv H.
    setoid_rewrite LOAD1 in H1. inv H1.
    inv H9.
    2: { inv H. }
    inv H4. inv H. inv H0; inv H.
    inv H8. inv H.
    2: { inv H4. }
    inv H9. inv H0; try inv H3. inv H.
    setoid_rewrite LOAD1 in H2. inv H2.
    setoid_rewrite LOAD in H1. inv H1.
    inv H5.
    2: { inv H. }
    inv H6.
    assert (XOREQ: (sem_xor (Vint n) tint (Vint (Int.repr 42)) tint m) = (Some (Vint (Int.xor n (Int.repr 42))))) by reflexivity.
    rewrite XOREQ in *.
    inv H10. 
    inv H11. inv H. setoid_rewrite STORE1 in H0. inv H0.
    inv STAR1; cbn [num_frames num_frames_cont] in *.
    (* evaluate skip_seq *)
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
      + intros. eapply hmap_process_internal with (n:=3%nat). eapply MPRED1. all: eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* free_list and return *)
    exploit loadv_rule. eapply MPRED2. intros (v2 & LOAD2 & SPEC2).
    inv SPEC2.
    inv WTFP. inv WTVAL. 
    inv WT. inv WTLOC.
    inv MODE. inv WT.
    exploit (free_rule Mptr m' loc2 0).    
    eapply sep_imp. eapply MPRED2.
    instantiate (1 := fun _ => True).
    econstructor. intros. destruct H. eapply contains_imp. eauto. eauto.
    intros. destruct H. econstructor. auto.
    reflexivity.
    intros (m3 & FREE1 & MPRED3).
    { split.
      + red. do 2 right.
        do 2 eexists. econstructor; eauto.
        econstructor. econstructor. reflexivity.
        econstructor. reflexivity. eauto.
        simpl. reflexivity.
        simpl. setoid_rewrite FREE1. eauto.
      + intros. inv H.
        (* inversion of return value *)
        inv H8. inv H.
        2: { inv H3. }
        inv H6. inv H0; inv H.
        setoid_rewrite LOAD2 in H1. inv H1. inv H9.
        simpl in H10. setoid_rewrite FREE1 in H10. inv H10.        
        eapply hmap_return_process; eauto.
        (* prove sem_wt_val after free operation *)
        eapply sem_wt_val_unchanged_blocks.
        2: { eapply Mem.free_unchanged_on. eauto. 
             simpl. intros. intro. destruct H0.
             - destruct H0; try contradiction. subst.
               simpl in MPRED2.
               destruct MPRED2 as (((A1 & A2 & A3) & A4) & A5).
               eapply A4. auto.
             - destruct H0; try contradiction. subst.
               simpl in MPRED2.
               destruct MPRED2 as (((A1 & A2 & A3) & A4) & A5).
               eapply A4. auto. }
        econstructor. econstructor. reflexivity.
        eauto. econstructor. eauto. eauto. auto.
        econstructor. econstructor. auto. }
    inv STEP.
    inv STAR1. inv NOTCALLRET.
    inv STEP.
    
  (* return process *)
  - split.
    + left. eexists. econstructor.
    + intros. inv H.
  
  (* call hmap_process *)
  - inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b1 Ptrofs.zero) = Some (Internal hmap_operate_on_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    exploit (function_entry_hmap_operate_on m (hmap_pred b2 fpl) b2 Ptrofs.zero kv). eapply HMAP.
    intros (b_hmap & b_key & m1 & ENTRY & MPRED1).
    split.
    + red. do 2 right.      
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply hmap_operate_on_internal1. eauto. 
      reflexivity. reflexivity. econstructor. auto.
      simpl. auto. lia.
  (* hmap_operate_on_internal1 *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hmap_operate_on_internal1 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    2: { destruct H7; try congruence. }
    2: { destruct H7; try congruence. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { generalize ((proj1 wf_senv) find_bucket). intros FINDF.
      exploit FINDF. reflexivity. clear FINDF.
      intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
      exploit load_rule. eapply sep_proj1. eapply MPRED.
      intros (v1 & LOAD1 & SPEC1). subst.
      exploit load_rule. eapply sep_proj1. eapply sep_proj2. eapply MPRED.
      intros (v2 & LOAD2 & SPEC2). subst.
      split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        reflexivity.
        econstructor. eapply eval_Evar_global. reflexivity. eauto.
        eapply deref_loc_reference. reflexivity.
        econstructor. econstructor. eapply eval_Evar_local.
        reflexivity. econstructor. reflexivity. eauto.
        reflexivity.
        econstructor. econstructor. eapply eval_Evar_local.
        reflexivity. econstructor. reflexivity. eauto.
        reflexivity.
        econstructor.
        (* find_funct *)
        simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
        rewrite Genv.find_def_spec.
        erewrite Genv.find_invert_symbol; eauto.
        reflexivity. reflexivity.
      - intros. inv H.
        simpl in H10. inv H10.
        inv H12. inv H3. inv H.
        2: { vm_compute in H3. congruence. }
        vm_compute in H8. inv H8. inv H0; simpl in H; inv H. 
        setoid_rewrite LOAD1 in H1. inv H1.
        vm_compute in H5. inv H5.
        inv H6. inv H3. inv H.
        2: { vm_compute in H3. congruence. }
        vm_compute in H8. inv H8. inv H0; simpl in H; inv H. 
        setoid_rewrite LOAD2 in H1. inv H1.
        vm_compute in H5. inv H5. inv H7.
        exploit Genv.find_funct_inv. eauto.
        intros (b1 & A1). subst.
        inv H11. inv H.
        vm_compute in H6. congruence.
        inv H0. simpl in H; inv H.
        2: { simpl in H1. inv H1. }
        simpl in H7.
        rewrite FINDF in H7. inv H7.
        eapply find_bucket_callstate; eauto.
        econstructor.
        eapply Genv.find_invert_symbol. eauto.
        (* cont *)
        econstructor. econstructor. reflexivity.
        reflexivity. auto. eauto.
        eapply sep_comm. rewrite sep_assoc.
        eapply MPRED1. } 
    lia.
    
  (** hmap_process after returning from find_bucket *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    { rewrite Ptrofs.unsigned_repr. auto.
      rewrite Nzeq in *. rewrite maxv. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros R.
      destruct Archi.ptr64; lia. }      
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hmap_operate_on_internal2 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    2: { inv H6. }
    (* load *buk from memory *)
    exploit (load_rule (bucket_val_pred m fp)). eapply MPRED.
    intros (v1 & LOAD1 & SPEC1).  unfold bucket_val_pred in SPEC1.
    (* load key from memory *)
    exploit (load_rule (eq (Vint ki))). eapply MPRED.
    intros (v2 & LOAD2 & SPEC2). subst. 
    (* evaluate the conditional expression *)
    assert (EVALB: eval_expr (Smallstep.globalenv (hash_map_sem se))
                     (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                     (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
                        (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
                     (Ebinop Oeq (Ederef (Etempvar buk List_box_ptr) List_ptr)
                        (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint)
                     (Val.of_bool (if Val.eq v1 Vnullptr then true else false))).
    { econstructor.
      econstructor. econstructor. econstructor. econstructor.
      econstructor. reflexivity. simpl. rewrite OFSEQ. eauto.
      econstructor. econstructor. reflexivity.
      simpl. unfold sem_cmp, cmp_ptr. simpl.
      (* we should show that the pointer (if not NULL) is a valid pointer *)
      destruct Val.eq in SPEC1. subst.
      reflexivity.
      inv SPEC1. inv WTFP. inv WTVAL. simpl in WF. congruence.
      replace (Rusttypes.sizeof ll_ce List_ty) with 32 in WTVAL by reflexivity.
      inv WTVAL.
      simpl. rewrite Int64.eq_true. simpl.
      setoid_rewrite (proj2 (Mem.valid_pointer_nonempty_perm m b0 0)).
      reflexivity.
      eapply Mem.perm_implies. eapply VALID. rewrite size_chunk_Mptr.
      destruct Archi.ptr64; lia. econstructor. }
    assert (BVAL: bool_val (Val.of_bool (if Val.eq v1 Vnullptr then true else false)) tint m = Some (if Val.eq v1 Vnullptr then true else false)).
    { destruct Val.eq; reflexivity. }    
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        (* evaluate (buk == NULL) *)
        eauto. eauto.
      - intros. eapply hmap_operate_on_internal2 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    2: { destruct H7; congruence. }
    2: { destruct H7; congruence. }
    exploit eval_expr_det. eapply H9. eapply EVALB.
    intros. subst. setoid_rewrite BVAL in H10. inv H10. clear H9.
    destruct Val.eq.
    (* evaluate the true branch (i.e., buk == NULL) *)
    { 
    assert (MPRED2: m |= hmap_pred b (fpl1 ++ fp :: fpl2)
                      ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
                      ** contains Mint32 b_key 0 (eq (Vint ki))).
    { eapply sep_imp.
      3: { reflexivity. }
      2: { unfold hmap_pred.
           eapply sepconj_morph_1. reflexivity.
           eapply hmap_pred_rec_split with (k := length fpl1).
           rewrite !app_length in FPLEN. simpl in FPLEN. lia.
           eauto. }
      rewrite app_nth2. rewrite Nat.sub_diag. cbn [nth].
      rewrite firstn_app, firstn_all. rewrite Nat.sub_diag. cbn [firstn].
      rewrite skipn_app. rewrite skipn_all2.
      rewrite Nat.sub_succ_l. rewrite Nat.sub_diag.
      rewrite !app_nil_r, app_nil_l. rewrite Z.add_0_l.
      cbn [skipn].
      replace (Datatypes.length fpl1) with (int_to_nat idx).
      replace (Z.of_nat (int_to_nat idx)) with (Int.unsigned idx).
      rewrite !sep_assoc. eapply MPRED.
      unfold int_to_nat. rewrite Z2Nat.id. reflexivity.
      eapply Int.unsigned_range.
      (* add int_to_nat idx = Datatypes.length fpl1 to the invariant *)
      symmetry. eapply hmap_pred_rec_fpl_length. eapply MPRED1.
      1-3: lia. }
    (* free blocks *)
    rewrite sep_comm in MPRED2. rewrite sep_assoc in MPRED2.
    exploit (free_rule Mptr m b_hmap 0). eapply MPRED2.
    intros (m1 & FREE1 & MP1).
    exploit free_rule. eapply MP1.
    intros (m2 & FREE2 & MP2).
    simpl in FREE1, FREE2.      
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        simpl. setoid_rewrite FREE1. setoid_rewrite FREE2. eauto.
      - intros. inv H.
        1,3: destruct H8; congruence.
        simpl in H7. setoid_rewrite FREE1 in H7. setoid_rewrite FREE2 in H7.
        inv H7.
        eapply hmap_operate_on_returnstate.
        instantiate (1 := b).
        inv CONT; simpl; econstructor; auto. eauto. }
    inv STEP.
    1,3: destruct H7; congruence.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    simpl in NOTCALLRET. contradiction.
    (* contradiction for the frames numbers *)
    inv STEP. rewrite <- H1 in FEQ2. simpl in FEQ2.
    exfalso. eapply Nat.neq_succ_diag_l; eauto. }

    (* evaluate the false branch *)
    { inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply hmap_operate_on_internal2 with (n:=3%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP; try (destruct H7; congruence).
      (* evaluate the call step *)
      generalize ((proj2 wf_senv) find). intros FINDF.
      exploit FINDF. reflexivity. clear FINDF.
      intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
      assert (FINDFUN: Genv.find_funct (Smallstep.globalenv (hash_map_sem se)) (Vptr b0 Ptrofs.zero) = Some find_ext).
      { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
        rewrite Genv.find_def_spec.
        erewrite Genv.find_invert_symbol; eauto.
        reflexivity. }
      (* evaluate function pointer *)
      assert (EVALFUN: eval_expr ge
          (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
          (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
             (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
          (Evar find (Tfunction (Tcons List_ptr (Tcons tint Tnil)) List_ptr cc_default))
          (Vptr b0 Ptrofs.zero)).
      { econstructor. eapply eval_Evar_global.
        reflexivity. eauto.
        eapply deref_loc_reference. reflexivity. }
      (* evaluate arguments *)
      assert (EVALARGS: eval_exprlist (Smallstep.globalenv (hash_map_sem se))
       (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
       (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
          (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m
       [Ederef (Etempvar buk List_box_ptr) List_ptr; Evar key tint]
       (Tcons List_ptr (Tcons tint Tnil)) [v1; Vint ki]).
      { econstructor.
        econstructor. econstructor. econstructor.
        reflexivity. econstructor. reflexivity.
        simpl. rewrite OFSEQ. eauto.
        eapply cast_val_casted. inv SPEC1.
        eapply RustOp.val_casted_to_ctype in CASTED. eauto.
        econstructor. econstructor. eapply eval_Evar_local.
        reflexivity. econstructor. reflexivity. eauto. reflexivity.
        econstructor. }
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - red. do 2 right.          
          do 2 eexists. econstructor.
          reflexivity. eauto. eauto.
          eauto. reflexivity.          
        - intros. inv H. inv H10.
          exploit eval_expr_det. eapply EVALFUN. eauto.
          intros. subst.
          exploit eval_exprlist_det. eapply EVALARGS. eauto.
          intros. subst.
          simpl in H13.
          setoid_rewrite FINDFUN in H13. inv H13. inv H14.
          rewrite <- sep_swap23, <- sep_swap12 in MPRED1.
          exploit bucket_pred_elim. eapply MPRED1.
          intros (v & MPRED2 & BUK & NIN & DISJOINT).          
          eapply hmap_operate_on_call_find with (fp:= fp).
          eapply MPRED2.
          (* prove disjointness of footprint *)
          eauto. eauto.
          eapply Genv.find_invert_symbol. eauto.
          (* cont *)
          econstructor; eauto.
          (* length *)
          rewrite !app_length in FPLEN.
          rewrite !app_length. simpl in FPLEN. lia.
          (* sup_include *)
          red. intros.
          eapply m_valid. eapply MPRED1.
          instantiate (1 := 0).
          simpl. left. eauto. }
      inv STEP.
      exploit eval_expr_det. eapply EVALFUN. eauto.
      intros. subst.      
      inv STAR; cbn [num_frames num_frames_cont] in *.
      simpl in NOTCALLRET. contradiction.
      inv STEP; simpl in FEQ3.
      simpl in FIND. setoid_rewrite FINDFUN in FIND. inv FIND.
      simpl in FIND. setoid_rewrite FINDFUN in FIND. inv FIND. inv H5. }

  (* call find state *)
  - assert (FINDFUN: Genv.find_funct ge (Vptr bf Ptrofs.zero) = Some find_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite FINDSYM. reflexivity. }
    split.
    + right. left.
      eexists. econstructor. eauto.
    + intros. inv H.
      rewrite FINDFUN in FIND. inv FIND.
      rewrite FINDFUN in FIND. inv FIND. inv H6.
  (* return from find *)
  - inv CONT. split.
    + do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H. eapply hmap_operate_on_internal3 with (n := 0%nat); eauto.
      econstructor. simpl. auto.
      rewrite !app_length in *. simpl. lia.
  (* execution after returning from find *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    { rewrite Ptrofs.unsigned_repr. auto.
      rewrite Nzeq in *. rewrite maxv. rewrite size_chunk_Mptr.
      generalize (Int.unsigned_range idx). intros R.
      destruct Archi.ptr64; lia. }    
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hmap_operate_on_internal3 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    2: { simpl in H6. contradiction. }    
    (* assign to *buk *)
    exploit bucket_val_spec_inv; eauto. intros (b1 & VEQ). subst.
    exploit store_rule. eapply MPRED.
    instantiate (1 := Vptr b1 Ptrofs.zero). instantiate (1 := eq (Vptr b1 Ptrofs.zero)).
    eauto. intros (m1 & STORE1 & MPRED2).
    (* show bucket_val_spec in m1 *)
    exploit bucket_val_spec_unchanged_on; eauto.
    eapply Mem.store_unchanged_on. eauto. intros. intro.
    eapply DISJOINT; eauto. simpl. left. split; eauto.
    intros VSPEC1.
    (* combine vspec and memory predicate *)
    exploit bucket_pred_intro. eapply MPRED2. 
    red. rewrite dec_eq_false. eauto. intro. vm_compute in H. inv H.
    intro. eapply DISJOINT; eauto.
    instantiate (1 := size_chunk Mptr * Int.unsigned idx).
    simpl. left. split; auto. rewrite size_chunk_Mptr.
    destruct Archi.ptr64; lia. eauto.
    intros MPRED3.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        econstructor. econstructor. reflexivity.
        econstructor. reflexivity. reflexivity.
        econstructor. reflexivity. simpl. rewrite OFSEQ. eauto.
      - intros. eapply hmap_operate_on_internal3 with (n:=2%nat).
        reflexivity. eauto. reflexivity. eapply MPRED1. eauto. eauto. 
        eapply starNf_step_right; eauto.
        1-2: inv H; simpl; auto. lia. eauto. eauto. }
    inv STEP.
    2: { destruct H7; congruence. }
    2: { destruct H7; congruence. }
    inv H9. inv H2.
    2: { inv H. }
    inv H11; inv H.
    inv H8. inv H4.
    2: { inv H. }
    inv H3. simpl in H10. inv H10.
    simpl in H0. rewrite OFSEQ in H0. setoid_rewrite STORE1 in H0. inv H0.
    (* combine MPERD3 *)
    rewrite sep_swap12, sep_swap23 in MPRED3.
    assert (MPRED4: m' |= hmap_pred loc (fpl1 ++ fp :: fpl2) **
                      contains Mptr b_hmap 0 (eq (Vptr loc Ptrofs.zero)) **
                      contains Mint32 b_key 0 (eq (Vint ki))).
    { unfold hmap_pred, HashMapCommon.hmap_pred.
      rewrite hmap_pred_rec_split with (k:=(int_to_nat idx)); eauto.
      exploit (hmap_pred_rec_fpl_length (int_to_nat idx) fpl1). eapply MPRED2.
      intros L1. rewrite <- L1 in *.
      rewrite firstn_app_3.
      rewrite <- (Nat.add_0_r (length fpl1)). 
      rewrite app_nth2_plus. cbn [nth]. rewrite Z.add_0_l.
      rewrite skipn_app. rewrite skipn_all2; try lia.
      replace ((S (length fpl1 + 0) - length fpl1))%nat with 1%nat by lia.
      cbn [skipn]. rewrite !app_nil_l. rewrite !Nat.add_0_r.
      replace (Z.of_nat (length fpl1)) with (Int.unsigned idx).
      rewrite !sep_assoc.
      exact MPRED3.
      rewrite L1. unfold int_to_nat. rewrite Z2Nat.id. reflexivity.
      eapply Int.unsigned_range. unfold int_to_nat. lia. }    
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* return from hmap_operate_on (may return to main or return to
    the environment *)
    { 
      (* free blocks *)
      rewrite sep_swap12 in MPRED4.
      exploit free_rule. eapply MPRED4.
      intros (m1 & FREE1 & MP1).
      rewrite sep_comm in MP1.
      exploit free_rule. eapply MP1.
      intros (m2 & FREE2 & MP2).
      simpl in FREE1, FREE2.
      inv CONT.
      (* return to the environment *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor. econstructor.
          simpl. setoid_rewrite FREE1. setoid_rewrite FREE2. eauto.
        - intros. inv H.
          simpl in H8. setoid_rewrite FREE1 in H8. setoid_rewrite FREE2 in H8.
          inv H8.
          eapply hmap_operate_on_returnstate.
          econstructor.  eauto. eauto. eauto. }
      (* return to main function *)
      { split.
        - red. do 2 right.
          do 2 eexists. econstructor. econstructor.
          simpl. setoid_rewrite FREE1. setoid_rewrite FREE2. eauto.
        - intros. inv H.
          simpl in H8. setoid_rewrite FREE1 in H8. setoid_rewrite FREE2 in H8.
          inv H8.
          eapply hmap_operate_on_returnstate.
          econstructor. eauto. eauto. eauto. }
    }
    (* return from hmap_process (we need to specify the cont of hmap_process) *)
    inv STAR0; try lia.
        
  (*  TODO: show returnstate in hmap_process is not stuck. We
    need to specify the continuation. *)
  - inv CONT.
    + split.
      * red. do 2 right. do 2 eexists. econstructor.
      * intros. inv H.
        eapply hmap_init_inv.
        eapply hmap_main_internal3 with (n:=0%nat).
        econstructor. eauto. eauto. simpl. auto.
        auto. lia.
    + split.
      * red. left. eexists. econstructor.
      * intros. inv H.
        
  (* call find_bucket *)
  - inv CALL. 
    assert (FIND: Genv.find_funct ge (Vptr b1 Ptrofs.zero) = Some (Internal find_bucket_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }    
    exploit (function_entry_find_bucket m (hmap_pred b2 fpl ** MP) b2 Ptrofs.zero kv). eapply HMAP.    
    intros (b_hmap & b_key & m1 & ENTRY & MPRED1).
    split.
    + red. do 2 right.      
      do 2 eexists. econstructor; eauto.
    + intros. inv H; rewrite FIND in FIND0; inv FIND0.
      exploit function_entry1_det. eauto. eapply ENTRY.
      intros (A1 & A2 & A3). subst.
      eapply find_bucket_internal1 with (n:=0%nat). reflexivity. eauto. auto. eauto.
      econstructor. simpl. auto. lia. 
  (* find_bucket_internal1  *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_bucket_internal1 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    2: { destruct H7; try congruence. }
    2: { destruct H7; try congruence. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { generalize ((proj2 wf_senv) hash). intros FINDF.
      exploit FINDF. reflexivity. clear FINDF.
      intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
      exploit load_rule. eapply sep_proj1. eapply sep_proj2. eapply MPRED.
      intros (v1 & LOAD1 & SPEC1). subst.
      split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        reflexivity.
        econstructor. eapply eval_Evar_global. reflexivity. eauto.
        eapply deref_loc_reference. reflexivity.
        econstructor. econstructor. eapply eval_Evar_local.
        reflexivity. econstructor. reflexivity. eauto.
        reflexivity.
        econstructor. econstructor. 
        reflexivity. econstructor. 
        (* find_funct *)
        simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
        rewrite Genv.find_def_spec.
        erewrite Genv.find_invert_symbol; eauto.
        reflexivity. reflexivity.
      - intros. inv H.
        simpl in H10. inv H10.
        inv H12. inv H3. inv H.
        2: { vm_compute in H3. congruence. }
        vm_compute in H8. inv H8. inv H0; simpl in H; inv H. 
        setoid_rewrite LOAD1 in H1. inv H1. vm_compute in H5. inv H5.
        inv H6. inv H3.
        2: { inv H. }
        erewrite cast_val_casted in H5.
        2: { econstructor. reflexivity. }
        inv H5.
        exploit Genv.find_funct_inv. eauto.
        intros (b1 & A1). subst.
        inv H11. inv H.
        vm_compute in H6. congruence.
        inv H0. simpl in H; inv H.
        2: { simpl in H1. inv H1. }
        inv H7. simpl in H8.
        unfold buk_size.
        replace (Int.repr 10) with Ni.
        2: { unfold Ni. rewrite Neq10. reflexivity. }
        eapply find_bucket_call_hash; eauto.
        econstructor. rewrite Nieq. auto.
        econstructor. reflexivity.
        econstructor. reflexivity.
        (* find_funct *)
        eapply Genv.find_invert_symbol. eauto.
        (* cont *)
        econstructor. eauto. }
    lia.
  (* call hash function *)
  - assert (FINDFUN: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some hash_ext).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.      
      rewrite FINDSYM. reflexivity. }
    split.
    + right. left. eexists.
      econstructor. eauto.
    + intros.
      inv H; rewrite FINDFUN in FIND; inv FIND.
      inv H6.
  (* return from hash function *)
  - inv COND. inv CONT.
    split.
    + do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H.
      eapply find_bucket_internal2; eauto.
      econstructor. simpl. auto. 
  (* execution after returning from hash *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_bucket_internal2 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. }
    inv STEP.
    2: { simpl in H6. contradiction. }
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { exploit load_rule. eapply sep_proj1. eapply MPRED.
      intros (v1 & LOAD1 & SPEC1). subst.
      (* free blocks *)
      exploit free_rule. eapply MPRED.
      intros (m1 & FREE1 & MP1).
      exploit free_rule. eapply MP1.
      intros (m2 & FREE2 & MP2).
      simpl in FREE1, FREE2.
      split.
      - red. do 2 right.
        do 2 eexists. econstructor.
        (* evaluate hmap + index *)
        econstructor. econstructor. eapply eval_Evar_local.
        reflexivity. econstructor. reflexivity. eauto.
        econstructor. reflexivity. reflexivity.
        reflexivity.
        simpl. setoid_rewrite FREE1. setoid_rewrite FREE2. eauto.
      - intros. inv H.
        destruct H8; congruence.
        2: { destruct H8; congruence. }
        inv H8.
        2: { inv H. }        
        inv H4. inv H.
        2: { inv H3. } inv H8.
        inv H0; simpl in H; inv H.
        setoid_rewrite LOAD1 in H1. inv H1.
        inv H5.
        2: { inv H. }
        vm_compute in H2. inv H2.
        inv H6. inv H9.
        rewrite Ptrofs.add_zero_l.
        (* free_list *)
        simpl in H10. setoid_rewrite FREE1 in H10.
        rewrite FREE2 in H10. inv H10.
        set (fpl1 := firstn (int_to_nat r) fpl).
        set (fp := nth (int_to_nat r) fpl fp_emp).
        set (fpl2 := skipn (S (int_to_nat r)) fpl).
        assert (OFSEQ: ((Ptrofs.mul (Ptrofs.repr (size_chunk Mptr)) (Ptrofs.of_intu r)))
                       = Ptrofs.repr ((size_chunk Mptr) * (Int.unsigned r))).
        { unfold Ptrofs.mul. 
          unfold Ptrofs.of_intu, Ptrofs.of_int.
          rewrite !Ptrofs.unsigned_repr. reflexivity.
          eapply Int.ltu_inv in INRAN. unfold Ni in INRAN.
          rewrite maxv. generalize (Int.unsigned_range r). intros.
          replace (Int.unsigned (nat_to_int N)) with 10 in *. lia.
          rewrite Neq10. reflexivity.
          rewrite maxv. rewrite size_chunk_Mptr.
          destruct Archi.ptr64; lia. }        
        setoid_rewrite OFSEQ.
        assert (RAN1: Int.unsigned r < Z.of_nat N).
        { eapply Int.ltu_inv in INRAN. rewrite Nieq in INRAN. 
          rewrite Int.unsigned_repr in INRAN. lia.
          eapply N_in_range. }
        eapply find_bucket_returnstate with (fpl1:=fpl1) (fp:= fp) (fpl2:= fpl2). 
        instantiate (1 := MP). eapply sep_assoc5.
        eapply sep_imp with (Q' := MP). eapply MP2.        
        eapply sepconj_morph_1. reflexivity.
        replace (Int.unsigned r) with (Z.of_nat (int_to_nat r)).
        2: { unfold int_to_nat. rewrite Z2Nat.id. auto.
             generalize (Int.unsigned_range r). lia. }
        eapply hmap_pred_rec_split.
        { unfold int_to_nat. lia. }
        eapply hmap_pred_fpl_length. eapply MP2.
        reflexivity. auto. eauto.        
        { exploit hmap_pred_fpl_length. eapply MP2. intros LEN.
          unfold fpl1, fp, fpl2. rewrite !app_length.
          rewrite firstn_length_le. cbn [length]. 
          rewrite skipn_length. rewrite <- Nat.sub_succ_l.
          simpl.
          rewrite Nat.add_sub_assoc. rewrite Nat.add_sub_swap. lia.
          lia. 
          unfold int_to_nat. lia.
          unfold int_to_nat. rewrite LEN. lia.
          unfold int_to_nat. rewrite LEN. lia. }           
        erewrite <- call_find_bucket_cont_eq_call_cont; eauto. }
    lia.
  (* return from find_bucket *)
  - inv CONT. 
    + inv CONT0.
      split.
      * do 2 right. do 2 eexists.
        econstructor.
      * intros. inv H.
        (* return to hmap_process *)
        eapply hmap_operate_on_internal2 with (n:= 0%nat).
        2: econstructor. reflexivity.
        eauto. auto. eauto. lia. auto. simpl. auto. auto. lia.
    (* return to hmap_set *)
    + inv CONT0. 
      split.
      * do 2 right. do 2 eexists.
        econstructor.
      * intros. inv H.
        (* return to hmap_process *)
        eapply hmap_set_inv. eapply hmap_set_internal2 with (n:=0%nat).
        econstructor. eauto. reflexivity. reflexivity.
        simpl. auto. eauto. lia. auto. lia.
Qed.
      
End SOUNDNESS.

Local Open Scope inv_scope.
(* Module total safety of hash_map_prog *)

(* ⟦hmap.c⟧ ⊩ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc
             ↠ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} *)
Lemma hash_map_module_safe:
  module_type_safe ((hmap_ext_inv @@ rs_own) @! cc_rust_c) (hmap_int_inv 10%nat) hash_map_sem SIF.
Proof.
  red. econstructor.
  (* cannot specify msafek_invariant for unknown reason *)
  eapply (Module_type_safe_components li_c li_c hash_map_sem ((hmap_ext_inv @@ rs_own) @! cc_rust_c) (hmap_int_inv 10%nat) SIF (fun se w s => sound_state 10%nat se w s)).
  intros se w SYMB VSE.
  destruct SYMB as (SEEQ & WF).
  econstructor.
  (* preservation *)
  - intros. eapply step_preservation_progress; eauto.
  (* progress *)
  - intros. left. eapply step_preservation_progress; eauto.
  (* initial safe *)
  - intros. eapply initial_preservation_progress; eauto.
  (* external safe *)
  - intros.
    exploit hash_map_external. reflexivity.
    eauto. eauto. eauto.
    intros (wI & w_rs1 & q_rs & A1 & A2 & A3 & A4 & A5).
    rewrite <- A4 in *.
    exists ((wI, (se, w_rs1)), tt).
    repeat apply conj.
    + econstructor. split.
      econstructor; eauto.
      econstructor. reflexivity. eauto.
      rewrite A4. reflexivity.
      econstructor.
    + econstructor. split; eauto.
      econstructor. eauto.
      eauto.
    + intros. inv H1. inv H2. inv H1. inv H4. inv H1.
      eapply A5; eauto.
  (* final state *)
  - intros. eapply final_progress; eauto.
Qed.
