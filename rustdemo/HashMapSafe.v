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

Local Open Scope error_monad_scope.
Local Open Scope sep_scope.
Import ListNotations.

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

(* Clight evaluation of expression is deterministic *)
Lemma eval_expr_det: forall ge e le m a v1 v2,
    eval_expr ge e le m a v1 ->
    eval_expr ge e le m a v2 ->
    v1 = v2.
Admitted.

Lemma eval_exprlist_det: forall ge e le m al tyl vl1 vl2,
    eval_exprlist ge e le m al tyl vl1 ->
    eval_exprlist ge e le m al tyl vl2 ->
    vl1 = vl2.
Admitted.

(* Separation predicate of bucket *)

Definition ll_ce := Rusttypes.prog_comp_env LinkedList.linked_list_mod.

Lemma ll_ce_composite_members_norepet:  forall id co,
    ll_ce ! id = Some co -> list_norepet (MoveChecking.name_members (Rusttypes.co_members co)).
Proof.
  intros.
  assert (P: PTree_Properties.for_all ll_ce (fun id co => proj_sumbool (list_norepet_dec ident_eq (MoveChecking.name_members (Rusttypes.co_members co)))) = true).
  { reflexivity. }
  eapply PTree_Properties.for_all_correct in P; eauto.
  eapply proj_sumbool_true. eapply P.
Qed.

Inductive bucket_val_spec m fp : Values.val -> Prop :=
| bucket_val_spec_intro: forall v
    (WTVAL: sem_wt_val ll_ce m fp v)
    (WTFP: wt_footprint ll_ce List_box fp)
    (NOREP: list_norepet (footprint_flat fp))
    (CASTED: RustOp.val_casted v List_box),
    bucket_val_spec m fp v.
      
Definition bucket_val_pred m fp v :=
  if Val.eq v Vnullptr then
    fp = fp_emp
  else
    bucket_val_spec m fp v.


  
Remark sizeof_List_ty: Rusttypes.sizeof ll_ce List_ty = 24.
  reflexivity. Defined.

Lemma bucket_val_spec_unchanged_on: forall m1 m2 fp v,
    Mem.unchanged_on (fun b _ => In b (footprint_flat fp)) m1 m2 ->
    bucket_val_spec m1 fp v ->
    bucket_val_spec m2 fp v.
Proof.
  intros until v. intros UNC PRED.  
  inv PRED. econstructor; eauto.
  eapply sem_wt_val_unchanged_blocks. eauto.
  eapply Mem.unchanged_on_implies. eauto.
  intros. simpl.
  inv WTFP. inv WTVAL. simpl in WF. congruence.
  rewrite sizeof_List_ty in *. inv WTVAL.
  simpl in H. simpl. destruct H; try contradiction; eauto.
  destruct H; try contradiction; eauto.
Qed.  


Lemma bucket_val_pred_unchanged_on: forall m1 m2 fp v,
    Mem.unchanged_on (fun b _ => In b (footprint_flat fp)) m1 m2 ->
    bucket_val_pred m1 fp v ->
    bucket_val_pred m2 fp v.
Proof.
  intros until v. intros UNC PRED.
  unfold bucket_val_pred in *. destruct Val.eq; auto.
  eapply bucket_val_spec_unchanged_on; eauto.
Qed.
  
Program Definition bucket_pred (b: block) (pos: Z) (fp: footprint) : massert :=
  {| m_pred m := m |= contains Mptr b pos (bucket_val_pred m fp)
                   (* disjointness: it is necessary because the
                   rely-guarantee of rs_own ensure that the footprint
                   outside fp is unchanged. Without this condition,
                   the contents of the bucket may be changed *)
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
    + eapply bucket_val_pred_unchanged_on.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. right. auto. auto.
Defined.
Next Obligation.
  destruct H0.
  - destruct H0; subst.
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies. eauto. constructor.
  - unfold bucket_val_pred in H6. destruct Val.eq in H6; subst.
    + inv H0.
    + inv H6.
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

Section SOUNDNESS.

Variable N : nat.

Context (se : Genv.symtbl).
(* Context (w: hmap_world). *)

Let ge := globalenv se hash_map_prog.

Let Ni := nat_to_int N.

Hypothesis Neq10: N = 10%nat.

Lemma Nieq : Ni = Int.repr 10.
Proof.
  unfold Ni. rewrite Neq10.
  reflexivity.
Qed.

(** Combine it with the wf_senv in LinkedListSafe *)
Hypothesis wf_senv: wf_senv se.

Remark hmap_ce: genv_cenv ge = PTree.empty composite.
  reflexivity. Qed.



Fixpoint hmap_pred_rec (num: nat) (fpl: list footprint) (b: block) (pos: Z) : massert :=
  match num, fpl with
  | O, nil => pure True
  | S num', fp :: fpl' =>
      bucket_pred b pos fp ** hmap_pred_rec num' fpl' b (pos + size_chunk Mptr)
  | _, _ =>
      pure False
  end.

(* [m|= (hmap_pred b fpl)] means that the memory contents in block b is
the list of the buckets occupying the footprint fpl *)
Definition hmap_pred (b: block) (fpl: list footprint) : massert :=
  contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
    ** hmap_pred_rec N fpl b 0.

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
  
Lemma hmap_pred_fpl_length: forall m b fpl,
    m |= hmap_pred b fpl ->
    length fpl = N.
Admitted.

Lemma sep_assoc5: forall A1 A2 A3 A4 A5 m,    
    m |= (A1 ** A2 ** A3 ** A4) ** A5 ->
    m |= A1 ** A2 ** A3 ** A4 ** A5.
Admitted.
    
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

(* The continuation (that inside Kcall) of calling find_bucket. The
caller can be hmap_process, hmap_set, hmap_remove. It outputs a
predicate which describe the contents of hmap_process. [b] is the
block storing the hash_map *)
Inductive call_find_bucket_from_operate_on (b: block) : cont -> massert -> Prop :=
| call_find_bucket_from_operate_on_intro: forall k e le b_hmap b_key ki
    (ENV: e = PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
    (LENV: le = create_undef_temps (fn_temps hmap_operate_on_func)),
    call_find_bucket_from_operate_on b (Kcall (Some buk) hmap_operate_on_func e le (return_find_bucket_cont k))
                                     (contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
                                        ** contains Mint32 b_key 0 (eq (Vint ki)))
.

Inductive call_find_bucket_cont (b: block) : cont -> massert -> Prop :=
(* from hmap_process *)
| call_find_bucket_cont_intro1: forall k MP
    (CONT: call_find_bucket_from_operate_on b k MP),
    call_find_bucket_cont b k MP
(* TODO: from hmap_set *)
.

Lemma call_find_bucket_cont_eq_call_cont: forall b k MP,
    call_find_bucket_cont b k MP ->
    k = call_cont k.
Admitted.

(* [b] is the block storing the hash map. The returned massert
specifies the stack contents in find_bucket and the contents in the
caller of find_bucket *)
Inductive call_hash_cont : cont -> massert -> Prop :=
| call_hash_cont_intro: forall k MP b_key b_hmap ki b fpl
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
| call_find_cont_intro: forall k idx fpl1 fpl2 b b_hmap b_key ki vspec,
    call_find_cont (Kcall (Some tmp) hmap_operate_on_func
       (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
       (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)))
          (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val))))
       (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr))
          k))
      (* The bucket location we load *)
      (contains Mptr b ((size_chunk Mptr) * (Int.unsigned idx)) vspec
        ** contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
         ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
         ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
         (* stack frame *)
         ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
         ** contains Mint32 b_key 0 (eq (Vint ki))).

Inductive call_hmap_operate_on: state -> Prop :=
| call_hmap_operate_on_intro: forall b1 b2 kv k m fpl
    (SYM: Genv.invert_symbol se b1 = Some hmap_process)
    (** TODO: specify the cont *)
    (HMAP: m |= hmap_pred b2 fpl),
    call_hmap_operate_on (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m).

Inductive call_find_bucket: state -> Prop :=
| call_find_bucket_intro: forall b1 b2 kv k m fpl MP
    (SYM: Genv.invert_symbol se b1 = Some find_bucket)
    (CONT: call_find_bucket_cont b2 k MP)
    (* MP is the predicate for the stack frames *)
    (HMAP: m |= hmap_pred b2 fpl ** MP),
    call_find_bucket (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m).
 

Inductive sound_state : state -> Prop :=
| hmap_operate_on_callstate: forall b1 b2 kv k m
    (CALL: call_hmap_operate_on (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)),
    sound_state (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)
| hmap_operate_on_internal1: forall t s b_hmap b_key fpl ki b m e le k n
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl)
    (ENV: e = PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
    (LENV: le = create_undef_temps (fn_temps hmap_operate_on_func))
    (STAR: starNf step1 num_frames ge n (State hmap_operate_on_func (fn_body hmap_operate_on_func) k e le m) t s)
    (NOTCALLRET: not_call_return_state s)
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
    (MPRED: m |= contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b ((size_chunk Mptr) * (Int.unsigned idx)) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (((size_chunk Mptr) * (Int.unsigned idx)) + size_chunk Mptr)
              (* stack frame *)
              ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki)))
    (MAXRAN: Int.unsigned idx < (Z.of_nat N))
    (NOTCALLRET: not_call_return_state s2)
    (RAN: (0 <= n <= 10)%nat),
    sound_state s2
| hmap_operate_on_call_find: forall m k MP fp ki bf v
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (FINDSYM: Genv.invert_symbol se bf = Some find)
    (CONT: call_find_cont k MP)
    (SUP: Mem.sup_include (footprint_flat fp) (Mem.support m)),
    (** TODO: specify the query_inv of (I @@ rs_own) *)
    sound_state (Callstate (Vptr bf Ptrofs.zero) [v; Vint ki] k m)
| hmap_operate_on_return_find: forall m k MP fp v
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (CONT: call_find_cont k MP),
    sound_state (Returnstate v k m)
(* execution after returning from find *)
| hmap_operate_on_internal3: forall k idx fpl1 fpl2 b b_hmap b_key ki vspec s0 t s m fp MP n v
    (SEQ: s0 = (State hmap_operate_on_func Sskip
                  (Kseq (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)) k) (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (set_opttemp (Some tmp) v (PTree.set buk (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx))) (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))))
                  m))
    (MPEQ: MP = contains Mptr b (size_chunk Mptr * Int.unsigned idx) vspec **
              contains Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z.of_nat N * size_chunk Mptr)))) **
              hmap_pred_rec (int_to_nat idx) fpl1 b 0 **
              hmap_pred_rec (N - 1 - int_to_nat idx) fpl2 b (size_chunk Mptr * Int.unsigned idx + size_chunk Mptr) **
              contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero)) **
              contains Mint32 b_key 0 (eq (Vint ki)))
    (MPRED: m |= MP)
    (DISJOINT: forall b ofs, m_footprint MP b ofs -> In b (footprint_flat fp) -> False)
    (VSPEC: bucket_val_spec m fp v)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0 <= n <= 3)%nat),
    sound_state s
(*     sound_state s *)
| hmap_operate_on_returnstate: forall k m,
    (** TODO: specify the cont *)
    sound_state (Returnstate Vundef k m)
| find_bucket_callstate: forall b1 b2 kv k m
    (CALL: call_find_bucket (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)),
    sound_state (Callstate (Vptr b1 Ptrofs.zero) [Vptr b2 Ptrofs.zero; Vint kv] k m)
| find_bucket_internal1: forall s0 t s n b_key b_hmap m k b fpl ki MP
    (SEQ: s0 = (State find_bucket_func (fn_body find_bucket_func) k
                  (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (create_undef_temps (fn_temps find_bucket_func)) m))
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl
              ** MP)
    (CONT: call_find_bucket_cont b k MP)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0 <= n <= 1)%nat),
    sound_state s
(* at_external state calling hash function in the Rust side *)
| find_bucket_call_hash: forall ki b k m MP
    (COND: hash_pre_cond_args Ni [Vint ki; Vint Ni])
    (FINDSYM: Genv.invert_symbol se b = Some hash)
    (CONT: call_hash_cont k MP)
    (MPRED: m |= MP),
    sound_state (Callstate (Vptr b Ptrofs.zero) [Vint ki; Vint Ni] k m)
| find_bucket_return_hash: forall v k m MP
    (COND: hash_post_cond_retv Ni v)
    (CONT: call_hash_cont k MP)
    (MPRED: m |= MP),
    sound_state (Returnstate v k m)
| find_bucket_internal2: forall s0 t s n b_key b_hmap m k b fpl ki MP r
    (SEQ: s0 = (State find_bucket_func Sskip
                  (Kseq (Sreturn (Some (Ebinop Oadd (Evar hmap List_box_ptr) (Etempvar index tuint) List_box_ptr))) k) (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env)) (set_opttemp (Some index) (Vint r) (PTree.set index Vundef (PTree.empty Values.val))) m))
    (INRAN: Int.ltu r Ni = true)
    (MPRED: m |= contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki))
              ** hmap_pred b fpl
              ** MP)
    (CONT: call_find_bucket_cont b k MP)
    (STAR: starNf step1 num_frames ge n s0 t s)
    (NOTCALLRET: not_call_return_state s)
    (RAN: (0 <= n <= 1)%nat),
    sound_state s
| find_bucket_returnstate: forall idx fpl1 fpl2 b fp m k MP
    (MPRED: m |= contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b (size_chunk Mptr * Int.unsigned idx) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b ((size_chunk Mptr * Int.unsigned idx) + size_chunk Mptr)
              ** MP)
    (MAXRAN: Int.unsigned idx < Z.of_nat N)
    (CONT: call_find_bucket_cont b k MP),
    sound_state (Returnstate (Vptr b (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx))) k m)
.


Lemma function_entry1_det: forall ge f vl m m1 m2 e1 le1 e2 le2,
    function_entry1 ge f vl m e1 le1 m1 ->
    function_entry1 ge f vl m e2 le2 m2 ->
    e1 = e2 /\ le1 = le2 /\ m1 = m2.
Admitted.

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


(* Soundness of at_external, using (I @@ rs_own @! cc_rust_c) as the interface *)

Definition find_rs_sig :=
  mksignature nil nil [List_box; Rusttypes.type_int32s] List_box cc_default ll_ce.

Definition hash_rs_sig :=
  mksignature nil nil [Rusttypes.type_int32s; type_int32u] type_int32u cc_default ll_ce.

Lemma hash_map_external: forall s q,
    sound_state s ->
    at_external ge s q ->
    exists wI w_rs q_rs,
      cc_rust_c_mq q_rs q
      /\ vq_hash_map wI q_rs
      /\ rs_own_query w_rs q_rs
      /\ wI.(hmap_senv) = se
      /\ forall r_rs r_c,
        vr_hash_map wI r_rs ->
        (* kripke relation *)
        (exists w_rs', rsw_acc w_rs w_rs' /\ rs_own_reply w_rs' r_rs) ->
        cc_rust_c_mr r_rs r_c ->
        (exists s', after_external s r_c s'
               /\ (forall s', after_external s r_c s' -> sound_state s')).
Proof.
  intros s q_c SINV ATEXT. inv ATEXT. unfold f in *.
  inv SINV; try simpl in NOTCALLRET; try contradiction.
  - inv CALL. 
    assert (FIND: Genv.find_funct ge (Vptr b1 Ptrofs.zero) = Some (Internal hmap_operate_on_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    rewrite H in FIND. inv FIND.
  (* call find *)
  - exists (Build_hmap_world (inl find) se (nat_to_int N)),
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
      eapply vq_hash_map_intro1 with (f:= find_func).
      eapply FINDFUN2.
      simpl. unfold Genv.is_internal.
      simpl in FINDFUN1. setoid_rewrite FINDFUN1. auto.
      reflexivity. reflexivity.
      (* casted *)
      econstructor.
      inv VSPEC. auto.
      econstructor. econstructor. auto.
      econstructor.
      eauto.
      (* pre-cond *)
      econstructor. 
      reflexivity. reflexivity. reflexivity.
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
    + intros ? ? A1 A2 A3. inv A1.
      2: { inv FIDEQ. }
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
      econstructor; eauto.
      econstructor. 
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
    exists (Build_hmap_world (inl hash) se (nat_to_int N)),
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
      replace [Rusttypes.type_int32s; type_int32u] with (type_list_of_typelist (Rusttypes.Tcons Rusttypes.type_int32s (Rusttypes.Tcons type_int32u Rusttypes.Tnil))).
      eapply vq_hash_map_intro1 with (f:= hash_func).
      eapply FINDFUN2.
      simpl. unfold Genv.is_internal.
      simpl in FINDFUN1. setoid_rewrite FINDFUN1. auto.
      vm_compute.
      reflexivity. reflexivity.
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
      reflexivity. reflexivity. reflexivity.
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
    + intros ? ? A1 A2 A3. inv A1.
      2: { inv FIDEQ. }
      destruct A2 as (w_rs' & ACC & A2). inv A2.
      inv A3.
      eexists. split.
      econstructor.
      intros s' AFEXT. inv AFEXT.
      inv CONT.
      inv ACC.
      eapply find_bucket_return_hash.
      (* post conditions *)
      inv FIDEQ. eauto.
      (* cont *)
      econstructor. eauto.
      eapply m_invar. eauto.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. auto.
Qed.


Lemma step_preservation_progress: forall s,
    sound_state s ->
    not_stuck (hash_map_sem se) s
    /\ (forall s' t, step1 ge s t s' ->
               sound_state s').
Proof.
  intros s INV. inv INV.
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
      reflexivity. reflexivity. econstructor.
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
    { generalize (wf_senv find_bucket). intros FINDF.
      simpl in FINDF. destruct FINDF as (?b & FINDF).
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
        reflexivity.
        eapply sep_comm. rewrite sep_assoc.
        eapply MPRED1. } 
    lia.
    
  (** TODO: hmap_process after returning from find_bucket *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    admit.
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
      replace (Rusttypes.sizeof ll_ce List_ty) with 24 in WTVAL by reflexivity.
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
           eapply hmap_pred_rec_split with (k := length fpl1). admit.
           admit. }
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
      admit. 1-3: lia. }      
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
        eapply hmap_operate_on_returnstate. }
    inv STEP.
    1,3: destruct H7; congruence.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    simpl in NOTCALLRET. contradiction.
    (* contradiction for the frames numbers *)
    admit. }

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
      generalize (wf_senv find). intros FINDF.
      simpl in FINDF. destruct FINDF as (?b & FINDF).
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
          econstructor.
          (* sup_include *)
          red. intros.
          eapply m_valid. eapply MPRED1.
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
  (* execution after returning from find *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (size_chunk Mptr * Int.unsigned idx)) =
                     (size_chunk Mptr * Int.unsigned idx)).
    admit.
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
        reflexivity. reflexivity. eapply MPRED1. eauto. eauto.
        eapply starNf_step_right; eauto.
        1-2: inv H; simpl; auto. lia. }
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
    { admit. }    
    inv STAR; cbn [num_frames num_frames_cont] in *.    
    (* return from hmap_process (we need to specify the cont of hmap_process) *)
    admit.
    admit.

  (*  TODO: show returnstate in hmap_process is not stuck. We
    need to specify the continuation. *)
  - admit.
    
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
      eapply find_bucket_internal1 with (n:=0%nat). reflexivity. eauto. eauto.
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
    { generalize (wf_senv hash). intros FINDF.
      simpl in FINDF. destruct FINDF as (?b & FINDF).
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
          admit. admit. }
        setoid_rewrite OFSEQ.
        eapply find_bucket_returnstate with (fpl1:=fpl1) (fp:= fp) (fpl2:= fpl2). 
        instantiate (1 := MP). eapply sep_assoc5.
        eapply sep_imp with (Q' := MP). eapply MP2.        
        eapply sepconj_morph_1. reflexivity.
        replace (Int.unsigned r) with (Z.of_nat (int_to_nat r)) by admit.
        eapply hmap_pred_rec_split. admit.
        eapply hmap_pred_fpl_length. eapply MP2.        
        reflexivity. admit.
        erewrite <- call_find_bucket_cont_eq_call_cont; eauto. }
    lia.
  (* return from find_bucket *)
  - inv CONT. inv CONT0.
    split.
    + do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H.
      (* return to hmap_process *)
      eapply hmap_operate_on_internal2 with (n:= 0%nat).
      2: econstructor. reflexivity.
      eauto. lia. simpl. auto. lia.
    
  Admitted.
      
End SOUNDNESS.

Local Open Scope inv_scope.
(* Module total safety of hash_map_prog *)

Lemma hash_map_module_safe:
  module_type_safe ((hmap_inv @@ rs_own) @! cc_rust_c) ((hmap_inv @@ rs_own) @! cc_rust_c) hash_map_sem SIF.
Proof.
  red. econstructor.
  (* cannot specify msafek_invariant for unknown reason *)
  eapply (Module_type_safe_components li_c li_c hash_map_sem ((hmap_inv @@ rs_own) @! cc_rust_c) ((hmap_inv @@ rs_own) @! cc_rust_c) SIF (fun se w => sound_state 10%nat se)).
  intros se ((w_hm, (?, w_rs)) & ?) SYMB VSE.
  inv SYMB. destruct H. inv H0. inv H.
  inv H0. inv H1. rename H2 into SYM1.
  econstructor.
  (* preservation *)
  - intros. eapply step_preservation_progress; eauto.
  (* progress *)
  - intros. left. eapply step_preservation_progress; eauto.
  (* initial safe *)
  - admit.
  (* external safe *)
  - intros.
    exploit hash_map_external. reflexivity.
    eauto. eauto.
    intros (wI & w_rs1 & q_rs & A1 & A2 & A3 & A4 & A5).
    rewrite <- A4 in *.
    exists ((wI, ((hmap_senv w_hm), w_rs1)), tt).
    repeat apply conj.
    + econstructor. split.
      econstructor; eauto.
      econstructor. reflexivity. eauto.
      rewrite A4. econstructor.
      econstructor.
    + econstructor. split; eauto.
      econstructor. eauto.
      eauto.
    + intros. inv H1. inv H2. inv H1. inv H4. inv H1.
      eapply A5; eauto.
  (* final state *)
  - admit.
Admitted.

