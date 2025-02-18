Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop Ctypes Ctypesdefs.
Require Import Values Globalenvs Memory.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import Clight HashMap LinkedList HashMapCommon.
Require Import Separation.
Require Import MoveCheckingFootprint MoveCheckingDomain.

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


Section SOUNDNESS.

Variable N : nat.

Context (se : Genv.symtbl).
Context (w: hmap_world).

Let ge := globalenv se hash_map_prog.

Let Ni := nat_to_int N.

Hypothesis Neq10: N = 10%nat.

Lemma Nieq : Ni = Int.repr 10.
Proof.
  unfold Ni. rewrite Neq10.
  reflexivity.
Qed.

(** Combine it with the wf_senv in LinkedListSafe *)
Hypothesis wf_senv: forall id,
    if in_dec ident_eq id (prog_defs_names hash_map_prog) then
      exists b, Genv.find_symbol se id = Some b
    else True.

Remark hmap_ce: genv_cenv ge = PTree.empty composite.
  reflexivity. Qed.

Definition ll_ce := Rusttypes.prog_comp_env LinkedList.linked_list_mod.

Definition bucket_val_pred m fp v :=
  if Val.eq v Vnullptr then
    fp = fp_emp
  else
    sem_wt_val ll_ce m fp v /\ wt_footprint ll_ce List_box fp.
    
Program Definition bucket_pred (b: block) (pos: Z) (fp: footprint) : massert :=
  {| m_pred m := m |= contains Mptr b pos (bucket_val_pred m fp);
    m_footprint b1 ofs1 := (b = b1 /\ pos <= ofs1 < pos + size_chunk Mptr)
                           \/ In b1 (footprint_flat fp); |}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

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


Lemma hmap_pred_rec_split: forall k n,
    (k < n)%nat ->
    forall fpl b pos,
      length fpl = n ->
      massert_imp (hmap_pred_rec n fpl b pos)
        (hmap_pred_rec k (firstn k fpl) b pos
           ** bucket_pred b (pos + (size_chunk Mptr * (Z.of_nat k))) (nth k fpl fp_emp)
           ** hmap_pred_rec (n - 1 - k) (skipn (S k) fpl) b (pos + size_chunk Mptr * (Z.of_nat k) + size_chunk Mptr)).
Proof.
  induction k.
  - intros. destruct n; try lia.
    simpl. destruct fpl; inv H0. simpl.
    etransitivity. eapply sepconj_morph_1.
    instantiate (1 := pure True ** bucket_pred b pos f).
    red. split. intros. eapply sep_pure. auto.
    intros. simpl in H0. destruct H0; try contradiction. auto.
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
    eapply sepconj_morph_1. reflexivity.
    eapply IHk. lia. auto.
    rewrite !skipn_cons.
    replace (S (Datatypes.length fpl) - 1 - S k)%nat with (length fpl - 1 - k)%nat.
    replace ((pos + size_chunk Mptr * Z.of_nat (S k))) with ((pos + size_chunk Mptr + size_chunk Mptr * Z.of_nat k)).
    replace (nth (S k) (f :: fpl) fp_emp) with (nth k fpl fp_emp) by auto.
    eapply sep_assoc.
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

(* Pre-condition of hmap_operate_on function *)
(** We should not make hmap_operate_on an external function because
its pre-condition of the hmap argument is not compatible with rs_own
because it cannot be called from Rust side. The rust module cannot
instantiate a value with type hmap_ty. One way to resolve this problem
is that prove manually {I'}M[..] refining {I@@rs_own}M[..] where I' is
a more dedicated condition that distinguish the call to
hmap_operate_on or process and then use different conditions. *)


(* state invariant *)

Definition return_find_bucket_cont k :=
  (Kseq
     (Sifthenelse
        (Ebinop Oeq (Ederef (Evar buk List_box_ptr) List_ptr)
           (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint) 
        (Sreturn None)
        (Ssequence
           (Scall (Some tmp)
              (Evar find
                 (Tfunction (Tcons List_ptr (Tcons tint Tnil)) List_ptr cc_default))
              [Ederef (Evar buk List_box_ptr) List_ptr; Evar key tint])
           (Sassign (Ederef (Evar buk List_box_ptr) List_ptr) (Evar tmp List_ptr)))) k).

(* The continuation (that inside Kcall) of calling find_bucket. The
caller can be hmap_operate_on, hmap_set, hmap_remove. It outputs a
predicate which describe the contents of hmap_operate_on. [b] is the
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
(* from hmap_operate_on *)
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

Inductive call_hmap_operate_on: state -> Prop :=
| call_hmap_operate_on_intro: forall b1 b2 kv k m fpl
    (SYM: Genv.invert_symbol se b1 = Some hmap_operate_on)
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
    (RAN: (0<= n <=1)%nat),
    sound_state s
(* return from find_bucket *)
| hmap_operate_on_internal2: forall t s1 s2 n idx fpl1 fpl2 b fp m ofs k b_hmap b_key ki
    (SEQ: s1 = (State hmap_operate_on_func Sskip (return_find_bucket_cont k)
                  (PTree.set key (b_key, tint) (PTree.set hmap (b_hmap, hmap_ty) empty_env))
                  (set_opttemp (Some buk)
                     (Vptr b (Ptrofs.mul (Ptrofs.repr (size_chunk Mptr)) (Ptrofs.of_int idx)))
                     (PTree.set buk Vundef (PTree.set tmp Vundef (PTree.empty Values.val)))) m))
    (STAR: starNf step1 num_frames ge n s1 t s2)
    (MPRED: m |= contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b (Ptrofs.unsigned ofs) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (Ptrofs.unsigned ofs + size_chunk Mptr)
              (* stack frame *)
              ** contains Mptr b_hmap 0 (eq (Vptr b Ptrofs.zero))
              ** contains Mint32 b_key 0 (eq (Vint ki)))
    (RAN: (0 <= n <= 10)%nat),
    sound_state s2
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
    (RAN: (0 <= n <= 1)%nat),
    sound_state s
(* at_external state calling hash function in the Rust side *)
| find_bucket_call_hash: forall ki b k m MP
    (COND: hash_pre_cond_args Ni [Vint ki; Vint Ni])
    (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some hash_ext)
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
    (RAN: (0 <= n <= 1)%nat),
    sound_state s
| find_bucket_returnstate: forall idx fpl1 fpl2 b fp m ofs k MP
    (OFSEQ: ofs = (Ptrofs.mul (Ptrofs.repr (size_chunk Mptr)) (Ptrofs.of_int idx)))
    (MPRED: m |= contains Mptr b (-size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr (Z_of_nat N * size_chunk Mptr))))
              ** hmap_pred_rec (int_to_nat idx) fpl1 b 0
              ** bucket_pred b (Ptrofs.unsigned ofs) fp
              ** hmap_pred_rec (N - 1 - (int_to_nat idx))%nat fpl2 b (Ptrofs.unsigned ofs + size_chunk Mptr)
              ** MP)
    (CONT: call_find_bucket_cont b k MP),
    sound_state (Returnstate (Vptr b ofs) k m)
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


  
Lemma step_preservation_progress: forall s,
    sound_state s ->
    not_stuck (hash_map_sem se) s
    /\ (forall s' t, step1 ge s t s' ->
               sound_state s').
Proof.
  intros s INV. inv INV.
  (* call hmap_operate_on *)
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
      reflexivity. reflexivity. econstructor. lia.
  (* hmap_operate_on_internal1 *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hmap_operate_on_internal1 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        inv H; simpl; auto. }
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
  (** TODO: hmap_operate_on after returning from find_bucket *)
  - admit.
  (* return from hmap_operate_on *)
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
      econstructor. lia.
  (* find_bucket_internal1  *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_bucket_internal1 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        inv H; simpl; auto. }
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
        simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
        rewrite Genv.find_def_spec.
        erewrite Genv.find_invert_symbol; eauto.
        reflexivity. 
        (* cont *)
        econstructor. eauto. }
    lia.
  (* call hash function *)
  - split.
    + right. left. eexists.
      econstructor. eauto.
    + intros.  inv H; rewrite FINDF in FIND; inv FIND.
      inv H6.
  (* return from hash function *)
  - inv COND. inv CONT.
    split.
    + do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H.
      eapply find_bucket_internal2; eauto.
      econstructor.
  (* execution after returning from hash *)
  - generalize MPRED as MPRED1. intros.
    generalize STAR as STAR1. intros.
    inv STAR.
    { split.
      - red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_bucket_internal2 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        inv H; simpl; auto. }
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
        eapply find_bucket_returnstate with (fpl1:=fpl1) (fp:= fp) (fpl2:= fpl2). reflexivity.
        assert (OFSEQ: (Ptrofs.unsigned
                          (Ptrofs.mul (Ptrofs.repr (size_chunk Mptr)) (Ptrofs.of_intu r)))
                       = (size_chunk Mptr) * (Int.unsigned r)).
        { admit. }
        setoid_rewrite OFSEQ.
        instantiate (1 := MP). eapply sep_assoc5.
        eapply sep_imp with (Q' := MP). eapply MP2.        
        eapply sepconj_morph_1. reflexivity.
        replace (Int.unsigned r) with (Z.of_nat (int_to_nat r)) by admit.
        eapply hmap_pred_rec_split. admit.
        eapply hmap_pred_fpl_length. eapply MP2.        
        reflexivity.
        erewrite <- call_find_bucket_cont_eq_call_cont; eauto. }
    lia.
  (* return from find_bucket *)
  - inv CONT. inv CONT0.
    split.
    + do 2 right. do 2 eexists.
      econstructor.
    + intros. inv H.
      (* return to hmap_operate_on *)
      eapply hmap_operate_on_internal2 with (n:= 0%nat). reflexivity.
      econstructor. eauto. lia.
    
  Admitted.
      
End SOUNDNESS.

