Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LinkedList.
Require Import Values Globalenvs Memory.
Require Import InitDomain.
Require Import Events.
Require Import Smallstep Rustlightown SmallstepLinkingSafe.
Require Import Separation.

Local Open Scope error_monad_scope.
Import ListNotations.

(* starN inside a function *)
Fixpoint num_frames_cont (k: cont) : nat :=
  match k with
  | Kstop => O
  | Kcall _ _ _ _ k' =>
      S (num_frames_cont k')
  | Kseq _ k
  | Kloop _ k
  | Kdropinsert _ _ k
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k
  | Klet _ _ k => num_frames_cont k
  end.

Definition num_frames (s: state) : nat :=
  match s with
  | State _ _ k _ _ _
  | Callstate _ _ k _
  | Returnstate _ k _
  | Dropinsert _ _ _ k _ _ _
  | Dropplace _ _ _ k _ _ _
  | Dropstate _ _ _ _ k _ => num_frames_cont k
  end.
              


Section CLOSURES.

Context {genv: Type}.
Context {state: Type}.

Variable step: genv -> state -> trace -> state -> Prop.
Variable numf: state -> nat.

Inductive starNf (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starNf_refl: forall s,
      starNf ge O s E0 s
  | starNf_step: forall n s t t1 s' t2 s''
      (STEP: step ge s t1 s')
      (STAR: starNf ge n s' t2 s'')
      (TRACE: t = t1 ** t2)
      (FEQ: numf s = numf s'),
      starNf ge (S n) s t s''.

Remark starNf_star:
  forall ge n s t s', starNf ge n s t s' -> star step ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark starNf_step_right ge: forall n s t t1 s' t2 s'',
    starNf ge n s t1 s' -> step ge s' t2 s'' -> t = t1 ** t2 ->
    numf s' = numf s'' ->
    starNf ge (S n) s t s''.
Admitted.

End CLOSURES.

Definition linked_list_sem := semantics linked_list_mod.

(* The kripke world used in proving partial safety *)
Record linked_list_world :=
  { hash_range : int }.

Section SOUNDNESS.

Context (se : Genv.symtbl).
Context (w: linked_list_world).

Let ge := globalenv se linked_list_mod.

Hypothesis wf_senv: forall id,
    if in_dec ident_eq id (prog_defs_names linked_list_mod) then
      exists b, Genv.find_symbol se id = Some b
    else True.

(** Local state of find function *)

Definition own_env_find t E1 E2 :=
  mkown
    (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) t)
    (add_place_list t (places_of_locals (fn_params find_func ++ fn_vars find_func)) (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) t))
    t
    E1 E2.
    (* (fun id : positive => Rustlightown.init_own_env_obligation_1 find_func t E id) *)
    (* (fun id : positive => Rustlightown.init_own_env_obligation_2 find_func t E id). *)

(* b0-b3 are blocks allocated for the parameters and variables in find
function *)
Definition find_env b0 b1 b2 b3 b4 :=
  (PTree.set tmp (b4, List_box)
     (PTree.set node (b3, Node_ty)
        (PTree.set _retv (b2, List_box)
           (PTree.set LinkedList.k (b0, type_int32s)
              (PTree.set l (b1, List_box) empty_env))))).


Definition return_find_cont (e: env) t E1 E2 k :=
  (Kcall
     (Plocal tmp List_box)
     find_func
     e
     (move_place_list
        (own_transfer_assign
           (move_place
              (init_place
                 (init_place
                    (own_env_find t E1 E2)
                    (Plocal l List_box))
                 (Plocal LinkedList.k type_int32s))
              (Pderef (Plocal l List_box) List_ty))
           (Plocal node Node_ty))
        (moved_place_list
           [Emoveplace
              (Pfield (Plocal node Node_ty) next List_box)
              List_box;
            Epure
              (Eplace (Plocal LinkedList.k type_int32s) type_int32s)]))   
     (Kseq
        (Sassign (Pfield (Plocal node Node_ty) next List_box)
           (Emoveplace (Plocal tmp List_box) List_box))
        (Klet tmp List_box
           (Kseq
              (Ssequence
                 (Sassign_variant
                    (Pderef (Plocal l List_box) List_ty) List Cons
                    (Emoveplace (Plocal node Node_ty) Node_ty))
                 (Ssequence
                    (Sassign (Plocal _retv List_box)
                       (Emoveplace (Plocal l List_box) List_box))
                    (Sreturn (Plocal _retv List_box))))
              (Klet node Node_ty k))))).
  
(* The continuation when calling find function or returning from the
last find function *)
Inductive sound_find_cont : cont -> Prop :=
| sound_find_Kstop:
    sound_find_cont Kstop
| sound_find_Kcall: forall k b0 b1 b2 b3 b4 t E1 E2
    (CONT: sound_find_cont k)
    (UNI: collect_func ge find_func = OK t),                      
    sound_find_cont (return_find_cont (find_env b0 b1 b2 b3 b4) t E1 E2 k).


Definition return_process_cont (e: env) t E1 E2 k :=
  (Kcall
     (Pfield (Plocal node Node_ty) LinkedList.val type_int32s)
     find_func
     e
     (own_transfer_assign
        (move_place
           (init_place
              (init_place
                 (own_env_find t E1 E2)
                 (Plocal l List_box))
              (Plocal LinkedList.k type_int32s))
           (Pderef (Plocal l List_box) List_ty))
        (Plocal node Node_ty))
       (Kseq
          (Ssequence
             (Sassign_variant (Pderef (Plocal l List_box) List_ty) List
                Cons (Emoveplace (Plocal node Node_ty) Node_ty))
             (Ssequence
                (Sassign (Plocal _retv List_box)
                   (Emoveplace (Plocal l List_box) List_box))
                (Sreturn (Plocal _retv List_box))))
          (Klet node Node_ty k))).       


(* continuation of the returnstate in find function *)
Inductive find_cont_ret_process : cont -> Prop :=
(* return from process *)
| find_return_process: forall k t b0 b1 b2 b3 b4 E1 E2
    (CONT: sound_find_cont k)
    (UNI: collect_func ge find_func = OK t),
    find_cont_ret_process (return_process_cont (find_env b0 b1 b2 b3 b4) t E1 E2 k)
.

(** Local state of hash function *)

Inductive hash_cont: cont -> Prop :=
| hash_cont_intro: hash_cont Kstop.

(* pre-post conditions of hash function *)

Inductive hash_pre_cond_args : list val -> Prop :=
| hash_pre_cond_args_intro: forall k
    (GTZ: Int.ltu Int.zero w.(hash_range) = true)
    (CASTED1: val_casted (Vint k) type_int32s)
    (CASTED1: val_casted (Vint w.(hash_range)) type_int32u),
    hash_pre_cond_args [Vint k; Vint w.(hash_range)].

Inductive hash_post_cond_retv : val -> Prop :=
| hash_post_cond_retv_intro: forall r    
    (INRAN: Int.ltu r w.(hash_range) = true),
    hash_post_cond_retv (Vint r).
    
(** Continuation parameterized by the function name *)

Definition sound_cont (f: ident) : cont -> Prop :=
  if ident_eq f find then
    sound_find_cont
  else
    if ident_eq f hash then
      hash_cont
    else
      fun _ => False.

Definition length_of_args (f: ident) : nat :=
  if ident_eq f find then
    2
  else
    if ident_eq f hash then
      2     
  else O.

Inductive call_func (f: ident) : state -> Prop :=
| call_func_intro: forall b vl k m
    (* ensured by valid_query *)
    (SYM: Genv.invert_symbol se b = Some f)
    (** TODO: some property of k *)
    (SCONT: sound_cont f k)
    (ARGS: length vl = length_of_args f),
    call_func f (Callstate (Vptr b Ptrofs.zero) vl k m).


(* returnstate in find function *)
Inductive return_find : state -> Prop :=
| return_find_intro: forall k v m,
    sound_find_cont k ->
    return_find (Returnstate v k m).

Inductive return_process : state -> Prop :=
| return_process_intro: forall k v m
    (CONT: find_cont_ret_process k),
    return_process (Returnstate v k m).


Definition not_call_return_state s :=
  match s with
  | Callstate _ _ _ _
  | Returnstate _ _ _ => False
  | _ => True
  end.


Inductive sound_state : state -> Prop :=
(** callstate of hash function *)
| hash_callstate: forall v al k m
    (CALL: call_func hash (Callstate v al k m))
    (PRE: hash_pre_cond_args al),
    sound_state (Callstate v al k m)
| hash_state_internal: forall v al k m t s1 n
    (CALL: call_func hash (Callstate v al k m))
    (STAR: starNf step num_frames ge n (Callstate v al k m) t s1)
    (PRECOND: hash_pre_cond_args al)
    (NOTCALL: not_call_return_state s1)
    (RAN: (1 <= n <= 11)%nat),
    sound_state s1
| hash_returnstate: forall v k m
    (CONT: sound_cont hash k)
    (PRE: hash_post_cond_retv v),
    sound_state (Returnstate v k m)

| callstate_find: forall v al k m
    (CALL: call_func find (Callstate v al k m)),
    sound_state (Callstate v al k m)
| find_state_internal1: forall s0 s1 t n
    (CALL: call_func find s0)
    (STAR: starNf step num_frames ge n s0 t s1)
    (* used to prevent complicated reasoning in proving query/reply
    invariant in at_external state or final state *)
    (NOTCALL: not_call_return_state s1)
    (RAN: (1 <= n <= 20)%nat),
    sound_state s1
| find_state_call_process: forall vf al k m
    (PROC: Genv.find_funct ge vf = Some process_ext)
    (CONT: find_cont_ret_process k),
    sound_state (Callstate vf al k m)
| find_state_return_process: forall v k m
    (CONT: find_cont_ret_process k),
    sound_state (Returnstate v k m)
(* state comes from return process *)
| find_state_internal2: forall s0 s1 s2 t1 t2 n
    (RET: return_process s0)
    (* prevent num_frames inconsistent between s0 and s2 *)
    (STEP: step ge s0 t1 s1)
    (STAR: starNf step num_frames ge n s1 t2 s2)
    (NOTCALL: not_call_return_state s2)
    (RAN: (0 <= n <= 28)%nat),
    sound_state s2          
(* state comes from return find *)
| find_state_internal3: forall s0 s1 s2 t1 t2 n
    (RET: return_find s0)
    (* prevent num_frames inconsistent between s0 and s2 *)
    (STEP: step ge s0 t1 s1)
    (STAR: starNf step num_frames ge n s1 t2 s2)
    (NOTCALL: not_call_return_state s2)
    (RAN: (0 <= n <= 28)%nat),
    sound_state s2
(* This state can be return from the current find function or return
from the last find function *)
| find_returnstate: forall v k m,
    sound_find_cont k ->
    sound_state (Returnstate v k m)
.

Lemma find_args_params_norepet:
  list_norepet
    (var_names (fn_params find_func) ++ var_names (fn_vars find_func)).
Proof.
  eapply proj_sumbool_true.
  instantiate (1 := list_norepet_dec ident_eq (var_names (fn_params find_func) ++ var_names (fn_vars find_func))).
  auto.
Qed.


Lemma init_own_env_find_progress:
  exists own, init_own_env (Smallstep.globalenv (linked_list_sem se)) find_func = OK own.        
  unfold init_own_env.
  destruct collect_func eqn: A. cbn [bind].
  set (empty_map := (PTree.map
                       (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                          InitDomain.Paths.empty) t)) in *.
  set (initParams:= (InitDomain.add_place_list t
                       (places_of_locals (fn_params find_func ++ fn_vars find_func))
                       empty_map)) in *.
  set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
  generalize (eq_refl flag).             
  generalize flag at 1 3.
  intros flag0 E. destruct flag0; try congruence.
  eexists; eauto.
  unfold flag in E. unfold initParams, empty_map in *.  
  unfold collect_func in A. 
  replace t with ((collect_stmt (Smallstep.globalenv (linked_list_sem se))
           (fn_body find_func)
           (fold_right
              (InitDomain.collect_place
                 (Smallstep.globalenv (linked_list_sem se)))
              (PTree.empty InitDomain.LPaths.t)
              (map
                 (fun elt : ident * type => Plocal (fst elt) (snd elt))
                 (fn_params find_func ++ fn_vars find_func))))) in *.
  vm_compute in E. congruence.
  congruence.
  unfold collect_func in A. congruence.
Qed.


Lemma init_own_env_hash_progress:
  exists own, init_own_env (Smallstep.globalenv (linked_list_sem se)) hash_func = OK own.        
Admitted.


Lemma function_entry_find_progress: forall vl m1,
    length_of_args find = length vl ->
  exists e m2, function_entry ge find_func vl m1 e m2.
Admitted.

Lemma function_entry_hash_progress: forall vl m1,
    length_of_args hash = length vl ->
  exists e m2, function_entry ge hash_func vl m1 e m2.
Admitted.


(* Compute (variant_field_offset (proj1_sig build_ce_ok) Nil [Member_plain Nil Tunit; Member_plain Cons Node_ty]). *)


Definition val_is_ptr (v: val) : bool :=
  match v with
  | Vptr _ _ => true
  | _ => false
  end.


Definition val_is_int (v: val) : bool :=
  match v with
  | Vint _ => true
  | _ => false
  end.

Lemma sound_cont_no_vars: forall f k,
    sound_cont f k ->
    cont_vars k = nil.
Proof.
  intros. unfold sound_cont in H.
  destruct ident_eq in H; try contradiction.
  inv H; reflexivity.
  destruct ident_eq in H; try contradiction.
  inv H; reflexivity.
Qed.

Lemma split_drop_place_find_retv: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get _retv w) (Plocal _retv List_box) List_box = OK [(Plocal _retv List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_l: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get l w) (Plocal l List_box) List_box = OK [(Pderef (Plocal l List_box) List_ty, true); (Plocal l List_box, false)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_deref_l: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get l w) (Pderef (Plocal l List_box) List_ty) List_ty = OK [(Pderef (Plocal l List_box) List_ty, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.


Lemma split_drop_place_find_node: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Plocal node Node_ty) Node_ty = OK [(Pfield (Plocal node Node_ty) key type_int32s, true);
    (Pfield (Plocal node Node_ty) LinkedList.val type_int32s, true);
    (Pfield (Plocal node Node_ty) next List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.

Lemma split_drop_place_find_node_next: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Pfield (Plocal node Node_ty) next List_box) List_box = OK [(Pfield (Plocal node Node_ty) next List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.

Lemma split_drop_place_find_tmp: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get tmp w) (Plocal tmp List_box) List_box = OK [(Plocal tmp List_box, true)].
Proof using se.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.


Lemma sound_call_cont: forall f k,
    sound_cont f k ->
    (* Actually ck is the same as k *)
    exists ck, call_cont k = Some ck
          /\ sound_cont f ck.
Admitted.

Lemma call_cont_num_frames_eq: forall k1 k2,
    call_cont k1 = Some k2 ->
    num_frames_cont k1 = num_frames_cont k2.
Proof.
  induction k1; intros k2 CK; simpl in *; inv CK; auto.
Qed.

Local Open Scope sep_scope.

Lemma step_preservation_progress: forall s,
    sound_state s ->
    (not_stuck (linked_list_sem se) s \/ step_mem_error ge s)
    /\ (forall s' t, step ge s t s' ->
               sound_state s').
Proof.
  intros s INV. inv INV.
  (* callstate in hash *)
  - generalize CALL as CALL1. intros.
    (* build s0 *)
    inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal hash_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    split.
    + left. red. right. right.
      edestruct (function_entry_hash_progress al m) as (e & m1 & ENT); eauto.
      destruct init_own_env_hash_progress as (own & INITOWN).
      do 2 eexists.
      econstructor; eauto.
    + intros. eapply hash_state_internal with (n:= 1%nat); eauto.
      econstructor; eauto. econstructor. 
      inv H; simpl; auto.
      inv H; simpl; auto. rewrite FIND in FIND0. inv FIND0.
      lia.
  (* internal state in hash function *)
  - generalize CALL as CALL1. intros.
    generalize STAR as STAR1. intros.
    (* build s0 *)
    inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal hash_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    inv STAR. lia.
    (** take one step *)
    inv STEP; try congruence.
    rewrite FIND in FIND0. inv FIND0.    
    unfold init_own_env in INITOWN.
    (* construct own_env *)
    destruct collect_func eqn: A; cbn [bind] in INITOWN; try congruence.
    set (empty_map := (PTree.map
                         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                            InitDomain.Paths.empty) t)) in *.
    set (initParams:= (InitDomain.add_place_list t
                         (places_of_locals (fn_params hash_func ++ fn_vars hash_func))
                       empty_map)) in *.
    set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
    generalize INITOWN. clear INITOWN.
    generalize (eq_refl flag).
    generalize flag at 1 3.
    intros flag0 E. destruct flag0; try congruence. intros. inv INITOWN.
    (* construct e *)
    inv ENTRY. inv ALLOC. inv H7. inv H9. inv H10.
    (* construct m' *)
    inv BIND. inv H10. inv H13.
    vm_compute in H3. inv H3.
    vm_compute in H4. inv H4.
    inv H9; simpl in H; try congruence. inv H.
    inv H12; simpl in H; try congruence. inv H.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* stop here: evaluate Ssequence *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hash_state_internal with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        inv H; simpl; auto.
        inv H; simpl; auto. lia.  } 
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign to Dassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hash_state_internal with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        inv H; simpl; auto.
        inv H; simpl; auto. lia.  } 
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_skip_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_skip_reassign.
        reflexivity.
      - intros. eapply hash_state_internal with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto.        
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    vm_compute in OWNTY. congruence.
    2: { unfold hash_body in H12; destruct H12; congruence. }
    (* construct the value computed by remainder *)
    generalize PRECOND as PRECOND1. intros.
    inv PRECOND.    
    exploit alloc_rule. eapply H6. lia. vm_compute. congruence.
    instantiate (1 := Separation.pure True). simpl. auto.
    intros PM1.
    exploit alloc_rule. eapply H8. lia. vm_compute. congruence.
    eapply PM1. intros PM2.
    exploit alloc_rule. eapply H7. lia. vm_compute. congruence.
    eapply PM2. intros PM3.
    rewrite <- !sep_assoc, sep_comm in PM3.
    eapply sep_drop in PM3.
    rewrite sep_comm in PM3.
    exploit storev_rule. eapply range_contains with  (ofs:=0) (chunk:= Mint32) .    
    eapply PM3. eapply Z.divide_0_r. 
    instantiate (1 := Vint k0). instantiate (1 := fun v => v = Vint k0). simpl. auto.
    intros (m1' & STORE1 & PM4).
    setoid_rewrite H0 in STORE1. inv STORE1.
    rewrite <- sep_assoc, sep_comm in PM4.
    exploit storev_rule. eapply range_contains with  (ofs:=0) (chunk:= Mint32).
    eapply PM4. eapply Z.divide_0_r. 
    instantiate (1 := Vint (hash_range w)). instantiate (1 := fun v => v = Vint (hash_range w)). simpl. auto.
    intros (m1'' & STORE2 & PM5).
    setoid_rewrite H1 in STORE2. inv STORE2.
    (* load k and range *)
    exploit load_rule. eapply PM5.
    intros (?v & LOAD1 & PV1). subst.
    exploit load_rule. eapply sep_pick1. eapply PM5.
    intros (?v & LOAD2 & PV2). subst.
    (* show that the remainder operation can succeed *)
    assert (MOD: exists r, sem_mod (Vint k0) (Ctypes.Tint I32 Signed noattr)
                   (Vint (hash_range w)) (Ctypes.Tint I32 Unsigned noattr) m1'' = Some (Vint r)
    /\ Int.ltu r (hash_range w) = true).
    {  simpl. unfold sem_mod, sem_binarith. simpl.
       replace ((Ctypes.Tint I32 Signed noattr)) with (to_ctype type_int32s) by reflexivity.
       replace ((Ctypes.Tint I32 Unsigned noattr)) with (to_ctype type_int32u) by reflexivity.       
       rewrite !cast_val_casted.
       2: { eapply val_casted_to_ctype. eauto. }
       unfold Cop.sem_cast. simpl.
       cbn [Archi.ptr64]. 
       exploit Int.ltu_inv. eauto.
       intros R1.
       unfold Int.eq. destruct zeq. lia.
       eexists. split. eauto.
       unfold Int.ltu. destruct zlt. auto.
       unfold Int.modu in g.
       rewrite Int.unsigned_repr in g.
       exploit (Z.mod_bound_or (Int.unsigned (cast_int_int I32 Unsigned k0)) (Int.unsigned (hash_range w))). lia.
       intros [E1|E2]; lia. 
       exploit (Z.mod_bound_or (Int.unsigned (cast_int_int I32 Unsigned k0)) (Int.unsigned (hash_range w))). lia.
       generalize (Int.unsigned_range_2 (hash_range w)). intros R2.
       intros [E1|E2]; lia.  }
    destruct MOD as (r & SEMOD & RSPEC).
    (* store the vaule to retv *)
    exploit storev_rule. eapply range_contains with  (ofs:=0) (chunk:= Mint32).
    eapply sep_comm.
    eapply PM5. eapply Z.divide_0_r. 
    instantiate (1 := Vint r). instantiate (1 := fun v => v = Vint r /\ Int.ltu r (hash_range w) = true). simpl. auto.
    intros (m1''' & STORE3 & PM6).
    
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.                
        do 2 eexists. econstructor. econstructor.
        reflexivity. reflexivity.
        intros. simpl. unfold type_int32u. congruence.
        econstructor. reflexivity.
        econstructor. econstructor. econstructor.
        econstructor. reflexivity.
        econstructor. reflexivity. eauto.
        econstructor. econstructor. reflexivity.
        econstructor. reflexivity. eauto.
        reflexivity. reflexivity.
        (* sem_mod *)
        simpl. eauto. simpl.
        reflexivity.
        econstructor. reflexivity. eauto.
      - intros. eapply hash_state_internal with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto.        
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv H13. inv H5.
    inv H14. inv H2. inv H9. inv H3. inv H11.
    inv H10. inv H3. inv H11.
    inv H5; simpl in H; inv H. setoid_rewrite LOAD1 in H2. inv H2.
    inv H9; simpl in H; inv H. setoid_rewrite LOAD2 in H2. inv H2. 
    simpl in H14. rewrite SEMOD in H14. inv H14.
    inv H15.
    inv H16; simpl in H; inv H. setoid_rewrite STORE3 in H2. inv H2. 
    (* load return value from _retv *)
    exploit load_rule. eapply sep_pick1.
    eapply PM6. intros (rv & LOAD3 & (SPEC1 & SPEC2)). subst.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate skip_sequence *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hash_state_internal with (n:=6%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia.  }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sreturn to Dreturn *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply hash_state_internal with (n:=7%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia.  }
    inv STEP.
    2: { destruct H12; congruence. }
    erewrite sound_cont_no_vars in *; eauto.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_return_before.
      - intros. eapply hash_state_internal with (n:=8%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia.  }
    inv STEP.   
    inv SDROP. destruct NOTRETURN; congruence.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_skip_return *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_skip_return. reflexivity.
      - intros. eapply hash_state_internal with (n:=9%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    vm_compute in OWNTY0. congruence. clear OWNTY0.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_skip_return. reflexivity.
      - intros. eapply hash_state_internal with (n:=10%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    vm_compute in OWNTY0. congruence. clear OWNTY0.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_return_after *)
    { exploit sound_call_cont; eauto.
      intros (ck & CK & SCONT1).
      split.
      - destruct (Mem.free_list m4 [(b0, 0, 4); (b1, 0, 4); (b2, 0, 4)]) eqn: FREE.
        + left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_return_after.
          econstructor. econstructor. econstructor.
          reflexivity. econstructor. reflexivity.
          eauto. simpl. reflexivity. eauto.
          reflexivity. eauto.
        + right. econstructor.
          eapply step_dropinsert_return_error2. eauto.
      - intros. inv H. inv SDROP.
        rewrite CK in CONT. inv CONT.
        eapply hash_returnstate; eauto.
        inv EXPR. inv H2. inv H4. inv H10.
        inv H9; simpl in H; inv H.
        setoid_rewrite LOAD3 in H2. inv H2.
        inv CAST. econstructor.
        eauto. }
    inv STEP. inv SDROP.  
    inv SCONT. simpl in CONT. inv CONT.
    inv STAR0.
    { split.
      + left. left.
        eexists. econstructor.
      + intros. inv H. }
    inv STEP.

  (* returnstate in hash *)
  - inv CONT. inv PRE.
    split.
    + left. left. eexists. econstructor.
    + intros. inv H.
    
  (* callstate in find *)
  - generalize CALL as CALL1. intros.
    (* build s0 *)
    inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal find_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    (* take zero step *)
    { split.
      - left. red. right. right.
        edestruct (function_entry_find_progress al m) as (e & m1 & ENT); eauto.
        destruct init_own_env_find_progress as (own & INITOWN).
        do 2 eexists.
        econstructor; eauto.
      - intros. eapply find_state_internal1 with (n:= 1%nat); eauto.
        econstructor; eauto. econstructor. 
        inv H; simpl; auto.
        inv H; simpl; auto. rewrite FIND in FIND0. inv FIND0.
        lia. }    
  - generalize CALL as CALL1.
    generalize STAR as STAR1. intros.
    (* build s0 *)
    inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal find_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    inv STAR. lia.
    (** take one step *)
    inv STEP; try congruence.
    rewrite FIND in FIND0. inv FIND0.    
    unfold init_own_env in INITOWN.
    (* construct own_env *)
    destruct collect_func eqn: A; cbn [bind] in INITOWN; try congruence.
    set (empty_map := (PTree.map
                         (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                            InitDomain.Paths.empty) t)) in *.
    set (initParams:= (InitDomain.add_place_list t
                         (places_of_locals (fn_params find_func ++ fn_vars find_func))
                       empty_map)) in *.
    set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
    generalize INITOWN. clear INITOWN.
    generalize (eq_refl flag).
    generalize flag at 1 3.
    intros flag0 E. destruct flag0; try congruence. intros. inv INITOWN.
    (* construct e *)
    inv ENTRY. inv ALLOC. inv H7. inv H9. inv H10. inv H11. inv H12.
    inv STAR0.
    (* stop here: evaluate the if statement *)
    { split.
      - left. red.
        (** decide whether there would be memory error  *)
        destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
        + exploit Mem.valid_access_load. eapply v. intros (v1 & LOAD1).
          (* we should show thata v1 must be a pointer *)
          destruct (val_is_ptr v1) eqn: VPTR.
          * destruct v1; simpl in VPTR; try congruence.
            destruct (Mem.valid_access_dec m' Mint32 b5 (Ptrofs.unsigned i) Readable) eqn: VA2.
            -- exploit Mem.valid_access_load. eapply v0. intros (v2 & LOAD2).
               destruct (val_is_int v2) eqn: VINT.
               ++ destruct v2; simpl in VINT; try congruence.
                  right. right.                  
                  do 2 eexists.
                  (* evaluate if then else *)
                  econstructor. econstructor. econstructor.
                  econstructor.
                  econstructor.
                  reflexivity. 
                  econstructor. reflexivity.
                  eauto. eauto. 1-3: reflexivity. 
                  (** TODO: range check. Make it a memory error state *)
                  simpl. unfold list_length_z. simpl.
                  admit.
                  reflexivity. 
                  simpl.
                  instantiate (1 := Int.eq i0 (Int.repr 0)).
                  destruct (Int.eq i0 (Int.repr 0)) eqn: EQZ; reflexivity.
               (* The tag is not an Int value *)
               ++ admit.
            (* The memory location of tag is not loadable *)
            -- admit.
          (* The value loaded from the place is not a pointer *)
          * admit.
        (* The block of l is not loadable *)
        + admit.
      (* Invariant preservation *)
      - intros. eapply find_state_internal1 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto.
        inv H; simpl; auto.
        inv H; simpl; auto. lia. }
    (* destruct the if step *)
    inv STEP.
    2: { destruct H12; unfold find_body in *; try congruence. }
    (* get the bool value *)
    simpl in H16. inv H14. inv H0.
    simpl in PTY. unfold List_ty in PTY. inv PTY.
    vm_compute in CO. inv CO. vm_compute in FTAG. inv FTAG.
    simpl in RANGE. unfold list_length_z in RANGE. simpl in RANGE.
    destruct (Int.eq tag (Int.repr 0)) eqn: EQZ; vm_compute in H16; inv H16.
    (** evaluate the if branch *)
    { inv STAR; cbn [num_frames] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=3%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto.
          inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H12; congruence. }
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sassign to Dassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          inv H; simpl; auto.
          inv H; simpl; auto. lia. }
      inv STEP. inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_reassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_reassign; auto.
          unfold init_place. cbn [own_universe].
          eapply split_drop_place_find_retv; eauto.
        - intros. eapply find_state_internal1 with (n:=5%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto.
          lia. }
      inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
      erewrite split_drop_place_find_retv in SPLIT; eauto. inv SPLIT.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold is_init, init_place. simpl.
          unfold collect_func in A. vm_compute in A. inv A. 
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=6%nat); eauto.
          eapply starNf_step_right; eauto.
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold is_init, init_place in OWN. simpl in OWN.
           unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { simpl in SCALAR. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=7%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: ealuate step_dropinsert_assign *)
      { split.
        - destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
          (* The argument l is loadable *)
          + exploit Mem.valid_access_load. eapply v. intros (?v & ?LOAD).
            * destruct (sem_cast v0 List_box List_box) eqn: CAST1.
              (* v0 can be casted *)
              -- destruct (Mem.valid_access_dec m' Mptr b2 0 Writable) eqn: VA2.
                 (* The return variable is writable *)
                 ++ edestruct Mem.valid_access_store with (v:= v1) as (?m & ?STORE).
                    eapply v2.
                    left. red. do 2 right.
                    do 2 eexists. econstructor.
                    econstructor; eauto.
                    simpl. unfold List_box. congruence.
                    econstructor. reflexivity.
                    econstructor. econstructor. econstructor.
                    reflexivity. econstructor. reflexivity.
                    eauto. econstructor. reflexivity. eauto.
                 (* The return variable is not writable *)
                 ++ right. econstructor.
                    eapply step_dropinsert_assign_error3.
                    econstructor. reflexivity.
                    econstructor. econstructor. econstructor.
                    reflexivity. econstructor. reflexivity.
                    eauto. eauto.
                    eapply assign_loc_value_mem_error. reflexivity.
                    eauto.
              (* v0 cannot be casted *)
              -- admit.
          (* The argument l is not loadable *)
          + right. econstructor.
            eapply step_dropinsert_assign_error1.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. eapply find_state_internal1 with (n:=8%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Kseq *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=9%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sreturn *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=10%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H12; congruence. }
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropinsert_return_before *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          erewrite sound_cont_no_vars; eauto.          
          eapply step_dropinsert_return_before.
        - intros. eapply find_state_internal1 with (n:=11%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP.
      erewrite sound_cont_no_vars in SDROP; eauto.
      inv SDROP. destruct NOTRETURN; congruence.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_return.
          reflexivity. reflexivity.
          eapply split_drop_place_find_l; eauto.
        - intros. eapply find_state_internal1 with (n:=12%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold List_box in OWNTY0. vm_compute in OWNTY0. congruence. }
      erewrite split_drop_place_find_l in SPLIT; eauto. inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=13%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN. inv STAR0.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=14%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=15%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_skip_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_skip_return.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=16%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      vm_compute in OWNTY1. congruence.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_return_after *)
      { split.
        - destruct (Mem.valid_access_dec m6 Mptr b2 0 Readable) eqn: ?VA.
          + exploit Mem.valid_access_load. eapply v0.
            intros (?v & ?LOAD).
            destruct (sem_cast v2 List_box List_box) eqn: ?CAST.
            * destruct (Mem.free_list m6 [(b3, 0, 16); (b4, 0, 8); (b1, 0, 8); (b2, 0, 8); (b0, 0, 4)]) eqn: ?FREELIST.
              -- left. red. do 2 right.
                 exploit sound_call_cont; eauto.
                 intros (ck & CK & SCK).
                 do 2 eexists. econstructor.
                 eapply step_dropinsert_return_after.
                 econstructor. econstructor. econstructor. reflexivity.
                 econstructor. reflexivity. eauto.
                 eauto. eauto. reflexivity. eauto.
              (* free_list memory error *)
              -- right. econstructor.
                 eapply step_dropinsert_return_error2; eauto.
            (* sem_cast fails *)
            * admit.
          + right. econstructor.
            eapply step_dropinsert_return_error1; eauto.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. inv H. inv SDROP.
          exploit sound_call_cont; eauto.
          intros (ck1 & CK & SCK). rewrite CONT in CK. inv CK.          
          eapply find_returnstate. eauto. }
      (* show that it cannot take more step using num_frames unchanged
      property *)
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (** show that the returnstate can take a step *)
      { exploit sound_call_cont; eauto.
        intros (ck1 & CK & SCK). rewrite CONT in CK. inv CK.
        vm_compute in SCK. inv SCK.
        (* ck1 is Kstop *)
        - split.
          (* final state *)
          + left. red. left.
            eexists. econstructor.
          + intros. inv H.
        (** TODO: ck1 is Kcall. Fill this code after finishing calling
        find *)
        - split.
          + destruct (val_casted_dec v2 List_box).
            * destruct (Mem.valid_access_dec m7 Mptr b11 0 Writable).
              -- edestruct Mem.valid_access_store with (v:= v2) as (?m & ?STORE).
                 eauto.
                 left. red. do 2 right.
                 do 2 eexists. econstructor. reflexivity.
                 econstructor.  reflexivity. eauto.
                 econstructor. reflexivity. eauto.
              -- right. eapply step_returnstate_error2.
                 reflexivity.
                 econstructor. reflexivity. 
                 econstructor. reflexivity. eauto.
            (** TODO: The return value is not val_casted. Treat it as
            a kind of memory error *)
            * admit.
          + intros.
            eapply find_state_internal3 with (n:=0%nat).
            2: eauto.
            econstructor. econstructor. eauto. eauto.
            econstructor. 
            inv H; simpl; eauto. lia. }
      (* num frames contradiction *)
      inv STEP.
      simpl in FEQ16.
      exfalso. eapply Nat.neq_succ_diag_l; eauto. }
        
    (* evaluate the else branch *)
    { cbn [num_frames num_frames_cont] in *.
      (* show that the tag is one *)
      generalize (Int.unsigned_range tag). intros TAGPOS.
      destruct (zeq (Int.unsigned tag) 0). rewrite <- e in EQZ.
      rewrite Int.repr_unsigned in EQZ. rewrite Int.eq_true in EQZ. congruence.
      assert (EQONE: Int.unsigned tag = 1). lia.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Slet *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=3%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      2: { destruct H12; congruence. }
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=4%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Sassign to Dassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=5%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_to_dropplace_reassign *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_reassign; auto.
          unfold init_place. cbn [own_universe].
          eapply split_drop_place_find_node; eauto.
        - intros. eapply find_state_internal1 with (n:=6%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
      erewrite split_drop_place_find_node in SPLIT; eauto. inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=7%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=8%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in A. vm_compute in A. inv A.
          reflexivity.
        - intros. eapply find_state_internal1 with (n:=9%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in A. vm_compute in A. inv A.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal1 with (n:=10%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.      
      (* stop here: evaluate step_dropinsert_assign *)
      { split.
        (* Note that the evaluation of conditional expression provides
        the fact of loading *l *)        
        - destruct (Mem.range_perm_dec m' b6 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) ((Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) + 16) Cur Readable).
          + exploit Mem.range_perm_loadbytes. eapply r. intros (bys & LOADBYTES).
            destruct (Mem.range_perm_dec m' b3 0 (0 + 16) Cur Writable).
            * edestruct Mem.range_perm_storebytes with (bytes:= bys) as (?m & ?STOREBYTES).
              erewrite Mem.loadbytes_length; eauto. eauto.
              left. red. do 2 right.
              do 2 eexists. econstructor.
              econstructor; eauto.
              vm_compute. congruence.
              econstructor. reflexivity.
              econstructor. econstructor. econstructor.
              eauto. reflexivity. reflexivity. eauto.
              rewrite EQONE. reflexivity.
              instantiate (1 := 8). reflexivity.
              eapply deref_loc_copy. eauto.
              simpl. reflexivity.
              (* assign_loc_copy *)
              eapply do_assign_loc_sound.
              unfold do_assign_loc.
              replace (sizeof (Smallstep.globalenv (linked_list_sem se))
               (typeof_place (Plocal node Node_ty))) with 16 by reflexivity.
              rewrite LOADBYTES.
              rewrite Ptrofs.unsigned_zero. rewrite STOREBYTES.
              destruct check_assign_copy.
              -- reflexivity.
              (** TODO: we can treat check_assign_copy failure as a
              kind of memory error which can be ruled out in move
              checking. The approach is that we add a case of memory
              error in step_assign when the type of LHS is
              Tstruct/Tvariant. We also check the RHS must be (Eplace
              p') so that we can prove check_assign_copy success by
              case analysis of (RHS = p') or (RHS <> p'), using the
              fact that different place must have different location
              *)
              -- admit.
            * right. econstructor.
              eapply step_dropinsert_assign_error3.
              econstructor. reflexivity.
              econstructor. econstructor. econstructor.
              eauto. reflexivity. reflexivity. eauto.
              rewrite EQONE. reflexivity.
              instantiate (1 := 8). reflexivity.
              eapply deref_loc_copy. eauto.
              simpl. reflexivity.
              eapply assign_loc_copy_mem_error2; eauto.
          + right. econstructor.
            eapply step_dropinsert_assign_error3.
            econstructor. reflexivity.
            econstructor. econstructor. econstructor.
            eauto. reflexivity. reflexivity. eauto.
            rewrite EQONE. reflexivity.
            instantiate (1 := 8). reflexivity.
            eapply deref_loc_copy. eauto.
            simpl. reflexivity.
            eapply assign_loc_copy_mem_error1; eauto.
        - intros. eapply find_state_internal1 with (n:=11%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate skip_seq *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=12%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate Ssequence *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
        - intros. eapply find_state_internal1 with (n:=13%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate Sifthenelse *)
      { split.
        - destruct (Mem.valid_access_dec m6 Mint32 b0 0 Readable).
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v2 type_int32s type_int32s) eqn: ?CAST.
            * destruct (Mem.valid_access_dec m6 Mint32 b3 0 Readable).
              -- exploit Mem.valid_access_load. eauto.
                 intros (?v & ?LOAD).
                 destruct (sem_cast v5 type_int32s type_int32s) eqn: ?CAST.
                 ++ exploit cast_val_is_casted. eapply CAST. intros ?CASTED.
                    exploit cast_val_is_casted. eapply CAST0. intros ?CASTED.
                    inv CASTED. inv CASTED0.
                    exploit sem_cast_id. eapply CAST. intros ?CCAST.
                    exploit sem_cast_id. eapply CAST0. intros ?CCAST.
                    left. red. do 2 right.
                    do 2 eexists. econstructor.
                    (* evaluate the binary equal *)
                    econstructor. econstructor.
                    econstructor. econstructor. reflexivity.
                    econstructor. reflexivity. eauto.
                    econstructor. econstructor. econstructor. reflexivity.
                    reflexivity. reflexivity.
                    reflexivity.
                    econstructor. reflexivity. eauto.
                    reflexivity. reflexivity.
                    simpl. unfold sem_cmp, sem_binarith. simpl.
                    erewrite CCAST. rewrite CCAST0.
                    reflexivity. reflexivity. simpl.
                    instantiate (1 := Int.eq n n1). 
                    destruct (Int.eq n n1) eqn: ?IEQ; reflexivity.
                 (* cast fails *)
                 ++ admit.
              (* load fails *)
              -- right.
                 eapply step_ifthenelse_error.
                 econstructor. econstructor.
                 right. eapply eval_Eplace_error2.
                 econstructor. econstructor. reflexivity. reflexivity.
                 econstructor. reflexivity.
                 econstructor. reflexivity. eauto.
            (* cast fails *)
            *  admit.
          (* load fails *)
          + right.
            eapply step_ifthenelse_error.
            econstructor. econstructor.
            left. eapply eval_Eplace_error2.
            econstructor. econstructor. 
            econstructor. reflexivity.
            eauto.
        - intros. eapply find_state_internal1 with (n:=14%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      destruct b7.
      
      (* evaluate the true branch *)
      { inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Scall to Dcall *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
          - intros. eapply find_state_internal1 with (n:=15%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; simpl; auto. lia. }
        inv STEP.
        inv STAR0; cbn [num_frames num_frames_cont] in *.
        (* evaluate step_dropinsert_skip_reassign *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
            eapply step_dropinsert_skip_reassign.
            reflexivity.
          - intros. eapply find_state_internal1 with (n:=16%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; inv SDROP; simpl; auto. lia.}
        inv STEP. inv SDROP.
        vm_compute in OWNTY0. congruence. clear OWNTY0.
        inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Dcall *)
        { split.
          - destruct (Mem.valid_access_dec m6 Mint32 b3 4 Readable).
            + exploit Mem.valid_access_load. eauto.
              intros (?v & ?LOAD).
              destruct (sem_cast v3 type_int32s type_int32s) eqn: ?CAST.
              * left. red. do 2 right.
                (* construct the block of process *)
                generalize (wf_senv process). intros FINDPRO.
                simpl in FINDPRO. destruct FINDPRO as (?b & FINDPRO).
                do 2 eexists. econstructor. econstructor.
                reflexivity. reflexivity.
                econstructor. econstructor. eauto.
                eapply deref_loc_reference. reflexivity.
                (* evaluate the arguments *)
                econstructor.
                econstructor. econstructor. econstructor.
                econstructor. reflexivity. reflexivity.
                reflexivity. reflexivity. econstructor. reflexivity.
                eauto. eauto.
                econstructor.
                (* find_funct *)
                simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
                rewrite Genv.find_def_spec.
                erewrite Genv.find_invert_symbol; eauto.
                reflexivity. reflexivity.
                simpl. auto.
              (* sem_cast fails *)
              * admit.
            (* load fails *)
            + right.
              generalize (wf_senv process). intros FINDPRO.
              simpl in FINDPRO. destruct FINDPRO as (?b & FINDPRO).
              econstructor.
              eapply step_dropinsert_call_error2.   
              econstructor. econstructor. eauto.
              eapply deref_loc_reference. reflexivity.
              reflexivity. econstructor. econstructor.
              eapply eval_Eplace_error2. econstructor.
              econstructor. reflexivity. reflexivity. reflexivity.
              reflexivity. econstructor. reflexivity.
              eauto.
          - intros. inv H. inv SDROP.
            (* show that vf points to process_ext *)
            inv H21. inv H0. inv DEF; simpl in H; try congruence.
            generalize (wf_senv process). intros FINDPRO.
            simpl in FINDPRO. destruct FINDPRO as (?b & FINDPRO). 
            simpl in GADDR. rewrite GADDR in FINDPRO. inv FINDPRO.
            eapply find_state_call_process.
            (* find_funct *)
            simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
            rewrite Genv.find_def_spec.
            erewrite Genv.find_invert_symbol; eauto.
            reflexivity.
            (* sound_find_cont *)
            simpl. econstructor. eauto. eauto. }
        inv STEP. inv SDROP. simpl in FEQ15.
        exfalso. eapply Nat.neq_succ_diag_l; eauto. }

      (* evaluate the false branch (i.e., calling find function) *)
      { inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Slet *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
          - intros. eapply find_state_internal1 with (n:=15%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; simpl; auto. lia. }
        inv STEP.
        inv STAR0; cbn [num_frames num_frames_cont] in *.
        (* evaluate Ssequence *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
          - intros. eapply find_state_internal1 with (n:=16%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; simpl; auto. lia. }
        inv STEP.
        inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate Scall to Dcall *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
          - intros. eapply find_state_internal1 with (n:=17%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; simpl; auto. lia. }
        inv STEP.
        inv STAR0; cbn [num_frames num_frames_cont] in *.
        (* evaluate step_dropinsert_to_dropplace_reassign *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
            eapply step_dropinsert_to_dropplace_reassign.
            reflexivity. reflexivity.
            eapply split_drop_place_find_tmp. eauto.
          - intros. eapply find_state_internal1 with (n:=18%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; inv SDROP; simpl; auto. lia.}
        inv STEP. inv SDROP.
        2: { vm_compute in OWNTY0. congruence. }
        clear OWNTY0.
        erewrite split_drop_place_find_tmp in SPLIT; eauto.
        inv SPLIT.
        inv STAR; cbn [num_frames num_frames_cont] in *.
        (* evaluate step_dropplace_init1 *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
            eapply step_dropplace_init1.
            unfold collect_func in A. vm_compute in A. inv A.
            reflexivity.
          - intros. eapply find_state_internal1 with (n:=19%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; inv SDROP; simpl; auto. lia.}
        inv STEP. inv SDROP.
        2: { unfold collect_func in A. vm_compute in A. inv A.
             vm_compute in OWN. congruence. }
        2: { simpl in SCALAR. congruence. }
        clear NOTOWN. 
        inv STAR0; cbn [num_frames num_frames_cont] in *.
        (* evaluate step_dropplace_return *)
        { split.
          - left. red. do 2 right.
            do 2 eexists. econstructor.
            eapply step_dropplace_return.
          - intros. eapply find_state_internal1 with (n:=20%nat); eauto.
            eapply starNf_step_right; eauto. 
            1-2: inv H; inv SDROP; simpl; auto. lia.}
        inv STEP. inv SDROP.
        inv STAR; cbn [num_frames num_frames_cont] in *.        
        (* evaluate Dcall *)
        { split.
          - (* construct the block of process *)
            generalize (wf_senv find). intros FINDF.
            simpl in FINDF. destruct FINDF as (?b & FINDF).
            destruct (Mem.valid_access_dec m6 Mptr b3 8 Readable).
            + exploit Mem.valid_access_load. eauto.
              intros (?v & ?LOAD).
              destruct (sem_cast v3 List_box List_box) eqn: ?CAST.
              * destruct (Mem.valid_access_dec m6 Mint32 b0 0 Readable).
                -- exploit Mem.valid_access_load. eauto.
                   intros (?v & ?LOAD).
                   destruct (sem_cast v6 type_int32s type_int32s) eqn: ?CAST.
                   ++ left. red. do 2 right.
                      do 2 eexists. econstructor. econstructor.
                      reflexivity. reflexivity.
                      econstructor. econstructor. eauto.
                      eapply deref_loc_reference. reflexivity.
                      (* evaluate the arguments *)
                      econstructor.
                      econstructor. econstructor. econstructor.
                      econstructor. reflexivity. reflexivity.
                      reflexivity. reflexivity. econstructor. reflexivity.
                      eauto. eauto.
                      econstructor. econstructor. econstructor. econstructor.
                      reflexivity. econstructor. reflexivity.
                      eauto. eauto.
                      econstructor.
                      (* find_funct *)
                      simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
                      rewrite Genv.find_def_spec.
                      erewrite Genv.find_invert_symbol; eauto.
                      reflexivity. reflexivity.
                      simpl. auto.
                   (* sem_cast fails *)
                   ++ admit.
                -- right. econstructor.
                   eapply step_dropinsert_call_error2.
                   econstructor. econstructor. eauto.
                   eapply deref_loc_reference. reflexivity. reflexivity.
                   eapply eval_Econs_mem_error2.
                   econstructor.
                   econstructor. econstructor. econstructor.
                   reflexivity. reflexivity.
                   reflexivity. reflexivity. econstructor. reflexivity.
                   eauto.
                   eapply eval_Econs_mem_error1.
                   econstructor. eapply eval_Eplace_error2.
                   econstructor. econstructor. econstructor.
                   reflexivity. eauto.
              (* sem_cast fails *)
              * admit.
            + right. econstructor.
              eapply step_dropinsert_call_error2.
              econstructor. econstructor. eauto.
              eapply deref_loc_reference. reflexivity. reflexivity.
              eapply eval_Econs_mem_error1.
              econstructor. eapply eval_Eplace_error2.
              econstructor. econstructor. econstructor.
              reflexivity. reflexivity. reflexivity.
              econstructor. reflexivity. eauto.
          - intros. inv H. inv SDROP.
            inv H21. inv H0.
            inv DEF; simpl in H; try congruence.
            eapply callstate_find. econstructor.
            eapply Genv.find_invert_symbol. eauto.
            econstructor. eauto. eauto.
            inv H22. inv H11. inv H21. reflexivity. }
        inv STEP. inv SDROP. simpl in FEQ19.
        exfalso. eapply Nat.neq_succ_diag_l; eauto. }
    }
    
  (* call process *)
  - split.
    + left. right. left.
      eexists. econstructor. simpl in PROC. simpl.
      rewrite PROC. f_equal. unfold process_ext. f_equal.
    (* use the fact that there is not step in the state of
    at_external *)
    + intros. inv H. rewrite PROC in FIND. inv FIND.
      rewrite PROC in FIND. inv FIND. inv H6.
  (* return from process *)
  - split.
    + inv CONT.
      destruct (val_casted_dec v type_int32s).
      * destruct (Mem.valid_access_dec m Mint32 b3 4 Writable).
        -- edestruct Mem.valid_access_store as (?m & ?STORE). eauto.
           left. do 2 right.
           do 2 eexists.
           econstructor. reflexivity.
           econstructor. econstructor. reflexivity. reflexivity.
           reflexivity. reflexivity.
           simpl. eauto.
           econstructor. reflexivity.
           eauto.
        -- right.
           eapply step_returnstate_error2. reflexivity.
           econstructor. econstructor. reflexivity. reflexivity.
           reflexivity. reflexivity.
           econstructor. reflexivity. eauto.
      (* val is not val_casted in returnstate *)
      * admit.
    + intros. eapply find_state_internal2 with (n:=0%nat).
      2: eauto.
      econstructor. auto.
      econstructor. inv H; simpl; auto. lia.
  (* execution after returning from process *)
  - generalize RET. intros RET1.
    generalize STEP. intros STEP1.
    generalize STAR as STAR1. intros.
    inv RET. inv STEP. inv CONT.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate skip_seq *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    (** The following code may be reused in the execution of returning
    from find *)
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Ssequence *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign_variant to Dassign_variant *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. eapply step_dropinsert_to_dropplace_reassign.
        reflexivity. reflexivity.
        eapply split_drop_place_find_deref_l. eauto.
      - intros. eapply find_state_internal2 with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { vm_compute in OWNTY. congruence. }
    erewrite split_drop_place_find_deref_l in SPLIT; eauto. inv SPLIT.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal2 with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. econstructor.
      - intros. eapply find_state_internal2 with (n:=6%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate assign_variant (many cases of memory error) *)
    { split.
      - destruct (Mem.valid_access_dec m2 Mptr b1 0 Readable).
        + exploit Mem.valid_access_load. eauto. intros (?v & ?LOAD).
          (* we should show thata v1 must be a pointer *)
          destruct (val_is_ptr v1) eqn: VPTR.
          * destruct v1; simpl in VPTR; try congruence.
            destruct (Mem.range_perm_dec m2 b3 0 (0 + 16) Cur Readable).
            -- exploit Mem.range_perm_loadbytes. eapply r. intros (bys & LOADBYTES).
               destruct (Mem.range_perm_dec m2 b5 (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 8))) (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 8)) + 16) Cur Writable).
               ++ edestruct Mem.range_perm_storebytes with (bytes:= bys) as (?m & ?STOREBYTES).
                  erewrite Mem.loadbytes_length; eauto. eauto.
                  destruct (Mem.valid_access_dec m0 Mptr b1 0 Readable).
                  ** exploit Mem.valid_access_load. eauto. intros (?v & ?LOAD).
                     (* we should show thata v1 must be a pointer *)
                     destruct (val_is_ptr v2) eqn: ?VPTR.
                     --- destruct v2; simpl in VPTR0; try congruence.
                         destruct (Mem.valid_access_dec m0 Mint32 b6 (Ptrofs.unsigned i0) Writable).
                         +++ edestruct Mem.valid_access_store as (?m & ?STORE). eauto.
                             left. red. do 2 right.
                             do 2 eexists. econstructor. econstructor.
                             1-5: reflexivity.
                             econstructor. econstructor. econstructor.
                             reflexivity. eapply deref_loc_copy. reflexivity.
                             econstructor. econstructor. reflexivity.
                             econstructor. reflexivity. eauto.
                             instantiate (1:= 8). reflexivity.
                             (* sem_cast *)
                             simpl. reflexivity.
                             (* memory copy *)
                             eapply do_assign_loc_sound.
                             unfold do_assign_loc.
                             replace (sizeof (Smallstep.globalenv (linked_list_sem se))
                                        (type_member (Member_plain Cons Node_ty))) with 16 by reflexivity.
                             rewrite Ptrofs.unsigned_zero. rewrite LOADBYTES.
                             rewrite STOREBYTES.
                             destruct check_assign_copy.
                             reflexivity.
                             (** TODO: we can treat check_assign_copy failure as a kind of memory error *)
                             admit.
                             reflexivity.
                             econstructor. econstructor. reflexivity.
                             econstructor. reflexivity.
                             eauto.
                             simpl. eauto.
                         (* All the following cases are memory error *)
                         +++ admit.
                     --- admit.
                  ** admit.
               ++ admit.
            -- admit.
          * admit.
        + admit.
      - intros. eapply find_state_internal2 with (n:=7%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal2 with (n:=8%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP. 
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal2 with (n:=9%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign to _retv *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal2 with (n:=10%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. eapply step_dropinsert_to_dropplace_reassign.
        reflexivity. reflexivity.
        eapply split_drop_place_find_retv. eauto.
      - intros. eapply find_state_internal2 with (n:=11%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { vm_compute in OWNTY0. congruence. }
    erewrite split_drop_place_find_retv in SPLIT; eauto. inv SPLIT.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal2 with (n:=12%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. econstructor.
      - intros. eapply find_state_internal2 with (n:=13%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Dassign *)
    { split.
      - destruct (Mem.valid_access_dec m3 Mptr b1 0 Readable).
        + exploit Mem.valid_access_load. eauto.
          intros (?v & ?LOAD).
          destruct (sem_cast v3 List_box List_box) eqn: ?CAST.
          * destruct (Mem.valid_access_dec m3 Mptr b2 0 Writable).
            -- edestruct Mem.valid_access_store as (?m & ?STORE). eauto.
               left. red. do 2 right.
               do 2 eexists. econstructor. econstructor.
               reflexivity. reflexivity.
               simpl. unfold List_box. congruence.
               econstructor. reflexivity.
               econstructor. econstructor. econstructor.
               reflexivity.
               econstructor. reflexivity. eauto. eauto.
               econstructor. reflexivity. eauto.
            -- right. econstructor.
               eapply step_dropinsert_assign_error3.
               econstructor. reflexivity.
               econstructor. econstructor. econstructor.
               reflexivity. econstructor. reflexivity. eauto.
               eauto. econstructor. reflexivity. eauto.
          * admit.
        + right. econstructor.
          eapply step_dropinsert_assign_error1.
          econstructor. eapply eval_Eplace_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. eapply find_state_internal2 with (n:=14%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal2 with (n:=15%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP. 
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* stop here: evaluate Sreturn *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=16%nat); eauto.
        eapply starNf_step_right; eauto. 
          1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropinsert_to_dropplace_escape (to drop the
      node) *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          simpl.
          erewrite sound_cont_no_vars with (f:= find); eauto.
          eapply step_dropinsert_to_dropplace_escape.
          reflexivity. reflexivity.
          eapply split_drop_place_find_node. eauto.
        - intros. eapply find_state_internal2 with (n:=17%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP.
      erewrite sound_cont_no_vars with (f:= find) in SDROP; eauto.
      inv SDROP.
      2: { vm_compute in OWNTY1. congruence. }
      erewrite split_drop_place_find_node in SPLIT; eauto.
      inv SPLIT.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in UNI. vm_compute in UNI. inv UNI.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=18%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in UNI. vm_compute in UNI. inv UNI.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=19%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in UNI. vm_compute in UNI. inv UNI.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=20%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal2 with (n:=21%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          econstructor.
        - intros. eapply find_state_internal2 with (n:=22%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropinsert_return_before *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_return_before.
        - intros. eapply find_state_internal2 with (n:=23%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      destruct NOTRETURN; congruence.
      inv STAR0; cbn [num_frames num_frames_cont] in *.      
      (* stop here: evaluate step_dropinsert_to_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_return.
          reflexivity. reflexivity.
          eapply split_drop_place_find_l; eauto.
        - intros. eapply find_state_internal2 with (n:=24%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold List_box in OWNTY0. vm_compute in OWNTY2. congruence. }
      erewrite split_drop_place_find_l in SPLIT; eauto. inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in UNI. vm_compute in UNI. inv UNI.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=25%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
       { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          unfold collect_func in UNI. vm_compute in UNI. inv UNI.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=26%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
           vm_compute in OWN. congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal2 with (n:=27%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_skip_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_skip_return.
          reflexivity.
        - intros. eapply find_state_internal2 with (n:=28%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      vm_compute in OWNTY3. congruence.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_return_after *)
      { split.
        - destruct (Mem.valid_access_dec m4 Mptr b2 0 Readable) eqn: ?VA.
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v5 List_box List_box) eqn: ?CAST.
            * destruct (Mem.free_list m4 [(b3, 0, 16); (b4, 0, 8); (b1, 0, 8); (b2, 0, 8); (b0, 0, 4)]) eqn: ?FREELIST.
              -- left. red. do 2 right.
                 exploit sound_call_cont; eauto.
                 instantiate (2 := find). eauto.
                 intros (ck & CK & SCK).
                 do 2 eexists. econstructor.
                 eapply step_dropinsert_return_after.
                 econstructor. econstructor. econstructor. reflexivity.
                 econstructor. reflexivity. eauto.
                 eauto. eauto. reflexivity. eauto.
              (* free_list memory error *)
              -- right. econstructor.
                 eapply step_dropinsert_return_error2; eauto.
            (* sem_cast fails *)
            * admit.
          + right. econstructor.
            eapply step_dropinsert_return_error1; eauto.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. inv H. inv SDROP.
          exploit (sound_call_cont find); eauto.
          intros (ck1 & CK & SCK). simpl in CONT. rewrite CONT in CK.
          inv CK.          
          eapply find_returnstate. eauto. }
      inv STEP. inv SDROP.
      (* show that it cannot take more step using num_frames unchanged
      property *)
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (** show that the returnstate can take a step *)
      { exploit (sound_call_cont find); eauto.
        intros (ck1 & CK & SCK). simpl in CONT. rewrite CONT in CK. inv CK.
        vm_compute in SCK. inv SCK.
        (* ck1 is Kstop *)
        - split.
          (* final state *)
          + left. red. left.
            eexists. econstructor.
          + intros. inv H.
        (** TODO: ck1 is Kcall. Fill this code after finishing calling
        find *)
        - split.
          + destruct (val_casted_dec v5 List_box).
            * destruct (Mem.valid_access_dec m5 Mptr b12 0 Writable).
              -- edestruct Mem.valid_access_store with (v:= v5) as (?m & ?STORE).
                 eauto.
                 left. red. do 2 right.
                 do 2 eexists. econstructor. reflexivity.
                 econstructor.  reflexivity. eauto.
                 econstructor. reflexivity. eauto.
              -- right. eapply step_returnstate_error2.
                 reflexivity.
                 econstructor. reflexivity. 
                 econstructor. reflexivity. eauto.
            (** TODO: The return value is not val_casted. Treat it as
            a kind of memory error *)
            * admit.
          + intros.
            eapply find_state_internal3 with (n:=0%nat).
            2: eauto.
            econstructor. econstructor. eauto. eauto.
            econstructor. 
            inv H; simpl; eauto. lia. }
      (* num frames contradiction *)
      inv STEP.
      simpl in FEQ28.
      exfalso. eapply Nat.neq_succ_diag_l; eauto.

  (* execution after returning from find (the code is similar to the
  last case *)
  - admit.

  (* state in find_returnstate (returing from find function) *)
  - inv H.
    (* ck1 is Kstop *)
    + split.
      (* final state *)
      * left. red. left.
        eexists. econstructor.
      * intros. inv H.
    (** TODO: ck1 is Kcall. Fill this code after finishing calling
      find *)
    + split.
      * destruct (val_casted_dec v List_box).
        -- destruct (Mem.valid_access_dec m Mptr b4 0 Writable).
           ++ edestruct Mem.valid_access_store with (v:= v) as (?m & ?STORE).
              eauto.
              left. red. do 2 right.
              do 2 eexists. econstructor. reflexivity.
              econstructor.  reflexivity. eauto.
              econstructor. reflexivity. eauto.
           ++ right. eapply step_returnstate_error2.
              reflexivity.
              econstructor. reflexivity. 
              econstructor. reflexivity. eauto.
      (** TODO: The return value is not val_casted. Treat it as
            a kind of memory error *)
        -- admit.
      * intros.
        eapply find_state_internal3 with (n:=0%nat).
        2: eauto.
        econstructor. econstructor. eauto. eauto.
        econstructor. 
        inv H; simpl; eauto. lia. 

Admitted.

End SOUNDNESS.


        
                
