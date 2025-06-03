Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LinkedList HashMap.
Require Import Values Globalenvs Memory.
Require Import InitDomain.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import HashMapCommon.
Require Import Rustlightown.
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
              

Definition linked_list_sem := semantics linked_list_mod.

Section SOUNDNESS.

Context (se : Genv.symtbl).
Context (w: hmap_world_ext).

Let ge := globalenv se linked_list_mod.

(* The following hypothese are derived from symtbl_inv *)
Hypothesis wf_senv: wf_senv se.
    
Hypothesis hmap_senv_eq: w.(hmap_senv_ext) = se.

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
Definition find_env b0 b1 b2 b3 b4 b5 :=
  (PTree.set tmpv (b5, Tbox_int)
     (PTree.set tmp (b4, List_box)
        (PTree.set node (b3, Node_ty)
           (PTree.set _retv (b2, List_box)
              (PTree.set LinkedList.k (b0, type_int32s)
                 (PTree.set l (b1, List_box) empty_env)))))).


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
| sound_find_Kcall: forall k b0 b1 b2 b3 b4 b5 t E1 E2
    (CONT: sound_find_cont k)
    (UNI: collect_func ge find_func = OK t),                      
    sound_find_cont (return_find_cont (find_env b0 b1 b2 b3 b4 b5) t E1 E2 k).


Definition return_process_cont (e: env) t E1 E2 k :=
  (Kcall (Plocal tmpv Tbox_int) find_func
     e
       (move_place
          (own_transfer_assign
             (move_place
                (init_place
                   (init_place
                      (own_env_find t E1 E2)
                      (Plocal l List_box))
                   (Plocal LinkedList.k type_int32s)) (Pderef (Plocal l List_box) List_ty))
             (Plocal node Node_ty)) (Pfield (Plocal node Node_ty) LinkedList.val Tbox_int))
       (Kseq
          (Sassign (Pfield (Plocal node Node_ty) LinkedList.val Tbox_int)
             (Emoveplace (Plocal tmpv Tbox_int) Tbox_int))
          (Klet tmpv Tbox_int
             (Kseq
                (Ssequence
                   (Sassign_variant (Pderef (Plocal l List_box) List_ty) List Cons
                      (Emoveplace (Plocal node Node_ty) Node_ty))
                   (Ssequence
                      (Sassign (Plocal _retv List_box)
                         (Emoveplace (Plocal l List_box) List_box))
                      (Sreturn (Plocal _retv List_box)))) (Klet node Node_ty k))))).


(* continuation of the returnstate in find function *)
Inductive find_cont_ret_process : cont -> Prop :=
(* return from process *)
| find_return_process: forall k t b0 b1 b2 b3 b4 b5 E1 E2
    (CONT: sound_find_cont k)
    (UNI: collect_func ge find_func = OK t),
    find_cont_ret_process (return_process_cont (find_env b0 b1 b2 b3 b4 b5) t E1 E2 k)
.

(** Local state of hash function *)

Inductive hash_cont: cont -> Prop :=
| hash_cont_intro: hash_cont Kstop.

(** Continuation parameterized by the function name *)

Definition sound_cont (f: ident) : cont -> Prop :=
  if ident_eq f find then
    sound_find_cont
  else
    if ident_eq f hash then
      hash_cont
    else
      fun _ => False.


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

(* own_env may come from the Nil branch or the Cons branch *)
Definition find_merge_own_env own t E1 E2 : Prop :=
  own = (own_transfer_assign
            (move_place
               (own_transfer_assign
                  (move_place
                     (own_transfer_assign
                        (move_place
                           (init_place
                              (init_place (own_env_find t E1 E2) (Plocal l List_box))
                              (Plocal LinkedList.k type_int32s))
                           (Pderef (Plocal l List_box) List_ty)) 
                        (Plocal node Node_ty))
                           (Pfield (Plocal node Node_ty) LinkedList.val Tbox_int))
                  (Plocal tmpv Tbox_int)) (Plocal tmpv Tbox_int))
            (Pfield (Plocal node Node_ty) LinkedList.val Tbox_int))
  \/ own = (own_transfer_assign
             (move_place
                (own_transfer_assign
                   (move_place
                      (own_transfer_assign
                         (move_place
                            (init_place (init_place (own_env_find t E1 E2) (Plocal l List_box))
                               (Plocal LinkedList.k type_int32s))
                            (Pderef (Plocal l List_box) List_ty)) (Plocal node Node_ty))
                      (Pfield (Plocal node Node_ty) next List_box)) 
                   (Plocal tmp List_box)) (Plocal tmp List_box))
             (Pfield (Plocal node Node_ty) next List_box)).

Inductive find_merge_pattern_match: state -> Prop :=
| find_merge_pattern_match_intro: forall k m b0 b1 b2 b3 b4 b5 own t E1 E2
    (OWNEQ: find_merge_own_env own t E1 E2)
    (COLLECT: collect_func ge find_func = OK (own_universe own))
    (SCONT: sound_find_cont k),
    find_merge_pattern_match
      (State find_func
         (Ssequence
            (Sassign_variant (Pderef (Plocal l List_box) List_ty) List Cons
               (Emoveplace (Plocal node Node_ty) Node_ty))
            (Ssequence
               (Sassign (Plocal _retv List_box)
                  (Emoveplace (Plocal l List_box) List_box))
               (Sreturn (Plocal _retv List_box)))) (Klet node Node_ty k)
         (find_env b0 b1 b2 b3 b4 b5)
         own
         m).

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
    (** Note: we need to record the called function of the current
    module in the invariant, so that we can choose the post condition
    when returning from the current module. But the recording would be
    difficult if there are lots of mutual call in the current module,
    where we should record the called function ident in the
    continuation predicate *)
    (FIDEQ: w.(hmap_callee_ext) = hash)
    (PRE: hash_pre_cond_args w.(hmap_hash_range_ext) al),
    sound_state (Callstate v al k m)
| hash_state_internal: forall v al k m t s1 n
    (CALL: call_func hash (Callstate v al k m))
    (FIDEQ: w.(hmap_callee_ext) = hash)
    (STAR: starNf step num_frames ge n (Callstate v al k m) t s1)
    (PRECOND: hash_pre_cond_args w.(hmap_hash_range_ext) al)
    (NOTCALL: not_call_return_state s1)
    (RAN: (1 <= n <= 11)%nat),
    sound_state s1
| hash_returnstate: forall v k m
    (CONT: sound_cont hash k)
    (FIDEQ: w.(hmap_callee_ext) = hash)
    (PRE: hash_post_cond_retv w.(hmap_hash_range_ext) v),
    sound_state (Returnstate v k m)

| callstate_find: forall v al k m
    (CALL: call_func find (Callstate v al k m))
    (FIDEQ: w.(hmap_callee_ext) = find),
    sound_state (Callstate v al k m)
| find_state_internal1: forall s0 s1 t n
    (CALL: call_func find s0)
    (FIDEQ: w.(hmap_callee_ext) = find)
    (STAR: starNf step num_frames ge n s0 t s1)
    (* used to prevent complicated reasoning in proving query/reply
    invariant in at_external state or final state *)
    (NOTCALL: not_call_return_state s1)
    (RAN: (1 <= n <= 20)%nat),
    sound_state s1
| find_state_call_process: forall b v k m
    (PROC: Genv.invert_symbol se b = Some process)
    (FIDEQ: w.(hmap_callee_ext) = find)
    (CASTED: val_casted v (Tbox type_int32s) )
    (CONT: find_cont_ret_process k),
    sound_state (Callstate (Vptr b Ptrofs.zero) [v] k m)
| find_state_return_process: forall v k m
    (CONT: find_cont_ret_process k)
    (FIDEQ: w.(hmap_callee_ext) = find),
    sound_state (Returnstate v k m)
(* state comes from return process *)
| find_state_internal2: forall s0 s1 s2 t1 t2 n
    (RET: return_process s0)
    (* prevent num_frames inconsistent between s0 and s2 *)
    (STEP: step ge s0 t1 s1)
    (STAR: starNf step num_frames ge n s1 t2 s2)
    (NOTCALL: not_call_return_state s2)
    (FIDEQ: w.(hmap_callee_ext) = find)
    (RAN: (0 <= n <= 12)%nat),
    sound_state s2          
(* state comes from return find *)
| find_state_internal3: forall s0 s1 s2 t1 t2 n
    (RET: return_find s0)
    (* prevent num_frames inconsistent between s0 and s2 *)
    (STEP: step ge s0 t1 s1)
    (STAR: starNf step num_frames ge n s1 t2 s2)
    (NOTCALL: not_call_return_state s2)
    (FIDEQ: w.(hmap_callee_ext) = find)
    (RAN: (0 <= n <= 12)%nat),
    sound_state s2
(* merge point of the pattern match in find function *)
| find_state_internal4: forall s1 s2 t2 n
    (RET: find_merge_pattern_match s1)
    (STAR: starNf step num_frames ge n s1 t2 s2)
    (NOTCALL: not_call_return_state s2)
    (FIDEQ: w.(hmap_callee_ext) = find)
    (RAN: (0 <= n <= 28)%nat),
    sound_state s2
(* This state can be return from the current find function or return
from the last find function *)
| find_returnstate: forall v k m
    (CONT: sound_find_cont k)
      (FIDEQ: w.(hmap_callee_ext) = find),
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

Lemma hash_args_params_norepet:
  list_norepet
    (var_names (fn_params hash_func) ++ var_names (fn_vars hash_func)).
Proof.
  eapply proj_sumbool_true.
  instantiate (1 := list_norepet_dec ident_eq (var_names (fn_params hash_func) ++ var_names (fn_vars hash_func))).
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
Proof.
 unfold init_own_env.
 destruct collect_func eqn: A. cbn [bind].

 set (empty_map := (PTree.map
                      (fun (_ : positive) (_ : InitDomain.LPaths.t) =>
                         InitDomain.Paths.empty) t)) in *.
 set (initParams:= (InitDomain.add_place_list t
                      (places_of_locals (fn_params hash_func ++ fn_vars hash_func))
                      empty_map)) in *.
 set (flag := check_own_env_consistency empty_map empty_map initParams t) in *.
 generalize (eq_refl flag).
 generalize flag at 1 3.
 intros flag0 E. destruct flag0; try congruence.
 eexists; eauto.
 unfold flag in E. unfold initParams, empty_map in *.  
 replace t with ((collect_stmt (Smallstep.globalenv (linked_list_sem se))
                    (fn_body hash_func)
                    (fold_right
                       (InitDomain.collect_place
                          (Smallstep.globalenv (linked_list_sem se)))
                       (PTree.empty InitDomain.LPaths.t)
                       (map
                          (fun elt : ident * type => Plocal (fst elt) (snd elt))
                          (fn_params hash_func ++ fn_vars hash_func))))) in *.
 vm_compute in E. congruence.
 unfold collect_func in A. congruence.
 unfold collect_func in A. congruence.
Qed.

Local Open Scope sep_scope.

Lemma function_entry_find_progress: forall vl m,
    length_of_args find = length vl ->
  exists e m2, function_entry ge find_func vl m e m2.
Proof.
  intros. destruct vl; inv H. destruct vl; inv H1. destruct vl; inv H0.
  destruct (Mem.alloc m 0 (sizeof ge List_box)) as (m1 & b1) eqn: A1.
  destruct (Mem.alloc m1 0 (sizeof ge type_int32s)) as (m2 & b2) eqn: A2.
  destruct (Mem.alloc m2 0 (sizeof ge List_box)) as (m3 & b3) eqn: A3.
  destruct (Mem.alloc m3 0 (sizeof ge Node_ty)) as (m4 & b4) eqn: A4.
  destruct (Mem.alloc m4 0 (sizeof ge List_box)) as (m5 & b5) eqn: A5.
  destruct (Mem.alloc m5 0 (sizeof ge Tbox_int)) as (m6 & b6) eqn: A6.
  exploit alloc_rule. eapply A1. lia. vm_compute. congruence.
  instantiate (1 := Separation.pure True). simpl. auto.
  intros PM1.
  exploit alloc_rule. eapply A2. lia. vm_compute. congruence.
  eapply PM1. intros PM2.
  exploit alloc_rule. eapply A3. lia. vm_compute. congruence.
  eapply PM2. intros PM3.
  exploit alloc_rule. eapply A4. lia. vm_compute. congruence.
  eapply PM3. intros PM4.
  exploit alloc_rule. eapply A5. lia. vm_compute. congruence.
  eapply PM4. intros PM5.
  exploit alloc_rule. eapply A6. lia. vm_compute. congruence.
  eapply PM5. intros PM6.
  (* store the first param *)
  exploit (storev_rule Mptr m6 b1 0 v (fun _ => True) (eq (Val.load_result Mptr v))).
  do 4 eapply sep_drop in PM6.
  eapply sep_swap12 in PM6.
  eapply range_contains with (ofs := 0).  rewrite Z.add_0_l. eapply PM6.
  eapply Z.divide_0_r. eauto.
  intros (m7 & STORE1 & PM7).
  (* store the second param *)
  exploit (storev_rule Mint32 m7 b2 0 v0 (fun _ => True) (eq (Val.load_result Mint32 v0))).
  eapply range_contains with (ofs := 0).  rewrite Z.add_0_l. eapply PM7.
  eapply Z.divide_0_r. eauto.
  intros (m8 & STORE2 & PM8).
  do 2 eexists.
  econstructor. eapply find_args_params_norepet.
  - repeat (econstructor; eauto).
  - econstructor. reflexivity.
    econstructor. reflexivity. eauto.
    econstructor. reflexivity.
    econstructor. reflexivity. eauto.
    econstructor.
Qed.

Lemma function_entry_hash_progress: forall vl m,
    length_of_args hash = length vl ->
  exists e m2, function_entry ge hash_func vl m e m2.
Proof.
  intros. destruct vl; inv H. destruct vl; inv H1. destruct vl; inv H0.
  destruct (Mem.alloc m 0 (sizeof ge type_int32s)) as (m1 & b1) eqn: A1.
  destruct (Mem.alloc m1 0 (sizeof ge type_int32u)) as (m2 & b2) eqn: A2.
  destruct (Mem.alloc m2 0 (sizeof ge type_int32u)) as (m3 & b3) eqn: A3.
  exploit alloc_rule. eapply A1. lia. vm_compute. congruence.
  instantiate (1 := Separation.pure True). simpl. auto.
  intros PM1.
  exploit alloc_rule. eapply A2. lia. vm_compute. congruence.
  eapply PM1. intros PM2.
  exploit alloc_rule. eapply A3. lia. vm_compute. congruence.
  eapply PM2. intros PM3.
  (* store the first param *)
  exploit (storev_rule Mint32 m3 b1 0 v (fun _ => True) (eq (Val.load_result Mint32 v))).
  do 1 eapply sep_drop in PM3.
  eapply sep_swap12 in PM3.
  eapply range_contains with (ofs := 0).  rewrite Z.add_0_l. eapply PM3.
  eapply Z.divide_0_r. eauto.
  intros (m4 & STORE1 & PM4).
  (* store the second param *)
  exploit (storev_rule Mint32 m4 b2 0 v0 (fun _ => True) (eq (Val.load_result Mint32 v0))).
  eapply range_contains with (ofs := 0).  rewrite Z.add_0_l. eapply PM4.
  eapply Z.divide_0_r. eauto.
  intros (m5 & STORE2 & PM5).
  do 2 eexists.
  econstructor. eapply hash_args_params_norepet.
  - repeat (econstructor; eauto).
  - econstructor. reflexivity.
    econstructor. reflexivity. eauto.
    econstructor. reflexivity.
    econstructor. reflexivity. eauto.
    econstructor.
Qed.
  


(* Compute (variant_field_offset (proj1_sig build_ce_ok) Nil [Member_plain Nil Tunit; Member_plain Cons Node_ty]). *)


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
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_l: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get l w) (Plocal l List_box) List_box = OK [(Pderef (Plocal l List_box) List_ty, true); (Plocal l List_box, false)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.

Lemma split_drop_place_find_deref_l: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get l w) (Pderef (Plocal l List_box) List_ty) List_ty = OK [(Pderef (Plocal l List_box) List_ty, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.
Qed.


Lemma split_drop_place_find_node: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Plocal node Node_ty) Node_ty = OK [(Pfield (Plocal node Node_ty) key type_int32s, true);
    (Pfield (Plocal node Node_ty) LinkedList.val (Tbox type_int32s), true);
    (Pfield (Plocal node Node_ty) next List_box, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.

Lemma split_drop_place_find_node_next: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Pfield (Plocal node Node_ty) next List_box) List_box = OK [(Pfield (Plocal node Node_ty) next List_box, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.

Lemma split_drop_place_find_node_val: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get node w) (Pfield (Plocal node Node_ty) LinkedList.val Tbox_int) Tbox_int = OK [(Pfield (Plocal node Node_ty) LinkedList.val Tbox_int, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.



Lemma split_drop_place_find_tmp: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get tmp w) (Plocal tmp List_box) List_box = OK [(Plocal tmp List_box, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.

Lemma split_drop_place_find_tmpv: forall w,
    collect_func ge find_func = OK w ->
    split_drop_place ge (PathsMap.get tmpv w) (Plocal tmpv Tbox_int) Tbox_int = OK [(Plocal tmpv Tbox_int, true)].
Proof.
  intros. unfold collect_func in H.
  vm_compute in H. inv H. reflexivity.  
Qed.


Lemma sound_call_cont: forall f k,
    sound_cont f k ->
    (* Actually ck is the same as k *)
    exists ck, call_cont k = Some ck
          /\ sound_cont f ck.
Proof.
  intros. unfold sound_cont in H.
  destruct ident_eq in H; subst.
  - inv H.
    + eexists. split; eauto.
      reflexivity. vm_compute. eapply sound_find_Kstop.
    + simpl. eexists. split; eauto.
      econstructor; eauto.
  - destruct ident_eq in H; subst; try contradiction.
    + inv H. eexists. split; eauto. reflexivity. econstructor.
Qed.
    
Lemma call_cont_num_frames_eq: forall k1 k2,
    call_cont k1 = Some k2 ->
    num_frames_cont k1 = num_frames_cont k2.
Proof.
  induction k1; intros k2 CK; simpl in CK; inv CK; auto.
Qed.


Lemma initial_preservation_progress: forall q,
    valid_query (linked_list_sem se) q = true ->
    query_inv hmap_ext_inv w q ->
    exists s, initial_state ge q s
         /\ (forall s, initial_state ge q s -> sound_state s).
Proof.
  intros q VQ QINV.
  (* destruct query_inv *)
  simpl in QINV. red in QINV.
  destruct q. simpl in QINV. destruct rsq_vf; try contradiction.
  destruct Ptrofs.eq_dec in QINV; try contradiction. subst.
  destruct Genv.invert_symbol eqn: SYM in QINV; try contradiction.  
  rewrite hmap_senv_eq in *.
  exploit Genv.find_def_spec. erewrite SYM.
  instantiate (1:= linked_list_mod).
  intros FINDF.
  red in QINV.
  eexists (Callstate (Vptr b Ptrofs.zero) rsq_args Kstop rsq_mem).
  (* two cases of i *)  
  repeat destruct ident_eq in QINV; try contradiction; subst.
  (* call find *)
  - split.
    + Strategy opaque [linked_list_mod].
      inv QINV. econstructor; eauto.
    + intros. inv H. inv QINV.
      eapply callstate_find.
      econstructor. eauto. econstructor.
      eauto. auto.
  (* call hash *)
  - inv QINV. split.
    + econstructor; eauto.
      rewrite hmap_senv_eq in *. eauto.
    + intros. inv H.
      eapply hash_callstate; eauto.
      econstructor; auto.
      constructor. inv PRECOND. reflexivity.
Qed.

Lemma linked_list_final: forall s r,
    sound_state s ->
    final_state s r ->
    reply_inv hmap_ext_inv w r.
Proof.
  intros s r SINV FINAL.
  simpl.
  inv FINAL. inv SINV; try simpl in NOTCALL; try contradiction.
  (* return from hash *)
  - rewrite FIDEQ.
    econstructor; eauto.
  (* call process (contradiction) *)
  - inv CONT.
  (* return from find *)
  - rewrite FIDEQ.
    econstructor; eauto.
Qed.

Lemma linked_list_external: forall s q,
    sound_state s ->
    at_external ge s q ->
    exists w', symtbl_inv list_ext_inv w' se
          /\ query_inv list_ext_inv w' q
          /\ forall r, reply_inv list_ext_inv w' r ->
                 (exists s', after_external s r s'
                        /\ (forall s', after_external s r s' -> sound_state s')).
Proof.
  intros s q SINV EXT. inv EXT.
  inv SINV; try simpl in NOTCALL; try contradiction.
  (* call hash (contradiction) *)
  - inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal hash_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    rewrite H in FIND. inv FIND.
  (* call find (contradiction) *)
  - inv CALL.
    assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (Internal find_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite SYM.
      auto. }
    rewrite H in FIND. inv FIND.
  (* call process *)
  - assert (FIND: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some process_ext).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite PROC.
      auto. }
    rewrite H in FIND. inv FIND.
    assert (FIND2: Genv.find_funct (Genv.globalenv se hash_map_prog) (Vptr b Ptrofs.zero) = Some (Ctypes.Internal process_func)).
    { simpl. destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff.
      rewrite Genv.find_def_spec. rewrite PROC.
      auto. }
    exists (Build_list_world_ext process se).
    split. simpl. split; auto.
    repeat apply conj; auto.
    + replace (genv_cenv ge) with (prog_comp_env linked_list_mod) by auto.
      simpl. red. simpl.
      rewrite dec_eq_true. rewrite PROC.
      red. rewrite dec_eq_true.
      replace [Tbox type_int32s] with (type_list_of_typelist (Tcons (Tbox type_int32s) Tnil)) by reflexivity.
      econstructor; eauto.
      econstructor. auto. econstructor.
    + intros. inv H0.
      destruct r.
      eexists. split. 
      econstructor.
      intros. inv H0.
      eapply find_state_return_process; eauto.
Qed.
      
Local Open Scope sep_scope.

Lemma step_hash_callstate_preservation_progress: forall v al k m
   (CALL: call_func hash (Callstate v al k m))
   (FIDEQ : hmap_callee_ext w = hash)
   (PRE : hash_pre_cond_args (hmap_hash_range_ext w) al),
    (not_stuck (linked_list_sem se) (Callstate v al k m) \/
       step_mem_error ge (Callstate v al k m)) /\
      (forall (s' : state) (t : trace), step ge (Callstate v al k m) t s' -> sound_state s').
Proof.
  intros.
  generalize CALL as CALL1. intros.
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
Qed.

(* simpl in H with a easy-to-check proof term. *)
Ltac simpl_in H :=
  let type_of_H := type of H in
  let type_of_H' := eval cbn in type_of_H in
  lazymatch goal with
  | |- ?Goal =>
      revert H;
      refine ((_ : type_of_H' -> Goal) : type_of_H -> Goal);
      intros H
  end.

Lemma bind_error: forall (A B: Type) (f: A -> res B) msg,
    bind (Error msg) f = Error msg.
Proof.
  intros. reflexivity.
Qed.

Lemma error_ok_contradict {A: Type}: forall (a: A) msg,
    Error msg = OK a -> False.
Proof.
  intros. congruence.
Qed.

Lemma step_hash_state_internal_preservation_progress: forall s v al k m t n
  (CALL : call_func hash (Callstate v al k m))
  (FIDEQ : hmap_callee_ext w = hash)
  (STAR : starNf step num_frames ge n (Callstate v al k m) t s)
  (PRECOND : hash_pre_cond_args (hmap_hash_range_ext w) al)
  (NOTCALL : not_call_return_state s)
  (RAN : (1 <= n <= 11)%nat),
    (not_stuck (linked_list_sem se) s \/ step_mem_error ge s) /\
      (forall (s' : state) (t0 : trace), step ge s t0 s' -> sound_state s').
Proof.
  intros.
  generalize CALL as CALL1. intros.
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
  (* construct own_env *)
  destruct (collect_func ge hash_func) eqn: A; unfold init_own_env in INITOWN.
  2: { rewrite A in INITOWN at 1. cbn [bind] in INITOWN. congruence. }
  rewrite A in INITOWN. cbn [bind] in INITOWN.
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
  instantiate (1 := Vint (hmap_hash_range_ext w)). instantiate (1 := fun v => v = Vint (hmap_hash_range_ext w)). simpl. auto.
  intros (m1'' & STORE2 & PM5).
  setoid_rewrite H1 in STORE2. inv STORE2.
  (* load k and range *)
  exploit load_rule. eapply PM5.
  intros (?v & LOAD1 & PV1). subst.
  exploit load_rule. eapply sep_pick1. eapply PM5.
  intros (?v & LOAD2 & PV2). subst.
  (* show that the remainder operation can succeed *)
  assert (MOD: exists r, sem_mod (Vint k0) (Ctypes.Tint I32 Signed noattr)
                      (Vint (hmap_hash_range_ext w)) (Ctypes.Tint I32 Unsigned noattr) m1'' = Some (Vint r)
                    /\ Int.ltu r (hmap_hash_range_ext w) = true).
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
     exploit (Z.mod_bound_or (Int.unsigned (cast_int_int I32 Unsigned k0)) (Int.unsigned (hmap_hash_range_ext w))). lia.
     intros [E1|E2]; lia. 
     exploit (Z.mod_bound_or (Int.unsigned (cast_int_int I32 Unsigned k0)) (Int.unsigned (hmap_hash_range_ext w))). lia.
     generalize (Int.unsigned_range_2 (hmap_hash_range_ext w)). intros R2.
     intros [E1|E2]; lia.  }
  destruct MOD as (r & SEMOD & RSPEC).
  (* store the vaule to retv *)
  exploit storev_rule. eapply range_contains with  (ofs:=0) (chunk:= Mint32).
  eapply sep_comm.
  eapply PM5. eapply Z.divide_0_r. 
  instantiate (1 := Vint r). instantiate (1 := fun v => v = Vint r /\ Int.ltu r (hmap_hash_range_ext w) = true). simpl. auto.
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
  
(* The Coq kernel would unfold collect_func when performing type
  checking in Qed, which makes the proof very slow!!! So we make it
  opaque before the Qed. Note that we should make it transparent when
  we want to unfold collect_func *)
(* tell type checker not to unfold collect_func in type checking *)
Strategy opaque [collect_func].  
Qed.

Lemma step_callstate_find_preservation_progress: forall v al k m
   (CALL : call_func find (Callstate v al k m))
   (FIDEQ : hmap_callee_ext w = find),
     (not_stuck (linked_list_sem se) (Callstate v al k m) \/
        step_mem_error ge (Callstate v al k m)) /\
       (forall (s' : state) (t : trace), step ge (Callstate v al k m) t s' -> sound_state s').
Proof.
  intros.  
  generalize CALL as CALL1. intros.
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
Qed.

Lemma step_find_state_internal1_preservation_progress: forall s s0 t n
   (CALL : call_func find s0)
   (FIDEQ : hmap_callee_ext w = find)
   (STAR : starNf step num_frames ge n s0 t s)
   (NOTCALL : not_call_return_state s)
   (RAN : (1 <= n <= 20)%nat),
     (not_stuck (linked_list_sem se) s \/ step_mem_error ge s) /\
       (forall (s' : state) (t0 : trace), step ge s t0 s' -> sound_state s').
Proof.
  Strategy transparent [collect_func].   
  intros.
  generalize CALL as CALL1.
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
  (* construct own_env *)
  destruct (collect_func ge find_func) eqn: A; unfold init_own_env in INITOWN.
  2: { rewrite A in INITOWN at 1. cbn [bind] in INITOWN. congruence. }
  rewrite A in INITOWN. cbn [bind] in INITOWN.
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
  inv ENTRY. inv ALLOC. inv H7. inv H9. inv H10. inv H11. inv H12. inv H13.
  inv STAR0.
  (* stop here: evaluate the if statement *)
  { split.
    - (** decide whether there would be memory error  *)
      destruct (Mem.valid_access_dec m' Mptr b1 0 Readable) eqn: VA1.
      + exploit Mem.valid_access_load. eapply v. intros (v1 & LOAD1).
        (* we should show thata v1 must be a pointer *)
        destruct (val_is_ptr v1) eqn: VPTR.
        * destruct v1; simpl in VPTR; try congruence.
          destruct (Mem.valid_access_dec m' Mint32 b6 (Ptrofs.unsigned i) Readable) eqn: VA2.
          -- exploit Mem.valid_access_load. eapply v0. intros (v2 & LOAD2).
             destruct (val_is_int v2) eqn: VINT.
             ++ destruct v2; simpl in VINT; try congruence.
                destruct (Z.lt_decidable (Int.unsigned i0) 2).
                ** left. red.
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
                   simpl. unfold list_length_z. simpl. auto.
                   reflexivity. 
                   simpl.
                   instantiate (1 := Int.eq i0 (Int.repr 0)).
                   destruct (Int.eq i0 (Int.repr 0)) eqn: EQZ; reflexivity.
                (* range check error *)
                ** right.
                   eapply step_ifthenelse_error. econstructor.
                   eapply eval_Ecktag_error3.
                   econstructor. econstructor. reflexivity.
                   econstructor. reflexivity. eauto. eauto. reflexivity.
                   reflexivity. reflexivity. eauto.
             (* The tag is not an Int value *)
             ++ right. eapply step_ifthenelse_error.
                econstructor. eapply eval_Ecktag_error2.
                econstructor. econstructor. reflexivity.
                econstructor. reflexivity. eauto. intros.
                intro. rewrite LOAD2 in H. inv H. simpl in *. congruence.               
          (* The memory location of tag is not loadable *)
          -- right. eapply step_ifthenelse_error.
             econstructor. eapply eval_Ecktag_error2.
             econstructor. econstructor. reflexivity.
             econstructor. reflexivity. eauto.
             intro. intro. eapply n.
             eapply Mem.load_valid_access. eauto.
        (* The value loaded from the place is not a pointer *)
        * right. apply step_ifthenelse_error.
          econstructor. eapply eval_Ecktag_error1.
          eapply eval_Pderef_error3. econstructor. reflexivity.
          econstructor. reflexivity. eauto. auto.
      (* The block of l is not loadable *)
      + right. eapply step_ifthenelse_error.
        econstructor. eapply eval_Ecktag_error1.
        eapply eval_Pderef_error2.
        econstructor. reflexivity.
        econstructor. reflexivity. eauto.          
    (* Invariant preservation *)
    - intros. eapply find_state_internal1 with (n:=2%nat); eauto.
      eapply starNf_step_right; eauto.
      inv H; simpl; auto.
      inv H; simpl; auto. lia. }
  (* destruct the if step *)
  inv STEP.
  2: { destruct H13; unfold find_body in H; try congruence. }
  (* get the bool value *)
  simpl in H17. inv H15. inv H0.
  simpl in PTY. unfold List_ty in PTY. inv PTY.
  vm_compute in CO. inv CO. vm_compute in FTAG. inv FTAG.
  simpl in RANGE. unfold list_length_z in RANGE. simpl in RANGE.
  destruct (Int.eq tag (Int.repr 0)) eqn: EQZ; vm_compute in H17; inv H17.
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
    2: { destruct H13; congruence. }
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
            -- right. econstructor.
               eapply step_dropinsert_assign_error5.
               econstructor. reflexivity.
               econstructor. econstructor. econstructor. reflexivity.
               econstructor. reflexivity. eauto. reflexivity.
               eauto.
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
    2: { destruct H13; congruence. }
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
      - destruct (Mem.valid_access_dec m7 Mptr b2 0 Readable) eqn: ?VA.
        + exploit Mem.valid_access_load. eapply v0.
          intros (?v & ?LOAD).
          destruct (sem_cast v2 List_box List_box) eqn: ?CAST.
          (*   Compute (blocks_of_env (proj1_sig build_ce_ok) (PTree.set tmpv (b5, Tbox_int) *)
          (* (PTree.set tmp (b4, List_box) *)
          (*    (PTree.set node (b3, Node_ty) *)
          (*       (PTree.set _retv (b2, List_box) *)
          (*          (PTree.set LinkedList.k (b0, type_int32s) *)
          (*             (PTree.set l (b1, List_box) empty_env))))))). *)
          * destruct (Mem.free_list m7 [(b3, 0, 24); (b4, 0, 8); (b1, 0, 8); (b5, 0, 8); (b2, 0, 8); (b0, 0, 4)]) eqn: ?FREELIST.
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
          * right. econstructor.
            eapply step_dropinsert_return_error3.
            econstructor. econstructor. econstructor. reflexivity.
            econstructor. reflexivity. eauto. reflexivity.
            eauto.
        + right. econstructor.
          eapply step_dropinsert_return_error1; eauto.
          econstructor. eapply eval_Eplace_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. inv H. inv SDROP.
        exploit sound_call_cont; eauto.
        intros (ck1 & CK & SCK). rewrite CONT in CK. inv CK.          
        eapply find_returnstate. eauto. eauto. }
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
      (** ck1 is Kcall. Fill this code after finishing calling
        find *)
      - split.
        + destruct (val_casted_dec v2 List_box).
          * destruct (Mem.valid_access_dec m8 Mptr b12 0 Writable).
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
          (** The return value is not val_casted. Treat it as
            a kind of error which is proved move checking *)
          * right. eapply step_returnstate_error3. reflexivity.
            econstructor. reflexivity. eauto.
        + intros.
          eapply find_state_internal3 with (n:=0%nat).
          2: eauto.
          econstructor. econstructor. eauto. eauto.
          econstructor. 
          inv H; simpl; eauto. eauto. lia. }
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
    2: { destruct H13; congruence. }
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
      - destruct (Mem.range_perm_dec m' b7 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) ((Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 8))) + 24) Cur Readable).
        + exploit Mem.range_perm_loadbytes. eapply r. intros (bys & LOADBYTES).
          destruct (Mem.range_perm_dec m' b3 0 (0 + 24) Cur Writable).
          * edestruct Mem.range_perm_storebytes with (bytes:= bys) as (?m & ?STOREBYTES).
            erewrite Mem.loadbytes_length; eauto. eauto.
            destruct (check_assign_copy (Smallstep.globalenv (linked_list_sem se)) (typeof_place (Plocal node Node_ty)) b3 Ptrofs.zero b7 (Ptrofs.add ofs (Ptrofs.repr 8))) eqn: CAC.
            -- left. red. do 2 right.
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
                          (typeof_place (Plocal node Node_ty))) with 24 by reflexivity.
               rewrite LOADBYTES.
               rewrite Ptrofs.unsigned_zero. rewrite STOREBYTES.
               rewrite CAC.
               reflexivity.
            (** TODO: we can treat check_assign_copy failure as a
              kind of memory error which can be ruled out in move
              checking. The approach is that we add a case of memory
              error in step_assign when the type of LHS is
              Tstruct/Tvariant. We also check the RHS must be (Eplace
              p') so that we can prove check_assign_copy success by
              case analysis of (RHS = p') or (RHS <> p'), using the
              fact that different place must have different location
             *)
            -- right. econstructor.
               eapply step_dropinsert_assign_error4.
               econstructor. reflexivity.
               econstructor. econstructor. econstructor.
               eauto. reflexivity. reflexivity. eauto.
               rewrite EQONE. reflexivity.
               instantiate (1 := 8). reflexivity.
               reflexivity. vm_compute. auto.
               auto.
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
      - destruct (Mem.valid_access_dec m7 Mint32 b0 0 Readable).
        + exploit Mem.valid_access_load. eauto.
          intros (?v & ?LOAD).
          destruct (Mem.valid_access_dec m7 Mint32 b3 0 Readable).
          * exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (Cop.sem_cast v2 Ctypes.type_int32s Ctypes.type_int32s m7) eqn: ?CAST.
            -- destruct (Cop.sem_cast v4 Ctypes.type_int32s Ctypes.type_int32s m7) eqn: ?CAST.
               ++ exploit Cop.cast_val_is_casted. eapply CAST. intros ?CASTED.
                  exploit Cop.cast_val_is_casted. eapply CAST0. intros ?CASTED.
                  (* FIXME: For now, we just use the fact that
                    Archi.ptr = true to prove that the value must not
                    be pointer (we cannot compare pointer with
                    int). In fact, we should consider to use rust
                    sem_cast in eval_Ebinop_error2. But for now we
                    cannot prove eval_pexpr_progress_no_mem_error as
                    the semantics of eval_Ebinop is too waek. It uses
                    sem_binary_operation_rust which operates on C
                    types.  *)
                  assert (CMP: exists bv, sem_cmp Ceq v2 (Ctypes.Tint I32 Signed noattr) v4 (Ctypes.Tint I32 Signed noattr) m7 = Some (Val.of_bool bv)).
                  { simpl. unfold sem_cmp, sem_binarith. simpl.
                    inv CASTED. inv CASTED0.
                    - setoid_rewrite CAST. setoid_rewrite CAST0. eauto.
                    - inv H2.
                    - inv H1. }
                  destruct CMP as (bv & CMP).
                  (* exploit sem_cast_id. eapply CAST. intros ?CCAST. *)
                  (* exploit sem_cast_id. eapply CAST0. intros ?CCAST. *)
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
                  simpl. eauto. 
                  reflexivity. 
                  instantiate (1 := bv). 
                  destruct bv eqn: ?IEQ; reflexivity.
               (* cast fails *)
               ++ right.
                  eapply step_ifthenelse_error.
                  econstructor. eapply eval_Ebinop_error2.
                  econstructor. econstructor. reflexivity.
                  econstructor. reflexivity. eauto.
                  econstructor. econstructor. econstructor. reflexivity. reflexivity.
                  reflexivity. reflexivity.
                  econstructor. reflexivity. eauto.
                  all: try reflexivity.
                  simpl. setoid_rewrite CAST0. auto.
            (* cast fails *)
            --  right.
                eapply step_ifthenelse_error.
                econstructor. eapply eval_Ebinop_error2.
                econstructor. econstructor. reflexivity.
                econstructor. reflexivity. eauto.
                econstructor. econstructor. econstructor. reflexivity. reflexivity.
                reflexivity. reflexivity.
                econstructor. reflexivity. eauto.
                all: try reflexivity.
                simpl. setoid_rewrite CAST. auto.
          (* load fails *)
          * right.
            eapply step_ifthenelse_error.
            econstructor. econstructor.
            right. eapply eval_Eplace_error2.
            econstructor. econstructor. reflexivity. reflexivity.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.                                
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
    destruct b8.
    
    (* evaluate the true branch *)
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
          eapply split_drop_place_find_tmpv. eauto.
        - intros. eapply find_state_internal1 with (n:=18%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { vm_compute in OWNTY0. congruence. }
      clear OWNTY0.
      erewrite split_drop_place_find_tmpv in SPLIT; eauto.
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
          1-2: inv H; inv SDROP; simpl; auto. lia. }
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
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.        
      (* evaluate Dcall *)
      { split.
        - destruct (Mem.valid_access_dec m7 Mptr b3 8 Readable).
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v3 Tbox_int Tbox_int) eqn: ?CAST.
            * left. red. do 2 right.
              (* construct the block of process *)
              generalize ((proj1 wf_senv) process). intros FINDPRO.
              exploit FINDPRO. reflexivity. clear FINDPRO.
              intros (?b & PRO_G & FINDPRO & FINDINFO & LINKORD).
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
            (* eval_exprlist sem_cast fails *)
            * generalize ((proj1 wf_senv) process). intros FINDPRO.
              exploit FINDPRO. reflexivity. clear FINDPRO.
              intros (?b & PRO_G & FINDPRO & FINDINFO & LINKORD).
              right. econstructor.
              eapply step_dropinsert_call_error2.
              econstructor. econstructor. eauto.
              eapply deref_loc_reference. reflexivity. reflexivity.
              (* evaluate the arguments *)
              eapply eval_Econs_mem_error3.
              econstructor.
              econstructor. econstructor. econstructor.
              reflexivity. reflexivity. reflexivity.
              reflexivity. econstructor. reflexivity.
              eauto. eauto.
          (* load fails *)
          + right.
            generalize ((proj1 wf_senv) process). intros FINDPRO.
            exploit FINDPRO. reflexivity. clear FINDPRO.
            intros (?b & PRO_G & FINDPRO & FINDINFO & LINKORD).
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
          inv H22. inv H0. inv DEF; simpl in H; try congruence.
          (* show arguments are casted*)
          inv H23. inv H12. inv H20.
          exploit cast_val_is_casted. eapply H3. intros CASTED.
          generalize ((proj1 wf_senv) process). intros FINDPRO.
          exploit FINDPRO. reflexivity. clear FINDPRO.
          intros (?b & PRO_G & FINDPRO & FINDINFO & LINKORD).
          simpl in GADDR. rewrite GADDR in FINDPRO. inv FINDPRO.
          eapply find_state_call_process.
          (* invert_symbol *)
          erewrite Genv.find_invert_symbol; eauto.
          auto. auto.
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
          1-2: inv H; inv SDROP; simpl; auto. lia. }
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
          1-2: inv H; inv SDROP; simpl; auto. lia. }
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
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *. 
      (* evaluate Dcall *)
      { split.
        - (* construct the block of find *)
          generalize ((proj2 wf_senv) find). intros FINDF.
          exploit FINDF. reflexivity. clear FINDF.
          intros (?b & PRO_G & FINDF & FINDINFO & LINKORD).
          destruct (Mem.valid_access_dec m7 Mptr b3 16 Readable).
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v3 List_box List_box) eqn: ?CAST.
            * destruct (Mem.valid_access_dec m7 Mint32 b0 0 Readable).
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
                 ++ right. econstructor. eapply step_dropinsert_call_error2.
                    econstructor. econstructor. eauto.
                    eapply deref_loc_reference. reflexivity. reflexivity.
                    (* evaluate the arguments *)
                    eapply eval_Econs_mem_error2.
                    econstructor.
                    econstructor. econstructor. econstructor.
                    reflexivity. reflexivity. reflexivity.
                    reflexivity. econstructor. reflexivity.
                    eauto. 
                    eapply eval_Econs_mem_error3.
                    econstructor.
                    econstructor. econstructor. reflexivity.
                    econstructor. reflexivity. eauto.
                    eauto.
              (* load errors *)
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
            * right. econstructor. eapply step_dropinsert_call_error2.
              econstructor. econstructor. eauto.
              eapply deref_loc_reference. reflexivity. reflexivity.
              (* evaluate the arguments *)
              eapply eval_Econs_mem_error3.
              econstructor.
              econstructor. econstructor. econstructor.
              reflexivity. reflexivity. reflexivity.
              reflexivity. econstructor. reflexivity.
              eauto. eauto.
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
          inv H22. inv H0.
          inv DEF; simpl in H; try congruence.
          eapply callstate_find. econstructor.
          eapply Genv.find_invert_symbol. eauto.
          econstructor. eauto. eauto.
          inv H23. inv H12. inv H22. reflexivity. eauto. }
      inv STEP. inv SDROP. simpl in FEQ19.
      exfalso. eapply Nat.neq_succ_diag_l; eauto. }
  }
  Strategy opaque [collect_func].
Qed.


Lemma step_preservation_progress: forall s,
    sound_state s ->
    (not_stuck (linked_list_sem se) s \/ step_mem_error ge s)
    /\ (forall s' t, step ge s t s' ->
               sound_state s').
Proof.
  Strategy transparent [collect_func].
  intros s INV. inv INV.
  (* callstate in hash *)
  - eapply step_hash_callstate_preservation_progress; eauto.
  (* internal state in hash function *)
  - eapply step_hash_state_internal_preservation_progress; eauto.    
  (* returnstate in hash *)
  - inv CONT. inv PRE.
    split.
    + left. left. eexists. econstructor.
    + intros. inv H.
  (* callstate in find *)
  - eapply step_callstate_find_preservation_progress; eauto.
  (* find_state_internal1 *)
  - eapply step_find_state_internal1_preservation_progress; eauto.    
  (* call process *)
  -  assert (FINDF: Genv.find_funct ge (Vptr b Ptrofs.zero) = Some (process_ext)).
    { simpl. rewrite dec_eq_true. unfold Genv.find_funct_ptr.
      rewrite Genv.find_def_spec.
      rewrite PROC. eauto. }
    split.    
    + left. right. left.
      eexists. econstructor.
      simpl in FINDF. setoid_rewrite FINDF.
      f_equal. unfold process_ext. f_equal.
    (* use the fact that there is not step in the state of
    at_external *)
    + intros. inv H. rewrite FINDF in FIND. inv FIND.
      rewrite FINDF in FIND. inv FIND. inv H6.
  (* return from process *)
  - split.
    + inv CONT.
      destruct (val_casted_dec v Tbox_int).
      * destruct (Mem.valid_access_dec m Mptr b5 0 Writable).
        -- edestruct Mem.valid_access_store as (?m & ?STORE). eauto.
           left. do 2 right.
           do 2 eexists.
           econstructor. reflexivity.
           econstructor. reflexivity. eauto.
           econstructor. reflexivity.
           eauto.
        -- right.
           eapply step_returnstate_error2. reflexivity.
           econstructor. econstructor. 
           econstructor. reflexivity. eauto.
      (* val is not val_casted in returnstate *)
      * right. eapply step_returnstate_error3; eauto.
        econstructor. reflexivity.
    + intros. eapply find_state_internal2 with (n:=0%nat).
      2: eauto.
      econstructor. auto.
      econstructor. inv H; simpl; auto. eauto. lia.
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
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign to Dassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_to_dropplace_reassign; auto.
        repeat_rewrite_eq_universe.
        erewrite split_drop_place_find_node_val; eauto.
      - intros. eapply find_state_internal2 with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
    erewrite split_drop_place_find_node_val in SPLIT; eauto. inv SPLIT.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal2 with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN. 
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_return *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_return.
      - intros. eapply find_state_internal2 with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *. 
    (* ealuate step_dropinsert_assign *)
    { split.
      - destruct (Mem.valid_access_dec m2 Mptr b5 0 Readable) eqn: VA1.
        (* The argument tmpv is loadable *)
        + exploit Mem.valid_access_load. eapply v0. intros (?v & ?LOAD).
          * destruct (sem_cast v1 Tbox_int Tbox_int) eqn: CAST1.
            (* v0 can be casted *)
            -- destruct (Mem.valid_access_dec m2 Mptr b3 8 Writable) eqn: VA2.
               (* The return variable is writable *)
               ++ edestruct Mem.valid_access_store with (v:= v2) as (?m & ?STORE).
                  eapply v3.
                  left. red. do 2 right.
                  do 2 eexists. econstructor.
                  econstructor; eauto.
                  simpl. unfold Tbox_int. congruence.
                  econstructor. econstructor. reflexivity. reflexivity.
                  reflexivity. reflexivity.
                  econstructor. econstructor. econstructor.
                  reflexivity. econstructor. reflexivity.
                  eauto. econstructor. reflexivity. eauto.
               (* node.val is not writable *)
               ++ right. econstructor.
                  eapply step_dropinsert_assign_error3.
                  econstructor. econstructor. reflexivity. reflexivity.
                  reflexivity. reflexivity. 
                  econstructor. econstructor. econstructor.
                  reflexivity. econstructor. reflexivity.
                  eauto. eauto.
                  eapply assign_loc_value_mem_error. reflexivity.
                  eauto.
            (* v0 cannot be casted *)
            -- right.
               econstructor. eapply step_dropinsert_assign_error5.
               econstructor. econstructor. reflexivity. reflexivity. reflexivity.
               reflexivity. econstructor. econstructor. econstructor.
               reflexivity. econstructor. reflexivity. eauto. reflexivity.
               eauto.
        (* tmpv is not loadable *)
        + right. econstructor.
          eapply step_dropinsert_assign_error1.
          econstructor. eapply eval_Eplace_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. eapply find_state_internal2 with (n:=6%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_end_let *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal2 with (n:=7%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }    
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_escape *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_to_dropplace_escape.
        repeat_rewrite_eq_universe.
        reflexivity. reflexivity.
        eapply split_drop_place_find_tmpv. eauto.          
      - intros. eapply find_state_internal2 with (n:=8%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { inv OWNTY0. }
    erewrite split_drop_place_find_tmpv in SPLIT; eauto.
    inv SPLIT.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal2 with (n:=9%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN. 
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_return *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_return.
      - intros. eapply find_state_internal2 with (n:=10%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.        
    (* evaluate step_dropinsert_escape_to_after *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_escape_to_after.
      - intros. eapply find_state_internal2 with (n:=11%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_endlet *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_endlet.
      - intros. eapply find_state_internal2 with (n:=12%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    destruct NOTRETURN. congruence.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate seq_skip *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. inv H.
        (* step to next invariant point *)
        eapply find_state_internal4 with (n:=0%nat); eauto.
        2: econstructor.
        econstructor; eauto. red. eauto. 
        lia. }
    (* contradiction with RAN *)
    lia.

  (* find_state_internal3 *)
  - generalize RET. intros RET1.
    generalize STEP. intros STEP1.
    generalize STAR as STAR1. intros.
    inv RET. inv STEP. inv H.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate skip_seq *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal3 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign to Dassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal3 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_to_dropplace_reassign; auto.
        repeat_rewrite_eq_universe.
        erewrite split_drop_place_find_node_next; eauto.
      - intros. eapply find_state_internal3 with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP; vm_compute in OWNTY; try congruence.
    erewrite split_drop_place_find_node_next in SPLIT; eauto. inv SPLIT.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal3 with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN. 
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_return *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_return.
      - intros. eapply find_state_internal3 with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *. 
    (* ealuate step_dropinsert_assign *)
    { split.
      - destruct (Mem.valid_access_dec m2 Mptr b4 0 Readable) eqn: VA1.
        (* The argument tmpv is loadable *)
        + exploit Mem.valid_access_load. eapply v0. intros (?v & ?LOAD).
          * destruct (sem_cast v1 Tbox_int Tbox_int) eqn: CAST1.
            (* v0 can be casted *)
            -- destruct (Mem.valid_access_dec m2 Mptr b3 16 Writable) eqn: VA2.
               (* The return variable is writable *)
               ++ edestruct Mem.valid_access_store with (v:= v2) as (?m & ?STORE).
                  eapply v3.
                  left. red. do 2 right.
                  do 2 eexists. econstructor.
                  econstructor; eauto.
                  simpl. unfold List_box. congruence.
                  econstructor. econstructor. reflexivity. reflexivity.
                  reflexivity. reflexivity.
                  econstructor. econstructor. econstructor.
                  reflexivity. econstructor. reflexivity.
                  eauto. econstructor. reflexivity. eauto.
               (* node.val is not writable *)
               ++ right. econstructor.
                  eapply step_dropinsert_assign_error3.
                  econstructor. econstructor. reflexivity. reflexivity.
                  reflexivity. reflexivity. 
                  econstructor. econstructor. econstructor.
                  reflexivity. econstructor. reflexivity.
                  eauto. eauto.
                  eapply assign_loc_value_mem_error. reflexivity.
                  eauto.
            (* v0 cannot be casted *)
            -- right. econstructor. eapply step_dropinsert_assign_error5.
               econstructor. econstructor. reflexivity. reflexivity. reflexivity.
               reflexivity. econstructor. econstructor. econstructor.
               reflexivity. econstructor. reflexivity. eauto. reflexivity.
               eauto.
        (* tmpv is not loadable *)
        + right. econstructor.
          eapply step_dropinsert_assign_error1.
          econstructor. eapply eval_Eplace_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. eapply find_state_internal3 with (n:=6%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_end_let *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal3 with (n:=7%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }    
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_escape *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_to_dropplace_escape.
        repeat_rewrite_eq_universe.
        reflexivity. reflexivity.
        eapply split_drop_place_find_tmp. eauto.
      - intros. eapply find_state_internal3 with (n:=8%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { inv OWNTY0. }
    erewrite split_drop_place_find_tmp in SPLIT; eauto.
    inv SPLIT.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        unfold collect_func in UNI. vm_compute in UNI. inv UNI.
        reflexivity.
      - intros. eapply find_state_internal3 with (n:=9%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { unfold collect_func in UNI. vm_compute in UNI. inv UNI.
         vm_compute in OWN. congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN. 
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_return *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_return.
      - intros. eapply find_state_internal3 with (n:=10%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.        
    (* evaluate step_dropinsert_escape_to_after *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_escape_to_after.
      - intros. eapply find_state_internal3 with (n:=11%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_endlet *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropinsert_endlet.
      - intros. eapply find_state_internal3 with (n:=12%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    destruct NOTRETURN. congruence.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate seq_skip *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. inv H.
        (* step to next invariant point *)
        eapply find_state_internal4 with (n:=0%nat); eauto.
        2: econstructor.
        econstructor; eauto. red. eauto.
        lia. }
    (* contradiction with RAN *)
    lia.
    
  (* find_state_internal4 *)
  - generalize RET. intros RET1.
    generalize STAR as STAR1. intros.
    inv RET. 
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (** The following code may be reused in the execution of returning
    from find *)
    (* evaluate Ssequence *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal4 with (n:=1%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign_variant to Dassign_variant *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal4 with (n:=2%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. eapply step_dropinsert_to_dropplace_reassign.
        reflexivity. reflexivity.
        eapply split_drop_place_find_deref_l. eauto.
      - intros. eapply find_state_internal4 with (n:=3%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { vm_compute in OWNTY. congruence. }
    erewrite split_drop_place_find_deref_l in SPLIT; eauto. inv SPLIT.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        (** TODO: OWNEQ has two cases  *)
        Ltac compute_own_env OWNEQ COLLECT :=
          red in OWNEQ; destruct OWNEQ; subst;
          unfold collect_func in COLLECT; vm_compute in COLLECT; inv COLLECT.
        compute_own_env OWNEQ COLLECT; reflexivity.
      - intros. eapply find_state_internal4 with (n:=4%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
    2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
    clear NOTOWN.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. econstructor.
      - intros. eapply find_state_internal4 with (n:=5%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate assign_variant (many cases of memory error) *)
    { split.
      - destruct (Mem.valid_access_dec m Mptr b1 0 Readable).
        + exploit Mem.valid_access_load. eauto. intros (?v & ?LOAD).
          (* we should show thata v1 must be a pointer (add an error
          case in evaluation of Pderef) *)
          destruct (val_is_ptr v0) eqn: VPTR.
          * destruct v0; simpl in VPTR; try congruence.
            destruct (Mem.range_perm_dec m b3 0 (0 + 24) Cur Readable).
            -- exploit Mem.range_perm_loadbytes. eapply r. intros (bys & LOADBYTES).
               destruct (Mem.range_perm_dec m b (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 8))) (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 8)) + 24) Cur Writable).
               ++ edestruct Mem.range_perm_storebytes with (bytes:= bys) as (?m & ?STOREBYTES).
                  erewrite Mem.loadbytes_length; eauto. eauto.
                  destruct (check_assign_copy (Smallstep.globalenv (linked_list_sem se)) (type_member (Member_plain Cons Node_ty)) b (Ptrofs.add i (Ptrofs.repr 8)) b3 Ptrofs.zero) eqn: CAC.
                  ** destruct (Mem.valid_access_dec m0 Mptr b1 0 Readable).
                     --- exploit Mem.valid_access_load. eauto. intros (?v & ?LOAD).
                         (* we should show thata v1 must be a pointer *)
                         destruct (val_is_ptr v1) eqn: ?VPTR.
                         +++ destruct v1; simpl in VPTR0; try congruence.
                             destruct (Mem.valid_access_dec m0 Mint32 b6 (Ptrofs.unsigned i0) Writable).
                             *** edestruct Mem.valid_access_store with (v:= (Vint (Int.repr 1))) as (?m & ?STORE). eauto.
                             
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
                                            (type_member (Member_plain Cons Node_ty))) with 24 by reflexivity.
                                 rewrite Ptrofs.unsigned_zero. rewrite LOADBYTES.
                                 rewrite STOREBYTES.
                                 rewrite CAC. 
                                 reflexivity.
                                 reflexivity.
                                 econstructor. econstructor. reflexivity.
                                 econstructor. reflexivity.
                                 eauto.
                                 simpl. eauto.
                             *** right. econstructor.
                                 eapply step_dropinsert_assign_variant_error5.
                                 1-3: reflexivity.
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
                                 replace (sizeof ge
                                            (type_member (Member_plain Cons Node_ty))) with 24 by reflexivity.
                                 rewrite Ptrofs.unsigned_zero. rewrite LOADBYTES.
                                 rewrite STOREBYTES.
                                 change ge with (Smallstep.globalenv (linked_list_sem se)).
                                 rewrite CAC. 
                                 reflexivity.
                                 econstructor. econstructor. reflexivity.
                                 econstructor. reflexivity.
                                 eauto. reflexivity. eauto.

                         (*  not pointer *)
                         +++ right. econstructor.
                             eapply step_dropinsert_assign_variant_error4.
                             1-3: reflexivity.
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
                             replace (sizeof ge
                                        (type_member (Member_plain Cons Node_ty))) with 24 by reflexivity.
                             rewrite Ptrofs.unsigned_zero. rewrite LOADBYTES.
                             rewrite STOREBYTES.
                             change ge with (Smallstep.globalenv (linked_list_sem se)).
                             rewrite CAC. 
                             reflexivity.
                             eapply eval_Pderef_error3. 
                             econstructor. reflexivity.
                             econstructor. reflexivity. eauto. auto.
                     --- right. econstructor.
                         eapply step_dropinsert_assign_variant_error4.
                         1-3: reflexivity.
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
                         replace (sizeof ge
                                    (type_member (Member_plain Cons Node_ty))) with 24 by reflexivity.
                         rewrite Ptrofs.unsigned_zero. rewrite LOADBYTES.
                         rewrite STOREBYTES.
                         change ge with (Smallstep.globalenv (linked_list_sem se)).
                         rewrite CAC. 
                         reflexivity.
                         eapply eval_Pderef_error2. 
                         econstructor. reflexivity.
                         econstructor. reflexivity. eauto.
                  (* check_assign_copy error *)
                  ** right. econstructor.
                     eapply step_dropinsert_assign_variant_error6; eauto.
                     reflexivity. reflexivity. reflexivity.
                     econstructor. econstructor. reflexivity.
                     econstructor. reflexivity. eauto.
                     econstructor. reflexivity. simpl. vm_compute. auto.
                     reflexivity.
               (* store_bytes error *)
               ++ right. econstructor.
                  eapply step_dropinsert_assign_variant_error3; eauto.
                  reflexivity. reflexivity. reflexivity.
                  econstructor. econstructor. 
                  econstructor. reflexivity.
                  eapply deref_loc_copy. reflexivity.
                  econstructor. econstructor. reflexivity.                     
                  econstructor. reflexivity. eauto.
                  instantiate (1 := 8). reflexivity.
                  reflexivity.
                  eapply assign_loc_copy_mem_error2. reflexivity. 
                  eauto.
            (* load bytes error *)
            -- right. econstructor.
               eapply step_dropinsert_assign_variant_error3; eauto.
               reflexivity. reflexivity. reflexivity.
               econstructor. econstructor. 
               econstructor. reflexivity.
               eapply deref_loc_copy. reflexivity.
               econstructor. econstructor. reflexivity.                     
               econstructor. reflexivity. eauto.
               instantiate (1 := 8). reflexivity.
               reflexivity.
               eapply assign_loc_copy_mem_error1. reflexivity. 
               eauto.
          (* not pointer *)
          * right. econstructor.
            eapply step_dropinsert_assign_variant_error2; eauto.
            econstructor. econstructor. econstructor. reflexivity.
            eapply deref_loc_copy. reflexivity.
            eapply eval_Pderef_error3.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto. auto.
        (* eval_place error *)
        + right. econstructor.
          eapply step_dropinsert_assign_variant_error2; eauto.
          econstructor. econstructor. econstructor. reflexivity.
          eapply deref_loc_copy. reflexivity.
          eapply eval_Pderef_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. eapply find_state_internal4 with (n:=6%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal4 with (n:=7%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP. 
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal4 with (n:=8%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate Sassign to _retv *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal4 with (n:=9%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropinsert_to_dropplace_reassign *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. eapply step_dropinsert_to_dropplace_reassign.
        reflexivity. reflexivity.
        eapply split_drop_place_find_retv. eauto.
      - intros. eapply find_state_internal4 with (n:=10%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { vm_compute in OWNTY0. congruence. }
    erewrite split_drop_place_find_retv in SPLIT; eauto. inv SPLIT.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate step_dropplace_init1 *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
        eapply step_dropplace_init1.
        compute_own_env OWNEQ COLLECT; reflexivity.
      - intros. eapply find_state_internal4 with (n:=11%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
    2: { simpl in SCALAR. congruence. }
    clear NOTOWN.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. econstructor.
      - intros. eapply find_state_internal4 with (n:=12%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* evaluate Dassign *)
    { split.
      - destruct (Mem.valid_access_dec m3 Mptr b1 0 Readable).
        + exploit Mem.valid_access_load. eauto.
          intros (?v & ?LOAD).
          destruct (sem_cast v2 List_box List_box) eqn: ?CAST.
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
          (* sem_cast error *)
          * right. econstructor. eapply step_dropinsert_assign_error5.
            econstructor. reflexivity. 
            econstructor. econstructor. econstructor.
            reflexivity. econstructor. reflexivity. eauto. reflexivity.
            eauto.
        + right. econstructor.
          eapply step_dropinsert_assign_error1.
          econstructor. eapply eval_Eplace_error2.
          econstructor. reflexivity.
          econstructor. reflexivity. eauto.
      - intros. eapply find_state_internal4 with (n:=13%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; inv SDROP; simpl; auto. lia. }
    inv STEP. inv SDROP.
    inv STAR0; cbn [num_frames num_frames_cont] in *.
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor. 
      - intros. eapply find_state_internal4 with (n:=14%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
    inv STEP. 
    inv STAR; cbn [num_frames num_frames_cont] in *.
    (* stop here: evaluate Sreturn *)
    { split.
      - left. red. do 2 right.
        do 2 eexists. econstructor.
      - intros. eapply find_state_internal4 with (n:=15%nat); eauto.
        eapply starNf_step_right; eauto. 
        1-2: inv H; simpl; auto. lia. }
      inv STEP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
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
        - intros. eapply find_state_internal4 with (n:=16%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP.
      erewrite sound_cont_no_vars with (f:= find) in SDROP; eauto.
      inv SDROP.
      2: { vm_compute in OWNTY1. congruence. }
      erewrite split_drop_place_find_node in SPLIT; eauto.
      inv SPLIT.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          compute_own_env OWNEQ COLLECT; reflexivity.
        - intros. eapply find_state_internal4 with (n:=17%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          compute_own_env OWNEQ COLLECT; reflexivity.
        - intros. eapply find_state_internal4 with (n:=18%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          compute_own_env OWNEQ COLLECT; reflexivity.
        - intros. eapply find_state_internal4 with (n:=19%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal4 with (n:=20%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          econstructor.
        - intros. eapply find_state_internal4 with (n:=21%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* evaluate step_dropinsert_return_before *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_return_before.
        - intros. eapply find_state_internal4 with (n:=22%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      destruct NOTRETURN; congruence.
      inv STAR; cbn [num_frames num_frames_cont] in *.      
      (* stop here: evaluate step_dropinsert_to_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_to_dropplace_return.
          reflexivity. reflexivity.
          eapply split_drop_place_find_l; eauto.
        - intros. eapply find_state_internal4 with (n:=23%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { unfold List_box in OWNTY0. vm_compute in OWNTY2. congruence. }
      erewrite split_drop_place_find_l in SPLIT; eauto. inv SPLIT.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          compute_own_env OWNEQ COLLECT; reflexivity.
        - intros. eapply find_state_internal4 with (n:=24%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      clear NOTOWN.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_init1 *)
       { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_init1.
          compute_own_env OWNEQ COLLECT; reflexivity.
        - intros. eapply find_state_internal4 with (n:=25%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      2: { compute_own_env OWNEQ COLLECT; vm_compute in OWN; congruence. }
      clear NOTOWN.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropplace_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropplace_return.
        - intros. eapply find_state_internal4 with (n:=26%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      inv STAR; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_skip_return *)
      { split.
        - left. red. do 2 right.
          do 2 eexists. econstructor.
          eapply step_dropinsert_skip_return.
          reflexivity.
        - intros. eapply find_state_internal4 with (n:=27%nat); eauto.
          eapply starNf_step_right; eauto. 
          1-2: inv H; inv SDROP; simpl; auto. lia. }
      inv STEP. inv SDROP.
      vm_compute in OWNTY3. congruence.
      inv STAR0; cbn [num_frames num_frames_cont] in *.
      (* stop here: evaluate step_dropinsert_return_after *)
      { split.
        - destruct (Mem.valid_access_dec m0 Mptr b2 0 Readable) eqn: ?VA.
          + exploit Mem.valid_access_load. eauto.
            intros (?v & ?LOAD).
            destruct (sem_cast v4 List_box List_box) eqn: ?CAST.
            * destruct (Mem.free_list m0 [(b3, 0, 24); (b4, 0, 8); (b1, 0, 8); (b5, 0, 8); (b2, 0, 8); (b0, 0, 4)]) eqn: ?FREELIST.
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
            * right. econstructor.
              eapply step_dropinsert_return_error3.
              econstructor. econstructor. econstructor. reflexivity.
              econstructor. reflexivity. eauto. reflexivity.
              eauto.
          + right. econstructor.
            eapply step_dropinsert_return_error1; eauto.
            econstructor. eapply eval_Eplace_error2.
            econstructor. reflexivity.
            econstructor. reflexivity. eauto.
        - intros. inv H. inv SDROP.
          exploit (sound_call_cont find); eauto.
          intros (ck1 & CK & SCK). simpl in CONT. rewrite CONT in CK.
          inv CK.          
          eapply find_returnstate; eauto. }
      inv STEP. inv SDROP.
      (* show that it cannot take more step using num_frames unchanged
      property *)
      inv STAR; cbn [num_frames num_frames_cont] in *.
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
        (** ck1 is Kcall. Fill this code after finishing calling
        find *)
        - split.
          + destruct (val_casted_dec v4 List_box).
            * destruct (Mem.valid_access_dec m4 Mptr b12 0 Writable).
              -- edestruct Mem.valid_access_store with (v:= v4) as (?m & ?STORE).
                 eauto.
                 left. red. do 2 right.
                 do 2 eexists. econstructor. reflexivity.
                 econstructor.  reflexivity. eauto.
                 econstructor. reflexivity. eauto.
              -- right. eapply step_returnstate_error2.
                 reflexivity.
                 econstructor. reflexivity. 
                 econstructor. reflexivity. eauto.
            (** The return value is not val_casted. Treat it as
            a kind of memory error *)
            * right. 
              eapply step_returnstate_error3.
              reflexivity.
              econstructor. reflexivity. eauto.
          + intros.
            eapply find_state_internal3 with (n:=0%nat); eauto.
            econstructor. econstructor. eauto. eauto.
            econstructor. 
            inv H; simpl; eauto. lia. }
      (* num frames contradiction *)
      inv STEP.
      simpl in FEQ26.
      exfalso. eapply Nat.neq_succ_diag_l; eauto.

  (* state in find_returnstate (returing from find function) *)
  - inv CONT.
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
      (** The return value is not val_casted. Treat it as
            a kind of memory error *)
        -- right. 
           eapply step_returnstate_error3.
           reflexivity.
           econstructor. reflexivity. eauto.
      * intros.
        eapply find_state_internal3 with (n:=0%nat); eauto.
        2: eauto.
        econstructor. econstructor. eauto. eauto.
        econstructor. 
        inv H; simpl; eauto. lia. 
Strategy opaque [collect_func].
Qed.

End SOUNDNESS.


Lemma linked_list_module_safe:
  module_type_safe list_ext_inv hmap_ext_inv linked_list_sem (mem_error linked_list_mod).
Proof.
  red. econstructor.
  (* cannot specify msafek_invariant for unknown reason *)
  eapply (Module_type_safe_components li_rs li_rs linked_list_sem list_ext_inv hmap_ext_inv (mem_error linked_list_mod) (fun se w => sound_state se w)).
  intros se w_hm SYMB VSE.
  destruct SYMB.
  econstructor.
  (* preservation *)
  - intros. eapply step_preservation_progress; eauto.
  (* progress *)
  - intros. eapply step_preservation_progress; eauto.
  (* initial safe *)
  - eapply initial_preservation_progress; eauto.
  (* external safe *)
  - eapply linked_list_external; eauto.
  (* final state *)
  - eapply linked_list_final; eauto.
Qed.
