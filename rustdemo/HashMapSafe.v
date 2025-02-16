Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop Ctypes.
Require Import Values Globalenvs Memory.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import Clight HashMap LinkedList.
Require Import Separation.
Require Import MoveCheckingFootprint MoveCheckingDomain.

Local Open Scope error_monad_scope.
Local Open Scope sep_scope.
Import ListNotations.

Definition hash_map_sem := semantics1 hash_map_prog.

Section SOUNDNESS.

Variable N : nat.

Context (se : Genv.symtbl).

Let ge := globalenv se hash_map_prog.

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

(** TODO: property of splitting hmap_pred_rec  *)

(* Pre-condition of hmap_operate_on function *)
(** We should not make hmap_operate_on an external function because
its pre-condition of the hmap argument is not compatible with rs_own
because it cannot be called from Rust side. The rust module cannot
instantiate a value with type hmap_ty. One way to resolve this problem
is that prove manually {I'}M[..] refining {I@@rs_own}M[..] where I' is
a more dedicated condition that distinguish the call to
hmap_operate_on or process and then use different conditions. *)


End SOUNDNESS.

