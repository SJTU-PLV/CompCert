Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Listmisc.
Require Import Rusttypes.

Import ListNotations.

(** This file defines the stacked borrow permission model *)

(** TODO: we want to just expose some interface to the borrow checking
proof, e.g., something like finding a support tag (i.e., the tag is
reborrowed from), because we also want to support tree borrow model by
keeping the existing proof. *)

Definition loc : Type := block * Z.

(* We use the address of the pointer place as the tag instead of
natural number in original sb (i.e., stacked borrow) model because we
want to prevent complicated retagging mechanism *)

Lemma loc_eq_dec: forall (l1 l2: loc), {l1 = l2} + {l1 <> l2}.
Proof.
  intros. destruct l1; destruct l2.
  destruct (eq_block b b0); destruct (Z.eq_dec z z0); subst.
  auto.
  right. congruence.
  right. congruence.
  right. congruence.
Qed.

(* Set of tags *)

Module Loc <: DecidableType.DecidableType.
  Definition t := loc.
  Definition eq := @eq t.
  Definition eq_dec := loc_eq_dec.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Loc.

Module Locs := FSetWeakList.Make(Loc).

Module BorStk(Tag: DecidableType).

(* We only record the list of Unique items *)
Definition t := list Tag.t.

(** Stacked borrow operations (mostly identical to the original stacked borrow) *)

Inductive access_from :=
| from_owner
| from_borrower (t: Tag.t).

(* Access a mutable referenced place must pop all the items above the
tag of this reference, so there is no need to pass access_kind to
access1 function *)
Definition access1 (stk: t) (bor: Tag.t) : option t :=
  match list_find (Tag.eq_dec bor) stk with
      | Some (idx, _) =>
          Some (skipn idx stk)
      | None => None
  end.


(** Reborrow: push a tag into the stack *)

Definition not_same_tag (t1 t2: Tag.t) : bool :=
  negb (Tag.eq_dec t1 t2).

Definition remove_old_item (stk: t) (tag: Tag.t) := 
  (filter (not_same_tag tag) stk).


(* Definition grant (stk: option t) (tag: Tag.t) : t := *)
(*   let stk1 := remove_old_item stk tag in *)
(*   tag :: stk1. *)


(* (* create a borrow stack for an owner path *) *)
(* Definition borrow_from_owner (access: access_kind) : t := *)
(*   match access with *)
(*   | ARead => *)
(*       SharedRO nil nil *)
(*   | AWrite => *)
(*       Unique nil *)
(*   end. *)

(* (* access the borrow stack of an owner, which may remove this stack *)
(* when the access is writing, i.e., the owner retrieve its ownership *) *)
(* Definition access_owner (stk: t) (access: access_kind) : option t := *)
(*   match stk, access with *)
(*   | SharedRO ro _, ARead => *)
(*       Some (SharedRO ro nil) *)
(*   | _, _ => *)
(*       None *)
(*   end. *)

End BorStk.

