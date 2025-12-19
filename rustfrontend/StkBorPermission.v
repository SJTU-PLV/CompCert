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

(* Inductive tag := *)
(* | Tagged (t: loc) *)
(* | Untagged. *)

Lemma loc_eq_dec: forall (l1 l2: loc), {l1 = l2} + {l1 <> l2}.
Proof.
  intros. destruct l1; destruct l2.
  destruct (eq_block b b0); destruct (Z.eq_dec z z0); subst.
  auto.
  right. congruence.
  right. congruence.
  right. congruence.
Qed.


(* Lemma tag_eq_dec: forall (t1 t2: tag), {t1 = t2} + {t1 <> t2}. *)
(* Proof. *)
(*   intros. destruct t1; destruct t2; auto. *)
(*   destruct (loc_eq_dec t t0); subst; auto.  *)
(*   all: right; congruence. *)
(* Qed. *)

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

Inductive item :=
| Unique (t: Tag.t)
(* Is there any benefit if we make the tag in sharero a set of tags? *)
| SharedReadOnly (t: Tag.t)
| SharedReadWrite.


Definition t := list item.

(** Stacked borrow operations (mostly identical to the original stacked borrow) *)

(* If bor is None, it means this access is from raw pointer place *)
Definition item_grants_access (bor: option Tag.t) (access: access_kind) (it: item) : bool :=
  match bor with
  | None =>
      match it with 
      | SharedReadWrite => true
      | _ => false
      end
  | Some t =>
      match it, access with
      | SharedReadOnly _, AWrite => false
      | SharedReadOnly t1, _ =>
          Tag.eq_dec t t1
      | Unique t1, _ =>
          Tag.eq_dec t t1
      | _, _ => false
      end
  end.

Inductive access_from :=
| from_local
| from_ref (t: Tag.t)
| from_raw.


(* Return the index of the granting item. If the tag is None, it means
that we are accessing a raw pointer variable *)
Definition find_granting (stk: t) (access: access_kind) (bor: option Tag.t) : option (nat * item) :=
  match list_find (item_grants_access bor access) stk with    
  | Some (idx, item) =>
      Some (idx, item)
  | _ => None
  end.

Definition item_is_sharedrw (it: item) :=
  match it with
  | SharedReadWrite => true
  | _ => false
  end.

(* Find the index RIGHT BEFORE the first incompatible item.
   Remember that 0 is the top of the stack. *)
Definition find_first_write_incompatible (stk: t) (it: item) : option nat :=
  match it with
  | Unique _ => Some (length stk)
  | SharedReadWrite =>
      match (list_find (fun it => negb (item_is_sharedrw it)) (rev stk)) with
      | Some (idx, _) => Some ((length stk) - idx)%nat
      | _ => Some O
      end
  | SharedReadOnly _ => None
  end.

(* Remove from `stk` the items before `idx`. *)
Fixpoint remove_items (stk: t) (idx: nat) : option t :=
  match idx, stk with
  (* Assumption: idx ≤ length stk *)
  | S _, nil => None
  | O, stk => Some stk
  | S idx, it :: stk =>
      remove_items stk idx
  end.

(* Replace any Unique permission with Disabled, starting from the top
of the stack. *)
Fixpoint replace_items' (acc stk : t) : option t :=
  match stk with
  | nil => Some acc
  | it :: stk =>
      match it with
      | Unique _ =>
          replace_items' acc stk
      | _ =>
          replace_items' (acc ++ [it]) stk
      end
  end.

Definition replace_items (stk: t) : option t :=
  replace_items' [] stk.

(* Test if a memory `access` using pointer tagged `tg` is granted.  If
   yes, return the new stack. *)
Definition access1 (stk: t) (access: access_kind) (af: access_from) : option t :=
  match af with
  | from_local =>
      match access with
      | AWrite =>
          (* remove all items *)
          Some nil
      | ARead =>
          (* On a read, *remove* all `Unique` above the granting item. *)
          match replace_items stk with
          | Some stk' =>
              Some stk'
          | None => None
          end
      end
  | _ =>     
      let bor := match af with | from_ref t => Some t | _ => None end in      
      (* Step 1: Find granting item. *)
      match find_granting stk access bor with
      | Some (idx, it) =>
          (* Step 2: Remove incompatible items. *)
          match access with
          | AWrite =>
              (* Remove everything above the write-compatible items, like a proper stack. *)
              match find_first_write_incompatible (firstn idx stk) it with
              | Some incompat_idx =>
                  match remove_items stk incompat_idx with
                  | Some stk' =>
                      Some stk'
                  | None => None
                  end
              | None => None
              end
          | ARead =>
              (* On a read, *remove* all `Unique` above the granting item. *)
              match replace_items (firstn idx stk) with
              | Some stk' =>
                  Some (stk' ++ skipn idx stk)
              | None => None
              end
          end
      | None => None
      end
  end.
      
(** Reborrow: push a tag into the stack *)

Definition tag_of_item (it: item) : option Tag.t :=
  match it with
  | Unique t
  | SharedReadOnly t => Some t
  | _ => None
  end.

Definition item_not_same_tag (it1 it2: item) : bool :=
  match tag_of_item it1, tag_of_item it2 with
  | Some t1, Some t2 =>
      negb (Tag.eq_dec t1 t2)
  | _, _ => true
  end.

Definition remove_old_item (stk: t) (it: item) :=  
  filter (item_not_same_tag it) stk.

(* If insert_idx is None, it means that we do not need to find the
location of the granting item and just need to push the new item on
the top. When we call [grant], we must guarantee that we have checked
the accssibility of this stack via [access1] *)
Definition grant (stk: t) (insert_idx: option nat) (it: item) : option t :=
  let stk1 := remove_old_item stk it in
  match insert_idx with
  | None =>
      Some (it :: stk1)
  | Some idx =>
      (* This case, which is used for inserting item adjacent to the
      sharerw, is not used in safe rust *)
      Some ((firstn idx stk) ++ [it] ++ (skipn idx stk))
  end.

End BorStk.


(** Instantiation of borrow stack using (block * Z) as the type of tags *)

Module BorStkPerm := BorStk(Loc).

Definition bor_stacks := NMap.t (ZMap.t (option BorStkPerm.t)).

Local Notation "a # b" := (NMap.get _ b a) (at level 1).
Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Definition init_stacks (stks: bor_stacks) (b: block) (lo hi: Z) : bor_stacks :=  
  let contents := repeat (Some (@nil BorStkPerm.item)) (Mem.interval_length lo hi) in
  NMap.set _ b (Mem.setN contents lo (ZMap.init None)) stks.

Definition set_stacks (stks: bor_stacks) (b: block) (ofs: Z) (stk: option BorStkPerm.t) : bor_stacks :=
  NMap.set _ b (ZMap.set ofs stk (stks # b)) stks.

Fixpoint for_each (stks: bor_stacks) (b: block) (ofs: Z) (n: nat) (dealloc: bool) (f: BorStkPerm.t -> option BorStkPerm.t) : option bor_stacks :=
  match n with
  | O => Some stks
  | S n =>
      match stks # b ## ofs with
      | Some stk =>
          match f stk with
          | Some stk' =>
              if dealloc then
                (* clear the borrow stack as it will be freed *)
                for_each (set_stacks stks b ofs None) b (ofs + 1) n dealloc f
              else 
                for_each (set_stacks stks b ofs (Some stk')) b (ofs + 1) n dealloc f
          | None => None
          end
      | None => None
      end
  end.

(* Perform the access check on a block of continuous memory. *)
Definition memory_read stks b ofs sz (af: BorStkPerm.access_from) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => BorStkPerm.access1 stk ARead af).

Definition memory_written stks b ofs sz (af: BorStkPerm.access_from) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => BorStkPerm.access1 stk AWrite af).

Definition memory_access stks b ofs sz (ak: access_kind) (af: BorStkPerm.access_from) : option bor_stacks :=
  match ak with
  | ARead =>
      memory_read stks b ofs sz af
  | AWrite =>
      memory_written stks b ofs sz af
  end.

Definition memory_free stks b (lo hi: Z) (af: BorStkPerm.access_from) : option bor_stacks :=
  let sz := Mem.interval_length lo hi in
  for_each stks b lo sz true (fun stk => BorStkPerm.access1 stk AWrite af).

Definition grantN (stks: bor_stacks) b ofs (sz: nat) (insert_idx: option nat) (new_it: BorStkPerm.item)  : option bor_stacks :=
  for_each stks b ofs sz false (fun stk => BorStkPerm.grant stk insert_idx new_it).
