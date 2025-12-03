Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Import AST.
Require Import FSetWeakList DecidableType.

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

Definition tag := loc.

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

Definition tag_eq_dec := loc_eq_dec.

(* Lemma tag_eq_dec: forall (t1 t2: tag), {t1 = t2} + {t1 <> t2}. *)
(* Proof. *)
(*   intros. destruct t1; destruct t2; auto. *)
(*   destruct (loc_eq_dec t t0); subst; auto.  *)
(*   all: right; congruence. *)
(* Qed. *)

(* Set of tags *)

Module Tag <: DecidableType.DecidableType.
  Definition t := tag.
  Definition eq := @eq t.
  Definition eq_dec := tag_eq_dec.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Tag.

Module Tags := FSetWeakList.Make(Tag).

Inductive item :=
| Unique (t: tag)
(* Is there any benefit if we make the tag in sharero a set of tags? *)
| SharedReadOnly (t: tag)
| SharedReadWrite.


(* Inductive stkbor_perm := Unique | SharedReadWrite | SharedReadOnly | Disabled. *)

(* Lemma stkbor_perm_eq_dec: forall (sp1 sp2: stkbor_perm), {sp1 = sp2} + {sp1 <> sp2}. *)
(* Proof. *)
(*   decide equality. *)
(* Qed. *)

(* Record item := mkItem { *)
(*   perm      : stkbor_perm; *)
(*   tg        : tag; *)
(* }. *)

(* Lemma item_eq_dec: forall (i1 i2: item), {i1 = i2} + {i1 <> i2}.  *)
(* Proof. *)
(*   generalize tag_eq_dec. *)
(*   generalize stkbor_perm_eq_dec. *)
(*   decide equality. *)
(* Qed. *)



Definition bor_stack := list item.
Definition bor_stacks := NMap.t (ZMap.t (option bor_stack)).

(** Stacked borrow operations (mostly identical to the original stacked borrow) *)

Inductive access_kind := AccessRead | AccessWrite.

(* If bor is None, it means this access is from raw pointer place *)
Definition item_grants_access (bor: option tag) (access: access_kind) (it: item) : bool :=
  match bor with
  | None =>
      match it with 
      | SharedReadWrite => true
      | _ => false
      end
  | Some t =>
      match it, access with
      | SharedReadOnly _, AccessWrite => false
      | SharedReadOnly t1, _ =>
          tag_eq_dec t t1
      | Unique t1, _ =>
          tag_eq_dec t t1
      | _, _ => false
      end
  end.

Inductive access_from :=
| from_local
| from_ref (t: tag)
| from_raw.

Fixpoint list_find {A} (f : A -> bool) (l: list A) : option (nat * A) :=  
  match l with
  | nil => None
  | x :: l => if f x then Some (O,x) else option_map (fun '(idx, elt) => (S idx, elt)) (list_find f l)
  end.

(* Return the index of the granting item. If the tag is None, it means
that we are accessing a raw pointer variable *)
Definition find_granting (stk: bor_stack) (access: access_kind) (bor: option tag) : option (nat * item) :=
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
Definition find_first_write_incompatible (stk: bor_stack) (it: item) : option nat :=
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
Fixpoint remove_items (stk: bor_stack) (idx: nat) : option bor_stack :=
  match idx, stk with
  (* Assumption: idx ≤ length stk *)
  | S _, nil => None
  | O, stk => Some stk
  | S idx, it :: stk =>
      remove_items stk idx
  end.

(* Replace any Unique permission with Disabled, starting from the top
of the stack. *)
Fixpoint replace_items' (acc stk : bor_stack) : option bor_stack :=
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

Definition replace_items (stk: bor_stack) : option bor_stack :=
  replace_items' [] stk.

(* Test if a memory `access` using pointer tagged `tg` is granted.  If
   yes, return the new stack. *)
Definition access1 (stk: bor_stack) (access: access_kind) (af: access_from) : option bor_stack :=
  match af with
  | from_local =>
      match access with
      | AccessWrite =>
          (* remove all items *)
          Some nil
      | AccessRead =>
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
          | AccessWrite =>
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
          | AccessRead =>
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
      

Local Notation "a # b" := (NMap.get _ b a) (at level 1).
Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Definition init_stacks (stks: bor_stacks) (b: block) (lo hi: Z) : bor_stacks :=  
  let contents := repeat (Some (@nil item)) (Mem.interval_length lo hi) in
  NMap.set _ b (Mem.setN contents lo (ZMap.init None)) stks.

Definition set_stacks (stks: bor_stacks) (b: block) (ofs: Z) (stk: option bor_stack) : bor_stacks :=
  NMap.set _ b (ZMap.set ofs stk (stks # b)) stks.

Fixpoint for_each (stks: bor_stacks) (b: block) (ofs: Z) (n: nat) (dealloc: bool) (f: bor_stack -> option bor_stack) : option bor_stacks :=
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
Definition memory_read stks b ofs sz (af: access_from) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => access1 stk AccessRead af).

Definition memory_written stks b ofs sz (af: access_from) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => access1 stk AccessWrite af).

Definition memory_access stks b ofs sz (ak: access_kind) (af: access_from) : option bor_stacks :=
  match ak with
  | AccessRead =>
      memory_read stks b ofs sz af
  | AccessWrite =>
      memory_written stks b ofs sz af
  end.

Definition memory_free stks b (lo hi: Z) (af: access_from) : option bor_stacks :=
  let sz := Mem.interval_length lo hi in
  for_each stks b lo sz true (fun stk => access1 stk AccessWrite af).

(** Reborrow: push a tag into the stack *)

Definition tag_of_item (it: item) : option tag :=
  match it with
  | Unique t
  | SharedReadOnly t => Some t
  | _ => None
  end.

Definition item_not_same_tag (it1 it2: item) : bool :=
  match tag_of_item it1, tag_of_item it2 with
  | Some t1, Some t2 =>
      negb (tag_eq_dec t1 t2)
  | _, _ => true
  end.

Definition remove_old_item (stk: bor_stack) (it: item) :=  
  filter (item_not_same_tag it) stk.

(* If insert_idx is None, it means that we do not need to find the
location of the granting item and just need to push the new item on
the top. When we call [grant], we must guarantee that we have checked
the accssibility of this stack via [access1] *)
Definition grant (stk: bor_stack) (insert_idx: option nat) (it: item) : option bor_stack :=
  let stk1 := remove_old_item stk it in
  match insert_idx with
  | None =>
      Some (it :: stk1)
  | Some idx =>
      (* This case, which is used for inserting item adjacent to the
      sharerw, is not used in safe rust *)
      Some ((firstn idx stk) ++ [it] ++ (skipn idx stk))
  end.

Definition grantN (stks: bor_stacks) b ofs (sz: nat) (insert_idx: option nat) (new_it: item)  : option bor_stacks :=
  for_each stks b ofs sz false (fun stk => grant stk insert_idx new_it).
