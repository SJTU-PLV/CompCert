Require Import Coqlib.
Require Import Maps.
Require Import Values.
Require Import Memory.
Require Import AST.

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
Inductive tag :=
| Tagged (t: loc)
| Untagged.

Lemma loc_eq_dec: forall (l1 l2: loc), {l1 = l2} + {l1 <> l2}.
Proof.
  intros. destruct l1; destruct l2.
  destruct (eq_block b b0); destruct (Z.eq_dec z z0); subst.
  auto. 
  right. congruence.
  right. congruence.
  right. congruence.
Qed.

Lemma tag_eq_dec: forall (t1 t2: tag), {t1 = t2} + {t1 <> t2}.
Proof.
  intros. destruct t1; destruct t2; auto.
  destruct (loc_eq_dec t t0); subst; auto. 
  all: right; congruence.
Qed.
  
Inductive stkbor_perm := Unique | SharedReadWrite | SharedReadOnly | Disabled.

Lemma stkbor_perm_eq_dec: forall (sp1 sp2: stkbor_perm), {sp1 = sp2} + {sp1 <> sp2}.
Proof.
  decide equality.
Qed.

Record item := mkItem {
  perm      : stkbor_perm;
  tg        : tag;
}.

Lemma item_eq_dec: forall (i1 i2: item), {i1 = i2} + {i1 <> i2}. 
Proof.
  generalize tag_eq_dec.
  generalize stkbor_perm_eq_dec.
  decide equality.
Qed.

Definition bor_stack := list item.
Definition bor_stacks := NMap.t (ZMap.t (option bor_stack)).

(** Stacked borrow operations (mostly identical to the original stacked borrow) *)

Inductive access_kind := AccessRead | AccessWrite.

Definition perm_grants_access (perm: stkbor_perm) (access: access_kind) : bool :=
  match perm, access with
  | Disabled, _ => false
  | SharedReadOnly, AccessWrite => false
  | _, _ => true
  end.

Definition matched_grant (access: access_kind) (bor: tag) (it: item) :=
  perm_grants_access it.(perm) access && (tag_eq_dec it.(tg) bor).

Fixpoint list_find {A} (f : A -> bool) (l: list A) : option (nat * A) :=  
  match l with
  | nil => None
  | x :: l => if f x then Some (O,x) else option_map (fun '(idx, elt) => (S idx, elt)) (list_find f l)
  end.

(* Return the index of the granting item. If the tag is None, it means
that we are accessing a local variable by its name *)
Definition find_granting (stk: bor_stack) (access: access_kind) (opt_tag: option tag) : option (nat * stkbor_perm) :=
  match opt_tag with
  | Some bor => 
      match list_find (matched_grant access bor) stk with    
      | Some (idx, item) =>
          Some (idx, item.(perm))
      | _ => None
      end
  | None =>
      Some (length stk, Unique)
  end.

(* Find the index RIGHT BEFORE the first incompatible item.
   Remember that 0 is the top of the stack. *)
Definition find_first_write_incompatible (stk: bor_stack) (pm: stkbor_perm) : option nat :=
  match pm with
  | Unique => Some (length stk)
  | SharedReadWrite =>
      match (list_find (fun it => negb (stkbor_perm_eq_dec it.(perm) SharedReadWrite)) (rev stk)) with
      | Some (idx, _) => Some ((length stk) - idx)%nat
      | _ => Some O
      end
  | SharedReadOnly | Disabled => None
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
      if stkbor_perm_eq_dec it.(perm) Unique then
        let new := mkItem Disabled it.(tg) in
        replace_items' (acc ++ [new]) stk
      else replace_items' (acc ++ [it]) stk
  end.

Definition replace_items (stk: bor_stack) : option bor_stack :=
  replace_items' [] stk.

(* Test if a memory `access` using pointer tagged `tg` is granted.  If
   yes, return the new stack. *)
Definition access1 (stk: bor_stack) (access: access_kind) (opt_tg: option tag) : option bor_stack :=
  (* Step 1: Find granting item. *)
  match find_granting stk access opt_tg with
  | Some (idx, p) =>
      (* Step 2: Remove incompatible items. *)
      match access with
      | AccessWrite =>
          (* Remove everything above the write-compatible items, like a proper stack. *)
          match find_first_write_incompatible (firstn idx stk) p with
          | Some incompat_idx =>
              match remove_items stk incompat_idx with
              | Some stk' =>
                  Some stk'
              | None => None
              end
          | None => None
          end
      | AccessRead =>
          (* On a read, *disable* all `Unique` above the granting item. *)
          match replace_items (firstn idx stk) with
          | Some stk' =>
              Some (stk' ++ skipn idx stk)
          | None => None
          end
      end
  | None => None
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
Definition memory_read stks b ofs sz (opt_tg: option tag) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => access1 stk AccessRead opt_tg).

Definition memory_written stks b ofs sz (opt_tg: option tag) : option bor_stacks :=
  for_each stks b ofs (Z.to_nat sz) false (fun stk => access1 stk AccessWrite opt_tg).

Definition memory_access stks b ofs sz (ak: access_kind) (opt_tg: option tag) : option bor_stacks :=
  match ak with
  | AccessRead =>
      memory_read stks b ofs sz opt_tg
  | AccessWrite =>
      memory_written stks b ofs sz opt_tg      
  end.

Definition memory_free stks b (lo hi: Z) (opt_tg: option tag) : option bor_stacks :=
  let sz := Mem.interval_length lo hi in
  for_each stks b lo sz true (fun stk => access1 stk AccessWrite opt_tg).

(** Reborrow: push a tag into the stack *)

Definition item_not_same_loc (it1 it2: item) : bool :=
  match (tg it1), (tg it2) with
  | Tagged l1, Tagged l2 =>
      negb (loc_eq_dec l1 l2)
  | _, _ => 
      true
  end.

Definition remove_old_item (stk: bor_stack) (it: item) :=
  filter (item_not_same_loc it) stk.

(* If tag_old is None, it means that we do not need to find the
granting item and just push the new item in the top. When we call
[grant], we must guarantee that we have checked the accssibility of
this stack via [access1] *)
Definition grant (stk: bor_stack) (it: item) (tag_old: option tag) : option bor_stack :=
  let stk1 := remove_old_item stk it in
  match tag_old with
  | None =>
      Some (it :: stk1)
  | Some t =>
      (* This case is not used in the semantic of safe Rust  *)
      let access := if perm_grants_access it.(perm) AccessWrite then AccessWrite else AccessRead in
      match find_granting stk access (Some t) with
      | Some (idx, p) =>
          Some ((firstn idx stk) ++ [it] ++ (skipn idx stk))
      | None => None
      end
  end.

Definition grantN (stks: bor_stacks) b ofs (sz: nat) (old_tag: option tag) (new_tag: tag) (pm: stkbor_perm) : option bor_stacks :=
  let it := mkItem pm new_tag in
  for_each stks b ofs sz false (fun stk => grant stk it old_tag).
