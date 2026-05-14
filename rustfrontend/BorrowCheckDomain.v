Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import FSetFacts.
Require Import Lattice.
Require Import Rusttypes Rustlight RustIR RustIRcfg.
Require Import Ordered.
Require FSetAVL.
Require Import Errors.
Require Import UnionFindDelete.
Require Import RegionLiveness.

Import ListNotations.
Scheme Equality for list.
Open Scope error_monad_scope.

(** ** The abstract domain for borrow checking based on Polonius *)

Definition mut_to_access_kind (mut: mutkind) : access_kind :=
  match mut with
  | Mutable => AWrite
  | Immutable => ARead
  end.

(** Loans  *)

Inductive loan : Type :=
| Lintern (mut: mutkind) (p: place)
| Lextern (org: origin).

Lemma loan_eq_dec: forall (l1 l2: loan), {l1 = l2} + {l1 <> l2}.
Proof.
  generalize Pos.eq_dec place_eq. intros.
  decide equality.
  decide equality.
Defined.

Module Loan <: DecidableType.DecidableType.
  Definition t := loan.
  Definition eq := @eq t.
  Definition eq_dec := loan_eq_dec.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Loan.

(* May-live loan set *)
Module LoanSet := FSetWeakList.Make(Loan).

Module LoanSetFacts := FSetFacts.WFacts(LoanSet).

Module LoanSetL := LFSet(LoanSet).

(* Lattice for state access path *)

Definition spath_mut : Type := spath * mutkind.

Lemma spath_mut_eq_dec: forall (l1 l2: spath_mut), {l1 = l2} + {l1 <> l2}.
Proof.
  generalize Pos.eq_dec spath_eq_dec. intros.
  decide equality.
  decide equality.
Defined.


Module SPathMut <: DecidableType.DecidableType.
  Definition t := spath_mut.
  Definition eq := @eq t.
  Definition eq_dec :=  spath_mut_eq_dec.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End SPathMut.

Module SPathSet := FSetWeakList.Make(SPathMut).

Module SPathSetFacts := FSetFacts.WFacts(SPathSet).

Module SPathSetL := LFSet(SPathSet).

(** Origin state *)

(* Origin state is a lattice parametric in the set of loans (or views) lattice *)

Module LOrgSt(LS: SEMILATTICE) <: SEMILATTICE.

Inductive origin_state : Type :=
| Live (ls: LS.t)
| Dead.
  
Definition t := origin_state.

Definition eq (x y: t) :=
  match x, y with
  | Live ls1, Live ls2 => LS.eq ls1 ls2
  | Dead, Dead => True
  | _, _ => False
  end.
  
Lemma eq_refl: forall x, eq x x.
Proof.
  intros. red. destruct x; auto.
  apply LS.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  intros. red in *.
  destruct x, y; auto.
  apply LS.eq_sym. auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  intros; red in *.
  destruct x, y, z; auto.
  eapply LS.eq_trans; eauto.
  contradiction.
Qed.
  
Definition beq (s1 s2 : t) : bool :=
  match s1, s2 with
  | Live ls1, Live ls2 => LS.beq ls1 ls2
  | Dead, Dead => true
  | _, _ => false
  end.

Lemma beq_correct: forall x y, beq x y = true -> eq x y.
Proof.
  intros. destruct x, y; red; simpl in *; auto; try congruence.
  eapply LS.beq_correct. auto.
Qed.  
  
Definition ge (x y: t) : Prop :=
  match x, y with
  | _, Dead => True
  | Dead, _ => False                
  | Live ls1, Live ls2 => LS.ge ls1 ls2
  end.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  intros; red in *; destruct x,y; auto.
  eapply LS.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  intros. red in *.
  destruct x, y, z; auto.
  eapply LS.ge_trans; eauto.
  contradiction.
Qed.

(* Definition bot := Live LoanSetL.bot. *)

(* If a region points to Dead, it means that this region would be
redefined later and not be used before this redefinition *)
Definition bot := Dead.

Lemma ge_bot: forall x, ge x bot.
Proof.
  intros. red. destruct x. simpl. auto.
  simpl. auto.
Qed.

(* Definition top := Dead. *)

(* Lemma ge_top: forall x, ge top x. *)
(* Proof. *)
(*   intros. red. destruct x; simpl; auto. *)
(* Qed. *)


Definition lub (x y: t) :=
  match x, y with
  | Dead, _ => y
  | _, Dead => x
  | Live ls1, Live ls2 => Live(LS.lub ls1 ls2)
  end.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  intros. destruct x, y; simpl; auto.
  apply LS.ge_lub_left.
  eapply LS.ge_refl.
  eapply LS.eq_refl.
Qed.

Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  intros. destruct x, y; simpl; auto.
  apply LS.ge_lub_right.
  eapply LS.ge_refl.
  eapply LS.eq_refl.
Qed.

End LOrgSt.

(** Two instances of LOrgSt: one is for static Polonius analysis where
we instantiate LS as loan sets and the other is for sound
approximation where we instantiate LS as set of access paths *)

Module LOrgLnSt := LOrgSt(LoanSetL).

Module LOrgPhSt := LOrgSt(SPathSetL).
Module LOrgPhOptSt := LOption(LOrgPhSt).

Global Instance LOrgLnSt_eq_equiv: 
  Equivalence (LOrgLnSt.eq).
Proof.
  split.
  red. eapply LOrgLnSt.eq_refl.
  red. eapply LOrgLnSt.eq_sym.
  red. eapply LOrgLnSt.eq_trans.
Defined.


Global Instance LOrgLnSt_lub_Proper:
  Proper (LOrgLnSt.eq ==> LOrgLnSt.eq ==> LOrgLnSt.eq) LOrgLnSt.lub.
Proof.
  intros ls1 ls2 A ls3 ls4 B.
  destruct ls1; destruct ls3; destruct ls2; destruct ls4; simpl in *.
  all: try rewrite A; try rewrite B; try reflexivity.
  all: try contradiction.
Defined.  

(** Lattice of disjoint-set mapping i.e., mapping of equivalent set
represented by union-find structure *)

Module LUFMap(L: SEMILATTICE) <: SEMILATTICE.

Record ds_map := mk { m: PTree.t L.t; uf: UFD.t }.

Definition t := ds_map.

Definition get (p: positive) (x: t) : L.t :=
  match (m x) ! (UFD.repr (uf x) p) with None => L.bot | Some x => x end.

Definition set (p: positive) (v: L.t) (x: t) : t :=
  let p' := UFD.repr (uf x) p in
  if L.beq v L.bot
  then mk (PTree.remove p' (m x)) (uf x)
  else mk (PTree.set p' v (m x)) (uf x).

Lemma gsspec:
  forall p v x q,
  L.eq (get q (set p v x)) (if peq (UFD.repr (uf x) q) (UFD.repr (uf x) p) then v else get q x).
Proof.
  intros. unfold get, set. destruct peq.
  - rewrite <- e. destruct L.beq eqn: A; simpl.
    + rewrite PTree.grs.
      eapply L.eq_sym.
      eapply L.beq_correct. auto.
    + rewrite PTree.gss. eapply L.eq_refl.
  - destruct L.beq eqn: A; simpl.
    + rewrite PTree.gro; auto.
      apply L.eq_refl.
    + rewrite PTree.gso; auto. apply L.eq_refl.
Qed.
    
Record eq' (x y: t) : Prop :=
  { uf_eq: UFD.eq (uf x) (uf y);
    m_eq: (forall p, L.eq (get p x) (get p y))}.

Definition eq := eq'.

Lemma eq_refl: forall x, eq x x.
Proof.
  intros. constructor.
  eapply UFD.eq_refl.
  intros. apply L.eq_refl.
Qed.

Lemma eq_sym: forall x y, eq x y -> eq y x.
Proof.
  intros. inv H. constructor.  
  eapply UFD.eq_sym. auto.
  intros. apply L.eq_sym; auto.
Qed.

Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
Proof.
  intros. inv H; inv H0. constructor.
  eapply UFD.eq_trans; eauto. 
  intros. eapply L.eq_trans; eauto.
Qed.

Definition beq_elt (mx my: PTree.t L.t) (x y: positive) : bool :=
  match mx ! x, my ! y with
  | None, None => true
  | Some v1, Some v2 => L.beq v1 v2
  | _, _ => false
  end.

Definition eqb_elt (dm1 dm2: t) a (v: UFD.vt) : bool :=
  (* the set of a in uf2 must be included in uf1 *)
  let x := (UFD.repr (uf dm1) a) in
  let y := (UFD.repr (uf dm2) a) in
  proj_sumbool (UFD.elt_eq x (UFD.repr (uf dm1) y))
  (* the values of representative nodes are equal *)
  && beq_elt (m dm1) (m dm2) x y.

Definition val_eqb_opt2 (m1: PTree.t L.t) (uf2: UFD.t) p (v2: L.t) : bool :=
  match (UFD.m uf2) ! p with
  (* p is a singleton in uf2 *)
  | None =>
      (* p must be a singleton in uf1 *)
      match m1 ! p with
      | Some v1 => L.beq v1 v2
      | _ => false
      end
  (* No need to check if p is not the representative node *)  
  | _ => true
  end.

(* It is used only if (m2 ! p is None && uf2 ! p = None) *)
Definition val_eqb_opt1 (m2: PTree.t L.t) (uf2: UFD.t) p (v1: L.t) : bool :=
  match (UFD.m uf2) ! p, m2 ! p with
  (* p is a singleton in uf2 and it is not mapped to anything but it
  is mapped to something in m1. Specifically, if p is not a singleton,
  it is checked by the second for_all predicate in beq, if p is mapped
  to something in m2, it is checked by the third for_all predicate in
  beq *)
  | None, None => false
  | _, _ => true
  end.


(* Keep in mind that even if (uf dm1) = (uf dm2), it does not mean
that the representative of some region [r] in (uf dm1) is equal to the
representative of [r] in (uf dm2). *)
Definition beq (dm1 dm2: t) : bool :=
  (* uf1 is included in uf2 *)
  UFD.geb (uf dm2) (uf dm1)
  (* uf2 is included in uf1 and all the values of representative nodes *)
  (* are equal *)
  && PTree_Properties.for_all (UFD.m (uf dm2)) (eqb_elt dm1 dm2)
  (* If the node is a singleton in dm2 (which is not checked in the *)
  (* previous for_all predicate), we need to check that they store the same *)
  (* value in the map *)
  && PTree_Properties.for_all (m dm2) (val_eqb_opt2 (m dm1) (uf dm2))
  && PTree_Properties.for_all (m dm1) (val_eqb_opt1 (m dm2) (uf dm2)).

Lemma beq_correct: forall dm1 dm2, beq dm1 dm2 = true -> eq dm1 dm2.
Proof.
  intros dm1 dm2 EQ. unfold beq in EQ.
  erewrite !andb_true_iff in EQ. destruct EQ as (((A & B) & C) & D).
  constructor.
  assert (E: UFD.geb (uf dm1) (uf dm2) = true).
  { unfold UFD.geb.
    eapply PTree_Properties.for_all_correct.
    intros.
    eapply PTree_Properties.for_all_correct in B.
    unfold eqb_elt in B. eapply andb_true_iff in B as (C1 & C2). eapply C1.
    eauto. }
  eapply UFD.eqb_correct. eapply andb_true_iff; eauto.
  intros. unfold get.  
  destruct (PTree.get p (UFD.m (uf dm2))) eqn: G.
  - eapply PTree_Properties.for_all_correct in G. 2: eauto.
    unfold eqb_elt, beq_elt in G. eapply andb_true_iff in G as (C1 & C2).
    destruct ((m dm1) ! (UFD.repr (uf dm1) p)) eqn: D1;
      destruct ((m dm2) ! (UFD.repr (uf dm2) p)) eqn: D2;
      try congruence.
    eapply L.beq_correct. auto. eapply L.eq_refl.
  - destruct (PTree.get p (UFD.m (uf dm1))) eqn: G1.
    + destruct v. destruct o.
      * exploit UFD.repr_some. eapply G1. intros S1.
        eapply UFD.geb_correct in S1. 2: eauto.
        destruct (UFD.elt_eq p e).
        (* Impossible: p must be a singleton in dm1 *)
        -- subst. exfalso. eapply UFD.repr_some_neq; eauto.
        -- destruct (UFD.clos_order_dec (uf dm2) p e).
           ++ eapply Operators_Properties.clos_rtn1_rt in c.
              eapply Operators_Properties.clos_rt_rt1n in c.
              inv c. congruence.
              destruct H as (y_cl & Gy).
              (* contradict with the consistency of uf *)
              eapply (UFD.mcon (uf dm2)) in Gy as (D1 & (p' & p_cl & D2 & D3)).
              congruence.
           ++ exfalso. eapply n0.
              red in S1. eapply UFD.repr_none in G. rewrite G in *.
              eapply UFD.repr_clos_order_root. auto.
      * erewrite (UFD.repr_none (uf dm2)); auto.
        erewrite (UFD.repr_none2 (uf dm1)); eauto.
        destruct ((m dm2) ! p) eqn: M2.
        -- eapply PTree_Properties.for_all_correct in M2. 2: eauto.
           unfold val_eqb_opt2 in M2. rewrite G in M2.
           destruct ((m dm1) ! p) eqn: M1; try congruence.
           eapply L.beq_correct. auto.
        -- destruct ((m dm1) ! p) eqn: M1.
           ++ eapply PTree_Properties.for_all_correct in M1. 2: eauto.
              unfold val_eqb_opt1 in M1. rewrite G in M1.
              rewrite M2 in M1. congruence.
           ++ apply L.eq_refl.
    + erewrite (UFD.repr_none (uf dm2)); auto.
      erewrite (UFD.repr_none (uf dm1)); eauto.
      destruct ((m dm2) ! p) eqn: M2.
      -- eapply PTree_Properties.for_all_correct in M2. 2: eauto.
         unfold val_eqb_opt2 in M2. rewrite G in M2.
         destruct ((m dm1) ! p) eqn: M1; try congruence.
         eapply L.beq_correct. auto.
      -- destruct ((m dm1) ! p) eqn: M1.
         ++ eapply PTree_Properties.for_all_correct in M1. 2: eauto.
            unfold val_eqb_opt1 in M1. rewrite G in M1.
            rewrite M2 in M1. congruence.
         ++ apply L.eq_refl.
Qed.

Record ge' (x y: t) : Prop :=
  { uf_ge: UFD.ge (uf x) (uf y);
    m_ge: forall p, L.ge (get p x) (get p y) }.

Definition ge := ge'.

Lemma ge_refl: forall x y, eq x y -> ge x y.
Proof.
  intros. inv H.
  constructor.
  eapply UFD.ge_refl. auto.
  intros. apply L.ge_refl. auto.
Qed.

Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
Proof.
  intros. inv H; inv H0. constructor.
  eapply UFD.ge_trans; eauto.
  intros. apply L.ge_trans with (get p y); auto.
Qed.

Definition bot : t := mk (PTree.empty _) UFD.empty.

Lemma get_bot: forall p, get p bot = L.bot.
Proof.
  intros; reflexivity.
Qed.

Lemma ge_bot: forall x, ge x bot.
Proof.
  intros. constructor.
  simpl. eapply UFD.ge_empty.
  intros. rewrite get_bot. apply L.ge_bot.
Qed.


Definition lub_acc (uf: UFD.t) (acc: PTree.t L.t) p v :=
  let r := (UFD.repr uf p) in
  match acc ! r with
  | Some v' =>
      PTree.set r (L.lub v v') acc
  | None =>
      PTree.set r v acc
  end.

Lemma lub_acc_incr1_aux: forall uf1 l m3 m1 p v,
    fold_left (fun (a : PTree.t L.t) (p0 : positive * L.t) => lub_acc uf1 a (fst p0) (snd p0)) l m1 = m3 ->
    m1 ! p = Some v ->
    exists v1, m3 ! p = Some v1 /\ L.ge v1 v.
Proof.
  induction l; intros m3 m1 p v F G; simpl in F.
  - subst. exists v. split; auto. eapply L.ge_refl.
    eapply L.eq_refl.
  - destruct a as (x & vx). simpl in *.
    destruct (peq p (UFD.repr uf1 x)).
    + subst.
      exploit IHl. instantiate (2 := (lub_acc uf1 m1 x vx)). reflexivity.
      unfold lub_acc. rewrite G. rewrite PTree.gss. eauto.
      intros (v1 & F1 & GE1).
      exists v1. split. auto. eapply L.ge_trans. eauto.
      eapply L.ge_lub_right.
    + destruct (m1 ! (UFD.repr uf1 x)) eqn: Gx.
      * exploit IHl. instantiate (2 := (lub_acc uf1 m1 x vx)). reflexivity.
        unfold lub_acc. rewrite Gx.
        erewrite PTree.gso. eapply G. auto.
        intros (v1 & F1 & GE1). 
        exists v1. split. subst. auto. auto.
      * exploit IHl. instantiate (2 := (lub_acc uf1 m1 x vx)). reflexivity.
        unfold lub_acc. rewrite Gx.
        erewrite PTree.gso. eapply G. auto.
        intros (v1 & F1 & GE1). 
        exists v1. split. subst. auto. auto.
Qed.


Lemma lub_acc_incr1: forall uf m m1 m2 p v,
    PTree.fold (lub_acc uf) m1 m = m2 ->
    m ! p = Some v ->
    exists v1, m2 ! p = Some v1 /\ L.ge v1 v.
Proof.
  intros uf1 m1 m2 m3.
  rewrite PTree.fold_spec.
  eapply lub_acc_incr1_aux.
Qed.
      
  
Lemma lub_acc_incr2: forall uf m m1 m2 p v,
    PTree.fold (lub_acc uf) m1 m = m2 ->
    m1 ! p = Some v ->
    exists v1, m2 ! (UFD.repr uf p) = Some v1 /\ L.ge v1 v.
Proof.
  intros until v. intros F G.
  rewrite PTree.fold_spec in F.
  generalize (PTree.elements_keys_norepet m1). intros N.
  exploit PTree.elements_remove. eauto.
  intros (l1 & l2 & A1 & A2). rewrite A1 in *.
  rewrite fold_left_app in F. simpl in F.
  set (m' := (fold_left
                (fun (a : PTree.t L.t) (p : positive * L.t) => lub_acc uf0 a (fst p) (snd p))
                l1 m0)) in *.
  assert (G1: exists v1, (lub_acc uf0 m' p v) ! (UFD.repr uf0 p) = Some v1 /\ L.ge v1 v).
  { unfold lub_acc.
    destruct (m'! (UFD.repr uf0 p)) eqn: Gp.
    - rewrite PTree.gss. eexists. split; eauto.
      eapply L.ge_lub_left.
    - rewrite PTree.gss. eexists. split; eauto.
      eapply L.ge_refl. eapply L.eq_refl. }
  destruct G1 as (v1 & G1 & GE).
  exploit lub_acc_incr1_aux. eauto. eauto.
  intros (v2 & B1 & B2).
  exists v2. split. auto.
  eapply L.ge_trans; eauto.
Qed.

Definition lub (dm1 dm2: t) : t :=
  let uf3 := UFD.join (uf dm1) (uf dm2) in
  let m3 := PTree.fold (lub_acc uf3) (m dm1) (PTree.empty L.t) in
  let m4 := PTree.fold (lub_acc uf3) (m dm2) m3 in
  mk m4 uf3.

Lemma ge_lub_left: forall x y, ge (lub x y) x.
Proof.
  intros dm1 dm2. constructor. 
  unfold lub. simpl. eapply UFD.join_ge1.
  intros.
  unfold get, lub. simpl.
  destruct ((m dm1) ! (UFD.repr (uf dm1) p)) eqn: G1.
  2: { eapply L.ge_bot. }
  exploit (lub_acc_incr2 (UFD.join (uf dm1) (uf dm2)) (PTree.empty _)); eauto. 
  intros (v1 & G1' & GE1).
  generalize (UFD.join_sound1 (uf dm1) (uf dm2) (UFD.repr (uf dm1) p) p).
  unfold UFD.sameclass. intros EQC.
  exploit EQC. eapply UFD.repr_canonical. intros EQC1.
  rewrite EQC1 in G1'.
  exploit lub_acc_incr1. reflexivity. eapply G1'.
  instantiate (1 := m dm2). instantiate (1 := (UFD.join (uf dm1) (uf dm2))).
  intros (v2 & G2 & GE2).
  rewrite G2. eapply L.ge_trans; eauto.
Qed.
  
Lemma ge_lub_right: forall x y, ge (lub x y) y.
Proof.
  intros dm1 dm2. constructor. 
  unfold lub. simpl. eapply UFD.join_ge2.
  intros.
  unfold get, lub. simpl.
  destruct ((m dm2) ! (UFD.repr (uf dm2) p)) eqn: G2.
  2: { eapply L.ge_bot. }
  exploit lub_acc_incr2. reflexivity. eapply G2.
  instantiate (1 := (PTree.fold (lub_acc (UFD.join (uf dm1) (uf dm2))) (m dm1) (PTree.empty L.t))).
  instantiate (1 := (UFD.join (uf dm1) (uf dm2))).
    intros (v1 & G1 & GE1).
  generalize (UFD.join_sound2 (uf dm1) (uf dm2) (UFD.repr (uf dm2) p) p).
  unfold UFD.sameclass. intros EQC.
  exploit EQC. eapply UFD.repr_canonical. intros EQC1.
  rewrite EQC1 in G1.
  rewrite G1. auto.
Qed.

(* Map functions for origin environment *)

Definition map1 (f: L.t -> L.t) (dm: t) :=
  mk (PTree.map1 f (m dm)) (uf dm).

Lemma gmap1: forall (f: L.t -> L.t) (i: positive) (dm: t),
    f L.bot = L.bot ->
    get i (map1 f dm) = f (get i dm).
Proof.
  intros. unfold get, map1. simpl.
  rewrite !PTree.gmap1.
  destruct PTree.get eqn: G; simpl; auto.
Qed.

(* Union of two representative node in the ds_map *)

(* The new representative node is the repr node of b *)
Definition union (a b: positive) (dm: t) : t :=
  let dm1 := set b (L.lub (get a dm) (get b dm)) dm in
  mk (m dm1) (UFD.union (uf dm1) a b).

(* Deletion of a node in the equivalent set. Maybe we can first
determinte whether this node is in the set or not and then delete it
if it is actually in the set? *)

Definition delete (p: positive) (dm: t) : t :=
  let (uf1, or) := UFD.delete (uf dm) p in
  match or with
  (* The set of p contains more than p, and r is the new repr node of
  set of p after deleting p *)
  | Some r =>
      (* change the repr node of the set of p to r. There may be no need
         to remove the value of repr(p) in the map of dm *)
      let m1 := PTree.set r (get p dm) (m dm) in
      (* clear the value of p. We can use delete_fresh_repr to prove
      that r <> p by choosing b which may be specific to the
      analysis *)
      let m2 := PTree.remove p m1 in
      mk m2 uf1
  | None =>
      (* p is the only element in the set *)
      let m1 := PTree.remove p (m dm) in
      mk m1 uf1
  end.


(* Applying liveness result to the disjoint-set map to remove dead
region from the domain of the map *)

Fixpoint remove_dead_regions (live: RegionSet.t) (regs: list origin) (dm: t) : t :=
  match regs with
  | nil => dm
  | r :: l' =>
      if RegionSet.mem r live then
        remove_dead_regions live l' dm
      else
        remove_dead_regions live l' (delete r dm)
  end.

Definition apply_liveness (live: RegionSet.t) (dm: t) : t :=
  (* We also append the domain in the (m dm) as we should consider the
  region that belongs to a singleton equivalent set *)
  let region_dom := map fst (PTree.elements (UFD.m (uf dm))) ++ map fst (PTree.elements (m dm)) in
  (* for each region in region_dom, if it is not live (i.e., not in
  live set), then it is deleted from the disjoint-set map *)
  remove_dead_regions live region_dom dm.

End LUFMap.

  
(** Origin environment *)

Module LOrgEnv := LUFMap(LOrgLnSt).

(* Only abstract regions (or origins) *)
Module LOrgPhEnv := LUFMap(LOrgPhOptSt).

(** Auxilary defintions and functions used for updating origin environment *)

Inductive access_mode_bor := Ashallow | Adeep.

Definition conflict_access (a: access_kind) (mut: mutkind) : bool :=
  match a, mut with
  | AWrite, _ => true
  | ARead, Mutable => true
  | ARead, Immutable => false
  end.

(* Definition of relevant loan between the accessed place p with
access mode am and the place p1 in some loan set *)
Definition relevant_place (p p1: place) am :=
  is_prefix_strict p1 p || 
  match am with
  | Ashallow =>
      is_shallow_prefix p p1
  | Adeep =>
      is_support_prefix p p1
  end.

(* Definition of the conflict relation between a place p and a set of
loan ls. It is used in the invalidation of ls when accessing *)
Definition conflict_loan p (am: access_mode_bor) (ak: access_kind) (l: loan) : bool :=
  match l with
  | Lintern mut p1 =>
      relevant_place p p1 am && conflict_access ak mut
  | Lextern _ =>
      (* It is impossible to access a external loan *)
      false
  end.

(* Accessing p is conflict with the origin state os *)
Definition conflict p (ls: LoanSet.t) am ak :=
  negb (LoanSet.for_all (fun ln => negb (conflict_loan p am ak ln)) ls).


(* Invalidate an origin *)
Definition illegal_access_in_origin_state (p: place) (am: access_mode_bor) (ak: access_kind) (r: origin) (os: LOrgLnSt.origin_state) : bool :=
  match os with
  | LOrgLnSt.Live ls =>
      if conflict p ls am ak then true
      else false
  | LOrgLnSt.Dead => false
  end.

(* Check whether we should invalidate each origin in the origin *)
(* environment *)
Definition illegal_access (oe: LOrgEnv.t) (p: place) (am: access_mode_bor) (ak: access_kind) : bool :=
  let m := (LOrgEnv.m oe) in
  PTree_Properties.exists_ m (illegal_access_in_origin_state p am ak).

(* Legacy code *)
(* (* Invalidate an origin *) *)
(* Definition invalidate_origin (p: place) (am: access_mode_bor) (ak: access_kind) (os: origin_state) : origin_state := *)
(*   match os with *)
(*   | Live ls => *)
(*       if conflict p ls am ak then Dead *)
(*       else os *)
(*   | Dead => Dead *)
(*   end. *)

(* (* Check whether we should invalidate each origin in the origin *) *)
(* (* environment *) *)
(* Definition invalidate_origins (oe: LOrgEnv.t) (p: place) (am: access_mode_bor) (ak: access_kind) : LOrgEnv.t := *)
(*   LOrgEnv.map1 (invalidate_origin p am ak) oe. *)


(* Definition of valid access of a place: check whether there is any *)
(* dead origin in the type of the place. Return an error report if *)
(* invalid access happens *)
(* Definition valid_access (oe: LOrgEnv.t) (p: place) : bool := *)
(*   let ty := local_type_of_place p in *)
(*   let orgs := origins_of_type ty in *)
(*   let check org := *)
(*     match LOrgEnv.get org oe with *)
(*     | Live _ => true *)
(*     | Dead => false *)
(*     end in *)
(*   forallb check orgs. *)

(** Top level environment for borrow checking *)

(* Define equality for errcode *)

Lemma errcode_eq : forall (c1 c2: errcode), {c1 = c2} + {c1 <> c2}.
  generalize string_dec Pos.eq_dec.
  decide equality.
Defined.

Module LoansEnv <: SEMILATTICE.
  
  Inductive t' := | Bot (* | Err (loc: node) (msg: errmsg)  *)| State (org_env: LOrgEnv.t).
  
  Definition t := t'.
 
  Definition eq (x y: t) : Prop :=
    match x, y with
    | Bot, Bot => True
    | State oe1, State oe2 =>
        LOrgEnv.eq oe1 oe2
    (* | Err pc1 msg1, Err pc2 msg2 => *)
    (*     Pos.eq pc1 pc2 /\ list_forall2 eq msg1 msg2 *)
    | _, _ => False
    end.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => false
    | State oe1, State oe2 =>
        LOrgEnv.beq oe1 oe2
    (* | Err pc1 msg1, Err pc2 msg2 => *)
    (*     Pos.eqb pc1 pc2 && List.list_eq_dec errcode_eq msg1 msg2 *)
    | _, _ => false
    end.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    (* Err is the top *)
    (* | Err pc1 _, Err pc2 _ => Pos.ge pc1 pc2 *)
    (* | Err _ _, _ => True *)
    (* | _, Err _ _ => False *)
    | State oe1, State oe2 =>
        LOrgEnv.ge oe1 oe2
    end.

  Definition bot := Bot.

  Definition lub (x y: t) :=
    match x,y with
    | _, Bot => x
    | Bot, _ => y
    (* | Err pc1 msg1, Err pc2 msg2 => *)
    (*     if Pos.ltb pc1 pc2 then Err pc2 msg2 else Err pc1 msg1 *)
    (* | Err _ _, State _ => x *)
    (* | State _, Err _ _ => y *)
    | State oe1, State oe2 =>
        State (LOrgEnv.lub oe1 oe2) 
    end.

  (** TODO  *)
  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End LoansEnv.

Global Instance LOrgEnv_set_Proper: Proper (eq ==> LOrgLnSt.eq ==> LOrgEnv.eq ==> LOrgEnv.eq) LOrgEnv.set.
Proof.
  intros r1 r2 A ls1 ls2 B le1 le2 C. subst.
  inv C. 
  constructor.
  unfold LOrgEnv.set.
  destruct ls1; destruct ls2; simpl in *; eauto.
  intros. rewrite !LOrgEnv.gsspec.
  destruct peq.
  - eapply uf_eq in e. rewrite e. rewrite peq_true. auto.
  - destruct peq.
    eapply uf_eq in e. unfold UFD.sameclass in e. rewrite e in n. congruence.
    auto.
Qed.  

(* One-to-one correspondence between (positive * positive) and
positive, which is used to construct whole-module loans
environment. This code is mainly copied from stdpp.countable. *)

Definition omap {A B : Type} (f : A -> B) (o : option A) : option B :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | xH => xH
  | xO p => xO (xO (prod_encode_fst p))
  | xI p => xI (xO (prod_encode_fst p))
  end.

Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | xH => xO xH
  | xO p => xO (xO (prod_encode_snd p))
  | xI p => xO (xI (prod_encode_snd p))
  end.

Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | xH, xH => xI xH
  | xO p, xH => xO (xI (prod_encode_fst p))
  | xI p, xH => xI (xI (prod_encode_fst p))
  | xH, xO q => xI (xO (prod_encode_snd q))
  | xH, xI q => xI (xI (prod_encode_snd q))
  | xO p, xO q => xO (xO (prod_encode p q))
  | xO p, xI q => xO (xI (prod_encode p q))
  | xI p, xO q => xI (xO (prod_encode p q))
  | xI p, xI q => xI (xI (prod_encode p q))
  end.

Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | xO (xO p) => omap xO (prod_decode_fst p)
  | xI (xO p) =>
      Some
        match prod_decode_fst p with
        | Some q => xI q
        | None => xH
        end
  | xO (xI p) => omap xO (prod_decode_fst p)
  | xI (xI p) =>
      Some
        match prod_decode_fst p with
        | Some q => xI q
        | None => xH
        end
  | xO xH => None
  | xI xH => Some xH
  | xH => Some xH
  end.

Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | xO (xO p) => omap xO (prod_decode_snd p)
  | xI (xO p) => omap xO (prod_decode_snd p)
  | xO (xI p) =>
      Some
        match prod_decode_snd p with
        | Some q => xI q
        | None => xH
        end
  | xI (xI p) =>
      Some
        match prod_decode_snd p with
        | Some q => xI q
        | None => xH
        end
  | xO xH => Some xH
  | xI xH => Some xH
  | xH => None
  end.

Definition encode_pos_pair (pq : positive * positive) : positive :=
  let '(p, q) := pq in
  prod_encode p q.

Definition decode_pos_pair (r : positive) : option (positive * positive) :=
  match prod_decode_fst r, prod_decode_snd r with
  | Some p, Some q => Some (p, q)
  | _, _ => None
  end.

Lemma prod_decode_encode_fst_fst :
  forall p,
    prod_decode_fst (prod_encode_fst p) = Some p.
Proof.
  induction p; simpl; rewrite ?IHp; reflexivity.
Qed.

Lemma prod_decode_fst_encode_snd :
  forall p,
    prod_decode_fst (prod_encode_snd p) = None.
Proof.
  induction p; simpl; rewrite ?IHp; reflexivity.
Qed.

Lemma prod_decode_encode_snd_snd :
  forall p,
    prod_decode_snd (prod_encode_snd p) = Some p.
Proof.
  induction p; simpl; rewrite ?IHp; reflexivity.
Qed.

Lemma prod_decode_snd_encode_fst :
  forall p,
    prod_decode_snd (prod_encode_fst p) = None.
Proof.
  induction p; simpl; rewrite ?IHp; reflexivity.
Qed.

Lemma prod_decode_encode_fst :
  forall p q,
    prod_decode_fst (prod_encode p q) = Some p.
Proof.
  induction p; intros q; destruct q; simpl;
    repeat
      match goal with
      | |- context [prod_decode_fst (prod_encode ?p ?q)] =>
          rewrite (IHp q)
      | |- context [prod_decode_fst (prod_encode_fst ?p)] =>
          rewrite prod_decode_encode_fst_fst
      | |- context [prod_decode_fst (prod_encode_snd ?p)] =>
          rewrite prod_decode_fst_encode_snd
      end;
    reflexivity.
Qed.

Lemma prod_decode_encode_snd :
  forall p q,
    prod_decode_snd (prod_encode p q) = Some q.
Proof.
  induction p; intros q; destruct q; simpl;
    repeat
      match goal with
      | |- context [prod_decode_snd (prod_encode ?p ?q)] =>
          rewrite (IHp q)
      | |- context [prod_decode_snd (prod_encode_snd ?p)] =>
          rewrite prod_decode_encode_snd_snd
      | |- context [prod_decode_snd (prod_encode_fst ?p)] =>
          rewrite prod_decode_snd_encode_fst
      end;
    reflexivity.
Qed.

Lemma decode_encode_pos_pair :
  forall pq,
    decode_pos_pair (encode_pos_pair pq) = Some pq.
Proof.
  intros [p q].
  unfold encode_pos_pair, decode_pos_pair.
  rewrite prod_decode_encode_fst.
  rewrite prod_decode_encode_snd.
  reflexivity.
Qed.

Lemma encode_pos_pair_inj :
  forall pq1 pq2,
    encode_pos_pair pq1 = encode_pos_pair pq2 ->
    pq1 = pq2.
Proof.
  intros pq1 pq2 H.
  apply (f_equal decode_pos_pair) in H.
  rewrite !decode_encode_pos_pair in H.
  injection H as H.
  exact H.
Qed.

Lemma encode_pos_pair_inj' :
  forall p1 q1 p2 q2,
    encode_pos_pair (p1, q1) = encode_pos_pair (p2, q2) ->
    p1 = p2 /\ q1 = q2.
Proof.
  intros p1 q1 p2 q2 H.
  apply encode_pos_pair_inj in H.
  inversion H; subst.
  split; reflexivity.
Qed.

