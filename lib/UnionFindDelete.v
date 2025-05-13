Require Coq.Program.Wf.
Require Import Coqlib.
Require Import FSets Equalities.
Require Import FSetWeakList DecidableType.

Open Scope nat_scope.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

(** A persistent union-find-delete data structure derived from the
UnionFind.v from CompCert. *)


Module Type MAP.
  Parameter elt: Type.
  Parameter elt_eq: forall (x y: elt), {x=y} + {x<>y}.
  Parameter t: Type -> Type.
  Parameter empty: forall (A: Type), t A.
  Parameter get: forall (A: Type), elt -> t A -> option A.
  Parameter set: forall (A: Type), elt -> A -> t A -> t A.
  Axiom gempty: forall (A: Type) (x: elt), get x (empty A) = None.
  Axiom gsspec: forall (A: Type) (x y: elt) (v: A) (m: t A),
    get x (set y v m) = if elt_eq x y then Some v else get x m.
End MAP.

Unset Implicit Arguments.

Module Type UNION_FIND_DELETE.
  Parameter elt: Type.
  Parameter elt_eq: forall (x y: elt), {x=y} + {x<>y}.
  Parameter t: Type.

  Parameter repr: t -> elt -> elt.
  Axiom repr_canonical: forall uf a, repr uf (repr uf a) = repr uf a.

  Definition sameclass (uf: t) (a b: elt) : Prop := repr uf a = repr uf b.
  Axiom sameclass_refl:
    forall uf a, sameclass uf a a.
  Axiom sameclass_sym:
    forall uf a b, sameclass uf a b -> sameclass uf b a.
  Axiom sameclass_trans:
    forall uf a b c,
    sameclass uf a b -> sameclass uf b c -> sameclass uf a c.
  Axiom sameclass_repr:
    forall uf a, sameclass uf a (repr uf a).

  Parameter empty: t.
  Axiom repr_empty:
    forall a, repr empty a = a.
  Axiom sameclass_empty:
    forall a b, sameclass empty a b -> a = b.

  Parameter find: t -> elt -> elt * t.
  Axiom find_repr:
    forall uf a, fst (find uf a) = repr uf a.
  Axiom find_unchanged:
    forall uf a x, repr (snd (find uf a)) x = repr uf x.
  Axiom sameclass_find_1:
    forall uf a x y, sameclass (snd (find uf a)) x y <-> sameclass uf x y.
  Axiom sameclass_find_2:
    forall uf a, sameclass uf a (fst (find uf a)).
  Axiom sameclass_find_3:
    forall uf a, sameclass (snd (find uf a)) a (fst (find uf a)).

  Parameter union: t -> elt -> elt -> t.
  Axiom repr_union_1:
    forall uf a b x, repr uf x <> repr uf a -> repr (union uf a b) x = repr uf x.
  Axiom repr_union_2:
    forall uf a b x, repr uf x = repr uf a -> repr (union uf a b) x = repr uf b.
  Axiom repr_union_3:
    forall uf a b, repr (union uf a b) b = repr uf b.
  Axiom sameclass_union_1:
    forall uf a b, sameclass (union uf a b) a b.
  Axiom sameclass_union_2:
    forall uf a b x y, sameclass uf x y -> sameclass (union uf a b) x y.
  Axiom sameclass_union_3:
    forall uf a b x y,
    sameclass (union uf a b) x y ->
       sameclass uf x y
    \/ sameclass uf x a /\ sameclass uf y b
    \/ sameclass uf x b /\ sameclass uf y a.

  Parameter merge: t -> elt -> elt -> t.
  Axiom repr_merge:
    forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
  Axiom sameclass_merge:
    forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.

  Parameter path_ord: t -> elt -> elt -> Prop.
  Axiom path_ord_wellfounded:
    forall uf, well_founded (path_ord uf).
  Axiom path_ord_canonical:
    forall uf x y, repr uf x = x -> ~path_ord uf y x.
  Axiom path_ord_merge_1:
    forall uf a b x y,
    path_ord uf x y -> path_ord (merge uf a b) x y.
  Axiom path_ord_merge_2:
    forall uf a b,
    repr uf a <> repr uf b -> path_ord (merge uf a b) b (repr uf a).

  Parameter pathlen: t -> elt -> nat.
  Axiom pathlen_zero:
    forall uf a, repr uf a = a <-> pathlen uf a = O.
  Axiom pathlen_merge:
    forall uf a b x,
    pathlen (merge uf a b) x =
      if elt_eq (repr uf a) (repr uf b) then
        pathlen uf x
      else if elt_eq (repr uf x) (repr uf a) then
        pathlen uf x + pathlen uf b + 1
      else
        pathlen uf x.
  Axiom pathlen_gt_merge:
    forall uf a b x y,
    repr uf x = repr uf y ->
    pathlen uf x > pathlen uf y ->
    pathlen (merge uf a b) x > pathlen (merge uf a b) y.

  (* Delete operation *)
  Parameter delete: t -> elt -> t.
  Axiom delete_repr:
    forall uf a, repr (delete uf a) a = a.
  Axiom delete_unchanged:
    forall uf a b, a <> b -> repr (delete uf a) b = repr uf b.
    
End UNION_FIND_DELETE.

Module UFD (M: MAP) : UNION_FIND_DELETE with Definition elt := M.elt.
  
Definition elt := M.elt.
Definition elt_eq := M.elt_eq.

Module Elt <: DecidableType.DecidableType.
  Definition t := M.elt.
  Definition eq := @eq M.elt.
  Definition eq_dec := M.elt_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Elt.

Module Elts := FSetWeakList.Make(Elt).

(* A set of equivalence classes over elt is represented by a map m.

   M.get a m = Some (a', cl) means that a' is the parent of a and cl
   are the children of a. The invariant is that a must be the parent
   of all the elements in cl. For now, we use Elts to represent
   the children set.

   M.get a m = None means that a is the canonical representative for
   its equivalence class. *)

(* The ordering over elt induced by such a map.
   repr_order m a a' iff M.get a' m = Some a.
   This ordering must be well founded. *)

Definition vt : Type := option elt * Elts.t.

Definition order (m: M.t vt) (a a': elt) : Prop :=
  exists (cl: Elts.t), M.get a' m = Some (Some a, cl).

Definition consistent (m: M.t vt) : Prop :=
  forall a b_opt a_cl,
    M.get a m = Some (b_opt, a_cl) ->
    (* all the children in a_cl points to a *)
    Elts.For_all (order m a) a_cl
    /\ (match b_opt with
       | Some b =>
           (* a is in the children of b *)
           (exists b' b_cl, M.get b m = Some (b', b_cl) /\ Elts.In a b_cl)
       | None =>
           (* a is the root *)
           True
       end).
             
Record unionfind : Type := mk { m: M.t vt;
                                mwf: well_founded (order m);
                                mcon: consistent m}.

Definition t := unionfind.

Definition getlink (m: M.t vt) (a: elt) : {a' | exists cl, M.get a m = Some (Some a', cl)} + {M.get a m = None \/ exists cl, M.get a m = Some (None, cl)}.
Proof.
  destruct (M.get a m) eqn: G.
  - destruct v as ([v1 |] & v2).
    + left. exists v1, v2. auto.
    + right. eauto.
  - right; auto.
Defined.

(* The canonical representative of an element *)

Section REPR.

Variable uf: t.

Definition F_repr (a: elt) (rec: forall b, order uf.(m) b a -> elt) : elt :=
  match getlink uf.(m) a with
  | inleft (exist a' P) => rec a' P
  | inright _ => a
  end.

Definition repr (a: elt) : elt := Fix uf.(mwf) (fun _ => elt) F_repr a.

Lemma repr_unroll:
  forall a, repr a = match M.get a uf.(m) with Some (Some a', _) => repr a' | _ => a end.
Proof.
  intros. unfold repr at 1. rewrite Fix_eq.
  unfold F_repr. destruct (getlink uf.(m) a) as [[a' (cl & P)] | [Q1 | (cl & Q2)]].
  rewrite P; auto.
  rewrite Q1; auto.
  rewrite Q2; auto.
  intros. unfold F_repr. destruct (getlink (m uf) x) as [[a' P] | Q]; auto.
Qed.

Lemma repr_none:
  forall a,
  M.get a uf.(m) = None ->
  repr a = a.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_none2:
  forall a cl,
  M.get a uf.(m) = Some (None, cl) ->
  repr a = a.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_some:
  forall a a' cl,
  M.get a uf.(m) = Some (Some a', cl) ->
  repr a = repr a'.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_res_none:
  forall (a: elt), M.get (repr a) uf.(m) = None \/ exists cl, M.get (repr a) uf.(m) = Some (None, cl).
Proof.
  apply (well_founded_ind (mwf uf)). intros.
  rewrite repr_unroll. destruct (M.get x (m uf)) as [([y|] & cl) | ] eqn:X; auto.
  eapply H. red. eauto.
  right. eauto.
Qed.

Lemma repr_canonical:
  forall (a: elt), repr (repr a) = repr a.
Proof.
  intros. destruct (repr_res_none a) as [A | (cl & B)].
  apply repr_none. auto. 
  eapply repr_none2. eauto.
Qed.

Lemma repr_some_diff:
  forall a a' cl, M.get a uf.(m) = Some (Some a', cl) -> a <> repr a'.
Proof.
  intros; red; intros.
  assert (repr a = a). rewrite H0 at 2. apply (repr_some a a' cl); auto.
  destruct (repr_res_none a) as [A | (cl' & B)].
  congruence. congruence.
Qed.

End REPR.

Definition sameclass (uf: t) (a b: elt) : Prop :=
  repr uf a = repr uf b.

Lemma sameclass_refl:
  forall uf a, sameclass uf a a.
Proof.
  intros. red. auto.
Qed.

Lemma sameclass_sym:
  forall uf a b, sameclass uf a b -> sameclass uf b a.
Proof.
  intros. red. symmetry. exact H.
Qed.

Lemma sameclass_trans:
  forall uf a b c,
  sameclass uf a b -> sameclass uf b c -> sameclass uf a c.
Proof.
  intros. red. transitivity (repr uf b). exact H. exact H0.
Qed.

Lemma sameclass_repr:
  forall uf a, sameclass uf a (repr uf a).
Proof.
  intros. red. symmetry. rewrite repr_canonical. auto.
Qed.

(* The empty unionfind structure (each element in its own class) *)

Lemma wf_empty:
  well_founded (order (M.empty vt)).
Proof.
  red. intros. apply Acc_intro. intros b RO. red in RO.
  destruct RO as (cl & RO).
  rewrite M.gempty in RO. discriminate.
Qed.

Lemma consistent_empty:
  consistent (M.empty vt).
Proof.
  red. intros. rewrite M.gempty in H. discriminate.
Qed.

Definition empty : t := mk (M.empty vt) wf_empty consistent_empty.

Lemma repr_empty:
  forall a, repr empty a = a.
Proof.
  intros. apply repr_none. simpl. apply M.gempty.
Qed.

Lemma sameclass_empty:
  forall a b, sameclass empty a b -> a = b.
Proof.
  intros. red in H. repeat rewrite repr_empty in H. auto.
Qed.

(* Merging two equivalence classes *)

Section IDENTIFY.

Variable uf: t.
Variables a b: elt.
Variable a_cl : Elts.t.           (* children of a *)
Hypothesis a_canon: (M.get a uf.(m) = None /\ a_cl = Elts.empty)
                    \/ M.get a uf.(m) = Some (None, a_cl).
Hypothesis not_same_class: repr uf b <> a.

Let b_new := match M.get b uf.(m) with
            | Some (c, b_cl) =>
                (c, Elts.add a b_cl)
            | None =>
                (None, Elts.add a Elts.empty)
            end.

Definition identify_ufm := M.set b b_new (M.set a (Some b, a_cl) uf.(m)).

Remark a_not_eq_b: a <> b.
Proof.
  intro. subst. apply not_same_class.
  destruct a_canon as [(A1 & A2)| A3].
  apply repr_none. auto.
  eapply repr_none2. eauto.
Qed.
  
Lemma identify_order:
  forall x y,
  order identify_ufm y x <->
  order uf.(m) y x \/ (x = a /\ y = b).
Proof.
  intros until y. unfold order, identify_ufm. rewrite !M.gsspec.
  split.
  - destruct (M.elt_eq x b).
    + subst. destruct (M.get b (m uf)) as [(c & b_cl) |] eqn: G1.
      * intros (cl & A). inv A. eauto.
      * intros (cl & A). inv A.
    + destruct (M.elt_eq x a).
      * subst. intros (cl & A). inv A. eauto.
      * intros (cl & A). eauto.
  - intros [(cl & G) | (A1 & A2)].
    + destruct (M.elt_eq x b).
      * subst. unfold b_new. rewrite G. eauto.
      * destruct (M.elt_eq x a).
        -- subst. rewrite G in a_canon.
           destruct a_canon as [(A1 & A2)| A3]; try congruence.
        -- eauto.
    + subst. rewrite dec_eq_false. 2: apply a_not_eq_b.
      rewrite dec_eq_true. eauto.
Qed.

Remark identify_Acc_b:
  forall x,
  Acc (order uf.(m)) x -> repr uf x <> a -> Acc (order identify_ufm) x.
Proof.
  induction 1; intros. constructor; intros.
  rewrite identify_order in H2. destruct H2 as [A | [A B]].
  - apply H0; auto.
    destruct A as (cl & A).
    rewrite <- (repr_some uf _ _ _ A). auto.
  - subst. elim H1.
    destruct a_canon as [(A1 & A2)| A3].
    apply repr_none. auto.
    eapply repr_none2. eauto.
Qed.

Remark identify_Acc:
  forall x,
  Acc (order uf.(m)) x -> Acc (order identify_ufm) x.
Proof.
  induction 1. constructor; intros.
  rewrite identify_order in H1. destruct H1 as [A | [A B]].
  auto.
  subst. apply identify_Acc_b; auto. apply uf.(mwf).
Qed.

Lemma identify_wf:
  well_founded (order identify_ufm).
Proof.
  red; intros. apply identify_Acc. apply uf.(mwf).
Qed.


Lemma identify_consistent:
  consistent identify_ufm.
Proof.
  red. intros x x_opt x_cl G.
  unfold identify_ufm in *.
  rewrite !M.gsspec in G.
  destruct (M.elt_eq x b).
  - subst. destruct (M.get b (m uf)) as [(c & b_cl) |] eqn: G1; inv G; unfold b_new in *.
    + split.
      * red. intros x IN. red.
        destruct (M.elt_eq x a).
        -- subst. rewrite !M.gsspec.
           rewrite dec_eq_false, dec_eq_true. eauto.
           apply a_not_eq_b.
        -- apply Elts.add_3 in IN; auto.
           eapply (mcon uf)in IN; eauto. destruct IN as (x_cl & Gx).
           assert (x <> b).
           { intro. subst. rewrite G1 in Gx. inv Gx.
             eapply repr_some_diff. eapply G1.

             rewrite repr_unroll. rewrite 
   
Definition identify := mk identify_ufm identify_wf identify_consistent.
  
Lemma repr_identify_1:
  forall x, repr uf x <> a -> repr identify x = repr uf x.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in *.
  destruct (M.get x (m uf)) as [a'|] eqn:X.
  rewrite <- H; auto.
  apply repr_some. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto. congruence.
  apply repr_none. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto.
Qed.

Lemma repr_identify_2:
  forall x, repr uf x = a -> repr identify x = repr uf b.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in H0. destruct (M.get x (m uf)) as [a'|] eqn:X.
  rewrite <- (H a'); auto.
  apply repr_some. simpl. rewrite M.gsspec. rewrite dec_eq_false; auto. congruence.
  subst x. rewrite (repr_unroll identify). simpl. rewrite M.gsspec.
  rewrite dec_eq_true. apply repr_identify_1. auto.
Qed.

End IDENTIFY.

(* Union *)

Remark union_not_same_class:
  forall uf a b, repr uf a <> repr uf b -> repr uf (repr uf b) <> repr uf a.
Proof.
  intros. rewrite repr_canonical. auto.
Qed.

Definition union (uf: t) (a b: elt) : t :=
  let a' := repr uf a in
  let b' := repr uf b in
  match M.elt_eq a' b' with
  | left EQ => uf
  | right NEQ => identify uf a' b' (repr_res_none uf a) (union_not_same_class uf a b NEQ)
  end.

Lemma repr_union_1:
  forall uf a b x, repr uf x <> repr uf a -> repr (union uf a b) x = repr uf x.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  apply repr_identify_1. auto.
Qed.

Lemma repr_union_2:
  forall uf a b x, repr uf x = repr uf a -> repr (union uf a b) x = repr uf b.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  congruence.
  rewrite <- (repr_canonical uf b). apply repr_identify_2. auto.
Qed.

Lemma repr_union_3:
  forall uf a b, repr (union uf a b) b = repr uf b.
Proof.
  intros. unfold union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto. apply repr_identify_1. auto.
Qed.

Lemma sameclass_union_1:
  forall uf a b, sameclass (union uf a b) a b.
Proof.
  intros; red. rewrite repr_union_2; auto. rewrite repr_union_3. auto.
Qed.

Lemma sameclass_union_2:
  forall uf a b x y, sameclass uf x y -> sameclass (union uf a b) x y.
Proof.
  unfold sameclass; intros.
  destruct (M.elt_eq (repr uf x) (repr uf a));
  destruct (M.elt_eq (repr uf y) (repr uf a)).
  repeat rewrite repr_union_2; auto.
  congruence. congruence.
  repeat rewrite repr_union_1; auto.
Qed.

Lemma sameclass_union_3:
  forall uf a b x y,
  sameclass (union uf a b) x y ->
     sameclass uf x y
  \/ sameclass uf x a /\ sameclass uf y b
  \/ sameclass uf x b /\ sameclass uf y a.
Proof.
  intros until y. unfold sameclass.
  destruct (M.elt_eq (repr uf x) (repr uf a));
  destruct (M.elt_eq (repr uf y) (repr uf a)).
  intro. left. congruence.
  rewrite repr_union_2; auto. rewrite repr_union_1; auto.
  rewrite repr_union_1; auto. rewrite repr_union_2; auto.
  repeat rewrite repr_union_1; auto.
Qed.

(* Merge *)

Definition merge (uf: t) (a b: elt) : t :=
  let a' := repr uf a in
  let b' := repr uf b in
  match M.elt_eq a' b' with
  | left EQ => uf
  | right NEQ => identify uf a' b (repr_res_none uf a) (not_eq_sym NEQ)
  end.

Lemma repr_merge:
  forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
Proof.
  intros. unfold merge, union. destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  destruct (M.elt_eq (repr uf x) (repr uf a)).
  repeat rewrite repr_identify_2; auto. rewrite repr_canonical; auto.
  repeat rewrite repr_identify_1; auto.
Qed.

Lemma sameclass_merge:
  forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.
Proof.
  unfold sameclass; intros. repeat rewrite repr_merge. tauto.
Qed.

(* Path order and merge *)

Definition path_ord (uf: t) : elt -> elt -> Prop := order uf.(m).

Lemma path_ord_wellfounded:
  forall uf, well_founded (path_ord uf).
Proof.
  intros. apply mwf.
Qed.

Lemma path_ord_canonical:
  forall uf x y, repr uf x = x -> ~path_ord uf y x.
Proof.
  intros; red; intros. hnf in H0.
  assert (M.get x (m uf) = None). rewrite <- H. apply repr_res_none.
  congruence.
Qed.

Lemma path_ord_merge_1:
  forall uf a b x y,
  path_ord uf x y -> path_ord (merge uf a b) x y.
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  red. simpl. red. rewrite M.gsspec. rewrite dec_eq_false. apply H.
  red; intros. hnf in H. generalize (repr_res_none uf a). congruence.
Qed.

Lemma path_ord_merge_2:
  forall uf a b,
  repr uf a <> repr uf b -> path_ord (merge uf a b) b (repr uf a).
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  congruence.
  red. simpl. red. rewrite M.gsspec. rewrite dec_eq_true; auto.
Qed.

(* Path length and merge *)

Section PATHLEN.

Variable uf: t.

Definition F_pathlen (a: elt) (rec: forall b, order uf.(m) b a -> nat) : nat :=
  match getlink uf.(m) a with
  | inleft (exist a' P) => S (rec a' P)
  | inright _ => O
  end.

Definition pathlen (a: elt) : nat := Fix uf.(mwf) (fun _ => nat) F_pathlen a.

Lemma pathlen_unroll:
  forall a, pathlen a = match M.get a uf.(m) with Some a' => S(pathlen a') | None => O end.
Proof.
  intros. unfold pathlen at 1. rewrite Fix_eq.
  unfold F_pathlen. destruct (getlink uf.(m) a) as [[a' P] | Q].
  rewrite P; auto.
  rewrite Q; auto.
  intros. unfold F_pathlen. destruct (getlink (m uf) x) as [[a' P] | Q]; auto.
Qed.

Lemma pathlen_none:
  forall a,
  M.get a uf.(m) = None ->
  pathlen a = 0.
Proof.
  intros. rewrite pathlen_unroll. rewrite H; auto.
Qed.

Lemma pathlen_some:
  forall a a',
  M.get a uf.(m) = Some a' ->
  pathlen a = S (pathlen a').
Proof.
  intros. rewrite pathlen_unroll. rewrite H; auto.
Qed.

Lemma pathlen_zero:
  forall a, repr uf a = a <-> pathlen a = O.
Proof.
  intros; split; intros.
  apply pathlen_none. rewrite <- H. apply repr_res_none.
  apply repr_none. rewrite pathlen_unroll in H.
  destruct (M.get a (m uf)); congruence.
Qed.

End PATHLEN.

(* Path length and merge *)

Lemma pathlen_merge:
  forall uf a b x,
  pathlen (merge uf a b) x =
    if M.elt_eq (repr uf a) (repr uf b) then
      pathlen uf x
    else if M.elt_eq (repr uf x) (repr uf a) then
      pathlen uf x + pathlen uf b + 1
    else
      pathlen uf x.
Proof.
  intros. unfold merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)).
  auto.
  set (uf' := identify uf (repr uf a) b (repr_res_none uf a) (not_eq_sym n)).
  pattern x. apply (well_founded_ind (mwf uf')); intros.
  rewrite (pathlen_unroll uf'). destruct (M.get x0 (m uf')) as [x'|] eqn:G.
  rewrite H; auto. simpl in G. rewrite M.gsspec in G.
  destruct (M.elt_eq x0 (repr uf a)). rewrite e. rewrite repr_canonical. rewrite dec_eq_true.
  inversion G. subst x'. rewrite dec_eq_false; auto.
  replace (pathlen uf (repr uf a)) with 0. lia.
  symmetry. apply pathlen_none. apply repr_res_none.
  rewrite (repr_unroll uf x0), (pathlen_unroll uf x0); rewrite G.
  destruct (M.elt_eq (repr uf x') (repr uf a)); lia.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x0 (repr uf a)); try discriminate.
  rewrite (repr_none uf x0) by auto. rewrite dec_eq_false; auto.
  symmetry. apply pathlen_zero; auto. apply repr_none; auto.
Qed.

Lemma pathlen_gt_merge:
  forall uf a b x y,
  repr uf x = repr uf y ->
  pathlen uf x > pathlen uf y ->
  pathlen (merge uf a b) x > pathlen (merge uf a b) y.
Proof.
  intros. repeat rewrite pathlen_merge.
  destruct (M.elt_eq (repr uf a) (repr uf b)). auto.
  rewrite H. destruct (M.elt_eq (repr uf y) (repr uf a)).
  lia. auto.
Qed.

(* Path compression *)

Section COMPRESS.

Variable uf: t.
Variable a b: elt.
Hypothesis a_diff_b: a <> b.
Hypothesis a_repr_b: repr uf a = b.

Lemma compress_order:
  forall x y,
  order (M.set a b uf.(m)) y x ->
  order uf.(m) y x \/ (x = a /\ y = b).
Proof.
  intros until y. unfold order. rewrite M.gsspec.
  destruct (M.elt_eq x a).
  intuition congruence.
  auto.
Qed.

Remark compress_Acc:
  forall x,
  Acc (order uf.(m)) x -> Acc (order (M.set a b uf.(m))) x.
Proof.
  induction 1. constructor; intros.
  destruct (compress_order _ _ H1) as [A | [A B]].
  auto.
  subst x y. constructor; intros.
  destruct (compress_order _ _ H2) as [A | [A B]].
  red in A. generalize (repr_res_none uf a). congruence.
  congruence.
Qed.

Lemma compress_wf:
  well_founded (order (M.set a b uf.(m))).
Proof.
  red; intros. apply compress_Acc. apply uf.(mwf).
Qed.

Definition compress := mk (M.set a b uf.(m)) compress_wf.

Lemma repr_compress:
  forall x, repr compress x = repr uf x.
Proof.
  apply (well_founded_ind (mwf compress)); intros.
  rewrite (repr_unroll compress).
  destruct (M.get x (m compress)) as [y|] eqn:G.
  rewrite H; auto.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x a).
  inversion G. subst x y. rewrite <- a_repr_b. apply repr_canonical.
  symmetry; apply repr_some; auto.
  simpl in G. rewrite M.gsspec in G. destruct (M.elt_eq x a).
  congruence.
  symmetry; apply repr_none; auto.
Qed.

End COMPRESS.

(* Find with path compression *)

Section FIND.

Variable uf: t.

Program Fixpoint find_x (a: elt) {wf (order uf.(m)) a} :
    { r: elt * t | fst r = repr uf a /\ forall x, repr (snd r) x = repr uf x } :=
  match M.get a uf.(m) with
  | Some a' =>
      match find_x a' with
      | pair b uf' => (b, compress uf' a b _ _)
      end
  | None => (a, uf)
  end.
Next Obligation.
  red. auto.
Qed.
Next Obligation.
  (* a <> b*)
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  apply repr_some_diff. auto.
Qed.
Next Obligation.
  destruct (find_x a') as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  rewrite B. apply repr_some. auto.
Qed.
Next Obligation.
  split.
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  symmetry. apply repr_some. auto.
  intros. rewrite repr_compress.
  destruct (find_x a')
  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous. auto.
Qed.
Next Obligation.
  split; auto. symmetry. apply repr_none. auto.
Qed.
Next Obligation.
  apply mwf.
Defined.

Definition find (a: elt) : elt * t := proj1_sig (find_x a).

Lemma find_repr:
  forall a, fst (find a) = repr uf a.
Proof.
  unfold find; intros. destruct (find_x a) as [[b uf'] [A B]]. simpl. auto.
Qed.

Lemma find_unchanged:
  forall a x, repr (snd (find a)) x = repr uf x.
Proof.
  unfold find; intros. destruct (find_x a) as [[b uf'] [A B]]. simpl. auto.
Qed.

Lemma sameclass_find_1:
  forall a x y, sameclass (snd (find a)) x y <-> sameclass uf x y.
Proof.
  unfold sameclass; intros. repeat rewrite find_unchanged. tauto.
Qed.

Lemma sameclass_find_2:
  forall a, sameclass uf a (fst (find a)).
Proof.
  intros. rewrite find_repr. apply sameclass_repr.
Qed.

Lemma sameclass_find_3:
  forall a, sameclass (snd (find a)) a (fst (find a)).
Proof.
  intros. rewrite sameclass_find_1. apply sameclass_find_2.
Qed.

End FIND.

End UF.

