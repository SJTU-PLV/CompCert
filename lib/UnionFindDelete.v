Require Coq.Program.Wf.
Require Import Coqlib.
Require Import FSets Equalities.
Require Import FSetWeakList DecidableType.
Require Import Relations.
Require Import Maps.

Open Scope nat_scope.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

(** A persistent union-find-delete data structure derived from the
UnionFind.v from CompCert. *)

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

  (** merge and pathlen are not used in our compiler, so we comment them for simplicity  *)
  Parameter merge: t -> elt -> elt -> t.
  Axiom repr_merge:
    forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
  Axiom sameclass_merge:
    forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.

  (* Parameter path_ord: t -> elt -> elt -> Prop. *)
  (* Axiom path_ord_wellfounded: *)
  (*   forall uf, well_founded (path_ord uf). *)
  (* Axiom path_ord_canonical: *)
  (*   forall uf x y, repr uf x = x -> ~path_ord uf y x. *)
  (* Axiom path_ord_merge_1: *)
  (*   forall uf a b x y, *)
  (*   path_ord uf x y -> path_ord (merge uf a b) x y. *)
  (* Axiom path_ord_merge_2: *)
  (*   forall uf a b, *)
  (*   repr uf a <> repr uf b -> path_ord (merge uf a b) b (repr uf a). *)

  (* Parameter pathlen: t -> elt -> nat. *)
  (* Axiom pathlen_zero: *)
  (*   forall uf a, repr uf a = a <-> pathlen uf a = O. *)
  (* Axiom pathlen_merge: *)
  (*   forall uf a b x, *)
  (*   pathlen (merge uf a b) x = *)
  (*     if elt_eq (repr uf a) (repr uf b) then *)
  (*       pathlen uf x *)
  (*     else if elt_eq (repr uf x) (repr uf a) then *)
  (*       pathlen uf x + pathlen uf b + 1 *)
  (*     else *)
  (*       pathlen uf x. *)
  (* Axiom pathlen_gt_merge: *)
  (*   forall uf a b x y, *)
  (*   repr uf x = repr uf y -> *)
  (*   pathlen uf x > pathlen uf y -> *)
  (*   pathlen (merge uf a b) x > pathlen (merge uf a b) y. *)
  
  (* Delete operation *)
  Parameter delete: t -> elt -> (t * option elt).
  Axiom delete_repr:
    forall uf a, repr (fst (delete uf a)) a = a.
  Axiom delete_repr_unchanged1: forall uf b x,
    repr uf b <> repr uf x ->
    repr (fst (delete uf b)) x = repr uf x.
  Axiom delete_repr_unchanged2: forall uf uf1 a b,
    a <> b ->
    delete uf a = (uf1, None) ->
    repr uf1 b = repr uf b.
  Axiom delete_fresh_repr: forall uf uf1 a b r,
    a <> b ->
    repr uf a = repr uf b ->
    delete uf a = (uf1, Some r) ->
    repr uf1 b = r.

  (* Join two union-find structures *)
  Parameter join: t -> t -> t.
  Axiom join_sound1: forall uf1 uf2 a b,
      sameclass uf1 a b ->
      sameclass (join uf1 uf2) a b.
  Axiom join_sound2: forall uf1 uf2 a b,
      sameclass uf2 a b ->
      sameclass (join uf1 uf2) a b.
  (* This lemma says that the join operate is not trivial *)
  (* Axiom join_sound3: forall uf1 uf2 a b, *)
  (*     sameclass (join uf1 uf2) a b -> *)
  (*     sameclass uf1 a b \/ sameclass uf1 a b \/ (exists c, sameclass uf1 a c /\ sameclass uf2 b c). *)

  (* Comparison of two union-find structures *)
  Parameter eq: t -> t -> Prop.
  Parameter ge: t -> t -> Prop.
  Axiom eq_refl: forall uf,
      eq uf uf.
  Axiom eq_sym: forall uf1 uf2,
      eq uf1 uf2 -> eq uf2 uf1.
  Axiom eq_trans: forall uf1 uf2 uf3,
      eq uf1 uf2 -> eq uf2 uf3 -> eq uf1 uf3.
  Axiom ge_refl: forall uf1 uf2,
      eq uf1 uf2 ->
      ge uf1 uf2.
  Axiom ge_trans: forall uf1 uf2 uf3,
      ge uf1 uf2 -> ge uf2 uf3 -> ge uf1 uf3.
  Axiom ge_antisym: forall uf1 uf2,
      ge uf1 uf2 -> ge uf2 uf1 -> eq uf1 uf2.

  Parameter geb: t -> t -> bool.
  Axiom geb_correct: forall uf1 uf2,
      geb uf1 uf2 = true ->
      ge uf1 uf2.
  Parameter eqb: t -> t -> bool. 
  Axiom eqb_correct: forall uf1 uf2,
      eqb uf1 uf2 = true ->
      eq uf1 uf2.
  
  (* (* We may use the representative node as a key in a map and want to *)
  (* compare the value with a comparison function *) *)
  (* Parameter geb_cmp : (elt -> elt -> bool) -> t -> t -> bool. *)
  (* Parameter eqb_cmp : (elt -> elt -> bool) -> t -> t -> bool. *)
  (* Parameter eq_cmp: (elt -> elt -> bool) -> t -> t -> Prop. *)
  (* Parameter ge_cmp: (elt -> elt -> bool) -> t -> t -> Prop. *)
  (* Axiom eq_cmp_refl: forall uf f, *)
  (*     (forall x, f x x = true) -> *)
  (*     eq_cmp f uf uf. *)
  (* Axiom eq_cmp_sym: forall uf1 uf2 f, *)
  (*     (forall x y, f x y = f y x) -> *)
  (*     eq_cmp f uf1 uf2 -> eq_cmp f uf2 uf1. *)
  (* Axiom eq_cmp_trans: forall uf1 uf2 uf3 f, *)
  (*     (forall x y z, f x y = true -> f y z = true -> f x z = true) -> *)
  (*     eq_cmp f uf1 uf2 -> eq_cmp f uf2 uf3 -> eq_cmp f uf1 uf3. *)
  (* Axiom ge_refl: forall uf, *)
  (*     ge uf uf. *)
  (* Axiom ge_trans: forall uf1 uf2 uf3, *)
  (*     ge uf1 uf2 -> ge uf2 uf3 -> ge uf1 uf3. *)
  (* Axiom ge_antisym: forall uf1 uf2, *)
  (*     ge uf1 uf2 -> ge uf2 uf1 -> eq uf1 uf2. *)

  
End UNION_FIND_DELETE.

(* For simplicity, we do not paramterize the map in the UFD module *)
Module UFD <: UNION_FIND_DELETE.

Definition elt := positive.
Definition elt_eq := peq.

Module Elt <: DecidableType.DecidableType.
  Definition t := elt.
  Definition eq := @eq elt.
  Definition eq_dec := elt_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Elt.

Module Elts := FSetWeakList.Make(Elt).

(* A set of equivalence classes over elt is represented by a map m.

   PTree.get a m = Some (a', cl) means that a' is the parent of a and cl
   are the children of a. The invariant is that a must be the parent
   of all the elements in cl. For now, we use Elts to represent
   the children set.

   PTree.get a m = None means that a is the canonical representative for
   its equivalence class. *)

(* The ordering over elt induced by such a map.
   repr_order m a a' iff PTree.get a' m = Some a.
   This ordering must be well founded. *)

Definition vt : Type := option elt * Elts.t.

Definition order (m: PTree.t vt) (a a': elt) : Prop :=
  exists (cl: Elts.t), PTree.get a' m = Some (Some a, cl).

Definition consistent (m: PTree.t vt) : Prop :=
  forall a b_opt a_cl,
    PTree.get a m = Some (b_opt, a_cl) ->    
    (* all the children in a_cl points to a *)
    Elts.For_all (order m a) a_cl
    /\ (match b_opt with
       | Some b =>
           (* a is in the children of b *)
           (exists b' b_cl, PTree.get b m = Some (b', b_cl) /\ Elts.In a b_cl)
       | None =>
           (* a is the root *)
           True
       end).
             
Record unionfind : Type := mk { m: PTree.t vt;
                                mwf: well_founded (order m);
                                mcon: consistent m}.

Definition t := unionfind.

Definition getlink (m: PTree.t vt) (a: elt) : {a' | exists cl, PTree.get a m = Some (Some a', cl)} + {PTree.get a m = None \/ exists cl, PTree.get a m = Some (None, cl)}.
Proof.
  destruct (PTree.get a m) eqn: G.
  - destruct v as ([v1 |] & v2).
    + left. exists v1, v2. auto.
    + right. eauto.
  - right; auto.
Defined.

Lemma get_elt_dec: forall (m: PTree.t vt) a,
    {v | PTree.get a m = Some v} + {PTree.get a m = None}.
Proof.
  intros. destruct (PTree.get a m0); eauto.
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
  forall a, repr a = match PTree.get a uf.(m) with Some (Some a', _) => repr a' | _ => a end.
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
  PTree.get a uf.(m) = None ->
  repr a = a.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_none2:
  forall a cl,
  PTree.get a uf.(m) = Some (None, cl) ->
  repr a = a.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_some:
  forall a a' cl,
  PTree.get a uf.(m) = Some (Some a', cl) ->
  repr a = repr a'.
Proof.
  intros. rewrite repr_unroll. rewrite H; auto.
Qed.

Lemma repr_res_none:
  forall (a: elt), PTree.get (repr a) uf.(m) = None \/ exists cl, PTree.get (repr a) uf.(m) = Some (None, cl).
Proof.
  apply (well_founded_ind (mwf uf)). intros.
  rewrite repr_unroll. destruct (PTree.get x (m uf)) as [([y|] & cl) | ] eqn:X; auto.
  eapply H. red. eauto.
  right. eauto.
Defined.

Lemma repr_res_none_dec:
  forall (a: elt), {cl | PTree.get (repr a) uf.(m) = Some (None, cl)} + {PTree.get (repr a) uf.(m) = None}.
Proof.
  apply (well_founded_induction_type (mwf uf)). intros.
  rewrite repr_unroll. destruct (PTree.get x (m uf)) as [([y|] & cl) | ] eqn:X1; auto.
  eapply X. red. eauto.
  left. eauto.
Defined.

Lemma repr_canonical:
  forall (a: elt), repr (repr a) = repr a.
Proof.
  intros. destruct (repr_res_none a) as [A | (cl & B)].
  apply repr_none. auto. 
  eapply repr_none2. eauto.
Qed.

Lemma repr_some_diff:
  forall a a' cl, PTree.get a uf.(m) = Some (Some a', cl) -> a <> repr a'.
Proof.
  intros; red; intros.
  assert (repr a = a). rewrite H0 at 2. apply (repr_some a a' cl); auto.
  destruct (repr_res_none a) as [A | (cl' & B)].
  congruence. congruence.
Qed.

Lemma repr_some_same:
  forall a cl, PTree.get a uf.(m) = Some (Some a, cl) -> a = repr a.
Proof.
  intros a cl. generalize (mwf uf a).
  generalize dependent cl.
  generalize dependent a.
  induction 1. intros G.
  eapply H0. red. eauto. auto.
Qed.

Lemma repr_some_neq:
  forall a a' cl, PTree.get a uf.(m) = Some (Some a', cl) -> a <> a'.
Proof.
  intros. red. intro. subst. eapply repr_some_diff.
  eauto. eapply repr_some_same; eauto.
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
  well_founded (order (PTree.empty vt)).
Proof.
  red. intros. apply Acc_intro. intros b RO. red in RO.
  destruct RO as (cl & RO).
  rewrite PTree.gempty in RO. discriminate.
Qed.

Lemma consistent_empty:
  consistent (PTree.empty vt).
Proof.
  red. intros. rewrite PTree.gempty in H. discriminate.
Qed.

Definition empty : t := mk (PTree.empty vt) wf_empty consistent_empty.

Lemma repr_empty:
  forall a, repr empty a = a.
Proof.
  intros. apply repr_none. simpl. apply PTree.gempty.
Qed.

Lemma sameclass_empty:
  forall a b, sameclass empty a b -> a = b.
Proof.
  intros. red in H. repeat rewrite repr_empty in H. auto.
Qed.

(* Decidability of order *)

Lemma order_dec uf a b:
  {order (m uf) b a} + {~ order (m uf) b a}.
Proof.
  destruct (PTree.get a (m uf)) eqn: Ga.
  - destruct v. destruct o.
    + destruct (peq e b).
      * subst. left. red. eauto.
      * right. intro. eapply n.
        destruct H. rewrite Ga in H. inv H. auto.
    + right. intro. 
      destruct H. congruence.
  - right. intro. 
    destruct H. congruence.
Defined.

(* Reflexive and transitive closure of order relation *)

Definition clos_order m := clos_refl_trans_n1 elt (order m).

(* Decidability of clos_order *)

Lemma clos_order_dec uf r:
  forall a,
  {clos_order (m uf) r a} + {~ clos_order (m uf) r a}.
Proof.
  apply (well_founded_induction_type (mwf uf)). intros.
  destruct (PTree.get x (m uf)) as [(x_par & x_cl)|]eqn: G.
  - destruct x_par as [x_par |].
    + rename H into X. edestruct X. red. eauto.
      * left. red. econstructor. red. eauto. auto.
      * destruct (peq x r).
        -- subst. left. constructor.
        -- right. intro. apply n.
           inv H. congruence. red in H0.
           destruct H0 as (x_cl' & Gx). rewrite G in Gx. inv Gx.
           auto.
    + destruct (peq x r).
      * subst. left. constructor.
      * right. intro. inv H0. congruence.
        red in H1. destruct H1 as (x_cl' & Gx). congruence.
  - destruct (peq x r).
    + subst. left. constructor.
    + right. intro. inv H0. congruence.
      red in H1. destruct H1 as (x_cl' & Gx). congruence.
Defined.

Lemma repr_clos_order: forall uf x y,
    clos_order (m uf) x y ->
    repr uf x = repr uf y.
Proof.
  induction 1. auto.
  erewrite IHclos_refl_trans_n1.
  destruct H as (z_cl & A).
  symmetry.
  eapply repr_some. eauto.
Qed.
  
(** Show that clos_order is partial order *)
Lemma clos_order_antisym: forall uf x y,
    clos_order (m uf) x y ->
    clos_order (m uf) y x ->
    x = y.
Proof.
  intro uf.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  inv H1. auto.
  (* x -> y0 ->* y and y -> *x so we have y ->* y0 which enables I.H. *)
  exploit (H y0 H2 y).
  - eapply clos_rt_rtn1. eapply rt_trans with (y:=x).
    econstructor. auto.
    apply clos_rtn1_rt. auto.
  - auto.
  - intros. subst.
    inv H0; auto.
    (* x -> y -> y0 ->* x *)
    exploit (H y H2 y0); auto.
    + eapply clos_rt_rtn1. eapply rt_trans with (y:=x).
      econstructor. auto.
      apply clos_rtn1_rt. auto.
    + econstructor. eauto. econstructor.
    + intros. subst. red in H1. destruct H1.
      exfalso. eapply repr_some_neq. eauto. auto.
Qed.


(* Merging two equivalence classes *)

Section IDENTIFY.

Variable uf: t.
Variables a b: elt.
Variable a_cl : Elts.t.           (* children of a *)
Hypothesis a_canon: (PTree.get a uf.(m) = None /\ a_cl = Elts.empty)
                    \/ PTree.get a uf.(m) = Some (None, a_cl).
Hypothesis not_same_class: repr uf b <> a.

Definition b_new := match PTree.get b uf.(m) with
            | Some (c, b_cl) =>
                (c, Elts.add a b_cl)
            | None =>
                (None, Elts.add a Elts.empty)
            end.

Definition identify_ufm := PTree.set b b_new (PTree.set a (Some b, a_cl) uf.(m)).

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
  intros until y. unfold order, identify_ufm. rewrite !PTree.gsspec.
  split.
  - destruct (peq x b).
    + subst. unfold b_new. destruct (PTree.get b (m uf)) as [(c & b_cl) |] eqn: G1.
      * intros (cl & A). inv A. eauto.
      * intros (cl & A). inv A.
    + destruct (peq x a).
      * subst. intros (cl & A). inv A. eauto.
      * intros (cl & A). eauto.
  - intros [(cl & G) | (A1 & A2)].
    + destruct (peq x b).
      * subst. unfold b_new. rewrite G. eauto.
      * destruct (peq x a).
        -- subst. rewrite G in a_canon.
           destruct a_canon as [(A1 & A2)| A3]; try congruence.
        -- eauto.
    + subst. rewrite dec_eq_false. 2: apply a_not_eq_b.
      rewrite dec_eq_true. eauto.
Qed.

Lemma identify_clos_order1:
  forall x y,
  clos_order identify_ufm y x ->
  clos_order uf.(m) y x \/ (clos_order (m uf) a x /\ clos_order (m uf) y b).
Proof.
  induction 1.
  - left. constructor.
  - destruct IHclos_refl_trans_n1.
    + eapply identify_order in H.
      destruct H.
      * left. econstructor; eauto.
      * destruct H. subst.
        right. split. constructor. auto.
    + destruct H1. right.
      split; auto.
      eapply identify_order in H.
      destruct H.
      * econstructor; eauto.
      * destruct H. subst. constructor.
Qed.

Lemma identify_clos_order2:
  forall x y,
  clos_order (m uf) y x ->
  clos_order identify_ufm y x.
Proof.
  induction 1.
  constructor.
  eapply clos_rt_rtn1. eapply rt_trans.
  eapply clos_rtn1_rt. eauto.
  econstructor. eapply identify_order. auto.
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
  rewrite !PTree.gsspec in G.
  destruct (peq x b).
  (* x = b *)
  - subst. unfold b_new in *.
    destruct (PTree.get b (m uf)) as [(c & b_cl) |] eqn: G1; inv G.
    + split.
      * red. intros x IN. red.
        destruct (peq x a).
        -- subst. rewrite !PTree.gsspec.
           rewrite dec_eq_false, dec_eq_true. eauto.
           apply a_not_eq_b.
        -- 
          apply Elts.add_3 in IN; auto.
           eapply (mcon uf)in IN; eauto. destruct IN as (x_cl & Gx).
           (* if x = b *)
           destruct (peq x b).
           ++ subst. rewrite G1 in Gx. inv Gx.
              rewrite !PTree.gsspec. rewrite dec_eq_true. unfold b_new. eauto.
           (* x <> b *)
           ++ rewrite !PTree.gsspec. rewrite !dec_eq_false. eauto. auto. auto.
      * destruct x_opt as [xb |]; auto.
        eapply (mcon uf) in G1 as G1'. destruct G1' as (A1 & (xb_par & xb_cl & G2 & G3)).
        destruct xb_par as [xb_par|].
        -- assert (ORD: order (m uf) xb_par xb).
           { red. eauto. }
           generalize (proj2 (identify_order xb xb_par) (or_introl ORD)). intros (cl' & ORD1).
           unfold identify_ufm, b_new in ORD1.
           rewrite G1 in ORD1. erewrite ORD1. do 2 eexists. split; eauto.
           rewrite !PTree.gsspec in ORD1.
           (* Adhoc *)
           destruct (peq xb b).
           ++ subst. inv ORD1. rewrite G1 in G2. inv G2.
              eapply Elts.add_2. auto.
           ++ destruct (peq xb a).
              ** subst. inv ORD1.
                 destruct a_canon as [(A4 & A2)| A3]; try congruence.
              ** setoid_rewrite G2 in ORD1. inv ORD1. auto.
        -- rewrite !PTree.gsspec.
           destruct (peq xb b).
           ++ subst. congruence.
           ++ destruct (peq xb a).
              ** subst. eapply repr_some in G1.
                 eapply repr_none2 in G2. congruence.
              ** eauto.
    + split; auto.
      red. intros x IN.
      destruct (elt_eq x a).
      * subst. red. rewrite !PTree.gsspec.
        rewrite dec_eq_false. rewrite dec_eq_true.
        eauto. apply a_not_eq_b.
      * eapply Elts.add_3 in IN; auto.
        exfalso. eapply Elts.empty_1. eauto.
  (* x <> b *)
  - destruct (elt_eq x a).
    (* x = a *)
    * subst. rewrite dec_eq_true in G. inv G.
      split. 
      -- red. intros y IN. red.
         destruct a_canon as [(A4 & A2)| A3]; try congruence.
         ++ subst. exfalso.
            eapply Elts.empty_1. eauto.
         ++ eapply (mcon uf) in A3 as (B1 & B2).
            eapply B1 in IN. red in IN.            
            destruct IN as (cl & G1).
            rewrite !PTree.gsspec.
            destruct (peq y b); subst; eauto.
            ** unfold b_new. rewrite G1. eauto.
            ** destruct (peq y a); subst; eauto.
               destruct a_canon as [(A4 & A2)| A3]; try congruence.
      -- rewrite PTree.gsspec. rewrite dec_eq_true.
         unfold b_new.
         destruct (PTree.get b (m uf)) as [(b_par & b_cl)| ] eqn: Gb.
         ++ do 2 eexists. split; eauto.
            eapply Elts.add_1. auto.
         ++ do 2 eexists. split; eauto.
            eapply Elts.add_1. auto.
    (* x <> a *)
    * rewrite dec_eq_false in G; auto.
      split.
      -- red. intros y IN. red.
         rewrite !PTree.gsspec.
         eapply (mcon uf) in G as (B1 & B2).
         eapply B1 in IN. red in IN.            
         destruct IN as (cl & G1).
         destruct (peq y b); subst; eauto.
         ++ unfold b_new. rewrite G1. eauto.
         ++ destruct (peq y a); subst; eauto.
            destruct a_canon as [(A4 & A2)| A3]; try congruence.
      -- eapply (mcon uf) in G as (B1 & B2).
         destruct x_opt as [x_par|]; auto.
         destruct B2 as (x_par_par & x_par_cl & C1 & C2).
         rewrite !PTree.gsspec. unfold b_new.
         destruct (peq x_par b).
         ++ subst. rewrite C1.
            do 2 eexists. split; eauto.
            eapply Elts.add_2. auto.
         ++ destruct (peq x_par a).
            ** subst. do 2 eexists. split; eauto.
               destruct a_canon as [(A4 & A2)| A3]; try congruence.
            ** do 2 eexists. split; eauto.
Qed.
         
         
Definition identify := mk identify_ufm identify_wf identify_consistent.
  
Lemma repr_identify_1:
  forall x, repr uf x <> a -> repr identify x = repr uf x.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in *.
  destruct (PTree.get x (m uf)) as [(a' & a_cl')|] eqn:X.
  - destruct a' as [a'|].
    + rewrite <- H; auto.
      destruct (peq x b).
      * subst.         
        eapply repr_some. simpl. unfold identify_ufm. rewrite PTree.gsspec.
        unfold b_new. rewrite X.
        rewrite dec_eq_true. eauto.
      * eapply repr_some. simpl. unfold identify_ufm. rewrite PTree.gsspec.
        rewrite dec_eq_false; auto.
        destruct (peq x a); try congruence.
        -- subst. destruct a_canon as [(A4 & A2)| A3]; try congruence.
        -- rewrite PTree.gsspec. rewrite dec_eq_false. eauto. auto.
      * red. eauto.
    + destruct (peq x b).
      * subst. 
        eapply repr_none2; eauto.      
        unfold identify, identify_ufm. simpl.
        unfold b_new. rewrite X. rewrite PTree.gsspec.
        rewrite dec_eq_true. eauto.
      * eapply repr_none2; eauto.
        unfold identify, identify_ufm. simpl.
        rewrite !PTree.gsspec.
        rewrite !dec_eq_false; eauto.
  - destruct (peq x b).
    * subst. 
      eapply repr_none2; eauto.
      unfold identify, identify_ufm. simpl.
      unfold b_new. rewrite X. rewrite PTree.gsspec.
      rewrite dec_eq_true. eauto.
    * eapply repr_none; eauto.
      unfold identify, identify_ufm. simpl.
      rewrite !PTree.gsspec.
      rewrite !dec_eq_false; eauto.
Qed.

Lemma repr_identify_2:
  forall x, repr uf x = a -> repr identify x = repr uf b.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in H0. destruct (PTree.get x (m uf)) as [(a' & a_cl')|] eqn:X.
  - destruct a' as [a'|].
    + exploit H. red. exists a_cl'. eapply X. auto.
      intros A. rewrite <- A. 
      destruct (peq x b). 
      * subst. eapply repr_some.
        unfold identify, identify_ufm, b_new. simpl.
        rewrite PTree.gsspec.
        rewrite dec_eq_true. rewrite X. eauto.
      * destruct (peq x a).
        -- subst. eapply repr_some_diff in X. congruence.
        -- eapply repr_some.
           unfold identify, identify_ufm, b_new. simpl.
           rewrite !PTree.gsspec.
           rewrite !dec_eq_false; auto. eauto.
    + subst.
      rewrite (repr_unroll identify).
      unfold identify, identify_ufm, b_new at 1. simpl.
      rewrite !PTree.gsspec. rewrite dec_eq_false. rewrite dec_eq_true.
      apply repr_identify_1. auto.
      apply a_not_eq_b.
  - subst. rewrite (repr_unroll identify).
      unfold identify, identify_ufm, b_new at 1. simpl.
      rewrite !PTree.gsspec. rewrite dec_eq_false. rewrite dec_eq_true.
      apply repr_identify_1. auto.
      apply a_not_eq_b.
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
  match peq a' b' with
  | left EQ' => uf
  | right NEQ =>
      match repr_res_none_dec uf a with
      | inright G1 => 
          identify uf a' b' Elts.empty (or_introl (conj G1 (eq_refl Elts.empty))) (union_not_same_class uf a b NEQ)
      | inleft (exist a'_cl G2) =>
          identify uf a' b' a'_cl (or_intror G2) (union_not_same_class uf a b NEQ)
      end          
  end.

Lemma repr_union_1:
  forall uf a b x, repr uf x <> repr uf a -> repr (union uf a b) x = repr uf x.
Proof.
  intros. unfold union. destruct (peq (repr uf a) (repr uf b)).
  auto.
  destruct (repr_res_none_dec uf a).
  - destruct s.
    apply repr_identify_1. auto.
  - apply repr_identify_1. auto.
Qed.

Lemma repr_union_2:
  forall uf a b x, repr uf x = repr uf a -> repr (union uf a b) x = repr uf b.
Proof.
  intros. unfold union. destruct (peq (repr uf a) (repr uf b)).
  congruence.
  destruct (repr_res_none_dec uf a).
  - destruct s.
    rewrite <- (repr_canonical uf b). apply repr_identify_2. auto.
  - rewrite <- (repr_canonical uf b). apply repr_identify_2. auto.
Qed.

Lemma repr_union_3:
  forall uf a b, repr (union uf a b) b = repr uf b.
Proof.
  intros. unfold union. destruct (peq (repr uf a) (repr uf b)).
  auto. destruct (repr_res_none_dec uf a).
  - destruct s.
    apply repr_identify_1. auto.
  - apply repr_identify_1. auto.
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
  destruct (peq (repr uf x) (repr uf a));
  destruct (peq (repr uf y) (repr uf a)).
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
  destruct (peq (repr uf x) (repr uf a));
  destruct (peq (repr uf y) (repr uf a)).
  intro. left. congruence.
  rewrite repr_union_2; auto. rewrite repr_union_1; auto.
  rewrite repr_union_1; auto. rewrite repr_union_2; auto.
  repeat rewrite repr_union_1; auto.
Qed.


(* Merge *)

Definition merge (uf: t) (a b: elt) : t :=
  let a' := repr uf a in
  let b' := repr uf b in
  match peq a' b' with
  | left EQ' => uf
  | right NEQ =>
      match repr_res_none_dec uf a with
      | inright G1 => 
          identify uf a' b Elts.empty (or_introl (conj G1 (eq_refl Elts.empty))) (not_eq_sym NEQ)
      | inleft (exist a'_cl G2) =>
          identify uf a' b a'_cl (or_intror G2) (not_eq_sym NEQ)
      end          
  end.

Lemma repr_merge:
  forall uf a b x, repr (merge uf a b) x = repr (union uf a b) x.
Proof.
  intros. unfold merge, union. destruct (peq (repr uf a) (repr uf b)).
  auto.
  destruct (repr_res_none_dec uf a) .
  - destruct (peq (repr uf x) (repr uf a)).
    + destruct s.
      repeat rewrite repr_identify_2; auto. rewrite repr_canonical; auto.
    + destruct s. repeat rewrite repr_identify_1; auto.
  - destruct (peq (repr uf x) (repr uf a)).
    + repeat rewrite repr_identify_2; auto. rewrite repr_canonical; auto.
    + repeat rewrite repr_identify_1; auto.
Qed.

Lemma sameclass_merge:
  forall uf a b x y, sameclass (merge uf a b) x y <-> sameclass (union uf a b) x y.
Proof.
  unfold sameclass; intros. repeat rewrite repr_merge. tauto.
Qed.

Lemma merge_clos_order1: forall uf a b x y,
    clos_order (m uf) y x ->
    clos_order (m (merge uf a b)) y x.
Proof.
  intros. unfold merge.
  destruct peq; auto.
  destruct repr_res_none_dec.
  destruct s. eapply identify_clos_order2; eauto.
  eapply identify_clos_order2; eauto.
Qed.


(** Cut operation used in deletion *)

Section CUT_EDGE.

Variable uf: t.
Variables a b: elt.
Variable a_cl : Elts.t.           (* children of a *)
Hypothesis a_edge: PTree.get a (m uf) = Some (Some b, a_cl).
Hypothesis a_not_eq_b: a <> b.

Definition b_cut :=
  match PTree.get b uf.(m) with
  | Some (c, b_cl) =>
      (c, Elts.remove a b_cl)
  | None =>
      (* Impossible *)
      (None, Elts.empty)
  end.

Definition cut_ufm := PTree.set b b_cut (PTree.set a (None, a_cl) (m uf)).

Lemma cut_ufm_order: forall x y,
    order (m uf) y x <->
    order cut_ufm y x \/ (order (m uf) b a /\ x = a /\ y = b).
Proof.
  intros x y. split.
  - intros A. red in A. destruct A as (x_cl & A).
    unfold cut_ufm, b_cut. simpl.
    exploit (mcon uf). eapply a_edge. intros (A1 & (c & b_cl & A2 & A3)).
    rewrite A2.
    destruct (peq x a).
    ** subst. right.
       rewrite A in a_edge. inv a_edge.
       repeat apply conj; auto.
       red. eauto.
    ** left. red.
       rewrite !PTree.gsspec.
       destruct peq; subst.
       --- rewrite A in A2. inv A2. eauto.
       --- rewrite dec_eq_false; eauto.
  - intros [A|(A1 & A2 & A3)].
    + red in A. destruct A as (x_cl & A).
      unfold cut_ufm, b_cut in A. simpl in A.
      exploit (mcon uf). eapply a_edge. intros (A1 & (c & b_cl & A2 & A3)).
      rewrite A2 in A.
      destruct (peq x a).
      --- subst. rewrite !PTree.gsspec in A.
          destruct peq; subst.
          +++ congruence.
          +++ rewrite dec_eq_true in A. inv A.
      --- rewrite !PTree.gsspec in A.
          destruct peq; subst.
          +++ inv A. red. eauto.
          +++ rewrite dec_eq_false in A; eauto.
              red. eauto.
    + subst. auto.
Qed.


Remark cut_ufm_Acc:
  forall x,
  Acc (order uf.(m)) x -> Acc (order cut_ufm) x.
Proof.
  induction 1. constructor; intros.
  eapply H0. eapply cut_ufm_order. eauto.
Qed.

Lemma cut_ufm_well_founded:
  well_founded (order cut_ufm).
Proof.
  red; intros. apply cut_ufm_Acc. apply uf.(mwf).
Qed.

Lemma cut_ufm_consistent:
  consistent cut_ufm.
Proof.
  red. intros x y x_cl Gx.
  exploit (mcon uf). eapply a_edge.
  intros (A1 & (b_par & b_cl & A2 & A3)).
  split.
  - red. intros z IN. red.
    unfold cut_ufm, b_cut in *. rewrite A2 in *.
    rewrite !PTree.gsspec in *.
    destruct (peq x b).
    + subst. inv Gx.
      destruct peq.
      * subst. exfalso.
        eapply Elts.remove_3 in IN.
        exploit (mcon uf). eapply A2. intros (B1 & B2).
        eapply B1 in IN. destruct IN as (b_cl' & Gb).
        eapply repr_some_neq; eauto.
      * destruct peq.
        -- subst. exfalso. eapply Elts.remove_1; eauto.
        -- eapply (mcon uf); eauto.
           eapply Elts.remove_3. eauto.
    + destruct (peq x a).
      * inv Gx. destruct peq.
        -- subst. eapply A1 in IN as (b_cl' & Gb).
           rewrite A2 in Gb. inv Gb. eauto.
        -- destruct peq.
           ++ subst. eapply A1 in IN as (a_cl' & Ga).
              exfalso. eapply repr_some_neq; eauto.
           ++ eapply (mcon uf); eauto.
      * destruct peq.
        -- subst. exploit (mcon uf). eapply Gx. intros (B1 & B2).
           eapply B1 in IN. destruct IN as (b_cl' & Gb).
           rewrite A2 in Gb. inv Gb. eauto.
        -- destruct peq.
           ++ subst. eapply (mcon uf) in IN. 2: eauto.
              destruct IN as (a_cl' & Ga). rewrite a_edge in Ga.
              inv Ga. congruence.
           ++ eapply (mcon uf); eauto.
  - destruct y as [y|]; auto.
    unfold cut_ufm, b_cut in *. rewrite A2 in *.
    rewrite !PTree.gsspec in *.
    destruct (peq x b).
    + inv Gx. destruct peq.
      * subst. exfalso. eapply repr_some_neq; eauto.
      * destruct peq.
        -- subst. exfalso. eapply n.
           eapply clos_order_antisym.
           econstructor. red. eauto. constructor.
           econstructor. red. eauto. constructor.
        -- eapply (mcon uf) in A2 as (B1 & B2). eauto.
    + destruct (peq x a).
      * inv Gx.
      * destruct peq.
        -- subst.
           eapply (mcon uf) in Gx as (B1 & (b' & b_cl' & B2 & B3)).
           rewrite A2 in B2. inv B2. do 2 eexists. split; eauto.
           eapply Elts.remove_2; eauto.
        -- destruct peq.
           ++ eapply (mcon uf) in Gx as (B1 & (b' & b_cl' & B2 & B3)).
              subst. do 2 eexists. split; eauto.
              rewrite a_edge in B2. inv B2. auto.
           ++ eapply (mcon uf) in Gx as (B1 & (b' & b_cl' & B2 & B3)).
              eauto.
Qed.
              
Definition cut' : t := mk cut_ufm cut_ufm_well_founded cut_ufm_consistent.

End CUT_EDGE.

Remark not_eq_trans {A: Type} : forall (a b c: A),
    a <> b -> b = c -> a <> c.
Proof. intros. subst. auto. Defined.

Section CUT.

Variable uf: t.
Variables a b: elt.

(* cut the edge from a to b *)
Definition cut : t :=
  match peq a b with
  (* a is equal to b *)
  | left EQ_ab => uf
  | right NEQ_ab =>
      match get_elt_dec (m uf) a with
      | inleft (exist (Some b', a_cl) Ga) =>          
          match peq b b' with
          | left EQ_bb' =>
              cut' uf a b' a_cl Ga (not_eq_trans a b b' NEQ_ab EQ_bb')
          (* a dose not point to b *)
          | right NEQ => uf
          end
      (* a is the root *)
      | inleft (exist (None, a_cl) _) => uf
      (* a is the root *)
      | inright _ => uf
      end
  end.

Lemma cut_a_root: forall a_cl,
  PTree.get a (m uf) = Some (Some b, a_cl) ->
  PTree.get a (m cut) = Some (None, a_cl).
Proof.
  intros a_cl Ga. unfold cut.
  destruct (peq a b).
  - exfalso. subst. eapply repr_some_neq; eauto.
  - destruct get_elt_dec.
    + destruct s. destruct x. rewrite e in Ga. inv Ga.      
      destruct peq; try congruence.
      unfold cut', cut_ufm. simpl.
      rewrite !PTree.gsspec.
      rewrite dec_eq_false, dec_eq_true; auto.
    + congruence.
Qed.


Lemma cut_b_result: forall c b_cl, 
  PTree.get b (m uf) = Some (c, b_cl) ->
  exists b_cl', PTree.get b (m cut) = Some (c, b_cl') /\ Elts.eq b_cl' (Elts.remove a b_cl).
Proof.
  intros c b_cl Gb.
  unfold cut.
  destruct (peq a b).
  - subst. exists b_cl.
    split; auto.
    exploit (mcon uf). eapply Gb. intros (A1 & A2).    
    repeat red. intros. split.
    + intros. eapply Elts.remove_2; auto.
      eapply A1 in H. destruct H as (a_cl & Ga).
      eapply not_eq_sym.
      eapply repr_some_neq. eauto.
    + intros. eapply Elts.remove_3. eauto.
  - destruct get_elt_dec.
    + destruct s as (v & Ga).
      destruct v as (a_par & a_cl).
      destruct a_par as [a_par|].
      * destruct peq.
        -- subst. unfold cut', cut_ufm, b_cut. simpl.
           rewrite PTree.gsspec. rewrite dec_eq_true.
           rewrite Gb. exists (Elts.remove a b_cl). split; auto.
           reflexivity.
        -- exists b_cl. split; auto.
           exploit (mcon uf). eapply Gb. intros (A1 & A2).
           repeat red. intros. split.
           ++ intros. eapply Elts.remove_2; auto.
              intro. subst. 
              eapply A1 in H. destruct H as (a0_cl & Ga0).
              rewrite Ga in Ga0. inv Ga0. congruence.
           ++ intros. eapply Elts.remove_3. eauto.
      * exists b_cl. split; auto.
        exploit (mcon uf). eapply Gb. intros (A1 & A2).
        repeat red. intros. split.
        -- intros. eapply Elts.remove_2; auto.
           intro. subst.
           eapply A1 in H. destruct H as (a0_cl & Ga0).
           rewrite Ga in Ga0. inv Ga0.
        -- intros. eapply Elts.remove_3. eauto.
    + exists b_cl. split; auto.
        exploit (mcon uf). eapply Gb. intros (A1 & A2).
        repeat red. intros. split.
        -- intros. eapply Elts.remove_2; auto.
           intro. subst.
           eapply A1 in H. destruct H as (a0_cl & Ga0).
           rewrite e in Ga0. inv Ga0.
        -- intros. eapply Elts.remove_3. eauto.
Qed.           
          
Lemma cut_order: forall x y,
    order (m uf) y x <->
    order (m cut) y x \/ (order (m uf) b a /\ x = a /\ y = b).
Proof.
  intros x y. split.
  - intros A. red in A. destruct A as (x_cl & A).
    unfold cut. destruct (peq a b).
    + subst. left. red. eauto.
    + destruct get_elt_dec.
      * destruct s as ((ob & a_cl) & Ga).
        destruct ob as [b'| ].
        -- destruct peq.
           ++ subst.
              eapply cut_ufm_order; eauto.
              red. eauto.
           ++ left. red. eauto.
        -- left. red. eauto.
      * left. red. eauto.
  - intros [A|(A1 & A2 & A3)].
    + red in A. destruct A as (x_cl & A).
      unfold cut in A. red. destruct (peq a b).
      * subst. eauto.
      * destruct get_elt_dec.
        -- destruct s as ((ob & a_cl) & Ga).
           destruct ob as [b'| ].
           ++ destruct peq.
              ** subst.
                 eapply cut_ufm_order; eauto. left. red. eauto.
              ** eauto.
           ++ eauto.
        -- eauto.
    + subst. auto.
Qed.

Lemma cut_clos_order1: forall x y,
    clos_order (m uf) y x ->
    clos_order (m cut) y x
    \/ (order (m uf) b a /\ clos_order (m cut) a x /\ clos_order (m cut) y b).
Proof.
  induction 1. left. constructor.
  destruct IHclos_refl_trans_n1.
  - eapply cut_order in H as [A1| (A2 & A3 & A4)].
    + left. eapply clos_rt_rtn1. eapply rt_trans.
      eapply clos_rtn1_rt. eauto.
      econstructor. auto.
    + subst. right. repeat apply conj; auto.
      constructor.
  - destruct H1 as (A1 & A2 & A3).
    eapply cut_order in H as [B1| (B2 & B3 & B4)].
    + right. repeat apply conj; auto.
      econstructor; eauto.
    + subst. right. repeat apply conj; auto.
      constructor.
Qed.

Lemma cut_clos_order2: forall x y,
    clos_order (m cut) y x ->
    clos_order (m uf) y x.
Proof.
  induction 1. constructor.
  econstructor. eapply cut_order. eauto. auto.
Qed.  

Lemma cut_clos_order3: forall x y,
    order (m uf) b a ->
    clos_order (m cut) a x ->
    clos_order (m cut) y b ->
    clos_order (m uf) y x.
Proof.
  intros. eapply clos_rt_rtn1. eapply rt_trans.
  eapply clos_rtn1_rt. eapply cut_clos_order2. eauto.
  eapply rt_trans. econstructor. eauto.
  eapply clos_rtn1_rt. eapply cut_clos_order2. eauto.
Qed.
  
Lemma cut_disjoint: forall x,
    order (m uf) b a ->
    clos_order (m uf) a x -> repr cut x = a.
Proof.
  intros x (a_cl & Ga).
  assert (NEQab: a <> b).
  { eapply repr_some_neq. eauto. }
  induction 1.
  - unfold cut.
    destruct peq; try congruence.
    destruct get_elt_dec.
    + destruct s as ((c & a_cl') & Ga'). destruct c as [c|].
      * destruct peq.
        -- subst. unfold cut', cut_ufm, b_cut. simpl.
           rewrite repr_unroll. simpl. rewrite !PTree.gsspec.
           rewrite dec_eq_false, dec_eq_true; auto.
        -- rewrite Ga in Ga'. inv Ga'. congruence.
      * congruence.
    + eapply repr_none. auto.
  - destruct H as (z_cl & Gz).
    assert (ORDyz: order (m uf) y z).
    { red. eauto. }
    eapply cut_order in ORDyz as [A|(A1 & A2 & A3)].
    + destruct A as (y_cl & Gy).
      erewrite repr_some. 2: eauto. auto.
    + subst.
      exfalso. eapply NEQab. eapply clos_order_antisym. eauto.
      econstructor. eauto. constructor.
Qed.

Lemma cut_get_not_a: forall x y x_cl,
    x <> a ->
    PTree.get x (m uf) = Some (y, x_cl) ->
    exists x_cl', PTree.get x (m cut) = Some (y, x_cl').
Proof.
  intros x y x_cl NEQ Gx.
  unfold cut. destruct peq.
  - subst. eauto.
  - destruct get_elt_dec.
    + destruct s as ((c & a_cl') & Ga'). destruct c as [c|].
      * exploit (mcon uf). eauto.
        intros (A1 & (c_par & c_cl & A2 & A3)).
        destruct peq.
        -- subst. unfold cut', cut_ufm, b_cut. simpl.
           rewrite A2. rewrite !PTree.gsspec.
           destruct peq.
           ++ subst. rewrite Gx in A2. inv A2. eauto.
           ++ rewrite dec_eq_false; eauto.
        -- eauto.
      * eauto.
    + eauto.
Qed.

Lemma cut_get_none: forall x,
    PTree.get x (m uf) = None ->
    PTree.get x (m cut) = None.
Proof.
  intros x Gx.
  unfold cut. destruct peq.
  - subst. eauto.
  - destruct get_elt_dec.
    + destruct s as ((c & a_cl') & Ga'). destruct c as [c|].
      * exploit (mcon uf). eauto.
        intros (A1 & (c_par & c_cl & A2 & A3)).
        destruct peq.
        -- subst. unfold cut', cut_ufm, b_cut. simpl.
           rewrite A2. rewrite !PTree.gsspec.
           destruct peq.
           ++ subst. rewrite Gx in A2. inv A2. 
           ++ rewrite dec_eq_false; eauto. intro. subst. congruence.
        -- eauto.
      * eauto.
    + eauto.
Qed.


Lemma cut_unchanged: forall x,
    ~ clos_order (m uf) a x -> repr cut x = repr uf x.
Proof.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in *.
  destruct (PTree.get x (m uf)) eqn: Gx.
  - destruct v as (c & x_cl).
    exploit cut_get_not_a. 2: eauto.
    intro. subst. eapply H0. constructor.
    intros (x_cl' & Gx').
    destruct c as [c|].
    + erewrite <- H.
      * eapply repr_some. eauto.
      * red. eauto.
      * intro. eapply H0.
        econstructor. red. eauto. auto.
    + eapply repr_none2. eauto.
  - eapply repr_none. eapply cut_get_none. auto.
Qed.        


(* cut operation does not change the path from the children except for
a of b *)
Lemma cut_local: forall x,
    clos_order (m uf) b x ->
    ~ clos_order (m uf) a x ->
    clos_order (m cut) b x.
Proof.
  intros x R1 R2. eapply cut_clos_order1 in R1.
  destruct R1 as [R1 | (A1 & A2 & A3)]; auto.
  exfalso. eapply R2.
  eapply cut_clos_order2. auto.
Qed.  

Lemma cut_same:
  ~ order (m uf) b a ->
  cut = uf.
Proof.
  intros N.
  unfold cut. destruct peq; auto.
  destruct get_elt_dec; auto.
  destruct s as ((c & a_cl') & Ga'). destruct c as [c|]; auto.
  destruct peq; auto.
  subst. exfalso. apply N. red. eauto.
Qed.

End CUT.

(** Link the children of the deleted node to a new node *)

Section LINK.
  
Variable uf : t.
Variable r b: elt.
Variable b_cl : Elts.t.

(* For simplicity: we utilize merge instead of identify which requires
lots of proof effort *)
Fixpoint link_children_acc (cl: list elt) (acc: t) :=
  match cl with
  | nil => acc
  | y :: cl' =>
      let acc1 := cut acc y b in
      let acc2 := merge acc1 y r in
      link_children_acc cl' acc2
  end.

Definition link_children : t := link_children_acc (Elts.elements b_cl) uf.

End LINK.

Lemma get_merge_cut: forall uf a b c r b_cl,
    order (m uf) b a ->
    PTree.get b (m uf) = Some (c, b_cl) ->
    a <> b ->
    b <> r ->
    exists b_cl', PTree.get b (m (merge (cut uf a b) a r)) = Some (c, b_cl')
             /\ Elts.eq b_cl' (Elts.remove a b_cl).
Proof. 
  intros.
  unfold merge. destruct peq.
  (* properties of cut: PTree.get b (m (cut uf a b)) = Some (None, Elts.remove a b_cl) *)
  eapply cut_b_result; eauto.
  destruct repr_res_none_dec. destruct s.
  + unfold identify, identify_ufm. simpl.
    erewrite cut_disjoint; auto. rewrite !PTree.gsspec. rewrite !dec_eq_false; auto.
    (* properties of cut *)
    eapply cut_b_result; eauto.
    constructor.
  + unfold identify, identify_ufm. simpl.
    erewrite cut_disjoint; auto. rewrite !PTree.gsspec. rewrite !dec_eq_false; auto.
    (* properties of cut *)
    eapply cut_b_result; eauto.
    constructor.
Qed.


Lemma merge_cut_clos_order: forall uf a b x r,
    ~ clos_order (m uf) b r ->
    clos_order (m (merge (cut uf a b) a r)) b x ->
    a <> b ->
    (* b <> r -> *)
    clos_order (m uf) b x.
Proof.
  intros until r. intros NBR BX NAB.
  unfold merge in BX. destruct peq in BX.
  - eapply cut_clos_order2. eauto.
  - destruct repr_res_none_dec in BX.
    + destruct s as (a_cl & G).
      assert (A1: clos_order (m (cut uf a b)) b x).
      { exploit identify_clos_order1; eauto. intros [A|(B & C)]; auto.
        (* how to show C is impossible *)
        exfalso. eapply NBR. eapply cut_clos_order2. eauto. }
      eapply cut_clos_order2. eauto.
    + assert (A1: clos_order (m (cut uf a b)) b x).
      { exploit identify_clos_order1; eauto. intros [A|(B & C)]; auto.
        exfalso. eapply NBR. eapply cut_clos_order2. eauto. }
      eapply cut_clos_order2. eauto.
Qed.      

Lemma merge_cut_inductive_hyp: forall uf a b r b_cl cl
    (Gb : PTree.get b (m uf) = Some (None, b_cl))
    (NEQ : repr uf r <> b)
    (EQV : forall y : Elts.elt, InA eq y (a :: cl) <-> Elts.In y b_cl)
    (RNIN : ~ Elts.In r b_cl)
    (NODUP : NoDupA eq (a :: cl))
    (NEQab : a <> b)
    (NEQbr : b <> r),
  exists b_cl',
    PTree.get b (m (merge (cut uf a b) a r)) = Some (None, b_cl')
    /\ Elts.eq b_cl' (Elts.remove a b_cl)
    /\ repr (merge (cut uf a b) a r) r <> b
    /\ (forall y : Elts.elt, InA eq y cl <-> Elts.In y b_cl')
    /\ ~ Elts.In r b_cl'
    /\ NoDupA eq cl.
Proof.
  intros.
  exploit get_merge_cut; eauto.
  eapply (mcon uf). eauto. eapply EQV. constructor. auto.
  intros (b_cl' & Gb' & EQ).
  exists b_cl'.
  repeat apply conj; auto.
  - rewrite repr_merge. rewrite repr_union_3.
    rewrite cut_unchanged. auto.
    (* ~ r ->* a *)
    intro C. eapply repr_clos_order in C. rewrite <- C in NEQ.
    eapply NEQ.
    generalize (mcon uf _ _ _ Gb). intros (A1 & A2).
    exploit A1.
    eapply EQV. econstructor. eauto.
    intros (a_cl & B).
    erewrite repr_some. eapply repr_none2. eauto. eauto.
  - intros. inv NODUP. split. 
    + intros IN. eapply EQ. eapply Elts.remove_2. intro. subst. contradiction.
      eapply EQV. eapply InA_cons. eauto.
    + intros IN.
      destruct (elt_eq y a). subst. exfalso.
      eapply Elts.remove_1; eauto. eapply EQ. auto.
      eapply EQ in IN. eapply Elts.remove_3 in IN. eapply EQV in IN.
      inv IN; congruence.
  - intro. eapply RNIN.
    eapply EQ in H. eapply Elts.remove_3. eauto.
  - inv NODUP. auto.
Qed.
    
Lemma repr_link_children_isolate_aux: forall cl uf r b b_cl
    (Gb: PTree.get b (m uf) = Some (None, b_cl))
    (NEQ: repr uf r <> b)
    (EQV: forall y, InA eq y cl <-> Elts.In y b_cl)
    (RNIN: ~ Elts.In r b_cl)
    (NODUP: NoDupA eq cl),
    repr (link_children_acc r b cl uf) b = b.
Proof.
  induction cl; intros; simpl.
  eapply repr_none2. eauto.
  assert (NEQab: a <> b).
  { generalize (mcon uf _ _ _ Gb). intros (A1 & A2).
    exploit A1.
    eapply EQV. econstructor. eauto.
    intros (a_cl & B).
    intro. subst. eapply repr_some_neq. eauto. auto. }
    assert (NEQbr: b <> r).
  { intro. subst. eapply NEQ. eapply repr_none2. eauto. }
  exploit merge_cut_inductive_hyp. 1-7: eauto.
  intros (b_cl' & A1 & A2 & A3 & A4 & A5 & A6).
  eapply IHcl with (b_cl := b_cl'); eauto.
Qed.

Lemma repr_link_children_unchanged_aux: forall cl uf r b b_cl x
    (Gb: PTree.get b (m uf) = Some (None, b_cl))
    (NEQ: repr uf r <> b)
    (EQV: forall y, InA eq y cl <-> Elts.In y b_cl)
    (RNIN: ~ Elts.In r b_cl)
    (NODUP: NoDupA eq cl)
    (UNREACH: ~ clos_order (m uf) b x),
    repr (link_children_acc r b cl uf) x = repr uf x.
Proof.
  induction cl; intros; simpl. auto.
  assert (NEQab: a <> b).
  { generalize (mcon uf _ _ _ Gb). intros (A1 & A2).
    exploit A1.
    eapply EQV. econstructor. eauto.
    intros (a_cl & B).
    intro. subst. eapply repr_some_neq. eauto. auto. }
    assert (NEQbr: b <> r).
  { intro. subst. eapply NEQ. eapply repr_none2. eauto. }
  assert (ORDba: order (m uf) b a).
  { eapply (mcon uf). eauto. eapply EQV. constructor. auto. }
  exploit merge_cut_inductive_hyp. 1-7: eauto.
  intros (b_cl' & A1 & A2 & A3 & A4 & A5 & A6).
  erewrite IHcl with (b_cl := b_cl'). 2-6: eauto.
  - assert (UNR1: ~ clos_order (m uf) a x).
    { intro. eapply UNREACH.
      eapply clos_rt_rtn1. eapply rt_trans.
      2: { eapply clos_rtn1_rt. eauto. }
      econstructor. eapply (mcon uf). eauto.
      eapply EQV. constructor. auto. }
    rewrite repr_merge. erewrite repr_union_1.
    + rewrite cut_unchanged; auto.       
    + rewrite cut_unchanged; auto.
      rewrite cut_disjoint; auto. 2: constructor.
      eapply (mcon uf) in Gb as (B1 & B2).
      exploit B1. eapply EQV. constructor. eauto.
      intros (a_cl & B). 
      intro. destruct (repr_res_none uf x) as [|(cl' & C)]; try congruence.
  (* ~ clos_order (m (merge (cut uf a b) a r)) b x *)
  - intro. eapply UNREACH.
    eapply merge_cut_clos_order. 2: eauto.
    intro. eapply NEQ. erewrite <- repr_clos_order. eapply repr_none2. eauto. auto.
    auto.
Qed.    

Lemma repr_link_children_relink_aux: forall cl uf r b b_cl x
    (Gb: PTree.get b (m uf) = Some (None, b_cl))
    (NEQ: repr uf r <> b)
    (EQV: forall y, InA eq y cl <-> Elts.In y b_cl)
    (RNIN: ~ Elts.In r b_cl)
    (NODUP: NoDupA eq cl)
    (NEQbx: b <> x)
    (REACH: clos_order (m uf) b x),
    repr (link_children_acc r b cl uf) x = repr uf r.
Proof.
  induction cl; intros; simpl.
  eapply clos_rtn1_rt in REACH. eapply clos_rt_rt1n in REACH.
  inv REACH. congruence.
  red in H. destruct H as (y_cl & Gy).
  eapply (mcon uf) in Gy as (A1 & (b' & b_cl' & A2 & A3)).
  rewrite Gb in A2. inv A2.
  exfalso. eapply Elts.empty_1. eapply EQV. eauto.
  (* inductive case *)
  assert (NEQab: a <> b).
  { generalize (mcon uf _ _ _ Gb). intros (A1 & A2).
    exploit A1.
    eapply EQV. econstructor. eauto.
    intros (a_cl & B).
    intro. subst. eapply repr_some_neq. eauto. auto. }
    assert (NEQbr: b <> r).
  { intro. subst. eapply NEQ. eapply repr_none2. eauto. }
  destruct (clos_order_dec (merge (cut uf a b) a r) b x).
  - exploit merge_cut_inductive_hyp. 1-7: eauto.
    intros (b_cl' & A1 & A2 & A3 & A4 & A5 & A6).
    erewrite IHcl with (b_cl := b_cl'). 2-8: eauto.        
    + exploit (mcon uf). eauto. intros (B1 & B2).
      exploit B1. eapply EQV. constructor. eauto.
      intros (a_cl & Ga).
      assert (UNR1: ~ clos_order (m uf) a r).
      { intro. eapply NEQ.
        erewrite <- repr_clos_order. 2: eauto.
        erewrite repr_some. eapply repr_none2. eauto.
        eauto. }
      rewrite repr_merge. erewrite repr_union_3.
      rewrite cut_unchanged. auto. auto.
  (* if ~ x ->* b in (merge (cut uf a b) a r) then (x -> * r) *)
  - exploit merge_cut_inductive_hyp. 1-7: eauto.
    intros (b_cl' & A1 & A2 & A3 & A4 & A5 & A6).    
    erewrite repr_link_children_unchanged_aux. 2-7: eauto.
    exploit (mcon uf). eauto. intros (C1 & C2).
    exploit C1. eapply EQV. constructor. eauto.
    intros (a_cl & Ga).
    assert (UNR1: ~ clos_order (m uf) a r).
    { intro. eapply NEQ.
      erewrite <- repr_clos_order. 2: eauto.
      erewrite repr_some. eapply repr_none2. eauto.
      eauto. }
    exploit (cut_clos_order1 uf a b x b). eapply REACH.
    intros [A|(B1 & B2 & B3)].
    + eapply merge_clos_order1 with (a:=a) (b:=r) in A. congruence.
    + rewrite repr_merge. erewrite repr_union_2.
      rewrite cut_unchanged; auto.
      rewrite !cut_disjoint; auto. constructor.
      eapply cut_clos_order2. eauto.
Qed.


Section LINK_PROOF.

Variable uf : t.
Variable r b: elt.
Variable b_cl : Elts.t.

Hypothesis get_b: PTree.get b (m uf) = Some (None, b_cl).
Hypothesis r_not_eq_b: repr uf r <> b.
Hypothesis r_not_in_cl: ~ Elts.In r b_cl.

Lemma b_children_repr_diff: forall c,
    Elts.In c b_cl -> c <> r.
Proof.
  intros. intro. subst. contradiction.
Qed.

Lemma repr_link_children_isolate: forall b_cl',
    Elts.eq b_cl' b_cl ->
    repr (link_children uf r b b_cl') b = b.
Proof.
  intros b_cl' EQ.
  unfold link_children.
  eapply repr_link_children_isolate_aux; eauto.
  eapply Elts.elements_3w.
  (* intros. split; intros. *)
  (* eapply Elts.elements_2; eauto. *)
  (* eapply Elts.elements_1; eauto. *)
  (* eapply Elts.elements_3w. *)
Qed.

      
Lemma repr_link_children_unchanged: forall x b_cl',
    Elts.eq b_cl' b_cl ->
    ~ clos_order (m uf) b x ->
    repr (link_children uf r b b_cl') x = repr uf x.
Proof.
  intros x b_cl' EQ R. unfold link_children.
  eapply repr_link_children_unchanged_aux; eauto.
  eapply Elts.elements_3w.
  (* intros. split; intros.   *)
  (* eapply Elts.elements_2; eauto. *)
  (* eapply Elts.elements_1; eauto. *)
  (* eapply Elts.elements_3w. *)
Qed.

Lemma repr_link_children_relink: forall x b_cl',
    Elts.eq b_cl' b_cl ->
    x <> b ->
    clos_order (m uf) b x ->
    repr (link_children uf r b b_cl') x = repr uf r.
Proof.
  intros x b_cl' EQ NEQ R. unfold link_children.
  eapply repr_link_children_relink_aux; eauto.
  eapply Elts.elements_3w.
  (* intros. split; intros. *)
  (* eapply Elts.elements_2; eauto. *)
  (* eapply Elts.elements_1; eauto. *)
  (* eapply Elts.elements_3w. *)
Qed.  

End LINK_PROOF.

(** Delete operation: it returns the new union-find and the new root if it is changed *)

Definition delete (uf: t) (a: elt) : t * option elt :=
  match PTree.get a (m uf) with
  | Some (Some r, a_cl) =>
      let uf1 := cut uf a r in (* cut a -> r *)
      (link_children uf1 r a a_cl, None)
  | Some (None, a_cl) =>         (* a is a root with children *)
      match Elts.choose a_cl with
      | None => (uf, None)
      | Some r =>
          let uf1 := cut uf r a in (* cut r -> a *)
          (* link the remain chidlren of a to the new root. *)
          (link_children uf1 r a (Elts.remove r a_cl), Some r)
      end
  | None =>                      (* a is a root without children, do nothing *)
      (uf, None)
  end.

Lemma delete_repr: forall uf a, repr (fst (delete uf a)) a = a.
Proof.
  intros. unfold delete.
  destruct (PTree.get a (m uf)) as [(r & a_cl) |] eqn: G.
  - destruct r as [r |].
    + simpl.
      erewrite repr_link_children_isolate. auto.
      (* premise of link_children *)
      * exploit cut_a_root. eauto. eauto.
      * rewrite cut_unchanged.
        eapply not_eq_sym.
        eapply repr_some_diff. eauto.
        intro A. eapply repr_some_neq. eauto.
        eapply clos_order_antisym. eauto.
        econstructor. red. eauto. constructor.
      * intro A.
        exploit (mcon uf). eauto. intros (A1 & (b & r_cl & A2 & A3)).
        eapply A1 in A. destruct A as (r_cl' & A4). rewrite A4 in A2. inv A2.
        eapply repr_some_neq. eauto.
        eapply clos_order_antisym.
        econstructor. red. eauto. constructor.
        econstructor. red. eauto. constructor.
      * reflexivity.
    + destruct (Elts.choose a_cl) as [r|] eqn: C.
      * simpl.
        assert (ORDra: order (m uf) a r).
        { eapply (mcon uf). eauto. eapply Elts.choose_1. auto. }
        exploit (cut_b_result uf r a). eauto.
        intros (a_cl' & Ga & EQ).        
        erewrite repr_link_children_isolate; eauto. 
        (* premise of link_children *)
      -- assert (NEQra: r <> a).
         { erewrite <- (repr_none2 uf a _); eauto.
           exploit (mcon uf). eauto. intros (A1 & A2).
           eapply Elts.choose_1 in C.
           eapply A1 in C. destruct C as (r_cl' & A4). 
           eapply repr_some_diff. eauto. }
         rewrite cut_disjoint; auto.
         constructor.
      -- intro. eapply EQ in H. eapply Elts.remove_1; eauto.
      -- symmetry. auto.
      * eapply repr_none2. eauto.
  - apply repr_none. auto.
Qed.


Lemma delete_repr_unchanged1: forall uf b x,
    repr uf b <> repr uf x ->
    repr (fst (delete uf b)) x = repr uf x.
Proof.
  intros uf b x R.
  unfold delete. destruct (PTree.get b (m uf)) eqn: Gb.
  - destruct v as (y & b_cl). destruct y as [y|].
    + simpl. erewrite repr_link_children_unchanged.
      * rewrite cut_unchanged. auto.
        intro. eapply R. eapply repr_clos_order. auto.
      * exploit cut_a_root. eauto. eauto. 
      * rewrite cut_unchanged.
        -- intro. eapply repr_some_diff. eauto. auto.
        -- intro. eapply repr_some_neq. eauto.
           eapply clos_order_antisym. eauto.
           econstructor. red. eauto. constructor.
      * intro. eapply repr_some_neq. eauto.
        eapply clos_order_antisym.
        2: { econstructor. red. eauto. constructor. }
        eapply (mcon uf) in Gb as (A1 & A2). eapply A1 in H as (cl & B).
        econstructor. red. eauto. constructor.
      * reflexivity.
      * intro. eapply R. eapply repr_clos_order. eapply cut_clos_order2. eauto.
    + destruct (Elts.choose b_cl) eqn: C; auto.
      assert (ORDbe: order (m uf) b e).
        { eapply (mcon uf). eauto. eapply Elts.choose_1. auto. }
      exploit (cut_b_result uf e b). eauto.
      intros (b_cl' & Gb' & EQ).
      simpl. erewrite repr_link_children_unchanged.
      * rewrite cut_unchanged. auto.
        intro. eapply R. eapply repr_clos_order.
        exploit (mcon uf). eapply Gb. intros (A1 & A2).
        eapply Elts.choose_1 in C. eapply A1 in C as (e_cl & C).
        eapply clos_rt_rtn1. eapply rt_trans. econstructor. red. eauto.
        eapply clos_rtn1_rt. eauto.
      * eauto.
      * assert (NEQeb: e <> b).
        { eapply (mcon uf) in Gb as (A1 & A2).
          eapply Elts.choose_1 in C. eapply A1 in C as (e_cl & C).
          eapply repr_some_neq. eauto. }
        rewrite cut_disjoint; auto.
        constructor.
      * intro. eapply EQ in H. eapply Elts.remove_1; eauto.
      * symmetry. eauto.
      * intro. eapply R. eapply repr_clos_order. eapply cut_clos_order2. eauto.
  - auto.
Qed.

Lemma delete_repr_unchanged2: forall uf uf1 a b,
    a <> b ->
    delete uf a = (uf1, None) ->
    repr uf1 b = repr uf b.
Proof.
  intros until b. intros NEQ DEL. unfold delete in DEL.
  destruct (PTree.get a (m uf)) as [(r & a_cl) |] eqn: G.
  - destruct r as [r|].
    + inv DEL.
      set (uf1 := (cut uf a r)).
      destruct (clos_order_dec uf1 a b).
      (* b ->* a *)
      * erewrite repr_link_children_relink.
        unfold uf1.
        rewrite cut_unchanged. 
        rewrite <- (repr_clos_order uf a b).
        symmetry. eapply repr_some. eauto.
        (* clos_order (m uf1) a b implies clos_order (m uf) a b *)
        -- unfold uf1 in c. eapply cut_clos_order2. eauto.
        (* ~ clos_order (m uf) a r *)
        -- intro. eapply repr_some_neq. eauto.
           eapply clos_order_antisym. eauto.
           red. econstructor. red. eauto. constructor.
        -- exploit (cut_a_root uf a r). eauto. eauto.
        -- unfold uf1.
           rewrite cut_unchanged.
           eapply repr_some_diff in G. auto.
           (* ~ clos_order (m uf) a r *)
           unfold uf1 in c. intro.
           eapply repr_some_neq. eapply G. eapply clos_order_antisym.
           eauto. econstructor. red. eauto. constructor.
        (* r not in a_cl *)
        -- generalize (mcon uf _ _ _ G). intros (A1 & (b' & b_cl' & A2 & A3)).
           intro B. eapply A1 in B. red in B. destruct B as (r_cl & G1).
           (* a -> r and r -> a are impossible *)
           eapply repr_some_neq. eapply G.
           eapply clos_order_antisym. econstructor. red. eauto.
           constructor. econstructor. red. eauto. constructor.
        -- reflexivity.
        -- auto.
        -- auto.
      (* ~ b ->* a *)
      * erewrite repr_link_children_unchanged.
        unfold uf1. rewrite cut_unchanged. auto.
        (* clos_order (m uf) a b implies clos_order (m uf1) a b *)
        -- intro. eapply n.
           eapply (cut_clos_order1 uf a r b a) in H.
           destruct H as [A|(A1 & A2 & A3)]; auto.           
        -- exploit (cut_a_root uf a r). eauto. eauto.
        -- unfold uf1.
           rewrite cut_unchanged.
           eapply repr_some_diff in G. auto.
           intro. eapply repr_some_neq. eapply G.
           eapply clos_order_antisym. eauto.
           econstructor. red. eauto. constructor.
        -- generalize (mcon uf _ _ _ G). intros (A1 & (b' & b_cl' & A2 & A3)).
           intro B. eapply A1 in B. red in B. destruct B as (r_cl & G1).
           (* a -> r and r -> a are impossible *)
           eapply repr_some_neq. eapply G.
           eapply clos_order_antisym.
           econstructor. red. eauto. constructor.
           econstructor. red. eauto. constructor.
        -- reflexivity.
        -- auto.
    + destruct (Elts.choose a_cl) as [r|] eqn: C; try congruence.
  - inv DEL. auto.
Qed.


Lemma repr_clos_order_root: forall uf x r,
    repr uf x = r ->
    clos_order (m uf) r x.
Proof.
  intros uf.
  intros x0; pattern x0. apply (well_founded_ind (mwf uf)); intros.
  rewrite (repr_unroll uf) in H0. destruct (PTree.get x (m uf)) as [(a' & a_cl')|] eqn:X.
  - destruct a' as [a'|].
    + econstructor. red. eauto.
      eapply H; eauto. red. eauto.
    + subst. constructor.
  - subst. constructor.
Qed.

  
Lemma delete_fresh_repr: forall uf uf1 a b r,
    a <> b ->
    repr uf a = repr uf b ->
    delete uf a = (uf1, Some r) ->
    repr uf1 b = r.
Proof.
  intros until r. intros NEQ RNEQ DEL.
  unfold delete in DEL.
  destruct (PTree.get a (m uf)) as [(r1 & a_cl) |] eqn: G; try congruence.
  - destruct r1 as [r1|]; try congruence.
    destruct (Elts.choose a_cl) as [r2|] eqn: C; try congruence.
    inv DEL.
    assert (ORDra: order (m uf) a r).
    { eapply (mcon uf). eauto. eapply Elts.choose_1. auto. }
    assert (NEQra: r <> a).
    { destruct  ORDra as (r_cl & Gr). eapply repr_some_neq. eauto. }   
    set (uf1 := (cut uf r a)).
    destruct (clos_order_dec uf1 a b).
    (* b ->* a *)
    * exploit (cut_b_result uf r a). eauto.
      intros (a_cl' & Ga' & EQ).
      erewrite repr_link_children_relink.
      -- apply cut_disjoint. auto.         
         constructor.
      (* properties of cut *)
      -- eauto. 
      -- unfold uf1. rewrite cut_disjoint; auto.
         constructor.
      -- intro. eapply EQ in H. eapply Elts.remove_1. 2: eapply H. auto.
      -- symmetry. auto.
      -- auto.
      -- auto.
    (* ~ b ->* a in uf1 *)
    * destruct (clos_order_dec uf a b).
      (* show b ->* r *)
      -- destruct (clos_order_dec uf r b).
         2: { exfalso. eapply n. eapply cut_local; eauto. }
         unfold uf1.
         exploit (cut_b_result uf r a). eauto.
         intros (a_cl' & Ga' & EQ).
         erewrite repr_link_children_unchanged; auto.
         ++ apply cut_disjoint. auto. auto.
         (* properties of cut *)
         ++ eauto. 
         ++ unfold uf1. rewrite cut_disjoint; auto.
            constructor.
         ++ intro. eapply EQ in H. eapply Elts.remove_1. 2: eapply H. auto.
         ++ symmetry. auto.
      -- exfalso. eapply n0. eapply repr_clos_order_root.
         rewrite <- RNEQ. eapply repr_none2. eauto.
Qed.
    

(* Path compression *)

Section COMPRESS.

Variable uf: t.
Variable a a' b: elt.
Hypothesis a_diff_b: a <> b.
Hypothesis a_repr_b: repr uf a = b.

(* To simplify the proof, we reuse merge and cut functions which do
not depend on any hypothesis *)
Definition compress := merge (cut uf a a') a b.

Lemma repr_compress:
  forall x, repr compress x = repr uf x.
Proof.
  intros x. unfold compress.
  rewrite repr_merge.
  destruct (clos_order_dec uf a x).
  - destruct (order_dec uf a a').
    + destruct o as (a_cl & Ga).
      rewrite <- (repr_clos_order uf a x); auto.
      erewrite repr_union_2.
      * rewrite cut_unchanged.
        rewrite <- a_repr_b. eapply repr_canonical.
        intro. eapply a_diff_b. inv H. auto. 
        red in H0. destruct H0 as (cl & Gra).
        destruct (repr_res_none_dec uf a); try congruence.
        destruct s. congruence.
      * rewrite !cut_disjoint. auto.
        red. eauto.
        constructor. red. eauto. auto.
    + replace (cut uf a a') with uf.
      2: symmetry; eapply cut_same; auto.
      rewrite <- (repr_clos_order uf a x); auto.
      rewrite repr_union_2. rewrite <- a_repr_b. eapply repr_canonical.
      symmetry. eapply repr_clos_order. auto.     
  - rewrite <- (cut_unchanged uf a a' x n).
    assert (R: ~ clos_order (m (cut uf a a')) a x).
    { intro. eapply n.
      eapply cut_clos_order2. eauto. }
    destruct (order_dec uf a a').
    + rewrite repr_union_1. auto.
      rewrite cut_unchanged; auto. rewrite cut_disjoint; auto.
      intro. eapply n. eapply repr_clos_order_root. auto. constructor.
    + replace (cut uf a a') with uf.
      2: symmetry; eapply cut_same; auto.
      destruct (elt_eq (repr uf a) (repr uf x)).
      * rewrite repr_union_2. rewrite <- e. rewrite <- a_repr_b.
        apply repr_canonical. auto.
      * rewrite repr_union_1; auto.
Qed.
  
End COMPRESS.

(* Find with path compression *)

Section FIND.

Variable uf: t.

Program Fixpoint find_x (a: elt) {wf (order uf.(m)) a} :
    { r: elt * t | fst r = repr uf a /\ forall x, repr (snd r) x = repr uf x } :=
  match PTree.get a uf.(m) with
  | Some (Some a', a_cl) =>
      match find_x a' with
      | pair b uf' => (b, compress uf' a a' b)
      end
  | Some (None, _)
  | None => (a, uf)
  end.
Next Obligation.
  red. rewrite <- Heq_anonymous. eauto.
Defined.
Next Obligation.
  destruct (find_x a')  as [[b' uf''] [A B]]. simpl in *. inv Heq_anonymous.
  split. symmetry. eapply repr_some. eauto.
  intros. erewrite repr_compress. eauto.
  eapply repr_some_diff. eauto.
  erewrite B. eapply repr_some. eauto.
Defined.
Next Obligation.
  split. symmetry. eapply repr_none2. eauto. auto.
Defined.
Next Obligation.
  split. symmetry. eapply repr_none. eauto. auto.
Defined.
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

(** Merging two union-find-delete structure *)

Fixpoint join_elt_acc (uf1 uf2: t) (l: list elt) : t :=
  match l with
  | nil => uf1
  | x :: l' =>
      let x1 := (repr uf1 x) in
      let x2 := (repr uf1 (repr uf2 x)) in
      if elt_eq x1 x2 then
        join_elt_acc uf1 uf2 l'
      else
        join_elt_acc (union uf1 x1 x2) uf2 l'
  end.
        
Definition join (uf1 uf2: t) := join_elt_acc uf1 uf2 (map fst (PTree.elements (m uf2))).
    
Lemma join_elt_acc_sound1_aux: forall uf2 l uf1 x y,
    sameclass uf1 x y ->
    sameclass (join_elt_acc uf1 uf2 l) x y.
Proof.
  induction l; intros until y; intros S.
  simpl in *. auto.
  simpl. destruct elt_eq.
  - auto.
  - eapply IHl.
    eapply sameclass_union_2. auto.
Qed.

Lemma join_sound1: forall uf1 uf2 a b,
      sameclass uf1 a b ->
      sameclass (join uf1 uf2) a b.
Proof.
  intros. unfold join. eapply join_elt_acc_sound1_aux. auto.
Qed.
   
Lemma join_elt_acc_sound2_aux: forall uf2 l uf1 x y
    (COM: forall e, In e l -> exists v, PTree.get e (m uf2) = Some v)
    (COR: forall e v, PTree.get e (m uf2) = Some v ->
                 In e l
                 \/ (* It is already added to uf1 *)
                   sameclass uf1 e (repr uf2 e))
    (DIS: list_norepet l)
    (S: sameclass uf2 x y),
    sameclass (join_elt_acc uf1 uf2 l) x y.
Proof.
  induction l; intros.
  - simpl in *.
    destruct (peq x y).
    + subst. eapply sameclass_refl.
    + unfold sameclass in *.
      generalize S as S1. intros.
      rewrite !repr_unroll in S.
      destruct (PTree.get x (m uf2)) eqn: Gx in S;
        destruct (PTree.get y (m uf2)) eqn: Gy in S.
      * exploit COR. eapply Gx. intros [A|B]; try contradiction.
        exploit COR. eapply Gy. intros [C|D]; try contradiction.
        rewrite B, D. rewrite S1. auto.
      * exploit COR. eapply Gx. intros [A|B]; try contradiction.
        erewrite (repr_none uf2 y) in S1. 2: eauto.
        destruct v. destruct o.
        -- rewrite S1 in B. auto.
        -- erewrite (repr_none2 uf2 x) in S1. 2: eauto. congruence.
      * exploit COR. eapply Gy. intros [A|B]; try contradiction.
        erewrite (repr_none uf2 x) in S1. 2: eauto.
        destruct v. destruct o.
        -- rewrite <- S1 in B. auto.
        -- erewrite (repr_none2 uf2 y) in S1. 2: eauto. congruence.
      * congruence.        
  - simpl. inv DIS.
    destruct elt_eq.
    + eapply IHl; eauto.
      intros. eapply COM. eapply in_cons. auto.
      intros. eapply COR in H.
      destruct (peq e0 a).
      * subst. right. auto.
      * destruct H; auto. inv H; try congruence. auto.
    + eapply IHl; eauto.
      intros. eapply COM. eapply in_cons. auto.
      intros. eapply COR in H.
      destruct (peq e a).
      * subst. right. red. rewrite repr_union_2.
        rewrite repr_union_1. rewrite repr_canonical. auto.
        rewrite repr_canonical. auto.
        rewrite repr_canonical. auto.
      * destruct H; auto. inv H; try congruence. auto.
        right.
        eapply sameclass_union_2. auto.
Qed.

(* Comparison of union-find structures *)

  Definition eq uf1 uf2 : Prop := forall a b,
      sameclass uf1 a b <->
      sameclass uf2 a b.
  Definition ge uf1 uf2 : Prop := forall a b,
      sameclass uf2 a b ->
      sameclass uf1 a b.
  Lemma eq_refl: forall uf,
      eq uf uf.
  Proof.
    intros. red. intros. split; auto.
  Qed.
  Lemma eq_sym: forall uf1 uf2,
      eq uf1 uf2 -> eq uf2 uf1.
  Proof.
    intros. unfold eq, sameclass in *. intros; split; intros; auto.
    apply H. auto.
    apply H. auto.
  Qed.  
  Lemma eq_trans: forall uf1 uf2 uf3,
      eq uf1 uf2 -> eq uf2 uf3 -> eq uf1 uf3.
  Proof.
    intros. unfold eq in *. intros. split; unfold sameclass in *; intros; auto.
    eapply H0. eapply H. auto.
    eapply H. eapply H0. auto.
  Qed.
  Lemma ge_refl: forall uf1 uf2,
      eq uf1 uf2 ->
      ge uf1 uf2.
  Proof.
    intros. red. red in H. intros. eapply H. auto.
  Qed.
  Lemma ge_trans: forall uf1 uf2 uf3,
      ge uf1 uf2 -> ge uf2 uf3 -> ge uf1 uf3.
  Proof.
    intros. unfold ge in *. intros. unfold sameclass in *; intros; auto.
  Qed.
  Lemma ge_antisym: forall uf1 uf2,
      ge uf1 uf2 -> ge uf2 uf1 -> eq uf1 uf2.
  Proof.
    intros. unfold ge, eq, sameclass in *. 
    intros; split; auto.
  Qed.

  Lemma ge_empty: forall uf,
      ge uf empty.
  Proof.
    intros. red. intros. red in H.
    rewrite !UFD.repr_empty in H. subst.
    apply UFD.sameclass_refl.
  Qed.

Lemma join_sound2: forall uf1 uf2 a b,
      sameclass uf2 a b ->
      sameclass (join uf1 uf2) a b.
Proof.
  intros. unfold join.
  eapply join_elt_acc_sound2_aux;
    auto.
  intros. eapply in_map_iff in H0 as ((x & v) & A1 & A2).
  inv A1. eapply PTree.elements_complete in A2. eauto.
  intros. eapply PTree.elements_correct in H0. left.
  eapply in_map_iff. exists (e, v). eauto.
  eapply PTree.elements_keys_norepet.
Qed.

Definition geb_elt (uf1 uf2: t) a (v: vt) : bool :=
  proj_sumbool (elt_eq (repr uf1 a) (repr uf1 (repr uf2 a))).

Definition geb (uf1 uf2: t) : bool :=
  PTree_Properties.for_all (m uf2) (geb_elt uf1 uf2).

Lemma geb_correct: forall uf1 uf2,
      geb uf1 uf2 = true ->
      ge uf1 uf2.
Proof.
  unfold geb, ge, sameclass.
  intros.
  destruct (PTree.get a (m uf2)) eqn: Ga;
    destruct (PTree.get b (m uf2)) eqn: Gb.
  - eapply PTree_Properties.for_all_correct in Ga. 2: eauto.
    unfold geb_elt in Ga. eapply proj_sumbool_true in Ga.
    eapply PTree_Properties.for_all_correct in Gb. 2: eauto.
    unfold geb_elt in Gb. eapply proj_sumbool_true in Gb.
    rewrite Ga, Gb, H0. auto.
  - eapply PTree_Properties.for_all_correct in Ga. 2: eauto.
    unfold geb_elt in Ga. eapply proj_sumbool_true in Ga.
    eapply repr_none in Gb.
    rewrite Ga, H0, Gb. auto.
  - eapply PTree_Properties.for_all_correct in Gb. 2: eauto.
    unfold geb_elt in Gb. eapply proj_sumbool_true in Gb.
    eapply repr_none in Ga.
    rewrite Gb, <- H0, Ga. auto.
  - eapply repr_none in Ga. eapply repr_none in Gb.
    rewrite Ga, Gb in H0. subst. auto.
Qed.

Definition eqb uf1 uf2 :=  geb uf1 uf2 && geb uf2 uf1.

Lemma eqb_correct: forall uf1 uf2,
      eqb uf1 uf2 = true ->
      eq uf1 uf2.
  Proof.
    intros. unfold eqb in H. apply andb_true_iff in H as (A1 & A2).
    red. intros. split; eapply geb_correct; auto.
  Qed.

Lemma join_ge1: forall uf1 uf2,
    ge (join uf1 uf2) uf1.
Proof.
  intros. red. intros.
  eapply join_sound1. auto.
Qed.

Lemma join_ge2: forall uf1 uf2,
    ge (join uf1 uf2) uf2.
Proof.
  intros. red. intros.
  eapply join_sound2. auto.
Qed.

End UFD.

