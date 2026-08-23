(* *********************************************************************)
(*                                                                     *)
(*                      RustCompCert frontend                          *)
(*                                                                     *)
(*  Miscellaneous properties about [PTree] maps: [set], [remove],      *)
(*  [map]/[map1], together with an implementation-independent          *)
(*  interface for generating fresh identifiers not present in the      *)
(*  domain of a map, and a concrete max+1 instance.                    *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Maps.
Require Import AST.

(** stdpp-style notation for a single-key update: [<[ x := v ]> m] is
    [PTree.set x v m].  Lookup binds after the whole update:
    [<[ x := v ]> m ! k] parses as [(<[ x := v ]> m) ! k].  As a
    standalone term, a chain is right-nested (innermost first), e.g.
    [<[ x1 := v1 ]> <[ x2 := v2 ]> m] is [PTree.set x1 v1
    (PTree.set x2 v2 m)]; to use a chain inside a larger statement,
    parenthesize it: [(<[ x1 := v1 ]> <[ x2 := v2 ]> m)]. *) 
Declare Scope map_fresh_scope.

Notation "<[ x := v ]> m" := (PTree.set x v m)
  (at level 1, left associativity, format "<[  x  :=  v  ]>  m") : map_fresh_scope.

Local Open Scope map_fresh_scope.

(** * Single-key lemmas: [set], [remove], [map] commute *)

(** [map1] commutes with [set].  This holds for an arbitrary key [x];
    no freshness hypothesis is needed. *)
Lemma map1_set: forall {A B} (f: A -> B) (x: positive) (v: A) (m: PTree.t A),
    PTree.map1 f (<[ x := v ]> m) = <[ x := f v ]> (PTree.map1 f m).
Proof.
  intros. apply PTree.extensionality. intro i.
  destruct (peq i x).
  - subst. rewrite !PTree.gmap1, !PTree.gss. simpl. auto.
  - rewrite !PTree.gmap1. rewrite !PTree.gso by auto. rewrite PTree.gmap1. auto.
Qed.

(** Key-aware variant of [map1_set], for [PTree.map]. *)
Lemma map_set: forall {A B} (f: positive -> A -> B) (x: positive) (v: A) (m: PTree.t A),
    PTree.map f (<[ x := v ]> m) = <[ x := f x v ]> (PTree.map f m).
Proof.
  intros. apply PTree.extensionality. intro i.
  destruct (peq i x).
  - subst. rewrite !PTree.gmap, !PTree.gss. simpl. auto.
  - rewrite !PTree.gmap. rewrite !PTree.gso by auto. rewrite PTree.gmap. auto.
Qed.

(** Setting then removing a fresh key restores the original map.
    The hypothesis [get x m = None] says that [x] is not in the domain
    of [m]; it is exactly what the [FRESH] interface below guarantees. *)
Lemma remove_set_fresh: forall {A} (x: positive) (v: A) (m: PTree.t A),
    PTree.get x m = None ->
    PTree.remove x (PTree.set x v m) = m.
Proof.
  intros. apply PTree.extensionality. intro i.
  destruct (peq i x).
  - subst. rewrite PTree.grs, H. auto.
  - rewrite PTree.gro, PTree.gso by auto. auto.
Qed.

(** [set] commutes on distinct keys. *)
Lemma set_comm: forall {A} (x y: positive) (v w: A) (m: PTree.t A),
    x <> y ->
    PTree.set y w (PTree.set x v m) = PTree.set x v (PTree.set y w m).
Proof.
  intros. apply PTree.extensionality. intro i.
  destruct (peq i x) as [Hix | Hnix].
  - destruct (peq i y) as [Hiy | Hniy].
    + subst. contradiction.
    + subst. rewrite PTree.gss. rewrite PTree.gso by congruence. rewrite PTree.gss. auto.
  - destruct (peq i y) as [Hiy | Hniy].
    + subst. rewrite PTree.gss. rewrite PTree.gso by congruence. rewrite PTree.gss. auto.
    + repeat rewrite PTree.gso by congruence. auto.
Qed.

(** [remove] commutes with [set] on distinct keys. *)
Lemma remove_set_comm: forall {A} (x y: positive) (v: A) (m: PTree.t A),
    x <> y ->
    PTree.remove y (PTree.set x v m) = PTree.set x v (PTree.remove y m).
Proof.
  intros. apply PTree.extensionality. intro i.
  destruct (peq i x) as [Hix | Hnix].
  - destruct (peq i y) as [Hiy | Hniy].
    + subst. contradiction.
    + subst. rewrite PTree.gss. rewrite PTree.gro by congruence. rewrite PTree.gss. auto.
  - destruct (peq i y) as [Hiy | Hniy].
    + subst. rewrite PTree.grs. rewrite PTree.gso by congruence. rewrite PTree.grs. auto.
    + rewrite PTree.gro by congruence. rewrite !PTree.gso by congruence. rewrite PTree.gro by congruence. auto.
Qed.

(** * List versions: [set_list] and [remove_list] *)

(** Set a list of values at a list of keys.  When the two lists have
    different lengths, only the common prefix is set. *)
Fixpoint set_list {A} (l: list positive) (vl: list A) (m: PTree.t A) {struct l} : PTree.t A :=
  match l, vl with
  | nil, nil => m
  | x :: l', v :: vl' => PTree.set x v (set_list l' vl' m)
  | _, _ => m
  end.

(** Remove a list of keys from a map. *)
Fixpoint remove_list {A} (l: list positive) (m: PTree.t A) {struct l} : PTree.t A :=
  match l with
  | nil => m
  | x :: l' => PTree.remove x (remove_list l' m)
  end.

(** stdpp-style notation for a list update: [<<[ l := vl ]>> m] is
    [set_list l vl m].  Like the single-key variant, lookup binds after
    the whole update ([<<[ l := vl ]>> m ! k] is
    [(<<[ l := vl ]>> m) ! k]) and chains can be parenthesized to
    combine multiple updates. *) 
Notation "<<[ l := vl ]>> m" := (set_list l vl m)
  (at level 1, left associativity, format "<<[  l  :=  vl  ]>>  m") : map_fresh_scope.

(** [map1] commutes with [set_list]; only the lengths need to agree. *)
Lemma set_list_map1: forall {A B} (f: A -> B) (l: list positive) (vl: list A) (m: PTree.t A),
    length l = length vl ->
    PTree.map1 f (set_list l vl m) = set_list l (map f vl) (PTree.map1 f m).
Proof.
  induction l; intros vl m Hlen; destruct vl; simpl in *; try discriminate.
  - auto.
  - injection Hlen as Hlen.
    rewrite map1_set. f_equal. apply IHl. exact Hlen.
Qed.

(** Setting keys not in [l] leaves them unchanged. *)
Lemma set_list_get: forall {A} (l: list positive) (vl: list A) (i: positive) (m: PTree.t A),
    length l = length vl -> ~ In i l ->
    PTree.get i (set_list l vl m) = PTree.get i m.
Proof.
  induction l; intros vl i m Hlen Hin; destruct vl; simpl in *; try discriminate.
  - auto.
  - injection Hlen as Hlen.
    rewrite PTree.gso.
    + apply IHl.
      * exact Hlen.
      * intros Hnin. apply Hin. right. exact Hnin.
    + intros Hix. subst. apply Hin. left. auto.
Qed.

(** [set] commutes with [set_list] when the key is not in the list. *)
Lemma set_list_set_comm: forall {A} (l: list positive) (vl: list A) (y: positive) (w: A) (m: PTree.t A),
    length l = length vl -> ~ In y l ->
    PTree.set y w (set_list l vl m) = set_list l vl (PTree.set y w m).
Proof.
  induction l; intros vl y w m Hlen Hin; destruct vl; simpl in *; try discriminate.
  - auto.
  - injection Hlen as Hlen.
    rewrite set_comm.
    + f_equal. apply IHl.
      * exact Hlen.
      * intros Hnin. apply Hin. right. exact Hnin.
    + intros Hay. apply Hin. left. exact Hay.
Qed.

(** Removing keys not in [l] leaves other keys unchanged. *)
Lemma remove_list_get: forall {A} (l: list positive) (i: positive) (m: PTree.t A),
    ~ In i l ->
    PTree.get i (remove_list l m) = PTree.get i m.
Proof.
  induction l; intros i m Hin; simpl in *.
  - auto.
  - rewrite PTree.gro.
    + apply IHl. intros Hnin. apply Hin. right. exact Hnin.
    + intros Hia. subst. apply Hin. left. auto.
Qed.

(** [remove_list] commutes with [set] when the key is not in the list. *)
Lemma remove_list_set_comm: forall {A} (l: list positive) (x: positive) (v: A) (m: PTree.t A),
    ~ In x l ->
    remove_list l (PTree.set x v m) = PTree.set x v (remove_list l m).
Proof.
  induction l; intros x v m Hin; simpl in *.
  - auto.
  - rewrite IHl.
    + rewrite remove_set_comm.
      * auto.
      * intros Hax. apply Hin. left. symmetry. exact Hax.
    + intros Hnin. apply Hin. right. exact Hnin.
Qed.

Lemma nodup_cons_inv: forall {A} (x: A) (l: list A),
    NoDup (x :: l) -> ~ In x l /\ NoDup l.
Proof.
  intros. inv H. split; auto.
Qed.

(** Setting a list of fresh keys and then removing them restores the
    original map.  [NoDup l] and [forall x, In x l -> get x m = None]
    are exactly the properties supplied by the [FRESH] interface. *)
Lemma remove_list_set_list: forall {A} (l: list positive) (vl: list A) (m: PTree.t A),
    length l = length vl -> NoDup l ->
    (forall x, In x l -> PTree.get x m = None) ->
    remove_list l (set_list l vl m) = m.
Proof.
  induction l; intros vl m Hlen Hnodup Hnone; destruct vl; simpl in *; try discriminate.
  - auto.
  - injection Hlen as Hlen.
    destruct (nodup_cons_inv a l Hnodup) as [Hnin Hnodup'].
    rewrite remove_list_set_comm.
    2: exact Hnin.
    rewrite remove_set_fresh.
    + apply IHl.
      * exact Hlen.
      * exact Hnodup'.
      * intros. apply Hnone. right. auto.
    + rewrite remove_list_get.
      * rewrite set_list_get.
        -- apply Hnone. left. auto.
        -- exact Hlen.
        -- exact Hnin.
      * exact Hnin.
Qed.

(** * Consecutive identifiers starting from [p] *)

Fixpoint npos (n: nat) (p: positive) : list positive :=
  match n with
  | O => nil
  | S n' => p :: npos n' (Pos.succ p)
  end.

Lemma npos_length: forall n p, length (npos n p) = n.
Proof.
  intros n. induction n; simpl; intros p.
  - auto.
  - f_equal. apply IHn.
Qed.

Lemma npos_ge: forall n p x, In x (npos n p) -> Ple p x.
Proof.
  induction n; simpl; intros.
  - contradiction.
  - destruct H.
    + subst. apply Ple_refl.
    + eapply Ple_trans; [ apply Ple_succ | apply IHn; exact H ].
Qed.

Lemma npos_nodup: forall n p, NoDup (npos n p).
Proof.
  induction n; simpl; intros.
  - constructor.
  - constructor.
    + intro H.
      apply (Plt_strict p).
      eapply Plt_Ple_trans.
      * apply Plt_succ.
      * exact (npos_ge n (Pos.succ p) p H).
    + apply IHn.
Qed.

(** * Maximum key of a map *)

Definition max_key {A} (m: PTree.t A) : positive :=
  PTree.fold (fun acc x _ => Pos.max acc x) m 1%positive.

Lemma fold_left_max_acc_le: forall {A} (l: list (positive * A)) (acc: positive),
    Ple acc (List.fold_left (fun a p => Pos.max a (fst p)) l acc).
Proof.
  induction l; simpl; intros.
  - apply Ple_refl.
  - eapply Ple_trans; [ apply Pos.le_max_l | apply IHl ].
Qed.

Lemma fold_left_max_le: forall {A} (l: list (positive * A)) (acc: positive) (x: positive),
    In x (map fst l) ->
    Ple x (List.fold_left (fun a p => Pos.max a (fst p)) l acc).
Proof.
  induction l; intros; simpl in *.
  - contradiction.
  - destruct H as [Hx | Hx].
    + subst. eapply Ple_trans; [ apply Pos.le_max_r | apply fold_left_max_acc_le ].
    + exact (IHl (Pos.max acc (fst a)) x Hx).
Qed.

Lemma max_key_spec: forall {A} (m: PTree.t A) (x: positive),
    In x (map fst (PTree.elements m)) -> Ple x (max_key m).
Proof.
  intros. unfold max_key. rewrite PTree.fold_spec. apply fold_left_max_le. exact H.
Qed.

(** * Implementation-independent interface for fresh identifiers *)

Module Type FRESH.
  Parameter fresh: forall {A: Type}, PTree.t A -> positive.
  Parameter fresh_spec: forall {A: Type} (m: PTree.t A),
      PTree.get (fresh m) m = None.
  Parameter fresh_idents: forall {A: Type}, PTree.t A -> nat -> list positive.
  Parameter fresh_idents_length: forall {A: Type} (m: PTree.t A) (n: nat),
      length (fresh_idents m n) = n.
  Parameter fresh_idents_nodup: forall {A: Type} (m: PTree.t A) (n: nat),
      NoDup (fresh_idents m n).
  Parameter fresh_idents_notin: forall {A: Type} (m: PTree.t A) (n: nat) (i: positive),
      In i (fresh_idents m n) -> PTree.get i m = None.
End FRESH.

(** The concrete max+1 instance: [fresh m] is the successor of the
    largest key of [m], and [fresh_idents m n] returns the [n]
    consecutive identifiers starting at [fresh m]. *)
Module FreshMax <: FRESH.
  Definition fresh {A: Type} (m: PTree.t A) : positive :=
    Pos.succ (max_key m).

  Definition fresh_idents {A: Type} (m: PTree.t A) (n: nat) : list positive :=
    npos n (fresh m).

  Lemma fresh_spec: forall {A: Type} (m: PTree.t A),
      PTree.get (fresh m) m = None.
  Proof.
    intros A m. unfold fresh.
    destruct (PTree.get (Pos.succ (max_key m)) m) eqn: G.
    - apply PTree.elements_correct in G.
      assert (Hin: In (Pos.succ (max_key m)) (map fst (PTree.elements m))).
      { apply in_map_iff. eexists (Pos.succ (max_key m), a). split. simpl. auto. exact G. }
      exfalso. apply (Plt_strict (max_key m)).
      eapply Plt_Ple_trans.
      + apply Plt_succ.
      + exact (max_key_spec m (Pos.succ (max_key m)) Hin).
    - auto.
  Qed.

  Lemma fresh_idents_length: forall {A: Type} (m: PTree.t A) (n: nat),
      length (fresh_idents m n) = n.
  Proof.
    intros. unfold fresh_idents. apply npos_length.
  Qed.

  Lemma fresh_idents_nodup: forall {A: Type} (m: PTree.t A) (n: nat),
      NoDup (fresh_idents m n).
  Proof.
    intros. unfold fresh_idents. apply npos_nodup.
  Qed.

  Lemma fresh_idents_notin: forall {A: Type} (m: PTree.t A) (n: nat) (i: positive),
      In i (fresh_idents m n) -> PTree.get i m = None.
  Proof.
    intros A m n i H. unfold fresh_idents in H.
    destruct (PTree.get i m) eqn: G.
    - apply PTree.elements_correct in G.
      assert (Hin: In i (map fst (PTree.elements m))).
      { apply in_map_iff. eexists (i, a). split. simpl. auto. exact G. }
      assert (Hle: Ple i (max_key m)) by (exact (max_key_spec m i Hin)).
      assert (Hge: Ple (fresh m) i) by (exact (npos_ge n (fresh m) i H)).
      exfalso. apply (Plt_strict (max_key m)).
      eapply Plt_Ple_trans.
      + apply Plt_succ.
      + eapply Ple_trans; [ exact Hge | exact Hle ].
    - auto.
  Qed.
End FreshMax.

(** * Fresh-key update notation *)

(** stdpp-style shorthand for updating the fresh (max+1) key:
    [<[ v ]> m] is [<[ FreshMax.fresh m := v ]> m], i.e. [PTree.set
    (FreshMax.fresh m) v m].  Lookup binds after the whole update:
    [<[ v ]> m ! k] parses as [(<[ v ]> m) ! k].  As a standalone term
    a chain is right-nested (innermost first): [<[ v2 ]> <[ v1 ]> m]
    stores [v1] at [FreshMax.fresh m] and [v2] at its successor.  To
    use a chain inside a larger statement, parenthesize it:
    [(<[ v2 ]> <[ v1 ]> m)].  When the fresh key itself is used as an
    index, parenthesize the application: [! (FreshMax.fresh m)]. *)
Notation "<[ v ]> m" := (<[ FreshMax.fresh m := v ]> m)
  (at level 1, left associativity, format "<[  v  ]>  m") : map_fresh_scope.

(** * [max_key] commutation with [set] and [set_list] *)

(** Upper bound for a left fold of maxima. *)
Lemma fold_max_le_bound: forall {A} (l: list (positive * A)) (acc b: positive),
    (forall x, In x (map fst l) -> Ple x b) ->
    Ple acc b ->
    Ple (List.fold_left (fun a p => Pos.max a (fst p)) l acc) b.
Proof.
  induction l; simpl; intros.
  - exact H0.
  - apply IHl; auto.
    apply Pos.max_lub; [ exact H0 | apply H; left; auto ].
Qed.

(** The accumulator is always below the result of a left fold of
    maxima (alias of [fold_left_max_acc_le]). *)
Lemma fold_max_ge_acc: forall {A} (l: list (positive * A)) (acc: positive),
    Ple acc (List.fold_left (fun a p => Pos.max a (fst p)) l acc).
Proof.
  intros. apply fold_left_max_acc_le.
Qed.

(** [1] is a lower bound on [max_key]. *)
Lemma max_key_ge_1: forall {A} (m: PTree.t A), Ple 1%positive (max_key m).
Proof.
  intros. unfold max_key. rewrite PTree.fold_spec. apply fold_left_max_acc_le.
Qed.

(** If every key of [m] is below [b], so is [max_key m]. *)
Lemma max_key_all_le: forall {A} (m: PTree.t A) (b: positive),
    (forall x, In x (map fst (PTree.elements m)) -> Ple x b) ->
    Ple (max_key m) b.
Proof.
  intros. unfold max_key. rewrite PTree.fold_spec. apply fold_max_le_bound.
  - exact H.
  - apply Pos.le_1_l.
Qed.

(** [max_key] of a [set] is bounded above by the maximum of the key and
    [max_key] of the original map. *)
Lemma max_key_set_upper: forall {A} (k: positive) (v: A) (m: PTree.t A),
    Ple (max_key (PTree.set k v m)) (Pos.max k (max_key m)).
Proof.
  intros. apply max_key_all_le.
  intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [[i w] [Hi Hw]].
  simpl in Hi. subst x.
  apply PTree.elements_complete in Hw.
  rewrite PTree.gsspec in Hw.
  destruct (peq i k).
  - subst. apply Pos.le_max_l.
  - apply Ple_trans with (max_key m).
    + apply max_key_spec. apply in_map_iff.
      eexists (i, w). split. simpl. auto. apply PTree.elements_correct. exact Hw.
    + apply Pos.le_max_r.
Qed.

(** [max_key] is monotone under [set]. *)
Lemma max_key_mono_set: forall {A} (k: positive) (v: A) (m: PTree.t A),
    Ple (max_key m) (max_key (PTree.set k v m)).
Proof.
  intros. apply max_key_all_le.
  intros x Hx.
  apply in_map_iff in Hx. destruct Hx as [[i w] [Hi Hw]].
  simpl in Hi. subst x.
  apply PTree.elements_complete in Hw.
  destruct (peq i k).
  - subst. apply max_key_spec. apply in_map_iff.
    eexists (k, v). split. simpl. auto. apply PTree.elements_correct. apply PTree.gss.
  - apply max_key_spec. apply in_map_iff.
    eexists (i, w). split. simpl. auto. apply PTree.elements_correct. rewrite PTree.gso; auto.
Qed.

(** [max_key] commutes with [set]. *)
Lemma max_key_set: forall {A} (k: positive) (v: A) (m: PTree.t A),
    max_key (PTree.set k v m) = Pos.max k (max_key m).
Proof.
  intros. apply Pos.le_antisym.
  - apply max_key_set_upper.
  - apply Pos.max_lub.
    + apply max_key_spec. apply in_map_iff.
      eexists (k, v). split. simpl. auto. apply PTree.elements_correct. apply PTree.gss.
    + apply max_key_mono_set.
Qed.

(** Maximum of a list of keys. *)
Definition max_key_list (l: list positive) : positive :=
  List.fold_right Pos.max 1%positive l.

(** [max_key] commutes with [set_list]. *)
Lemma max_key_set_list: forall {A} (l: list positive) (vl: list A) (m: PTree.t A),
    length l = length vl ->
    max_key (set_list l vl m) = Pos.max (max_key_list l) (max_key m).
Proof.
  induction l; intros vl m Hlen; destruct vl; simpl in *; try discriminate.
  - rewrite Pos.max_r by (apply max_key_ge_1). auto.
  - injection Hlen as Hlen.
    rewrite max_key_set.
    rewrite IHl by exact Hlen.
    rewrite Pos.max_assoc. auto.
Qed.

(** * Single-key fresh shorthand lemmas *)

(** Setting the fresh key makes [fresh] the successor of its previous
    value. *)
Lemma fresh_set_fresh: forall {A} (v: A) (m: PTree.t A),
    FreshMax.fresh (<[ v ]> m) = Pos.succ (FreshMax.fresh m).
Proof.
  intros.
  change (FreshMax.fresh (PTree.set (FreshMax.fresh m) v m)
          = Pos.succ (FreshMax.fresh m)).
  unfold FreshMax.fresh.
  rewrite max_key_set.
  apply Pos.succ_inj.
  rewrite Pos.max_l by (apply Ple_succ).
  auto.
Qed.

(** The fresh key maps to the fresh value. *)
Lemma get_fresh_set: forall {A} (v: A) (m: PTree.t A),
    (<[ v ]> m) ! (FreshMax.fresh m) = Some v.
Proof.
  intros.
  change (PTree.get (FreshMax.fresh m) (PTree.set (FreshMax.fresh m) v m) = Some v).
  apply PTree.gss.
Qed.

(** Removing the fresh key restores the original map. *)
Lemma remove_fresh_set: forall {A} (v: A) (m: PTree.t A),
    PTree.remove (FreshMax.fresh m) (<[ v ]> m) = m.
Proof.
  intros.
  change (PTree.remove (FreshMax.fresh m) (PTree.set (FreshMax.fresh m) v m) = m).
  apply remove_set_fresh.
  apply FreshMax.fresh_spec.
Qed.

(** * Batch version: [set_fresh_list] *)

(** Store the list [vl] at the consecutive fresh keys
    [FreshMax.fresh m .. FreshMax.fresh m + |vl| - 1]. *)
Definition set_fresh_list {A} (m: PTree.t A) (vl: list A) : PTree.t A :=
  set_list (FreshMax.fresh_idents m (length vl)) vl m.

(** stdpp-style shorthand for a batch of fresh-key updates: [<<[ vl ]>> m]
    is [set_fresh_list m vl], storing [vl] at the consecutive fresh keys
    [FreshMax.fresh m .. FreshMax.fresh m + |vl| - 1].  Like the other
    update notations, lookup binds after the whole update:
    [<<[ vl ]>> m ! k] parses as [(<<[ vl ]>> m) ! k]. *)
Notation "<<[ vl ]>> m" := (set_fresh_list m vl)
  (at level 1, left associativity, format "<<[  vl  ]>>  m") : map_fresh_scope.

(** [fresh] after a batch update is the successor of the maximum of the
    freshly used keys and the old [max_key]. *)
Lemma set_fresh_list_fresh: forall {A} (m: PTree.t A) (vl: list A),
    FreshMax.fresh (<<[ vl ]>> m) =
    Pos.succ (Pos.max (max_key_list (FreshMax.fresh_idents m (length vl))) (max_key m)).
Proof.
  intros. unfold set_fresh_list, FreshMax.fresh.
  rewrite max_key_set_list by apply FreshMax.fresh_idents_length.
  auto.
Qed.

(** Removing all the freshly used keys restores the original map. *)
Lemma set_fresh_list_remove: forall {A} (m: PTree.t A) (vl: list A),
    remove_list (FreshMax.fresh_idents m (length vl)) (<<[ vl ]>> m) = m.
Proof.
  intros. unfold set_fresh_list.
  apply remove_list_set_list.
  - apply FreshMax.fresh_idents_length.
  - apply FreshMax.fresh_idents_nodup.
  - intros x Hx. apply FreshMax.fresh_idents_notin with (n := length vl). exact Hx.
Qed.

(** Lookup of the [i]-th value stored by [set_list], using the [i]-th
    key. *)
Lemma set_list_nth: forall {A} (l: list positive) (vl: list A) (m: PTree.t A)
    (d: positive) (e: A) (i: nat),
    NoDup l -> length l = length vl -> (i < length l)%nat ->
    (set_list l vl m) ! (nth i l d) = Some (nth i vl e).
Proof.
  induction l; intros vl m d e i Hnodup Hlen Hlt;
    destruct vl as [| v vl]; simpl in *; try discriminate.
  - lia.
  - destruct i as [| i']; simpl in *.
    + change (PTree.get a (PTree.set a v (set_list l vl m)) = Some v).
      apply PTree.gss.
    + injection Hlen as Hlen.
      destruct (nodup_cons_inv a l Hnodup) as [Hnin Hnodup'].
      change (PTree.get (nth i' l d) (PTree.set a v (set_list l vl m))
              = Some (nth i' vl e)).
      rewrite PTree.gso.
      * apply IHl; auto. apply lt_S_n. exact Hlt.
      * intro Ha. subst a. apply Hnin. apply nth_In. apply lt_S_n. exact Hlt.
Qed.

(** Lookup of the [i]-th value stored by [set_fresh_list]. *)
Lemma set_fresh_list_get: forall {A} (m: PTree.t A) (vl: list A) (i: nat) (d: A),
    (i < length vl)%nat ->
    (<<[ vl ]>> m) ! (nth i (FreshMax.fresh_idents m (length vl)) 1%positive)
    = Some (nth i vl d).
Proof.
  intros. unfold set_fresh_list.
  apply set_list_nth.
  - apply FreshMax.fresh_idents_nodup.
  - apply FreshMax.fresh_idents_length.
  - rewrite FreshMax.fresh_idents_length. exact H.
Qed.

(** * Bridging the chain notation and the batch version *)

Lemma pos_succ_neq: forall (p: positive), p <> Pos.succ p.
Proof.
  intros p H.
  assert (Hsucc: Plt p (Pos.succ p)) by apply Plt_succ.
  apply (Plt_strict p).
  rewrite <- H in Hsucc.
  exact Hsucc.
Qed.

Lemma set_fresh_list_one: forall {A} (m: PTree.t A) (v: A),
    <<[ v :: nil ]>> m = <[ v ]> m.
Proof.
  intros. unfold set_fresh_list. simpl. reflexivity.
Qed.

Lemma set_fresh_list_two: forall {A} (m: PTree.t A) (v1 v2: A),
    (<[ v2 ]> <[ v1 ]> m) = <<[ v1 :: v2 :: nil ]>> m.
Proof.
  intros.
  rewrite fresh_set_fresh.
  unfold set_fresh_list. simpl.
  apply set_comm.
  apply pos_succ_neq.
Qed.
