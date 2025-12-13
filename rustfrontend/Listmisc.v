Require Import Coqlib.
Require Import AST.

Import ListNotations.

(** find an element from list  *)

Fixpoint list_find {A} (f : A -> bool) (l: list A) : option (nat * A) :=  
  match l with
  | nil => None
  | x :: l => if f x then Some (O,x) else option_map (fun '(idx, elt) => (S idx, elt)) (list_find f l)
  end.

Lemma list_find_some : forall (A: Type) (l: list A) f a idx,
    list_find f l = Some (idx, a) ->
    nth_error l idx = Some a /\ f a = true.
Admitted.


Lemma list_find_none : forall (A: Type) (l: list A) f,
    list_find f l = None ->
    forall x, In x l -> f x = false.
Admitted.


(* find an element with ident as the key *)

Definition find_field {A: Type} (id: ident) (l: list (ident * A)) : option A :=
  option_map (fun '(idx, (id, a)) => a) (list_find (fun '(id', _) => if ident_eq id id' then true else false) l). 


Lemma find_field_some: forall (A: Type) fid fpl (a: A),
    find_field fid fpl = Some a ->
    In (fid, a) fpl.
Proof.
  intros. unfold find_field in H.
  destruct (list_find (fun '(id', _) => if ident_eq fid id' then true else false) fpl) eqn: FIND; inv H.
  destruct p.
  exploit list_find_some. eauto. intros (A1 & B).
  destruct p.
  destruct ident_eq in B; try congruence.
  subst. eapply nth_error_in. eauto.
Qed.

Definition field_idents {A: Type} (l: list (ident * A)) : list ident :=
  map (fun '(fid, _) => fid) l.

(* only set the first occurence of fid *)
Fixpoint set_field {A: Type} (id: ident) (f: A -> A) (l: list (ident * A)) : list (ident * A) :=
  match l with
  | nil => nil
  | (id', a') :: l' =>
      if ident_eq id id' then
        (id, f a') :: l'
      else
        (id', a') :: (set_field id f l')
  end.

(* Properties for find_field and set_field *)

Lemma find_field_split : forall A fpl id (a:A),
    find_field id fpl = Some a ->
    exists l1 l2,
      fpl = l1 ++ (id, a) :: l2
      /\ ~ In id (field_idents l1).
Proof.
  induction fpl; simpl; intros.
  - inv H.
  - destruct a. unfold find_field in H.
    destruct ((list_find (fun '(id', _) => if ident_eq id id' then true else false)
             ((i, a) :: fpl))) eqn: FIND; inv H.
    simpl in FIND.
    destruct ident_eq in FIND.
    + inv FIND. exists nil, fpl.
      split. simpl. auto.
      intro. inv H.
    + destruct (list_find (fun '(id', _) => if ident_eq id id' then true else false)) eqn: FIND1; inv FIND.
      destruct p0 as (i1 & (i2 & a3)).
      exploit IHfpl. 
      unfold find_field. rewrite FIND1. reflexivity.
      intros (l1 & l2 & A1 & A2).
      subst.
      exists ((i,a)::l1), l2. split; auto.
      intro. inv H; congruence. 
Qed.
      
Lemma set_field_split : forall A l1 l2 id f (a: A),
    ~ In id (field_idents l1) ->
    set_field id f (l1 ++ (id, a) :: l2) = (l1 ++ (id, f a) :: l2).
Proof.
  induction l1; simpl; intros.
  - destruct ident_eq; try congruence.
  - destruct a. eapply Decidable.not_or in H.
    destruct H. destruct ident_eq; try congruence.
    f_equal. eauto.
Qed.
