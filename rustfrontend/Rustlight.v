Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.

Import ListNotations.

Local Open Scope error_monad_scope.

(** * High-level Rust-like language  *)


(** ** Place (used to build lvalue expression) *)

Inductive place : Type :=
| Plocal : ident -> type -> place
| Pfield : place -> ident -> type -> place 
(**r access a field of struct: p.(id)  *)
| Pderef : place -> type -> place
| Pdowncast: place -> ident -> type -> place 
(**r represent the location of a constructor *)
.

Lemma place_eq: forall (p1 p2: place), {p1=p2} + {p1<>p2}.
Proof.
  generalize type_eq ident_eq. intros.
  decide equality.
Defined.

Global Opaque place_eq.

Definition typeof_place p :=
  match p with
  | Plocal _ ty => ty
  | Pfield _ _ ty => ty
  | Pderef _ ty => ty
  | Pdowncast _ _ ty => ty
  end.


(** ** Expression *)

Inductive pexpr : Type :=
| Eunit                                 (**r unit value  *)
| Econst_int: int -> type -> pexpr       (**r integer literal *)
| Econst_float: float -> type -> pexpr   (**r double float literal *)
| Econst_single: float32 -> type -> pexpr (**r single float literal *)
| Econst_long: int64 -> type -> pexpr    (**r long integer literal *)
| Eplace: place -> type -> pexpr (**r use of a variable, the only lvalue expression *)
| Ecktag: place -> ident -> pexpr           (**r check the tag of variant, e.g. [Ecktag p.(fid)]. We cannot check a downcast *)
| Eref:  origin -> mutkind -> place -> type -> pexpr     (**r &[mut] p  *)
| Eunop: unary_operation -> pexpr -> type -> pexpr  (**r unary operation *)
| Ebinop: binary_operation -> pexpr -> pexpr -> type -> pexpr (**r binary operation *)
| Eglobal: ident -> type -> pexpr.                          (**r constant global variable, used as function id *)

(* The evaluaiton of expr may produce a moved-out place *)
Inductive expr : Type :=
| Emoveplace: place -> type -> expr
| Epure: pexpr -> expr.


Definition typeof_pexpr (pe: pexpr) : type :=
  match pe with
  | Eunit => Tunit
  | Ecktag _ _ => type_bool
  | Econst_int _ ty
  | Econst_float _ ty
  | Econst_single _ ty
  | Econst_long _ ty                
  | Eplace _ ty
  | Eref _ _ _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty => ty
  | Eglobal _ ty => ty
  end.

Definition typeof (e: expr) : type :=
  match e with
  | Emoveplace _ ty => ty
  | Epure pe => typeof_pexpr pe
    end.
                                  

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Slet : ident -> type -> statement -> statement (**r declare a variable. let ident: type in *)
| Sassign : place -> expr -> statement (**r assignment [place' = rvalue]. Downcast cannot appear in LHS *)
| Sassign_variant : place -> ident -> ident -> expr -> statement (**r assign variant to a place *)
| Sbox: place -> expr -> statement        (**r box assignment [place = Box::new(expr)]  *)
| Scall: place -> expr -> list expr -> statement (**r function call, p =
  f(...). The assignee is mandatory, because we need to ensure that
  the return value (may be a box) is received *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Sloop: statement -> statement (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : place -> statement.      (**r [return] statement *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue : option ident;
  fn_return: type;
  fn_callconv: calling_convention;
  (* Variables are allocated in the function entry but they are usable
  only after their declaration (i.e., Slet statement). TODO: add
  fn_vars to Rustsyntax and generate it in Rustsurface.ml *)
  fn_vars: list (ident * type);
  fn_params: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

(* (* Used in Rustlightown and RustIRgen *) *)
(* Fixpoint extract_vars (stmt: Rustlight.statement) : list (ident * type) := *)
(*   match stmt with *)
(*   | Slet id ty s => *)
(*       (id,ty) :: extract_vars s *)
(*   | Rustlight.Ssequence s1 s2 => *)
(*       extract_vars s1 ++ extract_vars s2 *)
(*   | Rustlight.Sifthenelse _ s1 s2 => *)
(*       extract_vars s1 ++ extract_vars s2 *)
(*   | Rustlight.Sloop s => *)
(*       extract_vars s *)
(*   | _ => nil *)
(*   end. *)

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.


Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc
  end.

(* Moved place of expressions *)

(* place with succesive Pdowncast in the end is not a valid owner. For
example, move (Pdowncast p) is equivalent to move p *)
Fixpoint valid_owner (p: place) :=
  match p with
  | Pdowncast p' _ _ => valid_owner p'
  | _ => p
  end.


Definition moved_place (e: expr) : option place :=
  match e with
  | Emoveplace p _ => Some (valid_owner p)
  | _ => None
  end.

Fixpoint moved_place_list (al: list expr) : list place :=
  match al with
  | e :: l =>
      match moved_place e with
      | Some p => p :: moved_place_list l
      | None => moved_place_list l
      end
  | nil => nil
  end.

(** Prefix of a place  *)

Fixpoint parent_places (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: parent_places p'
  | Pderef p' _ =>  p' :: parent_places p'
  | Pdowncast p' _ _ => p' :: parent_places p'
  end.

Fixpoint shallow_parent_places (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: shallow_parent_places p'
  | Pderef _ _ => nil
  (** FIXMEL: how to handle downcast? *)
  | Pdowncast p' _ _ => p' :: shallow_parent_places p'
  end.

Fixpoint support_parent_places (p: place) : list place :=
  match p with
  | Plocal _ _ => nil
  | Pfield p' _ _ => p' :: support_parent_places p'
  | Pderef p' _ =>
      match typeof_place p' with
      | Tbox _ 
      | Treference _ Mutable _ =>
          p' :: support_parent_places p'
      | Treference _ Immutable _ =>
          p' :: nil
      | _ => nil
      end
  | Pdowncast p' _ _ => p' :: support_parent_places p'
  end.


(* Similar to ProjectElem in rustc *)
Variant projection : Type :=
  | proj_deref (mut: mutkind)
  | proj_field (fid: ident)
  (* type of the variant here is used in valid_owner proof !! *)
  | proj_downcast (* (ty: type) *) (fid: ident) (* (fty: type) *)
.

Lemma projection_eq: forall (p1 p2: projection), {p1 = p2} + {p1 <> p2}.
Proof.
  generalize ident_eq type_eq mutkind_eq. intros.
  destruct p1; destruct p2; auto; try (right; congruence); decide equality.
Defined.

Definition path : Type := (ident * list projection).

Lemma path_eq: forall (p1 p2: path), {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1; destruct p2.
  destruct (ident_eq i i0); subst.
  destruct (list_eq_dec projection_eq l l0); subst. auto.
  all: right; congruence.
Defined.

Definition mutkind_of_type (ty: type) : mutkind :=
  match ty with
  | Treference _ Immutable _ => Immutable
  | _ => Mutable
  end.


(* relate place and path *)
Fixpoint path_of_place (p: place) : path :=
  match p with
  | Plocal id _ =>
      (id, nil)
  | Pderef p1 ty =>
      let (id, phl) := path_of_place p1 in      
      (id, phl ++ [proj_deref (mutkind_of_type ty)])
  | Pfield p1 fid _ =>
      let (id, phl) := path_of_place p1 in
      (id, phl ++ [proj_field fid])
  | Pdowncast p1 fid fty =>
      let (id, phl) := path_of_place p1 in
      (id, phl ++ [proj_downcast (* (typeof_place p1) *) fid (* fty *)])
  end.

Coercion path_of_place : place >-> path.

(* If ph1 is a prefix of phl2, return trues *)
Fixpoint projections_contain (phl1 phl2: list projection) : bool :=
  match phl1, phl2 with
  | nil, _ => true
  | ph1 :: phl1', ph2 :: phl2' =>
      if projection_eq ph1 ph2 then
        projections_contain phl1' phl2'
      else false
  | _, _ => false
  end.

Fixpoint projections_contain_strict (phl1 phl2: list projection) : bool :=
  match phl1, phl2 with
  | nil, nil => false
  | nil, _ => true
  | ph1 :: phl1', ph2 :: phl2' =>
      if projection_eq ph1 ph2 then
        projections_contain_strict phl1' phl2'
      else false
  | _, _ => false
  end.


Definition is_shallow_prefix_proj (phl: list projection) : bool :=
  negb (in_dec projection_eq (proj_deref Mutable) phl) && negb (in_dec projection_eq (proj_deref Immutable) phl).

Fixpoint projections_shallow_contain (phl1 phl2: list projection) : bool :=
  match phl1, phl2 with
  | nil, _ => is_shallow_prefix_proj phl2
  | ph1 :: phl1', ph2 :: phl2' =>
      if projection_eq ph1 ph2 then
        projections_shallow_contain phl1' phl2'
      else false
  | _, _ => false
  end.

(** Experiment code for new is_prefix without the comparison of type
information *)

(* The definition of is_prefix does not consider the type information
of the places. For example, (Plocal id int) is a prefix of (Pderef
(Plocal id int) int) *)
Definition is_prefix (p1 p2: place) : bool :=
  let (id1, phl1) := path_of_place p1 in
  let (id2, phl2) := path_of_place p2 in
  ident_eq id1 id2 && projections_contain phl1 phl2.

Definition is_shallow_prefix (p1 p2: place) : bool :=
  let (id1, phl1) := path_of_place p1 in
  let (id2, phl2) := path_of_place p2 in
  ident_eq id1 id2 && projections_shallow_contain phl1 phl2.


Definition is_support_prefix (p1 p2: place) : bool :=
  let phs := map path_of_place (p2 :: (support_parent_places p2)) in
  in_dec path_eq (path_of_place p1) phs.


Definition is_prefix_strict (p1 p2: place) : bool :=
  let (id1, phl1) := path_of_place p1 in
  let (id2, phl2) := path_of_place p2 in
  ident_eq id1 id2 && projections_contain_strict phl1 phl2.


Definition is_prefix_path (ph1 ph2: path) : bool := 
  let (id1, phl1) := ph1 in
  let (id2, phl2) := ph2 in
  ident_eq id1 id2 && projections_contain phl1 phl2.

Definition is_prefix_strict_path (ph1 ph2: path) : bool :=
  let (id1, phl1) := ph1 in
  let (id2, phl2) := ph2 in
  ident_eq id1 id2 && projections_contain_strict phl1 phl2.


Fixpoint local_of_place (p: place) :=
  match p with
  | Plocal id _ => id
  | Pfield p' _ _ => local_of_place p'
  | Pderef p' _ => local_of_place p'
  | Pdowncast p' _ _ => local_of_place p'
  end.

Lemma projections_contain_refl: forall l,
    projections_contain l l = true.
Proof.
  induction l; simpl; eauto.
  destruct projection_eq; try congruence; auto.
Qed.


Lemma projections_shallow_contain_refl: forall l,
    projections_shallow_contain l l = true.
Proof.
  induction l; simpl; eauto.
  destruct projection_eq; try congruence; auto.
Qed.


Lemma projections_contain_strict_not_refl: forall l,
    projections_contain_strict l l = false.
Proof.
  induction l; simpl; eauto.
  destruct projection_eq; try congruence; auto.
Qed.

Lemma projections_contain_trans: forall l1 l2 l3,
    projections_contain l1 l2 = true ->
    projections_contain l2 l3 = true ->
    projections_contain l1 l3 = true.
Proof.
  induction l1; intros; simpl in *.
  - destruct l2; simpl in *; auto.
  - destruct l2; simpl in *; auto.
    congruence.
    destruct projection_eq; try congruence. subst.
    destruct l3; try congruence.
    destruct projection_eq; eauto.
Qed.

Lemma projections_shallow_contain_is_shallow: forall l1 l2,
    projections_shallow_contain l1 l2 = true ->
    is_shallow_prefix_proj l1 = true ->
    is_shallow_prefix_proj l2 = true.
Proof.
  induction l1; intros; simpl in *; auto.
  destruct l2; try congruence.
  destruct projection_eq; subst; try congruence; auto.
  unfold is_shallow_prefix_proj in *.
  (* eapply negb_true_iff in H0. *)
  (* destruct (in_dec projection_eq proj_deref (p :: l1)); simpl in *; try congruence. *)
  (* eapply Decidable.not_or in n. destruct n. *)
  (* destruct projection_eq; try congruence. *)
  (* exploit (IHl1 l2).  auto. *)
  (* eapply negb_true_iff. destruct (in_dec projection_eq proj_deref l1); simpl; try congruence; auto. *)
  (* intros A. eapply negb_true_iff in A. *)
  (* destruct (in_dec projection_eq proj_deref l2); simpl in *; try congruence; auto.- *)
(* Qed. *)
Admitted.

Lemma projections_shallow_contain_trans: forall l1 l2 l3,
    projections_shallow_contain l1 l2 = true ->
    projections_shallow_contain l2 l3 = true ->
    projections_shallow_contain l1 l3 = true.
Proof.
  induction l1; intros; simpl in *.
  - eapply projections_shallow_contain_is_shallow; eauto.
  - destruct l2; simpl in *; auto.
    congruence.
    destruct projection_eq; try congruence. subst.
    destruct l3; try congruence.
    destruct projection_eq; eauto.
Qed.

Lemma projections_contain_strict_trans: forall l1 l2 l3,
    projections_contain_strict l1 l2 = true ->
    projections_contain_strict l2 l3 = true ->
    projections_contain_strict l1 l3 = true.
Proof.
  induction l1; intros; simpl in *.
  - destruct l2; simpl in *; auto.
    destruct l3; try congruence.
  - destruct l2; simpl in *; auto.
    congruence.
    destruct projection_eq; try congruence. subst.
    destruct l3; try congruence.
    destruct projection_eq; eauto.
Qed.

    
Ltac destr_prefix :=
  let POP1 := fresh "POP" in
  let POP2 := fresh "POP" in
  let PRE1 := fresh "PRE" in
  let PRE2 := fresh "PRE" in
  match goal with    
  | [H: is_prefix ?p1 ?p2 = true |- _ ] =>
      unfold is_prefix in H;
      destruct (path_of_place p1) eqn: POP1; try rewrite POP1 in *;
      destruct (path_of_place p2) eqn: POP2; try rewrite POP2 in *;
      erewrite andb_true_iff in H;
      destruct H as (PRE1 & PRE2);
      destruct ident_eq in PRE1; subst; simpl in *; try congruence
  | [H: is_prefix_strict ?p1 ?p2 = true |- _ ] =>
      unfold is_prefix_strict in H;
      destruct (path_of_place p1) eqn: POP1; try rewrite POP1 in *;
      destruct (path_of_place p2) eqn: POP2; try rewrite POP2 in *;
      erewrite andb_true_iff in H;
      destruct H as (PRE1 & PRE2);
      destruct ident_eq in PRE1; subst; simpl in *; try congruence
  | [H: is_shallow_prefix ?p1 ?p2 = true |- _ ] =>
      unfold is_shallow_prefix in H;
      destruct (path_of_place p1) eqn: POP1; try rewrite POP1 in *;
      destruct (path_of_place p2) eqn: POP2; try rewrite POP2 in *;
      erewrite andb_true_iff in H;
      destruct H as (PRE1 & PRE2);
      destruct ident_eq in PRE1; subst; simpl in *; try congruence
  end.

Lemma local_of_path_of_place: forall p,
    local_of_place p = fst (path_of_place p).
Proof.
  induction p; simpl; auto; destruct (path_of_place p); auto.
Qed.

Lemma is_prefix_same_local: forall p1 p2,
    is_prefix p1 p2 = true ->
    local_of_place p1 = local_of_place p2.
Proof.
  intros. 
  rewrite !local_of_path_of_place. destr_prefix.
Qed.  


Lemma is_prefix_strict_trans p1 p2 p3:
  is_prefix_strict p1 p2 = true ->
  is_prefix_strict p2 p3 = true ->
  is_prefix_strict p1 p3 = true.
Proof.
  intros. unfold is_prefix_strict.
  repeat destr_prefix. inv POP.
  eapply andb_true_iff. split; auto.
  destruct ident_eq; try congruence; auto.
  eapply projections_contain_strict_trans; eauto.
Qed.

Lemma is_prefix_refl: forall p, is_prefix p p = true.
Proof.
  intros. unfold is_prefix.
  destruct (path_of_place p) eqn: POP.
  eapply andb_true_iff. split. destruct ident_eq; try congruence; auto.
  eapply projections_contain_refl.
Qed.

Lemma is_prefix_trans: forall p1 p2 p3,
    is_prefix p1 p2 = true -> 
    is_prefix p2 p3 = true ->
    is_prefix p1 p3 = true.
Proof.
  intros. unfold is_prefix. repeat destr_prefix. inv POP.
  eapply andb_true_iff. split.
  destruct ident_eq; try congruence; auto.
  eapply projections_contain_trans; eauto.
Qed.

Lemma projections_contain_antisym: forall l1 l2,
    projections_contain_strict l1 l2 = true ->
    projections_contain l2 l1 = false.
Proof.
  induction l1; intros; simpl in *; auto.
  - destruct l2; try congruence. auto.
  - destruct l2; try congruence. auto.
    simpl. destruct projection_eq; subst; try destruct projection_eq; try congruence.
    auto.
Qed.
        
Lemma is_prefix_antisym: forall p1 p2,
    is_prefix_strict p1 p2 = true ->
    is_prefix p2 p1 = false.
Proof.
  intros. unfold is_prefix.
  destr_prefix. eapply andb_false_iff. right.
  eapply projections_contain_antisym. eauto.  
Qed.

Lemma projections_contain_app: forall l1 l2,
    projections_contain l1 (l1 ++ l2) = true.
Proof.
  induction l1; simpl; intros; auto.
  destruct projection_eq; try congruence.
Qed.

Lemma projections_contain_strict_app: forall l1 l2,
    l2 <> nil ->
    projections_contain_strict l1 (l1 ++ l2) = true.
Proof.
  induction l1; simpl; intros; auto.
  destruct l2; try congruence.
  destruct projection_eq; try congruence.
  eapply IHl1. auto.
Qed.

Lemma is_prefix_valid_owner: forall p,
    is_prefix (valid_owner p) p = true.
Proof.
  induction p.
  - simpl. eapply is_prefix_refl.
  - simpl. eapply is_prefix_refl.
  - simpl. eapply is_prefix_refl.
  - simpl. eapply is_prefix_trans; eauto.
    unfold is_prefix. simpl.
    destruct (path_of_place p) eqn: POP.
    eapply andb_true_iff.
    split.
    destruct ident_eq; try congruence; auto.
    eapply projections_contain_app; eauto.
Qed.

Ltac solve_prefix_left :=
  try (eapply andb_true_iff; split;
       [destruct ident_eq; try congruence; auto|]).

Lemma projections_contain_strict_trans2: forall l1 l2 l3,
    projections_contain l1 l2 = true ->
    projections_contain_strict l2 l3 = true ->
    projections_contain_strict l1 l3 = true.
Proof.
  induction l1; intros; simpl in *.
  - destruct l2; simpl in *; auto.
    destruct l3; try congruence.
  - destruct l2; simpl in *; auto.
    congruence.
    destruct projection_eq; try congruence. subst.
    destruct l3; try congruence.
    destruct projection_eq; eauto.
Qed.

Lemma projections_contain_strict_trans3: forall l1 l2 l3,
    projections_contain_strict l1 l2 = true ->
    projections_contain l2 l3 = true ->        
    projections_contain_strict l1 l3 = true.
Proof.
  induction l1; intros; simpl in *.
  - destruct l2; simpl in *; auto. congruence.
    destruct l3; try congruence.
  - destruct l2; simpl in *; auto.
    congruence.
    destruct projection_eq; try congruence. subst.
    destruct l3; try congruence.
    destruct projection_eq; eauto.
Qed.


(* similar to is_prefix_strict_trans_prefix *)
Lemma is_prefix_strict_trans_prefix2: forall p1 p2 p3,
    is_prefix p1 p2 = true ->
    is_prefix_strict p2 p3 = true ->
    is_prefix_strict p1 p3 = true.
Proof.
  intros. unfold is_prefix_strict.
  repeat destr_prefix. inv POP0.
  solve_prefix_left.
  eapply projections_contain_strict_trans2; eauto.
Qed.

Lemma projections_contain_strict_implies: forall l1 l2,
    projections_contain_strict l1 l2 = true ->
    projections_contain l1 l2 = true.
Proof.
  induction l1; simpl; intros; auto.
  destruct l2; try congruence.
  destruct projection_eq; subst; auto.
Qed.

  
Lemma is_prefix_strict_implies: forall p1 p2,
    is_prefix_strict p1 p2 = true ->
    is_prefix p1 p2 = true.
Proof.
  intros. unfold is_prefix. destr_prefix.
  solve_prefix_left.
  eapply projections_contain_strict_implies. auto.
Qed.

Lemma is_prefix_strict_not_refl: forall p,
    is_prefix_strict p p = false.
Proof.
  intros. unfold is_prefix_strict.
  destruct (path_of_place p).
  eapply andb_false_iff. right.
  eapply projections_contain_strict_not_refl.
Qed.


Lemma projections_shallow_contain_implies: forall l1 l2,
    projections_shallow_contain l1 l2 = true ->
    projections_contain l1 l2 = true.
Proof.
  induction l1; intros; simpl in *.
  - auto.
  - destruct l2; simpl in *; auto.
    destruct projection_eq; try congruence. subst. auto.
Qed.
    
  
Lemma is_shallow_prefix_is_prefix: forall p1 p2,
    is_shallow_prefix p1 p2 = true ->
    is_prefix p1 p2 = true.
Proof.
  intros. unfold is_prefix.
  destr_prefix. solve_prefix_left.
  eapply projections_shallow_contain_implies; auto.
Qed.

Lemma is_prefix_strict_trans_prefix: forall p1 p2 p3,
    is_prefix_strict p1 p2 = true ->
    is_prefix p2 p3 = true ->
    is_prefix_strict p1 p3 = true.
Proof.
  intros. unfold is_prefix_strict.
  repeat destr_prefix. inv POP.
  solve_prefix_left.
  eapply projections_contain_strict_trans3; eauto.
Qed.
  
Lemma is_shallow_prefix_refl: forall p,
    is_shallow_prefix p p = true.
Proof.
  intros. unfold is_shallow_prefix.
  destruct (path_of_place p).
  solve_prefix_left.
  eapply projections_shallow_contain_refl.
Qed.

Lemma is_shallow_prefix_trans: forall p1 p2 p3,
    is_shallow_prefix p1 p2 = true ->
    is_shallow_prefix p2 p3 = true ->
    is_shallow_prefix p1 p3 = true.
Proof.
  intros. unfold is_shallow_prefix. repeat destr_prefix.
  inv POP. solve_prefix_left.
  eapply projections_shallow_contain_trans; eauto.
Qed.

Lemma is_shallow_prefix_same_local: forall p1 p2,
    is_shallow_prefix p1 p2 = true ->
    local_of_place p1 = local_of_place p2.
Proof.
  intros. apply is_shallow_prefix_is_prefix in H.
  eapply is_prefix_same_local; eauto.
Qed.

Lemma valid_owner_same_local: forall p,
    local_of_place (valid_owner p) = local_of_place p.
Proof.
  induction p; simpl; auto.
Qed.

Lemma projections_not_contain_strict: forall l1 l2,
    projections_contain l1 l2 = false ->
    projections_contain l2 l1 = true ->
    projections_contain_strict l2 l1 = true.
Proof.
  induction l1; intros; simpl in *.
  congruence.
  destruct l2; simpl in *. auto.
  destruct projection_eq; subst; try destruct projection_eq in *; try congruence.
  eauto.
Qed.

Lemma is_not_prefix_strict: forall p1 p2,
    is_prefix p1 p2 = false ->
    is_prefix p2 p1 = true ->
    is_prefix_strict p2 p1 = true.
Proof.
  intros. unfold is_prefix_strict.
  repeat destr_prefix.
  solve_prefix_left.
  unfold is_prefix in H. rewrite POP in H. rewrite POP0 in H.
  destruct ident_eq in H; simpl in *; try congruence.
  eapply projections_not_contain_strict; auto.
Qed.                                    
  
(** Some trivial is_prefix lemma  *)

Lemma is_prefix_field: forall p1 fid fty,
    is_prefix p1 (Pfield p1 fid fty) = true.
Proof.
  intros. unfold is_prefix. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_app.
Qed.

Lemma is_prefix_strict_field: forall p1 fid fty,
    is_prefix_strict p1 (Pfield p1 fid fty) = true.
Proof.
  intros. unfold is_prefix_strict. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_strict_app.
  congruence.
Qed.

Lemma is_prefix_downcast: forall p1 fid fty,
    is_prefix p1 (Pdowncast p1 fid fty) = true.
Proof.
  intros. unfold is_prefix. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_app.
Qed.

Lemma is_prefix_strict_downcast: forall p1 fid fty,
    is_prefix_strict p1 (Pdowncast p1 fid fty) = true.
Proof.
  intros. unfold is_prefix_strict. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_strict_app.
  congruence.
Qed.


Lemma is_prefix_deref: forall p1 ty,
    is_prefix p1 (Pderef p1 ty) = true.
Proof.
  intros. unfold is_prefix. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_app.
Qed.

Lemma is_prefix_strict_deref: forall p1 ty,
    is_prefix_strict p1 (Pderef p1 ty) = true.
Proof.
  intros. unfold is_prefix_strict. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_contain_strict_app.
  congruence.
Qed.

(** Alternative definition of is_prefix which considers the type information *)

Definition is_prefix_type (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (parent_places p2).

Lemma In_place_trans: forall p3 p1 p2, In p1 (parent_places p2) ->
In p2 (parent_places p3) -> In p1 (parent_places p3).
Proof.
  induction p3; 
  simpl in *; try intros; auto.
  - destruct H0. subst.
    + auto.
    + right. apply IHp3 with p2. apply H. apply H0.
  - destruct H0. subst.
    + auto.
    + right. eapply IHp3. eapply H. apply H0.
  - destruct H0. subst.
    + auto.
    + right. eapply IHp3. eapply H. apply H0.
Qed.


Lemma in_parent_projection_is_prefix: forall p2 p1,
    In p1 (parent_places p2) ->
    is_prefix p1 p2 = true.
Proof.
  induction p2; intros p1 IN; simpl in *.
  - contradiction.
  - destruct IN; subst.
    + eapply is_prefix_field.
    + eapply is_prefix_trans. eapply IHp2; eauto.
      eapply is_prefix_field.
  - destruct IN; subst.
    + eapply is_prefix_deref.
    + eapply is_prefix_trans. eapply IHp2; eauto.
      eapply is_prefix_deref.
  - destruct IN; subst.
    + eapply is_prefix_downcast.
    + eapply is_prefix_trans. eapply IHp2; eauto.
      eapply is_prefix_downcast.
Qed.
      
Lemma is_prefix_type_is_prefix: forall p2 p1,
    is_prefix_type p1 p2 = true ->
    is_prefix p1 p2 = true.
Proof.
  intros p2 p1 PRE.
  unfold is_prefix_type in PRE.
  eapply orb_true_iff in PRE. destruct PRE.
  apply proj_sumbool_true in H. subst.
  apply is_prefix_refl.
  apply proj_sumbool_true in H.
  eapply in_parent_projection_is_prefix. auto.
Qed.


Lemma projections_shallow_contain_app: forall l1 l2,
    is_shallow_prefix_proj l2 = true ->
    projections_shallow_contain l1 (l1 ++ l2) = true.
Proof.
  induction l1; simpl; intros; auto.
  destruct projection_eq; try congruence. eauto.
Qed.


Lemma is_shallow_prefix_downcast: forall p1 fid fty,
    is_shallow_prefix p1 (Pdowncast p1 fid fty) = true.
Proof.
  intros. unfold is_shallow_prefix. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_shallow_contain_app.
  unfold is_shallow_prefix_proj.
  destruct in_dec; try congruence; simpl in *; auto.
  destruct i0; try contradiction. inv H.
Qed.

Lemma is_shallow_prefix_field: forall p1 fid fty,
    is_shallow_prefix p1 (Pfield p1 fid fty) = true.
Proof.
  intros. unfold is_shallow_prefix. simpl.
  destruct (path_of_place p1).
  solve_prefix_left.
  eapply projections_shallow_contain_app.
  unfold is_shallow_prefix_proj.
  destruct in_dec; try congruence; simpl in *; auto.
  destruct i0; try contradiction. inv H.
Qed.

Lemma valid_owner_is_shallow_prefix: forall p,
    is_shallow_prefix (valid_owner p) p = true.
Proof.
  induction p; simpl; try apply is_shallow_prefix_refl.
  eapply is_shallow_prefix_trans. eauto.
  eapply is_shallow_prefix_downcast.
Qed.

(** shallow and support prefix path  *)

(* The projected locaiton can be mutated *)
Definition is_support_prefix_proj (phl: list projection) : bool :=
  negb (in_dec projection_eq (proj_deref Immutable) phl).

Fixpoint projections_support_contain (phl1 phl2: list projection) : bool :=
  match phl1, phl2 with
  | nil, _ => is_support_prefix_proj phl2
  | ph1 :: phl1', ph2 :: phl2' =>
      if projection_eq ph1 ph2 then
        projections_support_contain phl1' phl2'
      else false
  | _, _ => false
  end.

Definition is_shallow_prefix_path (ph1 ph2: path) : bool := 
  let (id1, phl1) := ph1 in
  let (id2, phl2) := ph2 in
  ident_eq id1 id2 && projections_shallow_contain phl1 phl2.

Definition is_support_prefix_path (ph1 ph2: path) : bool := 
  let (id1, phl1) := ph1 in
  let (id2, phl2) := ph2 in
  ident_eq id1 id2 && projections_support_contain phl1 phl2.


(*

Definition is_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (parent_places p2).

Definition is_shallow_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (shallow_parent_places p2).

Definition is_support_prefix (p1 p2: place) : bool :=
  place_eq p1 p2 || in_dec place_eq p1 (support_parent_places p2).

Definition is_prefix_strict (p1 p2: place) : bool :=
  in_dec place_eq p1 (parent_places p2).


Lemma In_place_no_refl: forall p, ~In p (parent_places p).
Proof.
  unfold not. intros.  
  induction p. 
  - simpl in H. apply H.
  - simpl in H. destruct H.
    + apply IHp. 
      rewrite H at 2. simpl. left. reflexivity.
    + apply IHp. remember (Pfield p i t) as p'.
      assert (HF: In p (parent_places p')). rewrite Heqp'.
      simpl. left. reflexivity.
      eapply In_place_trans. eauto. eauto.
  - simpl in H. destruct H.
    + apply IHp. 
      rewrite H at 2. simpl. left. reflexivity.
    + apply IHp. remember (Pderef p t) as p'.
      assert (HF: In p (parent_places p')). rewrite Heqp'.
      simpl. left. reflexivity.
      eapply In_place_trans. eauto. eauto.
  - simpl in H. destruct H.
    + apply IHp. 
      rewrite H at 2. simpl. left. reflexivity.
    + apply IHp. remember (Pdowncast p i t) as p'.
      assert (HF: In p (parent_places p')). rewrite Heqp'.
      simpl. left. reflexivity.
      eapply In_place_trans. eauto. eauto.
Qed.

Lemma In_place_no_eql: forall p1 p2, In p1 (parent_places p2) ->
  p1 <> p2. 
Proof.
  intros. destruct (place_eq p1 p2).
  - subst. apply In_place_no_refl in H. contradiction.
  - apply n.
Qed.

Lemma is_prefix_strict_trans p1 p2 p3:
  is_prefix_strict p1 p2 = true ->
  is_prefix_strict p2 p3 = true ->
  is_prefix_strict p1 p3 = true.
Proof.
unfold is_prefix_strict. intros. 
destruct in_dec in H; cbn in * |-.
- destruct in_dec in H0; cbn in * |-.
  + destruct in_dec.
    * auto.
    * apply (In_place_trans p3 p1 p2 i) in i0. contradiction.
  + discriminate.
- discriminate.
Qed.

Lemma is_prefix_refl: forall p, is_prefix p p = true.
Proof.
  intros. unfold is_prefix. 
  unfold orb. destruct (place_eq p p).
  - simpl. reflexivity.
  - simpl. destruct in_dec.
    + auto.
    + auto.
Qed.

Lemma is_prefix_trans: forall p1 p2 p3, is_prefix p1 p2 = true -> 
is_prefix p2 p3 = true -> is_prefix p1 p3 = true.
Proof.
  unfold is_prefix. intros. unfold orb in *. destruct (place_eq p1 p3).
  - simpl. reflexivity.
  - simpl. destruct (place_eq p1 p2); simpl in *.
    + destruct (place_eq p2 p3); simpl in *.
      * subst. contradiction.
      * subst. auto.
    + destruct (place_eq p2 p3); simpl in *.
      * subst. auto.
      * apply (is_prefix_strict_trans p1 p2 p3 H H0).
Qed.

Lemma is_prefix_antisym: forall p1 p2,
    is_prefix_strict p1 p2 = true ->
    is_prefix p2 p1 = false.
Proof.
  unfold is_prefix, is_prefix_strict. intros. unfold orb in *.
  destruct (place_eq p2 p1); simpl; try congruence; auto.
  - subst. destruct in_dec in H; cbn in * |-. 
    apply In_place_no_eql in i. contradiction.
    discriminate.
  - destruct in_dec in *; cbn in * |-.
    destruct in_dec; simpl; try congruence; auto.
    eapply In_place_trans in i0. 2:{ eapply i. } 
    apply In_place_no_eql in i0. contradiction.
    discriminate.
Qed.

Lemma is_prefix_valid_owner: forall p,
    is_prefix (valid_owner p) p = true.
Proof.
  intros. unfold is_prefix. unfold orb.
  destruct (place_eq (valid_owner p) p); simpl; auto.
  destruct in_dec; simpl; auto. exfalso. apply n0.
  unfold valid_owner.
  induction p; unfold parent_places; simpl in *; try congruence.
  right.
  apply IHp. eapply Decidable.not_or in n0; destruct n0; auto.
  eapply Decidable.not_or in n0; destruct n0; auto.
Qed.

(* similar to is_prefix_strict_trans_prefix *)
Lemma is_prefix_strict_trans_prefix2: forall p1 p2 p3,
    is_prefix p1 p2 = true ->
    is_prefix_strict p2 p3 = true ->
    is_prefix_strict p1 p3 = true.
Proof.
  unfold is_prefix, is_prefix_strict. intros. unfold orb in *.
  destruct (place_eq p1 p2); simpl in *; try congruence; subst; auto.
  destruct in_dec in *; simpl in *; try congruence; subst; auto.
  destruct in_dec in *; simpl in *; try congruence; subst; auto.
  destruct in_dec in *; simpl in *; try congruence; subst; auto.
  exfalso. apply n0. eapply In_place_trans; eauto.
Qed.


Lemma is_prefix_strict_implies: forall p1 p2,
    is_prefix_strict p1 p2 = true ->
    is_prefix p1 p2 = true.
Proof.
  intros. unfold is_prefix. unfold is_prefix_strict in H.
  unfold orb. destruct (place_eq p1 p2).
  - reflexivity.
  - simpl. auto.
Qed.

Lemma is_prefix_strict_not_refl: forall p,
    is_prefix_strict p p = false.
Proof.
  intros. unfold is_prefix_strict. destruct in_dec; cbn in *.
  apply In_place_no_refl in i. contradiction.
  reflexivity.
Qed.

Lemma is_prefix_strict_iff: forall p1 p2,
    is_prefix_strict p1 p2 = true <-> (is_prefix p1 p2 = true /\ p1 <> p2).
Proof.
  intros. split; intros.
  - split.
    + apply is_prefix_strict_implies. apply H.
    + unfold not. intros. subst. rewrite is_prefix_strict_not_refl in H.
      discriminate.
  - destruct H as [H1 H2].
    unfold is_prefix_strict. unfold is_prefix in H1. unfold orb in H1.
    destruct (place_eq p1 p2); simpl in *.
    + contradiction.
    + auto.
Qed.


Lemma is_shallow_prefix_is_prefix: forall p1 p2,
    is_shallow_prefix p1 p2 = true ->
    is_prefix p1 p2 = true.
Proof.
  intros. unfold is_shallow_prefix in H. unfold is_prefix.
  unfold orb in H. destruct (place_eq p1 p2); simpl in *.
  reflexivity.
  induction p2; simpl in *; auto.
  - destruct (place_eq p2 p1);simpl in *; auto.
    destruct (in_dec place_eq p1 (shallow_parent_places p2)).
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
  - destruct (place_eq p2 p1);simpl in *; auto.
    destruct (in_dec place_eq p1 (shallow_parent_places p2)).
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
  - destruct (place_eq p2 p1);simpl in *; auto.
    destruct (in_dec place_eq p1 (shallow_parent_places p2)).
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
    destruct (in_dec place_eq p1 (parent_places p2)); simpl; auto.
Qed.

Lemma is_prefix_strict_trans_prefix: forall p1 p2 p3,
    is_prefix_strict p1 p2 = true ->
    is_prefix p2 p3 = true ->
    is_prefix_strict p1 p3 = true.
Proof.
  intros. rewrite is_prefix_strict_iff in H. destruct H as [H1 H2].
  destruct (place_eq p2 p3).
  - subst. rewrite is_prefix_strict_iff. auto.
  - assert(H3:is_prefix_strict p1 p2 = true). apply is_prefix_strict_iff.
    auto.
    assert(H4:is_prefix_strict p2 p3 = true). apply is_prefix_strict_iff.
    auto.
    apply is_prefix_strict_trans with p2. auto. auto.
Qed.

Lemma is_shallow_prefix_refl: forall p,
    is_shallow_prefix p p = true.
Proof.
  intros. unfold is_shallow_prefix. unfold orb.
  destruct (place_eq p p); simpl; auto.
Qed.

Lemma in_shallow_parent_projection_trans: forall p3 p2 p1,
    In p1 (shallow_parent_places p2) ->
    In p2 (shallow_parent_places p3) ->
    In p1 (shallow_parent_places p3).
Proof.
  induction p3; simpl in *; intros; try contradiction.
  - destruct H0.
    + subst. destruct (place_eq p2 p1); auto.
    + right. eapply IHp3. eauto. auto.
  - destruct H0.
    + subst. destruct (place_eq p2 p1); auto.
    + right. eapply IHp3. eauto. auto.
Qed.

Lemma is_shallow_prefix_trans: forall p1 p2 p3,
    is_shallow_prefix p1 p2 = true ->
    is_shallow_prefix p2 p3 = true ->
    is_shallow_prefix p1 p3 = true.
Proof.
  intros. unfold is_shallow_prefix in *.
  destruct (place_eq p1 p2); destruct (place_eq p2 p3); destruct (place_eq p1 p3); subst; try congruence; auto.
  simpl in *.
  repeat destruct in_dec; simpl in *; try congruence.
  exfalso. eapply n2.
  eapply in_shallow_parent_projection_trans; eauto.
Qed.

Lemma is_shallow_prefix_same_local: forall p1 p2,
    is_shallow_prefix p1 p2 = true ->
    local_of_place p1 = local_of_place p2.
Proof.
  intros. apply is_shallow_prefix_is_prefix in H.
  eapply is_prefix_same_local; eauto.
Qed.

Lemma valid_owner_same_local: forall p,
    local_of_place (valid_owner p) = local_of_place p.
Proof.
  induction p; simpl; auto.
Qed.

*)

Definition is_sibling (p1 p2: place) : bool :=
  Pos.eqb (local_of_place p1) (local_of_place p2)
  && negb (is_prefix p1 p2 && is_prefix p2 p1).

Fixpoint local_type_of_place (p: place) :=
  match p with
  | Plocal id ty => ty
  | Pfield p' ty _ => local_type_of_place p'
  | Pderef p' ty => local_type_of_place p'
  | Pdowncast p' _ _ => local_type_of_place p'
  end.
  

(** Classify function (copy from Cop.v)  *)
Inductive classify_fun_cases : Type :=
| fun_case_f (targs: typelist) (tres: type) (cc: calling_convention) (**r (pointer to) function *)
| fun_default.

Definition classify_fun (ty: type) :=
  match ty with
  | Tfunction _ _ args res cc => fun_case_f args res cc
  (** TODO: do we allow function pointer?  *)
  (* | Treference (Tfunction args res cc) _ => fun_case_f args res cc *)
  | _ => fun_default
  end.
  
Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.

Definition vars_to_drops (vars: list (ident * type)) : list place :=
  map (fun elt => Plocal (fst elt) (snd elt)) (filter (fun elt => drop_type (snd elt)) vars).

(** ** Notations of Rustlight program *)

Declare Custom Entry rustlight.
Declare Scope rustlight_scope.
Declare Custom Entry rustlight_aux.
Declare Custom Entry rustlight_place.
Declare Custom Entry rustlight_expr.

Notation "<{ s }>" := s (s custom rustlight_aux) : rustlight_scope.
Notation "s" := s (in custom rustlight_aux at level 0, s custom rustlight) : rustlight_scope.

(* Notations for statement (level > 50) *)
Notation "'if' e 'then' s1 'else' s2 'fi'" := (Sifthenelse e s1 s2) (in custom rustlight at level 80, e custom rustlight_expr at level 20, s1 at level 99, s2 at level 99) : rustlight_scope.
Notation "s1 ; s2" := (Ssequence s1 s2) (in custom rustlight at level 99, right associativity) : rustlight_scope.
Notation "'skip'" := Sskip (in custom rustlight at level 0) : rustlight_scope.
Notation "'break'" := Sbreak (in custom rustlight at level 0) : rustlight_scope.
Notation "'continue'" := Scontinue (in custom rustlight at level 0) : rustlight_scope.
(* Notation "'return0'" := (Sreturn None) (in custom rustlight at level 0) : rustlight_scope. *)
Notation "'return' p" := (Sreturn p) (in custom rustlight at level 80, p custom rustlight_place at level 20) : rustlight_scope.
Notation "'let' x : t 'in' s 'end' " := (Slet x t s) (in custom rustlight at level 80, s at level 99, x global, t global) : rustlight_scope.
Notation "'loop' s 'end'" := (Sloop s) (in custom rustlight at level 80, s at level 99) : rustlight_scope.
Notation "p :=b e " := (Sbox p e) (in custom rustlight at level 80, p custom rustlight_place at level 20, e custom rustlight_expr at level 20) : rustlight_scope.
Notation " p := e " := (Sassign p e) (in custom rustlight at level 80, p custom rustlight_place at level 20, e custom rustlight_expr at level 15) : rustlight_scope.
Notation " p :=v f1 :: f2 ( e ) " := (Sassign_variant p f1 f2 e) (in custom rustlight at level 80, p custom rustlight_place at level 20, e custom rustlight_expr at level 15, f1 global, f2 global) : rustlight_scope.
Notation " p <- f < fty > @ l " := (Scall p (Eglobal f fty)l) (in custom rustlight at level 80, p custom rustlight_place at level 20, f global, fty global, l custom rustlight_expr at level 20) : rustlight_scope.


(* Notation for place *)

Notation " ( x ) " := x (in custom rustlight_place at level 20) : rustlight_scope.
Notation " x # t " := (Plocal x t) (in custom rustlight_place at level 0, x global, t global) : rustlight_scope.
Notation " ! p " := (Pderef p (deref_type (typeof_pexpr p))) (in custom rustlight_place at level 10, p at level 20) : rustlight_scope.
Notation " p 'proj' x < t > " := (Pfield p x t) (in custom rustlight_place at level 10, x global, t global) : rustlight_scope.
Notation " p 'as' x < t > " := (Pdowncast p x t) (in custom rustlight_place at level 10, x global, t global) : rustlight_scope.


(* Notations for expression. Expression is at level 20 *)

Notation " ( x ) " := x (in custom rustlight_expr at level 20) : rustlight_scope.
Notation " 'pure' x " := (Epure x) (in custom rustlight_expr at level 20) : rustlight_scope.
Notation " { x , .. , y } " := (cons x .. (cons y nil) .. ) (in custom rustlight_expr at level 20) : rustlight_scope.
Notation " e1 < e2 " := ((Ebinop Ole e1 e2 type_bool)) (in custom rustlight_expr at level 15, e1 custom rustlight_expr, e2 custom rustlight_expr at level 20, left associativity) : rustlight_scope.
Notation " $ k " := ((Econst_int (Int.repr k) type_int32s)) (in custom rustlight_expr at level 10, k constr) : rustlight_scope.
Notation " 'Ett' " := Eunit (in custom rustlight_expr at level 10) : rustlight_scope.
Notation " e1 * e2 " := ((Ebinop Omul e1 e2 (typeof e1)))  (in custom rustlight_expr at level 15, e1 custom rustlight_expr, e2 custom rustlight_expr at level 20, left associativity) : rustlight_scope.
Notation " e1 - e2 " := ((Ebinop Osub e1 e2 (typeof e1)))  (in custom rustlight_expr at level 15, e1 custom rustlight_expr, e2 custom rustlight_expr at level 20, left associativity) : rustlight_scope.
Notation " e1 % e2 " := ((Ebinop Omod e1 e2 (typeof e1)))  (in custom rustlight_expr at level 15, e1 custom rustlight_expr, e2 custom rustlight_expr at level 20, left associativity) : rustlight_scope.
Notation " e1 == e2 " := ((Ebinop Oeq e1 e2 type_bool))  (in custom rustlight_expr at level 15, e1 custom rustlight_expr, e2 custom rustlight_expr at level 20, left associativity) : rustlight_scope.
Notation " 'copy' p " := ((Eplace p (typeof_place p))) (in custom rustlight_expr at level 20, p custom rustlight_place at level 20) : rustlight_scope.
Notation " 'move' p " := (Emoveplace p (typeof_place p)) (in custom rustlight_expr at level 20, p custom rustlight_place at level 20) : rustlight_scope.
Notation " 'cktag' p 'is' x " := (Ecktag p x) (in custom rustlight_expr at level 20, p custom rustlight_place at level 20, x global) : rustlight_scope.


(* Print Grammar constr. *)

Local Open Scope rustlight_scope.

Definition A : ident := 1%positive.
Definition B : ident := 2%positive.
Definition C : ident := 3%positive.
Definition D : ident := 4%positive.
Definition E : ident := 5%positive.


(* Print Custom Grammar rustlight. *)

Definition ident_to_place_int32s (id: ident) : place := Plocal id type_int32s.

Definition place_to_pexpr (p: place) : pexpr := (Eplace p (typeof_place p)).

Definition pexpr_to_expr (pe: pexpr) : expr := Epure pe.

Coercion ident_to_place_int32s : ident >-> place.
Coercion place_to_pexpr: place >-> pexpr.
Coercion pexpr_to_expr: pexpr >-> expr.

Fail Definition test_option_ident_to_expr : option expr  := Some A.
Definition test_option_ident_to_expr : option expr  := @Some expr A.

(* Print Graph. *)
(* Print Coercion Path ident expr. *)

Definition test : statement :=
  <{ let A : type_int32s in
     A#type_int32s := $1;
     A#type_int32s := $0;
     return (A#type_int32s);
     skip; break; return (A#type_int32s);
     if (($1) < ($0)) then
       B#type_int32s := copy C#type_int32s;
       A#type_int32s := copy B#type_int32s
     else
       A#type_int32s := copy C#type_int32s
     fi;
     loop
       A#type_int32s := copy C#type_int32s;
       B#type_int32s := copy A#type_int32s
     end;
     return (A#type_int32s)
     end }>.

(** ** Pretty printing for Rustlight programs  *)
