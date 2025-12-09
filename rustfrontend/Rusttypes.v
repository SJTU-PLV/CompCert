(** Type for Rustlight languages  *)

Require Import Axioms Coqlib Maps Errors.
Require Import AST Linking.
Require Import Ctypes.
Require Archi.

Set Asymmetric Patterns.

Local Open Scope error_monad_scope.

Inductive usekind : Type :=
| Copy
| Move.                        (**r used for types that are unsafe for copying *)


Inductive mutkind : Type :=
| Mutable
| Immutable.

Lemma mutkind_eq : forall (mut1 mut2 : mutkind), {mut1 = mut2} + {mut1 <> mut2}.
Proof.
  decide equality.
Defined.


Inductive flow_kind : Type := ByVal | ByRef.

Lemma flow_kind_eq : forall (fk1 fk2 : flow_kind), {fk1 = fk2} + {fk1 <> fk2}.
Proof.
  decide equality.
Defined.

Definition meet_flow_kinds (fk1 fk2: flow_kind) :=
  match fk1, fk2 with
  | ByRef, _ 
  | _, ByRef => ByRef
  | _, _ => ByVal
  end.

(** ** Origins  *)

Definition origin : Type := positive.

(* (org1, org2) means org1 is subset of org2 *)
Definition origin_rel : Type := origin * origin.

Lemma origin_rel_eq_dec : forall (p1 p2 : origin_rel) , {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1, p2.
  generalize Pos.eq_dec. intros.
  decide equality.
Defined.  


(** ** Types  *)

Inductive type : Type :=
| Tunit: type                                    (**r the [unit] type *)
| Tint: intsize -> signedness -> type       (**r integer types *)
| Tlong : signedness -> type
| Tfloat : floatsize -> type
| Tfunction: list origin -> list origin_rel -> typelist -> type -> calling_convention -> type    (**r function types *)
| Tbox: type -> type                                         (**r unique pointer  *)
| Treference: origin -> mutkind -> type -> type (**r reference type  *)
| Tarray: type -> Z -> type                    (**r array type, just used for constant string for now *)
| Tstruct: list origin -> ident -> type                              (**r struct types  *)
| Tvariant: list origin -> ident -> type                             (**r tagged variant types *)
with typelist : Type :=
| Tnil: typelist
| Tcons: type -> typelist -> typelist.


Fixpoint type_list_of_typelist (tl: typelist) : list type :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => hd :: type_list_of_typelist tl
  end.

Definition type_int32s := Tint I32 Signed.
Definition type_bool := Tint IBool Signed.  

Definition deref_type (ty: type) : type :=
  match ty with
  | Tbox ty' => ty'
  | Treference _ _ ty' => ty'
  | _ => Tunit
  end.

Definition return_type (ty: type) : type :=
  match ty with
  | Tfunction _ _ _ ty _ => ty
  | _ => Tunit
  end.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}.
Proof.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  generalize list_eq_dec Pos.eq_dec origin_rel_eq_dec ident_eq zeq bool_dec ident_eq intsize_eq signedness_eq attr_eq; intros.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
  decide equality.
Defined.
  

Global Opaque type_eq typelist_eq.

(* type equal except origins *)

Fixpoint type_eq_except_origins (ty1 ty2: type) : bool :=
  match ty1, ty2 with
  | Treference _ mut1 ty1, Treference _ mut2 ty2 =>
      match mut1, mut2 with
      | Mutable, Mutable => type_eq_except_origins ty1 ty2
      | Immutable, Immutable => type_eq_except_origins ty1 ty2
      | _, _ => false
      end
  | Tbox ty1, Tbox ty2 => type_eq_except_origins ty1 ty2
  | Tstruct _ id1, Tstruct _ id2
  | Tvariant _ id1, Tvariant _ id2 =>
      ident_eq id1 id2
  | _, _ => type_eq ty1 ty2
  end.

Lemma type_eq_except_origins_sym: forall ty1 ty2,
    type_eq_except_origins ty1 ty2 = type_eq_except_origins ty2 ty1.
Proof.
  induction ty1; destruct ty2; simpl; try auto.
  all: try unfold proj_sumbool; try eapply dec_eq_sym.
  destruct m; destruct m0; auto.
Qed.

Lemma type_eq_except_origins_refl: forall ty,
    type_eq_except_origins ty ty = true.
Proof.
  induction ty; simpl; auto.
  all: try unfold proj_sumbool; try eapply dec_eq_true.
  destruct m; auto.
Qed.

Fixpoint origins_of_type (ty: type) : list origin :=
  match ty with
  | Tbox ty => origins_of_type ty
  | Treference org _ ty => org :: origins_of_type ty
  | Tstruct orgs _ 
  | Tvariant orgs _ =>
      orgs
  | _ => nil
  end.

Fixpoint origin_in_type org ty : bool :=
  match ty with
  | Tbox ty => origin_in_type org ty
  | Treference org' _ ty =>
    Pos.eqb org org' || origin_in_type org ty
  | Tarray ty _ => origin_in_type org ty
  | Tstruct orgs _ 
  | Tvariant orgs _ =>
      in_dec Pos.eq_dec org orgs
  | _ => false
  end.

Fixpoint replace_type_with_dummy_origin (dummy: origin) (ty: type) : type :=
  match ty with
  | Tbox ty => Tbox (replace_type_with_dummy_origin dummy ty)
  | Treference _ mut ty =>
      Treference dummy mut (replace_type_with_dummy_origin dummy ty)
  | Tarray ty sz =>
      Tarray (replace_type_with_dummy_origin dummy ty) sz
  | Tstruct orgs id =>
      Tstruct (map (fun _ => dummy) orgs) id
  | Tvariant orgs id =>
      Tvariant (map (fun _ => dummy) orgs) id
  | _ => ty                      (* Is it correct? *)
  end.

Definition find_elt {A: Type} (id: ident) (l: list (ident * A)) : option A :=
  match find (fun '(id', v) => ident_eq id id') l with
  | Some (_, v) => Some v
  | None => None
  end.

(** TODO: use a map to maintain the substitution information *)
(* replace org with the the origin in rels *)
Definition replace_origin (rels: list (origin * origin)) (org: origin) : origin :=
  match find_elt org rels with
  | Some org' =>
      org'
  | None =>
      org
  end.

Fixpoint replace_origin_in_origin_rels (rels: list origin_rel) (subst: list (origin * origin)) : list origin_rel :=
  match rels with
  | nil => nil
  | (org1, org2) :: rels1 =>
      ((replace_origin subst org1), (replace_origin subst org2)) :: (replace_origin_in_origin_rels rels1 subst)
  end.


Fixpoint replace_origin_in_type (ty: type) (substs: list (origin * origin)) : type :=
  match ty with
  | Treference org mut ty =>
      let ty' := replace_origin_in_type ty substs in
      Treference (replace_origin substs org) mut ty'
  | Tbox ty =>
      let ty' := replace_origin_in_type ty substs in
      Tbox ty'
  | Tstruct orgs id  =>
      let orgs' := map (replace_origin substs) orgs in
      Tstruct orgs' id
  | Tvariant orgs id =>
      let orgs' := map (replace_origin substs) orgs in
      Tvariant orgs' id
  | Tfunction orgs rels tyl rty cc =>
      let tyl1 := replace_origin_in_typelist tyl substs in
      let ty1 := replace_origin_in_type rty substs in
      let orgs1 := map (replace_origin substs) orgs in
      let rels1 := replace_origin_in_origin_rels rels substs in
      Tfunction orgs1 rels1 tyl1 ty1 cc
  | _ => ty
  end

with replace_origin_in_typelist (tyl: typelist) (rels: list (origin * origin)) : typelist :=
       match tyl with
       | Tnil => Tnil
       | Tcons ty1 tyl1 =>
           Tcons (replace_origin_in_type ty1 rels) (replace_origin_in_typelist tyl1 rels)
       end
.

Lemma replace_origin_in_type_eq: forall ty1 ty2 rels,
    replace_origin_in_type ty1 rels = ty2 ->
    type_eq_except_origins ty1 ty2 = true.
Admitted.


(* Definition attr_of_type (ty: type) := *)
(*   match ty with *)
(*   | Tunit => noattr *)
(*   | Tint sz si a => a *)
(*   | Tlong si a => a *)
(*   | Tfloat sz a => a *)
(*   | Tfunction _ _ args res cc => noattr *)
(*   | Tbox p a => a *)
(*   | Treference _ mut ty a => a *)
(*   | Tarray _ _ a => a *)
(*   | Tstruct _ id a => a *)
(*   | Tvariant _ id a => a *)
(*   end. *)

(** access mode for Rust types  *)
Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed => By_value Mint8signed
  | Tint I8 Unsigned => By_value Mint8unsigned
  | Tint I16 Signed => By_value Mint16signed
  | Tint I16 Unsigned => By_value Mint16unsigned
  | Tint I32 _ => By_value Mint32
  | Tint IBool _ => By_value Mint8unsigned
  | Tlong _ => By_value Mint64
  | Tfloat F32 => By_value Mfloat32
  | Tfloat F64 => By_value Mfloat64                                   
  | Tunit => By_value Mint32
  | Tfunction _ _ _ _ _ => By_reference
  | Tbox _ => By_value Mptr
  | Treference _ _ _ => By_value Mptr
  | Tarray _ _ => By_reference
  | Tstruct _ _ => By_copy
  | Tvariant _ _ => By_copy
end.

(* Used to indicate which places need to be dropped *)
Definition drop_type (ty: type) : bool :=
  match ty with
  | Tunit
  | Tint _ _
  | Tlong _
  | Tfloat _
  | Tfunction _ _ _ _ _
  | Tarray _ _
  | Treference _ _ _ => false
  | _ => true
  end.


(** To C types *)

(* What Tbox corresponds to? *)
(** TODO: Tbox -> None. reference -> None, raw poinetr -> C pointer,
Option<reference> -> C pointer *)
Fixpoint to_ctype (ty: type) : Ctypes.type :=
  match ty with
  | Tunit => Ctypes.type_int32s  (* unit is set to zero *)
  (* | Tbox _  => None *)
  | Tint sz si => Ctypes.Tint sz si noattr
  | Tlong si => Ctypes.Tlong si noattr
  | Tfloat fz => Ctypes.Tfloat fz noattr
  | Tstruct _ id  => Ctypes.Tstruct id noattr
  (* variant = Struct {tag: .. ; f: union} *)
  | Tvariant _ id => Ctypes.Tstruct id noattr
  | Treference _ _ ty
  | Tbox ty => Tpointer (to_ctype ty) noattr
      (* match (to_ctype ty) with *)
      (* | Some ty' =>  *)
      (*     Some (Ctypes.Tpointer ty' attr) *)
      (* | _ => None *)
  (* end *)
  | Tarray ty sz => Ctypes.Tarray (to_ctype ty) sz noattr
  | Tfunction _ _ tyl ty cc =>
      Ctypes.Tfunction (to_ctypelist tyl) (to_ctype ty) cc
  end
    
with to_ctypelist (tyl: typelist) : Ctypes.typelist :=
       match tyl with
       | Tnil => Ctypes.Tnil
       | Tcons ty tyl =>
           Ctypes.Tcons (to_ctype ty) (to_ctypelist tyl)
       end.

(** Composite  *)

Inductive struct_or_variant : Set :=  Struct : struct_or_variant | TaggedUnion : struct_or_variant.

Inductive member : Type :=
  | Member_plain (id: ident) (t: type).

Definition members : Type := list member.

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_variant) (m: members) (orgs: list origin) (org_rels: list origin_rel).

Definition name_member (m: member) : ident :=
  match m with
  | Member_plain id _ => id
  end.

Definition type_member (m: member) : type :=
  match m with
  | Member_plain _ t => t
  end.

Definition name_composite_def (c: composite_definition) : ident :=
  match c with Composite id su m _ _ => id end.

Definition composite_def_eq (x y: composite_definition): {x=y} + {x<>y}.
Proof.
  generalize Pos.eq_dec origin_rel_eq_dec. intros.
  decide equality.
  decide equality.
  decide equality.
(* - decide equality. decide equality. apply N.eq_dec. apply bool_dec. *)
- apply list_eq_dec. decide equality.
  apply type_eq. (* apply ident_eq. *)
- decide equality.
(* - apply ident_eq. *)
Defined.

Global Opaque composite_def_eq. 

(** For type-checking, compilation and semantics purposes, the composite
  definitions are collected in the following [composite_env] environment.
  The [composite] record contains additional information compared with
  the [composite_definition], such as size and alignment information. *)

Record composite : Type := {
  co_generic_origins: list origin;
  co_origin_relations: list origin_rel;
  co_sv: struct_or_variant;
  co_members: members;
  (* co_attr: attr; *)
  co_sizeof: Z;
  co_alignof: Z;
  co_rank: nat;
  co_sizeof_pos: co_sizeof >= 0;
  co_alignof_two_p: exists n, co_alignof = two_power_nat n;
  co_sizeof_alignof: (co_alignof | co_sizeof)
}.

Definition composite_env : Type := PTree.t composite.

(** ** Complete types *)

(** A type is complete if it fully describes an object.
  All struct and variant names appearing in the type must be defined,
  unless they occur under a pointer or function type.  [void] and
  function types are incomplete types. *)

Fixpoint complete_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tunit => true
  | Tint _ _ => true
  | Tlong _ => true
  | Tfloat _ => true
  | Tfunction _ _ _ _ _ => false
  | Tbox _ => true
  | Treference _ _ _ => true
  | Tarray t' _ => complete_type env t'
  | Tstruct _ id | Tvariant _ id =>
      match env!id with Some co => true | None => false end
  end.

Definition complete_or_function_type (env: composite_env) (t: type) : bool :=
  match t with
  | Tfunction _ _ _ _ _ => true
  | _ => complete_type env t
  end.


(** ** Alignment of a type *)

(** Adjust the natural alignment [al] based on the attributes [a] attached
  to the type.  If an "alignas" attribute is given, use it as alignment
  in preference to [al]. *)


Fixpoint alignof (env: composite_env) (t: type) : Z :=
   (match t with
    | Tunit => 4
    | Tint I8 _ => 1
    | Tint I16 _ => 2
    | Tint I32 _ => 4
    | Tint IBool _ => 1
    | Tlong _ => Archi.align_int64
    | Tfloat F32 => 4
    | Tfloat F64 => Archi.align_float64
    | Tfunction _ _ _ _ _ => 1
    | Treference _ _ _
    | Tbox _ => if Archi.ptr64 then 8 else 4
    | Tarray t' _ => alignof env t'
      | Tstruct _ id | Tvariant _ id =>
          match env!id with Some co => co_alignof co | None => 1 end
    end).


Lemma alignof_two_p:
  forall env t, exists n, alignof env t = two_power_nat n.
Proof.
  induction t; simpl.
  exists 2%nat; auto.
  destruct i.
    exists 0%nat; auto.
    exists 1%nat; auto.
    exists 2%nat; auto.
    exists 0%nat; auto.
    unfold Archi.align_int64. destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
  destruct f.
    exists 2%nat; auto.
    unfold Archi.align_float64. destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
    exists 0%nat; auto.
    destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
    destruct Archi.ptr64; ((exists 2%nat; reflexivity) || (exists 3%nat; reflexivity)).
    apply IHt.
    destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
    destruct (env!i). apply co_alignof_two_p. exists 0%nat; auto.
Qed.

Lemma alignof_pos:
  forall env t, alignof env t > 0.
Proof.
  intros. destruct (alignof_two_p env t) as [n EQ]. rewrite EQ. apply two_power_nat_pos.
Qed.

(** Ownership type  *)

(** Program Fixpoint version of own_type. But the proof is compilated  *)
(* Program Fixpoint own_type (ce: composite_env) (ty: type) {measure (PTree_Properties.cardinal ce)} :  bool := *)
(*   match ty with *)
(*   | Tstruct id _ *)
(*   | Tvariant id _ => *)
(*       match ce ! id with *)
(*       | Some co => *)
(*           let ce' := PTree.remove id ce in *)
(*           let acc res m := *)
(*             let own := (match m with *)
(*                         | Member_plain fid fty => *)
(*                             own_type ce' fty *)
(*                         end) in *)
(*             (orb res own) in           *)
(*           fold_left acc co.(co_members) false *)
(*       | None => false *)
(*       end *)
(*   (** TODO: unique pointer and mutable reference are own type  *) *)
(*   | Tbox _ _ => true *)
(*   | Tunit | Tint _ _ _ | Tlong _ _ | Tfloat _ _ | Tfunction _ _ _ => false *)
(*   end. *)
(* Next Obligation. *)
(*   eapply PTree_Properties.cardinal_remove;eauto. *)
(* Defined. *)
(* Next Obligation. *)
(*   eapply PTree_Properties.cardinal_remove;eauto. *)
(* Defined. *)

Inductive composite_result (ce: composite_env) (id: ident) : Type :=
| co_none
| co_some (id1: ident) (co: composite) (P: ce ! id1 = Some co) (Q: id = id1).

Arguments co_none {ce id}.
Arguments co_some {ce id}.

Program Definition get_composite (ce: composite_env) (id: ident) : composite_result ce id :=
  match ce ! id with
  | None => co_none
  | Some co => co_some id co _ _
  end.


(** Recursion borrowed from Inlining.v  *)
Section OWN_TYPE.

Variable ce: composite_env.

Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> type -> bool.
  
Definition own_type' (ty: type) : bool :=
  match ty with
  | Tstruct _ id
  | Tvariant _ id =>
      match get_composite ce id with
      | co_some i co P Q =>
          let acc res m :=
            let own := (match m with
                        | Member_plain fid fty =>
                            rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) fty
                        end) in
            (orb res own) in
          fold_left acc co.(co_members) false
      | co_none => false
      end
  | Tbox _ => true
  | _ => false
  end.
 
End OWN_TYPE.                                    

Require Import Wfsimpl.

(* It is equivalent to type which has [Move (Noncopy)] and [Drop]
trait in Rust. For borrow checking, we need a new charaterized
function to identify [Move] type *)
(* Definition own_type (ce: composite_env) : type -> bool := *)
(*   Fixm (@PTree_Properties.cardinal composite) own_type' ce. *)

(* It is equal to the NonCopy in Rust *)
Definition move_type (ty: type) : bool :=
  match ty with
  | Tbox _
  | Tstruct _ _
  | Tvariant _ _
  | Treference _ Mutable _ => true
  | _ => false
  end.

(** Fuel version own_type  *)
(* (* If run out of fuel, return none *) *)
(* Fixpoint own_type (fuel: nat) (ce: composite_env) (ty: type) : option bool := *)
(*   match fuel with *)
(*   | O => None *)
(*   | S fuel' => *)
(*       match ty with *)
(*       | Tstruct id _ | Tvariant id _ => *)
(*           match ce ! id with *)
(*           | Some co => *)
(*               let acc res m := *)
(*                 let own := (match m with *)
(*                             | Member_plain fid fty => *)
(*                                 own_type fuel' ce fty *)
(*                             end) in *)
(*                 match res,own with *)
(*                 | None, _ => None *)
(*                 | _, None => None *)
(*                 | Some res, Some own => Some (orb res own) *)
(*                 end in           *)
(*               fold_left acc co.(co_members) (Some false) *)
(*           | None => Some false *)
(*           end *)
(*       (** TODO: unique pointer and mutable reference are own type  *) *)
(*       | Tbox _ _ => Some true *)
(*       | _ => Some false *)
(*       end *)
(*   end. *)



(** Size of a type  *)

Fixpoint sizeof (env: composite_env) (t: type) : Z :=
  match t with
  | Tunit => 4
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _
  | Tfloat F32 => 4
  | Tint IBool _ => 1
  | Tlong _
  | Tfloat F64 => 8
  | Tfunction _ _ _ _ _ => 1
  | Treference _ _ _
  | Tbox _ => if Archi.ptr64 then 8 else 4
  | Tarray t' n => sizeof env t' * Z.max 0 n
  | Tstruct _ id
  | Tvariant _ id =>
      match env!id with
      | Some co => co_sizeof co
      | None => 0
      end                    
  end.

Lemma type_eq_sizeof_eq (ty1 ty2: type) ce:
  type_eq_except_origins ty1 ty2 = true ->
  sizeof ce ty1 = sizeof ce ty2.
Proof.
  intros TEQ; induction ty1; destruct ty2; simpl in TEQ; try congruence.
  all: try eapply proj_sumbool_true in TEQ; inv TEQ.
  all: try reflexivity.
Qed.

Lemma sizeof_pos:
  forall env t, sizeof env t >= 0.
Proof.
  induction t; simpl.
- lia.
- destruct i; lia.
- lia.
- destruct f; lia.
- destruct Archi.ptr64; lia.
- destruct Archi.ptr64; lia.
- destruct Archi.ptr64; lia.
- change 0 with (0 * Z.max 0 z) at 2. apply Zmult_ge_compat_r. auto. lia.
- destruct (env!i). apply co_sizeof_pos. lia.
- destruct (env!i). apply co_sizeof_pos. lia.
Qed.

Fixpoint alignof_blockcopy (env: composite_env) (t: type) : Z :=
  match t with
  | Tunit => 4
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _
  | Tfloat F32 => 4
  | Tlong _
  | Tfloat F64 => 8
  | Tint IBool _ => 1
  | Tfunction _ _ _ _ _ => 1
  | Treference _ _ _
  | Tbox _ => if Archi.ptr64 then 8 else 4
  | Tarray t' _ => alignof_blockcopy env t'
  | Tstruct _ id 
  | Tvariant _ id  =>
      match env!id with
      | Some co => Z.min 8 (co_alignof co)
      | None => 1
      end
  end.

Lemma alignof_blockcopy_1248:
  forall env ty, let a := alignof_blockcopy env ty in a = 1 \/ a = 2 \/ a = 4 \/ a = 8.
Proof.
  assert (X: forall co, let a := Z.min 8 (co_alignof co) in
             a = 1 \/ a = 2 \/ a = 4 \/ a = 8).
  {
    intros. destruct (co_alignof_two_p co) as [n EQ]. unfold a; rewrite EQ.
    destruct n; auto.
    destruct n; auto.
    destruct n; auto.
    right; right; right. apply Z.min_l.
    rewrite two_power_nat_two_p. rewrite ! Nat2Z.inj_succ.
    change 8 with (two_p 3). apply two_p_monotone. lia.
  }
  induction ty; simpl.
  auto.
  destruct i; auto.
  auto.
  destruct f; auto.
  destruct Archi.ptr64; auto.
  destruct Archi.ptr64; auto.
  destruct Archi.ptr64; auto.
  apply IHty.
  destruct (env!i); auto.
  destruct (env!i); auto.
Qed.

Lemma sizeof_alignof_blockcopy_compat:
  forall env ty, (alignof_blockcopy env ty | sizeof env ty).
Proof.
  assert (X: forall co, (Z.min 8 (co_alignof co) | co_sizeof co)).
  {
    intros. apply Z.divide_trans with (co_alignof co). 2: apply co_sizeof_alignof.
    destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ.
    destruct n. apply Z.divide_refl.
    destruct n. apply Z.divide_refl.
    destruct n. apply Z.divide_refl.
    apply Z.min_case.
    exists (two_p (Z.of_nat n)).
    change 8 with (two_p 3).
    rewrite <- two_p_is_exp by lia.
    rewrite two_power_nat_two_p. rewrite !Nat2Z.inj_succ. f_equal. lia.
    apply Z.divide_refl.
  }
  induction ty; simpl. 
  apply Z.divide_refl.
  apply Z.divide_refl.
  apply Z.divide_refl.
  apply Z.divide_refl.
  apply Z.divide_refl.
  apply Z.divide_refl.
  destruct Archi.ptr64; apply Z.divide_refl.
  apply Z.divide_mul_l. auto.
  destruct (env!i). apply X. apply Z.divide_0_r.
  destruct (env!i). apply X. apply Z.divide_0_r.
Qed.

Lemma alignof_implies_alignof_blockcopy: forall env ty ofs,    
    (alignof env ty | ofs) ->
    (alignof_blockcopy env ty | ofs).
Proof.
  intros until ofs. intros AL.
  assert (X: forall co, (co_alignof co | ofs) -> (Z.min 8 (co_alignof co) | ofs)).
  { intros.
    destruct (co_alignof_two_p co) as [n EQ]. rewrite EQ in *.
    eapply Z.divide_trans; eauto.
    destruct n. apply Z.divide_refl.
    destruct n. apply Z.divide_refl.
    destruct n. apply Z.divide_refl.
    apply Z.min_case.
    exists (two_p (Z.of_nat n)).        
    rewrite two_power_nat_two_p. rewrite !Nat2Z.inj_succ.
    change 8 with (two_p 3).    
    rewrite <- two_p_is_exp by lia. f_equal. lia.    
    apply Z.divide_refl. }
  induction ty; simpl in *; auto.
  - simpl in *. destruct (env!i) eqn: CO; auto.    
  - simpl in *. destruct (env!i) eqn: CO; auto.
Qed.


(** ** Layout of struct fields *)

Section LAYOUT.

Variable env: composite_env.

Definition bitalignof (t: type) := alignof env t * 8.

Definition bitsizeof  (t: type) := sizeof env t * 8.

Definition bitalignof_intsize (sz: intsize) : Z :=
  match sz with
  | I8 | IBool => 8
  | I16 => 16
  | I32 => 32
  end.

(* The index of the variant *)
Fixpoint field_tag' (fid: ident) (ms: members) (pos: Z) : option Z :=
  match ms with
  | nil => None
  | m::ms =>
      match m with
      | Member_plain id _ =>
          if Pos.eqb fid id
          then Some pos
          else field_tag' fid ms (pos + 1)
      end
  end.

Definition field_tag (fid: ident) (ms:members) : option Z :=
  field_tag' fid ms 0.

Lemma field_tag_offset: forall ms id n n1 n2,
    field_tag' id ms n1 = Some n ->
    field_tag' id ms (n1 + n2) = Some (n + n2).
Proof.
  induction ms; intros.
  - simpl in H. inv H.
  - destruct a. simpl in H.
    destruct (Pos.eqb id id0) eqn: EQ. inv H.
    simpl. rewrite EQ. f_equal.
    simpl. rewrite EQ.
    rewrite Z.add_shuffle0. eapply IHms.
    auto.
Qed.

Lemma field_tag_pos': forall ms id n1 n2,
    n1 >= 0 ->
    field_tag' id ms n1 = Some n2 ->
    n2 >= 0.
Proof.
  induction ms; simpl; intros.
  inv H0.
  destruct a.
  destruct (Pos.eqb id id0) eqn: EQ. inv H0.
  lia.
  eapply IHms. 2: eauto.
  lia.
Qed.


Lemma field_tag_pos: forall ms id n,
    field_tag id ms= Some n ->
    n >= 0.
Proof.
  unfold field_tag. intros. 
  eapply field_tag_pos'; eauto.
  lia.
Qed.

Lemma field_tag_range': forall ms id n pos,
    field_tag' id ms pos = Some n ->
    n < pos + list_length_z ms.
Proof.
  induction ms; intros.
  inv H.
  rewrite list_length_z_cons.
  generalize (list_length_z_pos ms). intros.
  simpl in H. destruct a.
  destruct (id =? id0)%positive in H.
  inv H. lia.
  exploit IHms; eauto. intros. lia.
Qed.

Lemma field_tag_range: forall ms id n,
    field_tag id ms = Some n ->
    n < list_length_z ms.
Proof.
  intros. exploit field_tag_range'; eauto.
Qed.

    
Fixpoint type_tag' (ty: type) (ms: members) (pos: Z) {struct ms} : option (ident * Z) :=
  match ms with
  | nil => None
  | m::ms =>
      match m with
      | Member_plain id ty' =>
          if type_eq ty ty' then
            Some (id,pos)
          else
            type_tag' ty ms (pos + 1) 
      end
  end.

Definition type_tag (ty: type) (ms:members) : option (ident*Z) :=
  type_tag' ty ms 0.

Definition next_field (pos: Z) (m: member) : Z :=
  match m with
  | Member_plain _ t =>
      align pos (bitalignof t) + bitsizeof t
  end.

Definition layout_field (pos: Z) (m: member) : res Z :=
  match m with
  | Member_plain _ t =>
      OK (align pos (bitalignof t) / 8)
  end.

(** Some properties *)

Lemma bitalignof_intsize_pos:
  forall sz, bitalignof_intsize sz > 0.
Proof.
  destruct sz; simpl; lia.
Qed.

Lemma next_field_incr:
  forall pos m, pos <= next_field pos m.
Proof.
  intros. unfold next_field. destruct m.
- set (al := bitalignof t).
  assert (A: al > 0).
  { unfold al, bitalignof. generalize (alignof_pos env t). lia. }
  assert (pos <= align pos al) by (apply align_le; auto).
  assert (bitsizeof t >= 0).
  { unfold bitsizeof. generalize (sizeof_pos env t). lia. } 
  lia.
Qed.

Definition layout_start (p: Z) (bf: bitfield) :=
  p * 8 + match bf with Full => 0 | Bits sz sg pos w => pos end.

Definition layout_width (t: type) (bf: bitfield) :=
  match bf with Full => bitsizeof t | Bits sz sg pos w => w end.

Lemma layout_field_range: forall pos m ofs,
  layout_field pos m = OK ofs ->
  pos <= layout_start ofs Full 
  /\ layout_start ofs Full + layout_width (type_member m) Full <= next_field pos m.
Proof.
  intros until ofs; intros L. unfold layout_start, layout_width. destruct m; simpl in L.
- inv L. simpl.
  set (al := bitalignof t).
  set (q := align pos al).
  assert (A: al > 0).
  { unfold al, bitalignof. generalize (alignof_pos env t). lia. }
  assert (B: pos <= q) by (apply align_le; auto).
  assert (C: (al | q)) by (apply align_divides; auto).
  assert (D: (8 | q)). 
  { apply Z.divide_transitive with al; auto. apply Z.divide_factor_r. }
  assert (E: q / 8 * 8 = q).
  { destruct D as (n & E). rewrite E. rewrite Z.div_mul by lia. auto. }
  rewrite E. lia.
Qed.

Definition layout_alignment (t: type) (bf: bitfield) :=
  match bf with
  | Full => alignof env t
  | Bits sz _ _ _ => bitalignof_intsize sz / 8
  end.

Lemma layout_field_alignment: forall pos m ofs,
  layout_field pos m = OK ofs ->
  (layout_alignment (type_member m) Full | ofs).
Proof.
  intros until ofs; intros L. destruct m; simpl in L.
- inv L; simpl. 
  set (q := align pos (bitalignof t)).
  assert (A: (bitalignof t | q)).
  { apply align_divides. unfold bitalignof. generalize (alignof_pos env t). lia. }
  destruct A as [n E]. exists n. rewrite E. unfold bitalignof. rewrite Z.mul_assoc, Z.div_mul by lia. auto.
Qed.

End LAYOUT.


(** ** Size and alignment for composite definitions *)

(** The alignment for a structure or variant is the max of the alignment
  of its members.  Padding bitfields are ignored. *)

Fixpoint alignof_composite' (env: composite_env) (ms: members) : Z :=
  match ms with
  | nil => 1
  | m :: ms => 
      Z.max (alignof env (type_member m)) (alignof_composite' env ms)
  end.

Definition alignof_composite (env: composite_env) (sv: struct_or_variant) (ms: members) : Z :=
  match sv with
  | Struct => alignof_composite' env ms
  | TaggedUnion =>
      Z.max (alignof env type_int32s) (alignof_composite' env ms)
  end.

(** The size of a structure corresponds to its layout: fields are
  laid out consecutively, and padding is inserted to align
  each field to the alignment for its type.  Bitfields are packed
  as described above. *)

Fixpoint bitsizeof_struct (env: composite_env) (cur: Z) (ms: members) : Z :=
  match ms with
  | nil => cur
  | m :: ms => bitsizeof_struct env (next_field env cur m) ms
  end.


Definition sizeof_struct (env: composite_env) (m: members) : Z :=
  bytes_of_bits (bitsizeof_struct env 0 m).

(** The size of an variant is the size of tagged (4 bytes) plus the
max of the sizes of its members. *)

Fixpoint sizeof_variant' (env: composite_env) (ms: members) : Z :=
  (match ms with
  | nil => 0
  | m :: ms => Z.max (sizeof env (type_member m)) (sizeof_variant' env ms)
  end).

Definition sizeof_variant (env: composite_env) (ms: members) : Z :=
  bytes_of_bits (align 32 ((alignof_composite' env ms) * 8) + (align (sizeof_variant' env ms) (alignof_composite' env ms) * 8)).

(** Some properties *)

Lemma alignof_composite_two_p':
  forall env m, exists n, alignof_composite' env m = two_power_nat n.
Proof.
  induction m; simpl.
- exists 0%nat; auto.
- apply Z.max_case; auto. apply alignof_two_p.
Qed.

Lemma alignof_composite_two_p:
  forall env m sv, exists n, alignof_composite env sv m = two_power_nat n.
Proof.
  intros. destruct sv.
  - apply alignof_composite_two_p'.
  - simpl. apply Z.max_case. exists 2%nat. auto.
    apply alignof_composite_two_p'.
Qed.

Lemma alignof_composite'_pos:
  forall env m,  (alignof_composite' env m) > 0.
Proof.
  intros.
  exploit alignof_composite_two_p'.
  intros [n EQ].
  rewrite EQ; apply two_power_nat_pos.
Qed.


Lemma alignof_composite_pos:
  forall env m sv, (alignof_composite env sv m) > 0.
Proof.
  intros.
  exploit alignof_composite_two_p.
  intros [n EQ].
  rewrite EQ; apply two_power_nat_pos.
Qed.

Lemma bitsizeof_struct_incr:
  forall env m cur, cur <= bitsizeof_struct env cur m.
Proof.
  induction m; simpl; intros.
- lia.
- apply Z.le_trans with (next_field env cur a).
  apply next_field_incr. apply IHm.
Qed.

Lemma sizeof_variant'_pos:
  forall env m, 0 <= sizeof_variant' env m.
Proof.
  induction m; simpl; extlia.  
Qed.

Lemma sizeof_variant_pos:
  forall env m, 0 <= sizeof_variant env m.
Proof.
  intros. unfold sizeof_variant.
  generalize (sizeof_variant'_pos env m).
  intros.
  (* apply Z.le_lteq in H as LELT. destruct LELT. *)
  (* apply Z.gt_lt_iff in H0. *)
  generalize (alignof_composite_two_p' env m). intros (n & A).
  generalize (two_power_nat_pos n). rewrite A. intros B.
  generalize (align_le 32 (two_power_nat n * 8) B). intros.
  generalize (align_le (sizeof_variant' env m) (two_power_nat n) B). intros.
  unfold bytes_of_bits.
  change 0 with (0 / 8) at 1. apply Z.div_le_mono; lia.
Qed.

Lemma sizeof_variant_ge4:
  forall env m, 4 <= sizeof_variant env m.
Proof.
  intros. unfold sizeof_variant.
  generalize (sizeof_variant'_pos env m).
  intros.
  (* apply Z.le_lteq in H as LELT. destruct LELT. *)
  (* apply Z.gt_lt_iff in H0. *)
  generalize (alignof_composite_two_p' env m). intros (n & A).
  generalize (two_power_nat_pos n). rewrite A. intros B.
  generalize (align_le 32 (two_power_nat n * 8) B). intros.
  generalize (align_le (sizeof_variant' env m) (two_power_nat n) B). intros.
  unfold bytes_of_bits.
  change 4 with (32 / 8) at 1. apply Z.div_le_mono; lia.
Qed.


(** Type ranks *)

(** The rank of a type is a nonnegative integer that measures the direct nesting
  of arrays, struct and variant types.  It does not take into account indirect
  nesting such as a struct type that appears under a pointer or function type.
  Type ranks ensure that type expressions (ignoring pointer and function types)
  have an inductive structure. *)

Definition rank_type (ce: composite_env) (t: type) : nat :=
  match t with
  | Tstruct _ id | Tvariant _ id =>
      match ce!id with
      | None => O
      | Some co => S (co_rank co)
      end
  | _ => O
  end.

Fixpoint rank_members (ce: composite_env) (m: members) : nat :=
  match m with
  | nil => 0%nat
  | Member_plain _ t :: m => Init.Nat.max (rank_type ce t) (rank_members ce m)
  end.


(** ** Rust types and back-end types *)

(** Extracting a type list from a function parameter declaration. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

(** Translating C types to Cminor types and function signatures. *)

Definition typ_of_type (t: type) : AST.typ :=
  match t with
  | Tunit => AST.Tint
  | Tint _ _ => AST.Tint
  | Tlong _ => AST.Tlong
  | Tfloat F32 => AST.Tsingle
  | Tfloat F64 => AST.Tfloat
  | Tfunction _ _ _ _ _ | Treference _ _ _ | Tbox _ | Tarray _ _ | Tstruct _ _ | Tvariant _ _ => AST.Tptr
  end.

Definition rettype_of_type (t: type) : AST.rettype :=
  match t with
  | Tunit => AST.Tint
  | Tint I32 _ => AST.Tint
  | Tint I8 Signed => AST.Tint8signed
  | Tint I8 Unsigned => AST.Tint8unsigned
  | Tint I16 Signed => AST.Tint16signed
  | Tint I16 Unsigned => AST.Tint16unsigned
  | Tint IBool _ => AST.Tint8unsigned
  | Tlong _ => AST.Tlong
  | Tfloat F32 => AST.Tsingle
  | Tfloat F64 => AST.Tfloat
  | Tbox _ | Treference _ _ _ => Tptr
  | Tarray _ _ | Tfunction _ _ _ _ _ | Tstruct _ _ | Tvariant _ _ => AST.Tvoid
  end.

Fixpoint typlist_of_typelist (tl: typelist) : list AST.typ :=
  match tl with
  | Tnil => nil
  | Tcons hd tl => typ_of_type hd :: typlist_of_typelist tl
  end.

Definition signature_of_type (args: typelist) (res: type) (cc: calling_convention): signature :=
  mksignature (typlist_of_typelist args) (rettype_of_type res) cc.


(** * Construction of the composite environment *)

(** Compute the flow kind for each generic origin  *)

(*
Import ListNotations.

Definition update_flow_kinds_from_region (env: composite_env) (fenv: PTree.t flow_kind) (org: origin) (fk: flow_kind) : res (PTree.t flow_kind) :=
  match fenv ! org with
  | Some org_fk =>
      OK (PTree.set org (meet_flow_kinds org_fk fk) fenv)
  | None =>
      Error [MSG "This origin does not exist in the flow_kind environment (update_flow_kinds_from_region)"; CTX org]
  end.
  
(* fkl is the flow_kind list from the compositie of this origins *)
Fixpoint update_flow_kinds_from_region_list (env: composite_env) (fenv: PTree.t flow_kind) (orgs: list origin) (fkl: list flow_kind) (fk: flow_kind) : res (PTree.t flow_kind) :=
  match orgs, fkl with
  | nil, nil => OK fenv
  | org1 :: l1, fk2 :: l2 =>
      do fenv1 <- update_flow_kinds_from_region env fenv org1 (meet_flow_kinds fk fk2);
      update_flow_kinds_from_region_list env fenv1 l1 l2 fk
  | _, _ => Error (msg "Impossible (update_flow_kinds_from_region_list)")
  end.

Fixpoint update_flow_kinds_from_type (env: composite_env) (fenv: PTree.t flow_kind) (ty: type) (fk: flow_kind) : res (PTree.t flow_kind) :=
  match ty with
  | Treference org mut ty1 =>
      do fenv1 <- update_flow_kinds_from_region env fenv org fk;
      let fk1 := match mut with
                 | Mutable => ByRef
                 | Immutable => ByVal
                 end in
      update_flow_kinds_from_type env fenv1 ty1 (meet_flow_kinds fk1 fk)
  | Tbox ty1 =>
      update_flow_kinds_from_type env fenv ty1 (meet_flow_kinds ByVal fk)
  | Tstruct orgs id
  | Tvariant orgs id =>
      match env ! id with
      | Some co =>
          update_flow_kinds_from_region_list env fenv orgs (map snd co.(co_generic_origins)) fk
      | None =>
          Error (MSG "Incomplete struct or variant (update_flow_kinds_from_type)" :: CTX id :: nil)
      end
  | _ => OK fenv
  end.

Fixpoint update_flow_kinds_from_members (env: composite_env) (fenv: PTree.t flow_kind) (membs: members) : res (PTree.t flow_kind) :=
  match membs with
  | nil => OK fenv
  | Member_plain _ ty :: membs1 =>
      do fenv1 <- update_flow_kinds_from_type env fenv ty ByVal;
      update_flow_kinds_from_members env fenv1 membs1
  end.

Definition init_flow_kind_env (orgs: list origin) : PTree.t flow_kind :=
  PTree_Properties.of_list (combine orgs (repeat ByVal (length orgs))).

Fixpoint set_flow_finds_on_orgs (fenv: PTree.t flow_kind) (orgs: list origin) : res (list (origin * flow_kind)) :=
  match orgs with
  | nil => OK nil
  | org :: orgs1 =>
      match fenv ! org with
      | Some fk => 
          do l <- set_flow_finds_on_orgs fenv orgs1;
          OK ((org, fk) :: l)
      | None =>
          Error (msg "Impossible (set_flow_finds_on_args)")
      end
  end. 

Definition flow_kinds_of_composite (env: composite_env) (orgs: list origin) (membs: members) : res (list (origin * flow_kind)) :=
  let fenv0 := init_flow_kind_env orgs in
  do fenv1 <- update_flow_kinds_from_members env fenv0 membs;
  set_flow_finds_on_orgs fenv1 orgs.

Lemma flow_kinds_of_composite_regions: forall env orgs membs orgs_fks,
    flow_kinds_of_composite env orgs membs = OK orgs_fks ->
    map fst orgs_fks = orgs.
Admitted.

*)

Definition sizeof_composite (env: composite_env) (sv: struct_or_variant) (m: members) : Z :=
  match sv with
  | Struct => sizeof_struct env m
  | TaggedUnion  => sizeof_variant env m
  end.

Lemma sizeof_composite_pos:
  forall env su m, 0 <= sizeof_composite env su m.
Proof.
  intros. destruct su; simpl.
- unfold sizeof_struct, bytes_of_bits.
  assert (0 <= bitsizeof_struct env 0 m) by apply bitsizeof_struct_incr.
  change 0 with (0 / 8) at 1. apply Z.div_le_mono; lia.
- apply sizeof_variant_pos.
Qed.


Fixpoint complete_members (env: composite_env) (ms: members) : bool :=
  match ms with
  | nil => true
  | m :: ms => complete_type env (type_member m) && complete_members env ms
  end.

Lemma complete_member:
  forall env m ms,
  In m ms -> complete_members env ms = true -> complete_type env (type_member m) = true.
Proof.
  induction ms as [|m1 ms]; simpl; intuition auto.
  InvBooleans; inv H1; auto.
  InvBooleans; eauto.
Qed.

Definition check_comp_defs_complete (env: composite_env) : res composite_env :=
  PTree.fold (fun acc id comp =>
    do ce <- acc;
    match complete_members env comp.(co_members) with
    | false => Error (MSG "Incomplete struct or variant " :: CTX id :: nil)
    | true => OK ce
    end) env (OK env).

Program Definition composite_of_def
     (env: composite_env) (id: ident) (su: struct_or_variant) (m: members) (* (a: attr) *) (orgs: list origin) (org_rels: list origin_rel)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or variant " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or variant " :: CTX id :: nil)
  | None, true =>
      let al := (alignof_composite env su m) in
      OK {| co_generic_origins := orgs;
            co_origin_relations := org_rels;
            co_sv := su;
            co_members := m;
            (* co_attr := a; *)
            co_sizeof := align (sizeof_composite env su m) al;
            co_alignof := al;
            co_rank := rank_members env m;
            co_sizeof_pos := _;
            co_alignof_two_p := _;
            co_sizeof_alignof := _ |}
  end.
Next Obligation.
  apply Z.le_ge. eapply Z.le_trans. eapply sizeof_composite_pos.
  apply align_le; apply alignof_composite_pos.
Defined.
Next Obligation.
  apply alignof_composite_two_p.
Defined.
Next Obligation.
  apply align_divides. apply alignof_composite_pos.
Defined.

(** The composite environment for a program is obtained by entering
  its composite definitions in sequence.  The definitions are assumed
  to be listed in dependency order: the definition of a composite
  must precede all uses of this composite, unless the use is under
  a pointer or function type. *)

Fixpoint add_composite_definitions (env: composite_env) (defs: list composite_definition) : res composite_env :=
  match defs with
  | nil => OK env
  | Composite id su m orgs org_rels :: defs =>
      do co <- composite_of_def env id su m orgs org_rels;
      add_composite_definitions (PTree.set id co env) defs
      (* check_comp_defs_complete ce *)
  end.

Definition build_composite_env (defs: list composite_definition) :=
  add_composite_definitions (PTree.empty _) defs.

(** ** Byte offset and bitfield designator for a field of a structure *)

Fixpoint field_type (id: ident) (ms: members) {struct ms} : res type :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms => if ident_eq id (name_member m) then OK (type_member m) else field_type id ms
  end.

Lemma field_type_implies_field_tag: forall ms id ty,
    field_type id ms = OK ty ->
    exists tag, field_tag id ms = Some tag
           /\ list_nth_z ms tag = Some (Member_plain id ty).
Proof.
  induction ms; intros.
  - simpl in H. inv H.
  - simpl in H. destruct ident_eq.
    + subst. inv H.
      exists 0. destruct a. simpl. split.
      unfold field_tag, field_tag'. rewrite Pos.eqb_refl.
      auto. auto.
    + generalize (IHms id ty H). intros (tag & A & B).
      exists (tag + 1). destruct a. simpl in *. split.
      * unfold field_tag, field_tag'.
        eapply Pos.eqb_neq in n. rewrite n.
        fold field_tag'. eapply field_tag_offset.
        auto.
      * generalize (field_tag_pos ms id tag A). intros GE.
        destruct zeq. lia.
        rewrite <- B. f_equal.
        lia.
Qed.

(** [field_offset env id fld] returns the byte offset for field [id]
  in a structure whose members are [fld].  It also returns a
  bitfield designator, giving the location of the bits to access
  within the storage unit for the bitfield. *)

Fixpoint field_offset_rec (env: composite_env) (id: ident) (ms: members) (pos: Z)
                          {struct ms} : res Z :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms =>
      if ident_eq id (name_member m)
      then layout_field env pos m
      else field_offset_rec env id ms (next_field env pos m)
  end.

Definition field_offset (env: composite_env) (id: ident) (ms: members) : res Z :=
  field_offset_rec env id ms 0.


Lemma align_zero: forall n,
    n > 0 ->
    align 0 n = 0.
Proof.
  intros. unfold align.
  rewrite Z.add_0_l.
  erewrite Z.div_small; try lia.
Qed.

Lemma field_type_implies_field_offset_rec: forall ms id ty ce s,
    field_type id ms = OK ty ->
    exists fofs, field_offset_rec ce id ms s = OK fofs.
Proof.
  induction ms; intros.
  - simpl in H. inv H.
  - simpl in H. destruct ident_eq.
    + subst. inv H.
      destruct a. simpl.
      destruct ident_eq; try congruence. eauto.
    + destruct a. simpl in *.
      destruct ident_eq; try congruence.
      generalize (IHms id ty ce ((align s (bitalignof ce t) + bitsizeof ce t)) H). intros (fofs & A). eauto.
Qed.

Lemma field_type_implies_field_offset: forall ms id ty ce,
    field_type id ms = OK ty ->
    exists fofs, field_offset ce id ms = OK fofs.
Proof.
  intros. unfold field_offset.
  eapply field_type_implies_field_offset_rec; eauto.
Qed.
  
(** field_offset_all returns all the byte offset for fileds in a structure  *)

Fixpoint field_offset_all_rec (env: composite_env) (ms: members) (pos: Z)
                          {struct ms} : res (list Z) :=
  match ms with
  | nil => OK nil
  | m :: ms =>
      do ofsm <- layout_field env pos m;
      do ofsms <- field_offset_all_rec env ms (next_field env pos m);
      OK (ofsm :: ofsms)
  end.

Definition field_offset_all (env: composite_env) (ms: members) : res (list Z) :=
  field_offset_all_rec env ms 0.

(* [field_zero_or_padding m] returns true if the field is a zero length bitfield
   or does not have a name *)
Definition field_zero_or_padding (m: member) : bool :=
  match m with
  | Member_plain _ _ => false
  (* | Member_bitfield _ _ _ _ w p => orb (zle w 0) p *)
  end.

(** [layout_struct env ms accu pos] computes the layout of all fields of a struct that
    are not unnamed or zero width bitfield members *)
Fixpoint layout_struct_rec (env: composite_env) (ms: members)
                           (accu: list (ident * Z)) (pos: Z)
                           {struct ms} : res (list (ident * Z)) :=
  match ms with
  | nil => OK accu
  | m :: ms =>
      if field_zero_or_padding m then
        layout_struct_rec env ms accu (next_field env pos m)
      else
        do p <- layout_field env pos m;
        layout_struct_rec env ms (((name_member m), p) :: accu) (next_field env pos m)
  end.

Definition layout_struct (env: composite_env) (ms: members) : res (list (ident * Z)) :=
  layout_struct_rec env ms nil 0.

(** Some sanity checks about field offsets.  First, field offsets are
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall env id ofs ty ms pos,
  field_offset_rec env id ms pos = OK ofs -> field_type id ms = OK ty ->
  pos <= layout_start ofs Full
  /\ layout_start ofs Full + layout_width env ty Full <= bitsizeof_struct env pos ms.
Proof.
  induction ms as [ | m ms]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)).
  + inv H0. 
    exploit layout_field_range; eauto.
    generalize (bitsizeof_struct_incr env ms (next_field env pos m)).
    simpl.
    lia.
  + exploit IHms; eauto.
    generalize (next_field_incr env pos m).
    simpl.
    lia.
Qed.

Lemma field_offset_in_range_gen:
  forall env ms id ofs ty,
  field_offset env id ms = OK ofs -> field_type id ms = OK ty ->
  0 <= layout_start ofs Full
  /\ layout_start ofs Full + layout_width env ty Full <= bitsizeof_struct env 0 ms.
Proof.
  intros. eapply field_offset_rec_in_range; eauto.
Qed.

Corollary field_offset_in_range:
  forall env ms id ofs ty,
  field_offset env id ms = OK ofs -> field_type id ms = OK ty ->
  0 <= ofs /\ ofs + sizeof env ty <= sizeof_struct env ms.
Proof.
  intros. exploit field_offset_in_range_gen; eauto. 
  unfold layout_start, layout_width, bitsizeof, sizeof_struct. intros [A B].
  assert (C: forall x y, x * 8 <= y -> x <= bytes_of_bits y).
  { unfold bytes_of_bits; intros. 
    assert (P: 8 > 0) by lia.
    generalize (Z_div_mod_eq (y + 7) 8 P) (Z_mod_lt (y + 7) 8 P).
    lia. }
  split. lia. apply C. lia.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall env id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset env id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  layout_start ofs1 Full+ layout_width env ty1 Full <= layout_start ofs2 Full
  \/ layout_start ofs2 Full + layout_width env ty2 Full <= layout_start ofs1 Full.
Proof.
  intros until fld. unfold field_offset. generalize 0 as pos.
  induction fld as [|m fld]; simpl; intros.
- discriminate.
- destruct (ident_eq id1 (name_member m)); destruct (ident_eq id2 (name_member m)).
+ congruence.
+ inv H0.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. simpl. lia.
+ inv H2.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. simpl. lia.
+ eapply IHfld; eauto.
Qed.

Lemma field_offset_no_overlap_simplified:
  forall env id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset env id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof env ty1 <= ofs2
  \/ ofs2 + sizeof env ty2 <= ofs1.
Proof.
  intros. exploit field_offset_no_overlap.
  eapply H. eapply H0.
  eapply H1. eapply H2.
  auto. unfold layout_start. simpl.
  rewrite ! Z.add_0_r. unfold bitsizeof.
  lia.
Qed.
  
(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Lemma field_offset_prefix:
  forall env id ofs fld2 fld1,
  field_offset env id fld1 = OK ofs ->
  field_offset env id (fld1 ++ fld2) = OK ofs.
Proof.
  intros until fld1. unfold field_offset. generalize 0 as pos.
  induction fld1 as [|m fld1]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)); auto.
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned_gen:
  forall env id fld ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (layout_alignment env ty Full | ofs).
Proof.
  intros until ty. unfold field_offset. generalize 0 as pos. revert fld.
  induction fld as [|m fld]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)).
+ inv H0. eapply layout_field_alignment; eauto.
+ eauto.
Qed.

Corollary field_offset_aligned:
  forall env id fld ofs ty,
  field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
  intros. exploit field_offset_aligned_gen; eauto.
Qed.

(** [variant_field_offset env id ms] returns the byte offset (plus 4 bytes) and
    bitfield designator for accessing a member named [id] of a variant
    whose members are [ms].  The byte offset is always 0. *)

Definition variant_field_offset (env: composite_env) (id: ident) (ms: members) : res Z :=
  if existsb (fun m => proj_sumbool (ident_eq id (name_member m))) ms then
    (* align all the members *)
    OK (align 32 (alignof_composite' env ms * 8) / 8)
  else Error (MSG "Unknown field " :: CTX id :: nil).

(* variant_field_offset in range *)

Lemma variant_field_offset_in_range_aux: forall ce ms fty fid,
    field_type fid ms = OK fty ->
    sizeof ce fty <= sizeof_variant' ce ms.
Proof.
  induction ms; intros; simpl in *; try congruence.
  destruct ident_eq in H. inv H. lia.
  generalize (IHms fty fid H); eauto. lia.
Qed.

Corollary variant_field_offset_in_range:
  forall env ms id ofs ty,
  variant_field_offset env id ms = OK ofs -> field_type id ms = OK ty ->
  (* skip the offset of tag *)
  4 <= ofs /\ ofs + sizeof env ty <= sizeof_variant env ms.
Proof.
  intros. unfold variant_field_offset in H.
  destruct existsb eqn: EX in H; try congruence.
  inv H. split.
  - assert (POS: (alignof_composite' env ms * 8) > 0).
    { generalize (alignof_composite'_pos env ms). lia. }
    generalize (align_le 32 (alignof_composite' env ms * 8) POS).
    intros A1.
    eapply Z.div_le_lower_bound. lia. auto.
  - unfold sizeof_variant.
    unfold bytes_of_bits.
    eapply Z.div_le_lower_bound. lia.
    rewrite Z.mul_add_distr_l.
    rewrite <- (Z.add_assoc _ _ 7).    
    eapply Z.add_le_mono.
    eapply Z.mul_div_le. lia.
    assert (LE: sizeof env ty <= align (sizeof_variant' env ms) (alignof_composite' env ms)).
    { eapply Z.le_trans.
      2: eapply align_le.
      eapply variant_field_offset_in_range_aux; eauto.
      eapply alignof_composite'_pos. }
    lia.
Qed.

    
(* I don't know how to prove it *)
(* Lemma align_mul_div: forall x y n, *)
(*     n > 0 -> *)
(*     x > 0 -> *)
(*     y > 0 -> *)
(*     (align (x * n) (y * n)) / n = align x y. *)

(** Properties used for subplace  *)

Lemma alignof_composite_max_aux: forall ce fld fid fty,
    field_type fid fld = OK fty ->
    alignof ce fty <= alignof_composite' ce fld.
Proof.
  induction fld; intros; simpl in *; try congruence.
  destruct ident_eq in H.
  - inv H. lia.
  - generalize (IHfld fid  fty H); eauto. lia.
Qed.

Lemma alignof_composite_max: forall ce co fid fty,
    field_type fid (co_members co) = OK fty ->
    alignof ce fty <= alignof_composite ce (co_sv co) (co_members co).
Proof.
  intros. destruct (co_sv co).
  - simpl. eapply alignof_composite_max_aux. eauto.
  - simpl. generalize (alignof_composite_max_aux ce (co_members co) fid fty H); eauto.
    lia.
Qed.

(** The alignment of subfiled divides the alignment of the complete
     composite *)
Lemma field_alignof_divide_composite: forall fty fid co ce,
    field_type fid (co_members co) = OK fty ->
    (alignof ce fty | alignof_composite ce (co_sv co) (co_members co)).
Proof.
  intros fty fid co ce0 FTY.
  generalize (alignof_composite_two_p ce0 (co_members co) (co_sv co)).
  intros (n2 & A2).
  generalize (alignof_two_p ce0 fty).
  intros (n1 & A1).
  rewrite A1. rewrite A2.
  do 2 erewrite two_power_nat_equiv in *.
  set (nz1:= Z.of_nat n1) in *.
  set (nz2:= Z.of_nat n2) in *.
  assert (LE: nz1 <= nz2).
  { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
    unfold nz2. eapply Nat2Z.is_nonneg.
    rewrite <- A1. rewrite <- A2.
    eapply alignof_composite_max. eauto. }
  exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
  rewrite MZEQ. erewrite Z.pow_add_r; auto.
  eapply Z.divide_factor_r.
  unfold nz1. eapply Nat2Z.is_nonneg.
Qed.

Lemma tag_align_divide_composite: forall co ce,
    (4 | alignof_composite ce TaggedUnion (co_members co)).
Proof.
  intros. simpl.
  generalize (alignof_composite_two_p' ce (co_members co)).
  intros (n2 & A2). rewrite A2.
  erewrite two_power_nat_equiv in *.
  replace 4 with (2 ^ 2) by lia.
  eapply Z.max_case_strong; intros.
  eapply Z.divide_refl.
  assert (LE: 2 <= Z.of_nat n2).
  { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
    eapply Nat2Z.is_nonneg. auto. }
  exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
  rewrite MZEQ. erewrite Z.pow_add_r; auto.
  eapply Z.divide_factor_r.
  lia.
Qed.

Lemma variant_field_offset_aligned:
  forall env id fld ofs ty,
  variant_field_offset env id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
  intros. unfold variant_field_offset in H.
  destruct existsb eqn: EX in H; try congruence.
  inv H.
  replace (alignof env ty) with (alignof env ty * 8 / 8).
  2: { eapply Z.div_mul. lia. }
  eapply Z.divide_div. lia. eapply Z.divide_mul_r. eapply Z.divide_refl.
  eapply Z.divide_trans.
  2: { eapply align_divides.
       generalize (alignof_composite'_pos env fld).
       lia. }
  eapply Z.mul_divide_mono_r.
  generalize (alignof_composite_two_p' env fld).
  intros (n2 & A2).
  generalize (alignof_two_p env ty).
  intros (n1 & A1).
  rewrite A1. rewrite A2.
  do 2 erewrite two_power_nat_equiv in *.
  set (nz1:= Z.of_nat n1) in *.
  set (nz2:= Z.of_nat n2) in *.
  assert (LE: nz1 <= nz2).
  { eapply Z.pow_le_mono_r_iff with (a:= 2). lia.
    unfold nz2. eapply Nat2Z.is_nonneg.
    rewrite <- A1. rewrite <- A2.
    eapply alignof_composite_max_aux. eauto. }
  exploit Z.le_exists_sub; eauto. intros (p & MZEQ & PG).
  rewrite MZEQ. erewrite Z.pow_add_r; auto.
  eapply Z.divide_factor_r.
  unfold nz1. eapply Nat2Z.is_nonneg.
Qed.


(** Stability properties for alignments, sizes, and ranks.  If the type is
  complete in a composite environment [env], its size, alignment, and rank
  are unchanged if we add more definitions to [env]. *)

Section STABILITY.

Variables env env': composite_env.
Hypothesis extends: forall id co, env!id = Some co -> env'!id = Some co.

Lemma alignof_stable:
  forall t, complete_type env t = true -> alignof env' t = alignof env t.
Proof.
  induction t; simpl; intros; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
Qed.

Lemma sizeof_stable:
  forall t, complete_type env t = true -> sizeof env' t = sizeof env t.
Proof.
  induction t; simpl; intros; auto.
  rewrite IHt by auto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
Qed.

Lemma complete_type_stable:
  forall t, complete_type env t = true -> complete_type env' t = true.
Proof.
  induction t; simpl; intros; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
Qed.

Lemma rank_type_stable:
  forall t, complete_type env t = true -> rank_type env' t = rank_type env t.
Proof.
  induction t; simpl; intros; auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
  destruct (env!i) as [co|] eqn:E; try discriminate.
  erewrite extends by eauto. auto.
Qed.

Lemma alignof_composite_stable':
  forall ms , complete_members env ms = true -> alignof_composite' env' ms = alignof_composite' env ms.
Proof.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans. rewrite alignof_stable by auto. rewrite IHms by auto. auto.
Qed.  

Lemma alignof_composite_stable:
  forall ms sv, complete_members env ms = true -> alignof_composite env' sv ms = alignof_composite env sv ms.
Proof.
  intros. destruct sv;simpl.
  generalize dependent ms.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans.  
  rewrite alignof_stable by auto. rewrite IHms by auto. auto.
  f_equal.   generalize dependent ms.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans.  
  rewrite alignof_stable by auto. rewrite IHms by auto. auto.
Qed.

Remark next_field_stable: forall pos m,
  complete_type env (type_member m) = true -> next_field env' pos m = next_field env pos m.
Proof.
  destruct m; simpl; intros.
- unfold bitalignof, bitsizeof. rewrite alignof_stable, sizeof_stable by auto. auto.
Qed.

Lemma bitsizeof_struct_stable:
  forall ms pos, complete_members env ms = true -> bitsizeof_struct env' pos ms = bitsizeof_struct env pos ms.
Proof.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans. rewrite next_field_stable by auto. apply IHms; auto.
Qed.

Lemma sizeof_variant_stable':
  forall ms, complete_members env ms = true -> sizeof_variant' env' ms = sizeof_variant' env ms.
Proof.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans. rewrite sizeof_stable by auto. rewrite IHms by auto. auto.
Qed.

Lemma sizeof_variant_stable:
  forall ms, complete_members env ms = true -> sizeof_variant env' ms = sizeof_variant env ms.
Proof.
  unfold sizeof_variant. intros. rewrite sizeof_variant_stable'.
  f_equal. f_equal. f_equal. f_equal. eapply alignof_composite_stable'.
  auto.
  f_equal. f_equal. eapply alignof_composite_stable'.
  auto.
  auto.
Qed.


Lemma sizeof_composite_stable:
  forall su ms, complete_members env ms = true -> sizeof_composite env' su ms = sizeof_composite env su ms.
Proof.
  intros. destruct su; simpl.
  unfold sizeof_struct. f_equal. apply bitsizeof_struct_stable; auto.
  apply sizeof_variant_stable; auto.
Qed.

Lemma complete_members_stable:
  forall ms, complete_members env ms = true -> complete_members env' ms = true.
Proof.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans. rewrite complete_type_stable by auto. rewrite IHms by auto. auto.
Qed.

Lemma rank_members_stable:
  forall ms, complete_members env ms = true -> rank_members env' ms = rank_members env ms.
Proof.
  induction ms as [|m ms]; simpl; intros.
  auto.
  InvBooleans. destruct m; auto. f_equal; auto. apply rank_type_stable; auto.
Qed.

Remark layout_field_stable: forall pos m,
  complete_type env (type_member m) = true -> layout_field env' pos m = layout_field env pos m.
Proof.
  destruct m; simpl; intros.
- unfold bitalignof. rewrite alignof_stable by auto. auto.
Qed.

Lemma field_offset_stable:
  forall f ms, complete_members env ms = true -> field_offset env' f ms = field_offset env f ms.
Proof.
  intros until ms. unfold field_offset. generalize 0.
  induction ms as [|m ms]; simpl; intros.
- auto.
- InvBooleans. destruct (ident_eq f (name_member m)).
  apply layout_field_stable; auto.
  rewrite next_field_stable by auto. apply IHms; auto.
Qed.

Lemma variant_field_offset_stable:
  forall f ms, complete_members env ms = true -> variant_field_offset env' f ms = variant_field_offset env f ms.
Proof.
  simpl; intros. unfold variant_field_offset.
  destruct (existsb (fun m : member => ident_eq f (name_member m)) ms); auto.
  do 4 f_equal.
  eapply alignof_composite_stable'. auto.
Qed.

End STABILITY.


Lemma add_composite_definitions_incr:
  forall id co defs env1 env2,
  add_composite_definitions env1 defs = OK env2 ->
  env1!id = Some co -> env2!id = Some co.
Proof.
  induction defs; simpl; intros.
- inv H; auto.
- destruct a; monadInv H.
  eapply IHdefs; eauto. rewrite PTree.gso; auto.
  red; intros; subst id0. unfold composite_of_def in EQ. rewrite H0 in EQ; discriminate.
Qed.

(** It follows that the sizes and alignments contained in the composite
  environment produced by [build_composite_env] are consistent with
  the sizes and alignments of the members of the composite types. *)

Record composite_consistent (env: composite_env) (co: composite) : Prop := {
  co_consistent_complete:
     complete_members env (co_members co) = true;
  co_consistent_alignof:
     co_alignof co = alignof_composite env co.(co_sv) (co_members co);
  co_consistent_sizeof:
     co_sizeof co = align (sizeof_composite env (co_sv co) (co_members co)) (co_alignof co);
  co_consistent_rank:
     co_rank co = rank_members env (co_members co)
}.

Definition composite_env_consistent (env: composite_env) : Prop :=
  forall id co, env!id = Some co -> composite_consistent env co.

Lemma composite_consistent_stable:
  forall (env env': composite_env)
         (EXTENDS: forall id co, env!id = Some co -> env'!id = Some co)
         co,
  composite_consistent env co -> composite_consistent env' co.
Proof.
  intros. destruct H as [A B C D]. constructor. 
  eapply complete_members_stable; eauto.
  symmetry; rewrite B. apply alignof_composite_stable; auto. 
  symmetry; rewrite C. f_equal. apply sizeof_composite_stable; auto.
  symmetry; rewrite D. apply rank_members_stable; auto.
Qed.

Lemma composite_of_def_consistent:
  forall env id su m co orgs rels,
  composite_of_def env id su m orgs rels = OK co ->
  composite_consistent env co.
Proof.
  unfold composite_of_def; intros. 
  destruct (env!id); try discriminate. destruct (complete_members env m) eqn:C; inv H.
  constructor; auto.
Qed. 

Theorem build_composite_env_consistent:
  forall defs env, build_composite_env defs = OK env -> composite_env_consistent env.
Proof.
  cut (forall defs env0 env,
       add_composite_definitions env0 defs = OK env ->
       composite_env_consistent env0 ->
       composite_env_consistent env).
  intros. eapply H; eauto. red; intros. rewrite PTree.gempty in H1; discriminate.
  induction defs as [|d1 defs]; simpl; intros.
- inv H; auto.
- destruct d1; monadInv H.
  eapply IHdefs; eauto.
  set (env1 := PTree.set id x env0) in *.
  assert (env0!id = None). 
  { unfold composite_of_def in EQ. destruct (env0!id). discriminate. auto. }
  assert (forall id1 co1, env0!id1 = Some co1 -> env1!id1 = Some co1).
  { intros. unfold env1. rewrite PTree.gso; auto. congruence. }
  red; intros. apply composite_consistent_stable with env0; auto.
  unfold env1 in H2; rewrite PTree.gsspec in H2; destruct (peq id0 id).
+ subst id0. inversion H2; clear H2. subst co.
  eapply composite_of_def_consistent; eauto.
+ eapply H0; eauto. 
Qed.

(** Moreover, every composite definition is reflected in the composite environment. *)

Theorem build_composite_env_charact:
  forall id su m defs env orgs rels,
  build_composite_env defs = OK env ->
  In (Composite id su m orgs rels) defs ->
  exists co, env!id = Some co /\ co_members co = m /\ co_sv co = su /\ co_generic_origins co = orgs /\ co_origin_relations co = rels.
Proof.
  intros until defs. unfold build_composite_env. generalize (PTree.empty composite) as env0.
  revert defs. induction defs as [|d1 defs]; simpl; intros.
- contradiction.
- destruct d1; monadInv H.
  destruct H0; [idtac|eapply IHdefs;eauto]. inv H.
  unfold composite_of_def in EQ.
  destruct (env0!id) eqn:E; try discriminate.
  destruct (complete_members env0 m) eqn:C; simplify_eq EQ. clear EQ; intros EQ.
  exists x.
  split. eapply add_composite_definitions_incr; eauto. apply PTree.gss.
  subst x; auto.
Qed.

Theorem build_composite_env_domain:
  forall env defs id co,
  build_composite_env defs = OK env ->
  env!id = Some co ->
  In (Composite id (co_sv co) (co_members co) (co_generic_origins co) (co_origin_relations co)) defs.
Proof.
  intros env0 defs0 id co.
  assert (REC: forall l env env',
    add_composite_definitions env l = OK env' ->
    env'!id = Some co ->
    env!id = Some co \/ In (Composite id (co_sv co) (co_members co) (co_generic_origins co) (co_origin_relations co)) l).
  { induction l; simpl; intros. 
  - inv H; auto.
  - destruct a; monadInv H. exploit IHl; eauto.
    unfold composite_of_def in EQ. destruct (env!id0) eqn:E; try discriminate.
    destruct (complete_members env m) eqn:C; simplify_eq EQ. clear EQ; intros EQ.
    rewrite PTree.gsspec. intros [A|A]; auto.
    destruct (peq id id0); auto.
    inv A. rewrite <- H0; auto.
  }
  intros. exploit REC; eauto. rewrite PTree.gempty. intuition congruence.
Qed.

(** As a corollay, in a consistent environment, the rank of a composite type
  is strictly greater than the ranks of its member types. *)

Remark rank_type_members:
  forall ce m ms, In m ms -> (rank_type ce (type_member m) <= rank_members ce ms)%nat.
Proof.
  induction ms; simpl; intros.
- tauto.
- destruct a; destruct H; subst; simpl.
  + lia.
  + apply IHms in H. lia.
  (* + lia. *)
  (* + apply IHms; auto. *)
Qed.

Lemma rank_struct_member:
  forall ce id co m orgs,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In m (co_members co) ->
  (rank_type ce (type_member m) < rank_type ce (Tstruct orgs id))%nat.
Proof.
  intros; simpl. rewrite H0.
  erewrite co_consistent_rank by eauto.
  exploit (rank_type_members ce); eauto.
  lia.
Qed.

Lemma rank_union_member:
  forall ce id co m orgs,
  composite_env_consistent ce ->
  ce!id = Some co ->
  In m (co_members co) ->
  (rank_type ce (type_member m) < rank_type ce (Tvariant orgs id))%nat.
Proof.
  intros; simpl. rewrite H0.
  erewrite co_consistent_rank by eauto.
  exploit (rank_type_members ce); eauto.
  lia.
Qed.


Set Implicit Arguments.

Section PROGRAMS.

(** move to Rusttypes *)
Variable F: Type.

Inductive fundef : Type :=
| Internal: F -> fundef
| External: list origin -> list origin_rel -> external_function -> typelist -> type -> calling_convention -> fundef.

Global Instance rustlight_fundef_is_internal : FundefIsInternal fundef :=
  fun f =>
    match f with
      | Internal _ => true
      | _ => false
    end.


Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_types: list composite_definition;
  prog_comp_env: composite_env;
  prog_comp_env_eq: build_composite_env prog_types = OK prog_comp_env
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.

End PROGRAMS.

Arguments External {F} _ _ _ _.

Unset Implicit Arguments.

(** * Separate compilation and linking *)

(** ** Linking types *)

Global Program Instance Linker_types : Linker type := {
  link := fun t1 t2 => if type_eq t1 t2 then Some t1 else None;
  linkorder := fun t1 t2 => t1 = t2
}.
Next Obligation.
  destruct (type_eq x y); inv H. auto.
Defined.

Global Opaque Linker_types.

(** ** Linking composite definitions *)

Definition check_compat_composite (l: list composite_definition) (cd: composite_definition) : bool :=
  List.forallb
    (fun cd' =>
      if ident_eq (name_composite_def cd') (name_composite_def cd) then composite_def_eq cd cd' else true)
    l.

Definition filter_redefs (l1 l2: list composite_definition) :=
  let names1 := map name_composite_def l1 in
  List.filter (fun cd => negb (In_dec ident_eq (name_composite_def cd) names1)) l2.

Definition link_composite_defs (l1 l2: list composite_definition): option (list composite_definition) :=
  if List.forallb (check_compat_composite l2) l1
  then Some (l1 ++ filter_redefs l1 l2)
  else None.

Lemma link_composite_def_inv:
  forall l1 l2 l,
  link_composite_defs l1 l2 = Some l ->
     (forall cd1 cd2, In cd1 l1 -> In cd2 l2 -> name_composite_def cd2 = name_composite_def cd1 -> cd2 = cd1)
  /\ l = l1 ++ filter_redefs l1 l2
  /\ (forall x, In x l <-> In x l1 \/ In x l2).
Proof.
  unfold link_composite_defs; intros.
  destruct (forallb (check_compat_composite l2) l1) eqn:C; inv H.
  assert (A: 
    forall cd1 cd2, In cd1 l1 -> In cd2 l2 -> name_composite_def cd2 = name_composite_def cd1 -> cd2 = cd1).
  { rewrite forallb_forall in C. intros.
    apply C in H. unfold check_compat_composite in H. rewrite forallb_forall in H. 
    apply H in H0. rewrite H1, dec_eq_true in H0. symmetry; eapply proj_sumbool_true; eauto. }
  split. auto. split. auto. 
  unfold filter_redefs; intros. 
  rewrite in_app_iff. rewrite filter_In. intuition auto. 
  destruct (in_dec ident_eq (name_composite_def x) (map name_composite_def l1)); simpl; auto.
  exploit list_in_map_inv; eauto. intros (y & P & Q).
  assert (x = y) by eauto. subst y. auto.
Qed.

Global Program Instance Linker_composite_defs : Linker (list composite_definition) := {
  link := link_composite_defs;
  linkorder := @List.incl composite_definition
}.
Next Obligation.
  apply incl_refl.
Defined.
Next Obligation.
  red; intros; eauto.
Defined.
Next Obligation.
  apply link_composite_def_inv in H; destruct H as (A & B & C).
  split; red; intros; apply C; auto.
Defined.

(** Connections with [build_composite_env]. *)

Lemma add_composite_definitions_append:
  forall l1 l2 env env'',
  add_composite_definitions env (l1 ++ l2) = OK env'' <->
  exists env', add_composite_definitions env l1 = OK env' /\ add_composite_definitions env' l2 = OK env''.
Proof.
  induction l1; simpl; intros.
- split; intros. exists env; auto. destruct H as (env' & A & B). congruence.
- destruct a; simpl. destruct (composite_of_def env id su m orgs org_rels); simpl.
  apply IHl1. 
  split; intros. discriminate. destruct H as (env' & A & B); discriminate.
Qed.

Lemma composite_eq:
  forall su1 m1 sz1 al1 r1 pos1 al2p1 szal1
         su2 m2 sz2 al2 r2 pos2 al2p2 szal2 orgs1 orgs2 rels1 rels2,
  su1 = su2 -> m1 = m2 -> sz1 = sz2 -> al1 = al2 -> r1 = r2 -> orgs1 = orgs2 -> rels1 = rels2 ->
  Build_composite orgs1 rels1 su1 m1 sz1 al1 r1 pos1 al2p1 szal1 = Build_composite orgs2 rels2 su2 m2 sz2 al2 r2 pos2 al2p2 szal2.
Proof.
  intros. subst.
  assert (pos1 = pos2) by apply proof_irr. 
  assert (al2p1 = al2p2) by apply proof_irr.
  assert (szal1 = szal2) by apply proof_irr.
  subst. reflexivity.
Qed.

Lemma composite_of_def_eq:
  forall env id co,
  composite_consistent env co ->
  env!id = None ->
  composite_of_def env id (co_sv co) (co_members co) (co_generic_origins co) (co_origin_relations co) = OK co.
Proof.
  intros. destruct H as [A B C D]. unfold composite_of_def. rewrite H0, A.
  destruct co; simpl in *. f_equal. apply composite_eq; auto. rewrite C, B; auto. 
Qed.

Lemma composite_consistent_unique:
  forall env co1 co2,
  composite_consistent env co1 ->
  composite_consistent env co2 ->
  co_sv co1 = co_sv co2 ->
  co_members co1 = co_members co2 ->
  co_generic_origins co1 = co_generic_origins co2 ->
  co_origin_relations co1 = co_origin_relations co2 ->
  co1 = co2.
Proof.
  intros. destruct H, H0. destruct co1, co2; simpl in *. apply composite_eq; congruence.
Qed.

Lemma composite_of_def_stable:
  forall (env env': composite_env)
         (EXTENDS: forall id co, env!id = Some co -> env'!id = Some co)
         id su m co orgs rels,
  env'!id = None ->
  composite_of_def env id su m orgs rels = OK co ->
  composite_of_def env' id su m orgs rels = OK co.
Proof.
  intros. 
  unfold composite_of_def in H0. 
  destruct (env!id) eqn:E; try discriminate.
  destruct (complete_members env m) eqn:CM; try discriminate.
  transitivity (composite_of_def env' id (co_sv co) (co_members co) (co_generic_origins co) (co_origin_relations co)).
  inv H0; auto. 
  apply composite_of_def_eq; auto. 
  apply composite_consistent_stable with env; auto. 
  inv H0; constructor; auto.
Qed.

Lemma link_add_composite_definitions:
  forall l0 env0,
  build_composite_env l0 = OK env0 ->
  forall l env1 env1' env2,
  add_composite_definitions env1 l = OK env1' ->
  (forall id co, env1!id = Some co -> env2!id = Some co) ->
  (forall id co, env0!id = Some co -> env2!id = Some co) ->
  (forall id, env2!id = if In_dec ident_eq id (map name_composite_def l0) then env0!id else env1!id) ->
  ((forall cd1 cd2, In cd1 l0 -> In cd2 l -> name_composite_def cd2 = name_composite_def cd1 -> cd2 = cd1)) ->
  { env2' |
      add_composite_definitions env2 (filter_redefs l0 l) = OK env2'
  /\ (forall id co, env1'!id = Some co -> env2'!id = Some co)
  /\ (forall id co, env0!id = Some co -> env2'!id = Some co) }.
Proof.
  induction l; simpl; intros until env2; intros ACD AGREE1 AGREE0 AGREE2 UNIQUE.
- inv ACD. exists env2; auto.
- destruct a. destruct (composite_of_def env1 id su m) as [x|e] eqn:EQ; try discriminate.
  simpl in ACD.
  generalize EQ. unfold composite_of_def at 1. 
  destruct (env1!id) eqn:E1; try congruence.
  destruct (complete_members env1 m) eqn:CM1; try congruence. 
  intros EQ1.
  simpl. destruct (in_dec ident_eq id (map name_composite_def l0)); simpl.
+ eapply IHl; eauto.
* intros. rewrite PTree.gsspec in H0. destruct (peq id0 id); auto.
  inv H0.
  exploit list_in_map_inv; eauto. intros ([id' su' m' orgs' org_rels'] & P & Q).
  assert (X: Composite id su m orgs org_rels = Composite id' su' m' orgs' org_rels').
  { eapply UNIQUE. auto. auto. rewrite <- P; auto. }
  inv X.
  exploit build_composite_env_charact; eauto. intros (co' & U & V & W & X & Y). 
  assert (co' = co).
  { apply composite_consistent_unique with env2.
    apply composite_consistent_stable with env0; auto. 
    eapply build_composite_env_consistent; eauto.
    apply composite_consistent_stable with env1; auto.
    inversion EQ1; constructor; auto. 
    inversion EQ1; auto.
    inversion EQ1; auto.
    inversion EQ1; auto.
    inversion EQ1; auto. }
  subst co'. apply AGREE0; auto. 
* intros. rewrite AGREE2. destruct (in_dec ident_eq id0 (map name_composite_def l0)); auto. 
  rewrite PTree.gsspec. destruct (peq id0 id); auto. subst id0. contradiction.
+ assert (E2: env2!id = None).
  { rewrite AGREE2. rewrite pred_dec_false by auto. auto. }
  assert (E3: composite_of_def env2 id su m orgs org_rels = OK x).
  { eapply composite_of_def_stable. eexact AGREE1. eauto. eauto. }
  rewrite E3. simpl. eapply IHl; eauto. 
* intros until co; rewrite ! PTree.gsspec. destruct (peq id0 id); auto.
* intros until co; rewrite ! PTree.gsspec. intros. destruct (peq id0 id); auto.
  subst id0. apply AGREE0 in H0. congruence.
* intros. rewrite ! PTree.gsspec. destruct (peq id0 id); auto. subst id0. 
  rewrite pred_dec_false by auto. auto.
Qed.

Theorem link_build_composite_env:
  forall l1 l2 l env1 env2,
  build_composite_env l1 = OK env1 ->
  build_composite_env l2 = OK env2 ->
  link l1 l2 = Some l ->
  { env |
     build_composite_env l = OK env
  /\ (forall id co, env1!id = Some co -> env!id = Some co)
  /\ (forall id co, env2!id = Some co -> env!id = Some co) }.
Proof.
  intros. edestruct link_composite_def_inv as (A & B & C); eauto.
  edestruct link_add_composite_definitions as (env & P & Q & R).
  eexact H.
  eexact H0.
  instantiate (1 := env1). intros. rewrite PTree.gempty in H2; discriminate.
  auto.
  intros. destruct (in_dec ident_eq id (map name_composite_def l1)); auto.
  rewrite PTree.gempty. destruct (env1!id) eqn:E1; auto. 
  exploit build_composite_env_domain. eexact H. eauto.
  intros. apply (in_map name_composite_def) in H2. elim n; auto. 
  auto.
  exists env; split; auto. subst l. apply add_composite_definitions_append. exists env1; auto. 
Qed.

(** ** Linking function definitions *)

Definition link_fundef {F: Type} (fd1 fd2: fundef F) :=
  match fd1, fd2 with
  | Internal _, Internal _ => None
  | External orgs1 rels1 ef1 targs1 tres1 cc1, External orgs2 rels2 ef2 targs2 tres2 cc2 =>
      if external_function_eq ef1 ef2
      && typelist_eq targs1 targs2
      && type_eq tres1 tres2
      && calling_convention_eq cc1 cc2
      && list_eq_dec Pos.eq_dec orgs1 orgs2
      && list_eq_dec origin_rel_eq_dec rels1 rels2
      then Some (External orgs1 rels1 ef1 targs1 tres1 cc1)
      else None
  | Internal f, External orgs rels ef targs tres cc =>
      match ef with EF_external id sg => Some (Internal f) | _ => None end
  | External orgs rels ef targs tres cc, Internal f =>
      match ef with EF_external id sg => Some (Internal f) | _ => None end
  end.

Inductive linkorder_fundef {F: Type}: fundef F -> fundef F -> Prop :=
  | linkorder_fundef_refl: forall fd,
      linkorder_fundef fd fd
  | linkorder_fundef_ext_int: forall f id sg targs tres cc orgs rels,
      linkorder_fundef (External orgs rels (EF_external id sg) targs tres cc) (Internal f).

Global Program Instance Linker_fundef (F: Type): Linker (fundef F) := {
  link := link_fundef;
  linkorder := linkorder_fundef
}.
Next Obligation.
  constructor.
Defined.
Next Obligation.
  inv H; inv H0; constructor.
Defined.
Next Obligation.
  destruct x, y; simpl in H.
+ discriminate.
+ destruct e; inv H. split; constructor.
+ destruct e; inv H. split; constructor.
+ destruct (external_function_eq e e0 && typelist_eq t t1 && type_eq t0 t2 && calling_convention_eq c c0 && list_eq_dec Pos.eq_dec l l1 && list_eq_dec origin_rel_eq_dec l0 l2) eqn:A; inv H.
  InvBooleans. subst. split; constructor.
Defined.

Remark link_fundef_either:
  forall (F: Type) (f1 f2 f: fundef F), link f1 f2 = Some f -> f = f1 \/ f = f2.
Proof.
  simpl; intros. unfold link_fundef in H. destruct f1, f2; try discriminate.
- destruct e; inv H. auto.
- destruct e; inv H. auto.
- destruct (external_function_eq e e0 && typelist_eq t t1 && type_eq t0 t2 && calling_convention_eq c c0 && list_eq_dec Pos.eq_dec l l1 &&
        list_eq_dec origin_rel_eq_dec l0 l2); inv H; auto.
Qed.

Global Opaque Linker_fundef.

(** ** Linking programs *)

Definition lift_option {A: Type} (opt: option A) : { x | opt = Some x } + { opt = None }.
Proof.
  destruct opt. left; exists a; auto. right; auto. 
Defined.

Definition link_program {F:Type} (p1 p2: program F): option (program F) :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      match lift_option (link p1.(prog_types) p2.(prog_types)) with
      | inright _ => None
      | inleft (exist typs EQ) =>
          match link_build_composite_env
                   p1.(prog_types) p2.(prog_types) typs
                   p1.(prog_comp_env) p2.(prog_comp_env)
                   p1.(prog_comp_env_eq) p2.(prog_comp_env_eq) EQ with
          | exist env (conj P Q) =>
              Some {| prog_defs := p.(AST.prog_defs);
                      prog_public := p.(AST.prog_public);
                      prog_main := p.(AST.prog_main);
                      prog_types := typs;
                      prog_comp_env := env;
                      prog_comp_env_eq := P |}
          end
      end
  end.

Definition linkorder_program {F: Type} (p1 p2: program F) : Prop :=
  linkorder (program_of_program p1) (program_of_program p2)
  /\ (forall id co, p1.(prog_comp_env)!id = Some co -> p2.(prog_comp_env)!id = Some co).

Global Program Instance Linker_program (F: Type): Linker (program F) := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  split. apply linkorder_refl. auto.
Defined.
Next Obligation.
  destruct H, H0. split. eapply linkorder_trans; eauto.
  intros; auto.
Defined.
Next Obligation.
  revert H. unfold link_program.
  destruct (link (program_of_program x) (program_of_program y)) as [p|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types x) (prog_types y))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types x) (prog_types y) typs
       (prog_comp_env x) (prog_comp_env y) (prog_comp_env_eq x)
       (prog_comp_env_eq y) EQ) as (env & P & Q & R).
  destruct (link_linkorder _ _ _ LP). 
  intros X; inv X.
  split; split;  auto.
Defined.

Global Opaque Linker_program.

(** ** Commutation between linking and program transformations *)

Section LINK_MATCH_PROGRAM_GEN.

Context {F G: Type}.
Variable match_fundef: program F -> fundef F -> fundef G -> Prop.

Hypothesis link_match_fundef:
  forall ctx1 ctx2 f1 tf1 f2 tf2 f,
  link f1 f2 = Some f ->
  match_fundef ctx1 f1 tf1 -> match_fundef ctx2 f2 tf2 ->
  exists tf, link tf1 tf2 = Some tf /\ (match_fundef ctx1 f tf \/ match_fundef ctx2 f tf).

Let match_program (p: program F) (tp: program G) : Prop :=
    Linking.match_program_gen match_fundef eq p p tp
 /\ prog_types tp = prog_types p.

Theorem link_match_program_gen:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p -> match_program p1 tp1 -> match_program p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_program p tp.
Proof.
  intros until p; intros L [M1 T1] [M2 T2].
  destruct (link_linkorder _ _ _ L) as [LO1 LO2].
Local Transparent Linker_program.
  simpl in L; unfold link_program in L.
  destruct (link (program_of_program p1) (program_of_program p2)) as [pp|] eqn:LP; try discriminate.
  assert (A: exists tpp,
               link (program_of_program tp1) (program_of_program tp2) = Some tpp
             /\ Linking.match_program_gen match_fundef eq p pp tpp).
  { eapply Linking.link_match_program; eauto.
  - intros.
    Local Transparent Linker_types.
    simpl in *. destruct (type_eq v1 v2); inv H. exists v; rewrite dec_eq_true; auto.
  }
  destruct A as (tpp & TLP & MP).
  simpl; unfold link_program. rewrite TLP.
  destruct (lift_option (link (prog_types p1) (prog_types p2))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types p1) (prog_types p2) typs
           (prog_comp_env p1) (prog_comp_env p2) (prog_comp_env_eq p1)
           (prog_comp_env_eq p2) EQ) as (env & P & Q). 
  rewrite <- T1, <- T2 in EQ.
  destruct (lift_option (link (prog_types tp1) (prog_types tp2))) as [[ttyps EQ']|EQ']; try congruence.
  assert (ttyps = typs) by congruence. subst ttyps. 
  destruct (link_build_composite_env (prog_types tp1) (prog_types tp2) typs
         (prog_comp_env tp1) (prog_comp_env tp2) (prog_comp_env_eq tp1)
         (prog_comp_env_eq tp2) EQ') as (tenv & R & S).
  assert (tenv = env) by congruence. subst tenv.
  econstructor; split; eauto. inv L. split; auto.
Qed.

End LINK_MATCH_PROGRAM_GEN.

Section LINK_MATCH_PROGRAM.

Context {F G: Type}.
Variable match_fundef: fundef F -> fundef G -> Prop.

Hypothesis link_match_fundef:
  forall f1 tf1 f2 tf2 f,
  link f1 f2 = Some f ->
  match_fundef f1 tf1 -> match_fundef f2 tf2 ->
  exists tf, link tf1 tf2 = Some tf /\ match_fundef f tf.

Let match_program (p: program F) (tp: program G) : Prop :=
    Linking.match_program (fun ctx f tf => match_fundef f tf) eq p tp
 /\ prog_types tp = prog_types p.

Theorem link_match_program:
  forall p1 p2 tp1 tp2 p,
  link p1 p2 = Some p -> match_program p1 tp1 -> match_program p2 tp2 ->
  exists tp, link tp1 tp2 = Some tp /\ match_program p tp.
Proof.
  intros. destruct H0, H1. 
Local Transparent Linker_program.
  simpl in H; unfold link_program in H.
  destruct (link (program_of_program p1) (program_of_program p2)) as [pp|] eqn:LP; try discriminate.
  assert (A: exists tpp,
               link (program_of_program tp1) (program_of_program tp2) = Some tpp
             /\ Linking.match_program (fun ctx f tf => match_fundef f tf) eq pp tpp).
  { eapply Linking.link_match_program. 
  - intros. exploit link_match_fundef; eauto. intros (tf & A & B). exists tf; auto.
  - intros.
    Local Transparent Linker_types.
    simpl in *. destruct (type_eq v1 v2); inv H4. exists v; rewrite dec_eq_true; auto.
  - eauto.
  - eauto.
  - eauto.
  - apply (link_linkorder _ _ _ LP).
  - apply (link_linkorder _ _ _ LP). }
  destruct A as (tpp & TLP & MP).
  simpl; unfold link_program. rewrite TLP.
  destruct (lift_option (link (prog_types p1) (prog_types p2))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types p1) (prog_types p2) typs
           (prog_comp_env p1) (prog_comp_env p2) (prog_comp_env_eq p1)
           (prog_comp_env_eq p2) EQ) as (env & P & Q). 
  rewrite <- H2, <- H3 in EQ.
  destruct (lift_option (link (prog_types tp1) (prog_types tp2))) as [[ttyps EQ']|EQ']; try congruence.
  assert (ttyps = typs) by congruence. subst ttyps. 
  destruct (link_build_composite_env (prog_types tp1) (prog_types tp2) typs
         (prog_comp_env tp1) (prog_comp_env tp2) (prog_comp_env_eq tp1)
         (prog_comp_env_eq tp2) EQ') as (tenv & R & S).
  assert (tenv = env) by congruence. subst tenv.
  econstructor; split; eauto. inv H. split; auto.
  unfold program_of_program; simpl. destruct pp, tpp; exact MP.
Qed.

End LINK_MATCH_PROGRAM.

(** ** Rust Interface *)

Require Import Memory Values.
Require Import LanguageInterface.

Record rust_signature : Type := mksignature {
  rs_sig_generic_origins: list origin;
  rs_sig_origins_relation: list origin_rel;
  rs_sig_args: list type;
  rs_sig_res: type;
  rs_sig_cc: calling_convention;
  rs_sig_comp_env: composite_env;
}.
  
Record rust_query :=
  rsq {
    rsq_vf: val;
    rsq_sg: rust_signature;
    rsq_args: list val;
    rsq_mem: mem;
  }.

Record rust_reply :=
  rsr {
    rsr_retval: val;
    rsr_mem: mem;
  }.

Canonical Structure li_rs :=
  {|
    query := rust_query;
    reply := rust_reply;
    entry := rsq_vf;
  |}.

(** Rust calling convention *)
Require Import CKLR CKLRAlgebra.
Require Import CallconvAlgebra.

Inductive cc_rs_query R (w: world R): relation rust_query :=
  | cc_rs_query_intro vf1 vf2 sg vargs1 vargs2 m1 m2:
      Val.inject (mi R w) vf1 vf2 ->
      Val.inject_list (mi R w) vargs1 vargs2 ->
      match_mem R w m1 m2 ->
      vf1 <> Vundef ->
      cc_rs_query R w (rsq vf1 sg vargs1 m1) (rsq vf2 sg vargs2 m2).

Inductive cc_rs_reply R (w: world R): relation rust_reply :=
  | cc_rs_reply_intro vres1 vres2 m1' m2':
      Val.inject (mi R w) vres1 vres2 ->
      match_mem R w m1' m2' ->
      cc_rs_reply R w (rsr vres1 m1') (rsr vres2 m2').

Program Definition cc_rs (R: cklr): callconv li_rs li_rs :=
  {|
    ccworld := world R;
    match_senv := match_stbls R;
    match_query := cc_rs_query R;
    match_reply := (<> cc_rs_reply R)%klr;
  |}.
Next Obligation.
  intros. eapply match_stbls_proj in H. eapply Genv.mge_public; eauto.
Qed.
Next Obligation.
  split.
  intros.
  eapply match_stbls_proj in H. erewrite <- Genv.valid_for_match; eauto.
  intros.
  eapply match_stbls_proj in H. erewrite Genv.valid_for_match; eauto.
Qed.

(** Simulation convention between Rust and C (only transform signature) *)

Definition signature_of_rust_signature (sig: rust_signature) : signature :=
  mksignature (map typ_of_type sig.(rs_sig_args)) (rettype_of_type sig.(rs_sig_res)) sig.(rs_sig_cc).

Inductive cc_rust_c_mq: rust_query -> c_query -> Prop :=
| cc_rust_c_mq_intro vf sg vargs m:
  (* how to relate signature? *)
  cc_rust_c_mq (rsq vf sg vargs m) (cq vf (signature_of_rust_signature sg) vargs m).

Inductive cc_rust_c_mr: rust_reply -> c_reply -> Prop :=
| cc_rust_c_mr_intro vres m:
  cc_rust_c_mr (rsr vres m) (cr vres m).

Program Definition cc_rust_c: callconv li_rs li_c :=
  {|
    ccworld := unit;
    match_senv _ := eq;
    match_query _ := cc_rust_c_mq;
    match_reply _ := cc_rust_c_mr;
  |}.
Next Obligation.
  split; auto.
Defined.

(* Properties of cc_rs *)
Global Instance cc_rs_ref:
  Monotonic (@cc_rs) (subcklr ++> ccref).
Proof.
intros Q R HQR. red in HQR |- *.
  intros w se1 se2 q1 q2 Hse Hq.
  destruct Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm].
  specialize (HQR w se1 se2 m1 m2 Hse Hm) as (wr & HseR & HmR & Hincr & HQR').
  exists wr. simpl in *. repeat apply conj; auto.
  - constructor; eauto.
  - intros r1 r2 (wr' & Hw' & Hr). destruct Hr as [v1 v2 m1' m2' Hvres Hm'].
    specialize (HQR' wr' m1' m2' Hm' Hw') as (w' & HmQ' & HwQ' & Hincr').
    eexists. split; eauto. constructor; eauto.
Qed.


Lemma match_rs_query_compose R12 R23 w12 w23:
  eqrel
    (cc_rs_query (R12 @ R23) (w12, w23))
    (rel_compose (cc_rs_query R12 w12) (cc_rs_query R23 w23)).
Proof.
  split.
  - intros _ _ [vf1 vf3 sg vargs1 vargs3 m1 m3 Hvf Hvargs Hm].
    simpl in *.
    apply val_inject_compose in Hvf. destruct Hvf as (vf2 & Hvf12 & Hv23).
    apply val_inject_list_compose in Hvargs. destruct Hvargs as (vargs2 & ? & ?).
    destruct Hm as (m2 & Hm12 & Hm23).
    exists (rsq vf2 sg vargs2 m2); split; constructor; simpl; eauto.
    destruct Hvf12; congruence.
  - intros q1 q3 (q2 & Hq12 & Hq23).
    destruct Hq23 as [vf1 vf2 sg vargs2 vargs3 m2 m3 Hvf Hvargs23 Hm23 Hvf1].
    inv Hq12.
    constructor; simpl.
    + apply val_inject_compose. ercompose; eauto.
    + apply val_inject_list_compose. ercompose; eauto.
    + ercompose; eauto.
    + auto.
Qed.

Lemma cc_rs_compose R12 R23:
  cceqv (cc_rs (R12 @ R23)) (cc_rs R12 @ cc_rs R23).
Proof.
split.
  - intros [w12 w23] se1 se3 q1 q3 (se2 & Hse12 & Hse23) Hq.
    apply match_rs_query_compose in Hq as (q2 & Hq12 & Hq23).
    exists (se2, w12, w23).
    repeat apply conj; cbn; eauto.
    intros r1 r3 (r2 & (w12' & Hw21' & Hr12) & (w23' & Hw23' & Hr23)).
    exists (w12', w23'). split. constructor; cbn; auto.
    destruct Hr12; inv Hr23.
    constructor; cbn; eauto.
    apply val_inject_compose; eauto.
  - intros [[se2 w12] w23] se1 se3 q1 q3 (Hse12 & Hse23) (q2 & Hq12 & Hq23).
    cbn in *. exists (w12, w23). repeat apply conj; eauto.
    + apply match_rs_query_compose; eauto.
    + intros r1 r3 ([w12' w23'] & Hw' & Hr).
      destruct Hr. cbn in *.
      apply val_inject_compose in H.
      destruct Hw' as [? ?], H as (vi & ? & ?), H0 as (mi & ? & ?).
      exists (rsr vi mi).
      split; eexists; constructor; eauto; constructor; eauto.
Qed.


(** Properties used in the proof of borrow checking *)

Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.

Lemma  co_alignof_pos: forall co,
    co_alignof co > 0.
Proof.
  intros.
  generalize (co_alignof_two_p co). intros (n & ALPOW).
  rewrite ALPOW. rewrite two_power_nat_equiv.
  generalize (Nat2Z.is_nonneg n). intros A.
  exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia.
  eauto. lia.
Qed.

(* The original field_type only produces the type with generic regions
of this struct/enum, but we need it to produce types with internal
regions of the current function. *)
(** TODO: use it to replace some code in ReplaceOrigins.v *)
Definition place_field_type (co: composite) (fid: ident) (orgs: list origin) : res type :=
   do fty <- field_type fid co.(co_members);
   let rels := combine (co.(co_generic_origins)) orgs in
   OK (replace_origin_in_type fty rels).

Lemma place_field_type_res: forall co fid orgs fty,
    place_field_type co fid orgs = OK fty ->
    exists fty', field_type fid (co_members co) = OK fty' /\ type_eq_except_origins fty fty' = true.
Admitted.

Lemma place_field_type_inv: forall co fid orgs fty,
    place_field_type co fid orgs = OK fty ->
    exists fty', 
      field_type fid (co_members co) = OK fty' 
      /\ fty = replace_origin_in_type fty' (combine (co_generic_origins co) orgs).
Admitted.


Lemma field_offset_in_max_range ce: forall ofs fofs co fty fid,
    field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = Struct ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.
  intros until fid; intros FOFS FTY R1 COMP STRUCT.
  generalize (Ptrofs.unsigned_range ofs). intros RAN1.
  generalize (sizeof_pos ce fty). intros SZGT.
  generalize (field_offset_in_range ce (co_members co) _ _ _ FOFS FTY).
  intros (DELR1 & DELR2). 
  (* not easy range proof *)
  assert (RAN2: Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned).
  {
    erewrite co_consistent_sizeof in *; eauto.
    rewrite STRUCT in *. simpl in *.
    generalize (align_le (sizeof_struct ce (co_members co)) (co_alignof co) (co_alignof_pos co)).
    intros. lia. }
  lia.
Qed.

Lemma field_offset_in_max_range1 ce: forall ofs fofs co fty fid orgs,
    field_offset ce fid (co_members co) = OK fofs ->
    place_field_type co fid orgs = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = Struct ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.
  intros. exploit place_field_type_res. eauto.
  intros (fty' & FTY' & TEQ).
  erewrite type_eq_sizeof_eq; eauto.
  eapply field_offset_in_max_range; eauto.
Qed.

Lemma variant_field_offset_in_max_range ce: forall ofs fofs co fty fid,
    variant_field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = TaggedUnion ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.  
  intros until fid; intros FOFS FTY R1 COMP ENUM.
  generalize (Ptrofs.unsigned_range ofs). intros RAN1.
  generalize (sizeof_pos ce fty). intros SZGT.
  generalize (variant_field_offset_in_range ce (co_members co) _ _ _ FOFS FTY).
  intros (DELR1 & DELR2). 
  (* not easy range proof *)
  assert (RAN2: Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned).
  {
    erewrite co_consistent_sizeof in *; eauto.
    rewrite ENUM in *. simpl in *.
    generalize (align_le (sizeof_variant ce (co_members co)) (co_alignof co) (co_alignof_pos co)).
    intros. lia. }
  lia.
Qed.

Lemma variant_field_offset_in_max_range1 ce: forall ofs fofs co fty fid orgs,
    variant_field_offset ce fid (co_members co) = OK fofs ->
    place_field_type co fid orgs = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = TaggedUnion ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.  
  intros. exploit place_field_type_res. eauto.
  intros (fty' & FTY' & TEQ).
  erewrite type_eq_sizeof_eq; eauto.
  eapply variant_field_offset_in_max_range; eauto.
Qed.

