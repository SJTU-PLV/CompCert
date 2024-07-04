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


(** ** Origins  *)

Definition origin : Type := positive.

Definition origin_rel : Type := origin * origin.

Lemma origin_rel_eq_dec : forall (p1 p2 : origin_rel) , {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1, p2.
  generalize Pos.eq_dec. intros.
  decide equality.
Qed.  


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
  | Tstruct _ id1, Tstruct _ id2
  | Tvariant _ id1, Tvariant _ id2 =>
      ident_eq id1 id2
  | _, _ => type_eq ty1 ty2
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


(** Composite  *)

Inductive struct_or_variant : Set :=  Struct : struct_or_variant | TaggedUnion : struct_or_variant.

Inductive member : Type :=
  | Member_plain (id: ident) (t: type).

Definition members : Type := list member.

Inductive composite_definition : Type :=
  Composite (id: ident) (su: struct_or_variant) (m: members) (a: attr) (orgs: list origin) (org_rels: list origin_rel).

Definition name_member (m: member) : ident :=
  match m with
  | Member_plain id _ => id
  end.

Definition type_member (m: member) : type :=
  match m with
  | Member_plain _ t => t
  end.

Definition member_is_padding (m: member) : bool :=
  match m with
  | Member_plain _ _ => false
  end.

Definition name_composite_def (c: composite_definition) : ident :=
  match c with Composite id su m a _ _ => id end.

Definition composite_def_eq (x y: composite_definition): {x=y} + {x<>y}.
Proof.
  generalize Pos.eq_dec origin_rel_eq_dec. intros.
  decide equality.
  decide equality.
  decide equality.
- decide equality. decide equality. apply N.eq_dec. apply bool_dec.
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
  co_attr: attr;
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

Definition align_attr (a: attr) (al: Z) : Z :=
  match attr_alignas a with
  | Some l => two_p (Z.of_N l)
  | None => al
  end.

Fixpoint alignof (env: composite_env) (t: type) : Z :=
   (match t with
    | Tunit => 1
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

Remark align_attr_two_p:
  forall al a,
  (exists n, al = two_power_nat n) ->
  (exists n, align_attr a al = two_power_nat n).
Proof.
  intros. unfold align_attr. destruct (attr_alignas a).
  exists (N.to_nat n). rewrite two_power_nat_two_p. rewrite N_nat_Z. auto.
  auto.
Qed.

Lemma alignof_two_p:
  forall env t, exists n, alignof env t = two_power_nat n.
Proof.
  induction t; simpl.
  exists 0%nat; auto.
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

(** Recursion borrowed from Inlining.v  *)
Section OWN_TYPE.

Variable ce: composite_env.

Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> type -> bool.

Inductive composite_result : Type :=
| co_none : composite_result
| co_some (id: ident) (co: composite) (P: ce ! id = Some co).

Program Definition get_composite (id: ident) : composite_result :=
  match ce ! id with
  | None => co_none
  | Some co => co_some id co _
  end.

Definition own_type' (ty: type) : bool :=
  match ty with
  | Tstruct _ id
  | Tvariant _ id =>
      match get_composite id with
      | co_some i co P =>
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
Definition own_type (ce: composite_env) : type -> bool :=
  Fixm (@PTree_Properties.cardinal composite) own_type' ce.

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
  | Tunit => 1
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
  | Tunit => 1
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

Definition layout_field (pos: Z) (m: member) : res (Z * bitfield) :=
  match m with
  | Member_plain _ t =>
      OK (align pos (bitalignof t) / 8, Full)
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

Lemma layout_field_range: forall pos m ofs bf,
  layout_field pos m = OK (ofs, bf) ->
  pos <= layout_start ofs bf 
  /\ layout_start ofs bf + layout_width (type_member m) bf <= next_field pos m.
Proof.
  intros until bf; intros L. unfold layout_start, layout_width. destruct m; simpl in L.
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

Lemma layout_field_alignment: forall pos m ofs bf,
  layout_field pos m = OK (ofs, bf) ->
  (layout_alignment (type_member m) bf | ofs).
Proof.
  intros until bf; intros L. destruct m; simpl in L.
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
     if member_is_padding m
     then alignof_composite' env ms
     else Z.max (alignof env (type_member m)) (alignof_composite' env ms)
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

Definition bytes_of_bits (n: Z) := (n + 7) / 8.

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
  align 4 (sizeof_variant' env ms) + sizeof_variant' env ms.

(** Some properties *)

Lemma alignof_composite_two_p':
  forall env m, exists n, alignof_composite' env m = two_power_nat n.
Proof.
  induction m; simpl.
- exists 0%nat; auto.
- destruct (member_is_padding a); auto.
  apply Z.max_case; auto. apply alignof_two_p.
Qed.

Lemma alignof_composite_two_p:
  forall env m sv, exists n, alignof_composite env sv m = two_power_nat n.
Proof.
  intros. destruct sv.
  - apply alignof_composite_two_p'.
  - simpl. apply Z.max_case. exists 2%nat. auto.
    apply alignof_composite_two_p'.
Qed.


Lemma alignof_composite_pos:
  forall env m a sv, align_attr a (alignof_composite env sv m) > 0.
Proof.
  intros.
  exploit align_attr_two_p. apply (alignof_composite_two_p env m sv).
  instantiate (1 := a). intros [n EQ].
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
  apply Z.le_lteq in H as LELT. destruct LELT.
  apply Z.gt_lt_iff in H0.
  generalize (align_le 4 (sizeof_variant' env m)). intros.
  lia.
  rewrite <- H0. simpl. lia.
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
     (env: composite_env) (id: ident) (su: struct_or_variant) (m: members) (a: attr) (orgs: list origin) (org_rels: list origin_rel)
     : res composite :=
  match env!id, complete_members env m return _ with
  | Some _, _ =>
      Error (MSG "Multiple definitions of struct or variant " :: CTX id :: nil)
  | None, false =>
      Error (MSG "Incomplete struct or variant " :: CTX id :: nil)
  | None, true =>
      let al := align_attr a (alignof_composite env su m) in
      OK {| co_generic_origins := orgs;
            co_origin_relations := org_rels;
            co_sv := su;
            co_members := m;
            co_attr := a;
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
  apply align_attr_two_p. apply alignof_composite_two_p.
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
  | Composite id su m a orgs org_rels :: defs =>
      do co <- composite_of_def env id su m a orgs org_rels;
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

(** [field_offset env id fld] returns the byte offset for field [id]
  in a structure whose members are [fld].  It also returns a
  bitfield designator, giving the location of the bits to access
  within the storage unit for the bitfield. *)

Fixpoint field_offset_rec (env: composite_env) (id: ident) (ms: members) (pos: Z)
                          {struct ms} : res (Z * bitfield) :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms =>
      if ident_eq id (name_member m)
      then layout_field env pos m
      else field_offset_rec env id ms (next_field env pos m)
  end.

Definition field_offset (env: composite_env) (id: ident) (ms: members) : res (Z * bitfield) :=
  field_offset_rec env id ms 0.

(** field_offset_all returns all the byte offset for fileds in a structure  *)

Fixpoint field_offset_all_rec (env: composite_env) (ms: members) (pos: Z)
                          {struct ms} : res (list (Z * bitfield)) :=
  match ms with
  | nil => OK nil
  | m :: ms =>
      do ofsm <- layout_field env pos m;
      do ofsms <- field_offset_all_rec env ms (next_field env pos m);
      OK (ofsm :: ofsms)
  end.

Definition field_offset_all (env: composite_env) (ms: members) : res (list (Z * bitfield)) :=
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
                           (accu: list (ident * Z * bitfield)) (pos: Z)
                           {struct ms} : res (list (ident * Z * bitfield)) :=
  match ms with
  | nil => OK accu
  | m :: ms =>
      if field_zero_or_padding m then
        layout_struct_rec env ms accu (next_field env pos m)
      else
        do (p, b) <- layout_field env pos m;
        layout_struct_rec env ms (((name_member m), p ,b) :: accu) (next_field env pos m)
  end.

Definition layout_struct (env: composite_env) (ms: members) : res (list (ident * Z * bitfield)) :=
  layout_struct_rec env ms nil 0.

(** Some sanity checks about field offsets.  First, field offsets are
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall env id ofs bf ty ms pos,
  field_offset_rec env id ms pos = OK (ofs, bf) -> field_type id ms = OK ty ->
  pos <= layout_start ofs bf
  /\ layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env pos ms.
Proof.
  induction ms as [ | m ms]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)).
  + inv H0. 
    exploit layout_field_range; eauto.
    generalize (bitsizeof_struct_incr env ms (next_field env pos m)).
    lia.
  + exploit IHms; eauto.
    generalize (next_field_incr env pos m).
    lia.
Qed.

Lemma field_offset_in_range_gen:
  forall env ms id ofs bf ty,
  field_offset env id ms = OK (ofs, bf) -> field_type id ms = OK ty ->
  0 <= layout_start ofs bf
  /\ layout_start ofs bf + layout_width env ty bf <= bitsizeof_struct env 0 ms.
Proof.
  intros. eapply field_offset_rec_in_range; eauto.
Qed.

Corollary field_offset_in_range:
  forall env ms id ofs ty,
  field_offset env id ms = OK (ofs, Full) -> field_type id ms = OK ty ->
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
  forall env id1 ofs1 bf1 ty1 id2 ofs2 bf2 ty2 fld,
  field_offset env id1 fld = OK (ofs1, bf1) -> field_type id1 fld = OK ty1 ->
  field_offset env id2 fld = OK (ofs2, bf2) -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  layout_start ofs1 bf1 + layout_width env ty1 bf1 <= layout_start ofs2 bf2
  \/ layout_start ofs2 bf2 + layout_width env ty2 bf2 <= layout_start ofs1 bf1.
Proof.
  intros until fld. unfold field_offset. generalize 0 as pos.
  induction fld as [|m fld]; simpl; intros.
- discriminate.
- destruct (ident_eq id1 (name_member m)); destruct (ident_eq id2 (name_member m)).
+ congruence.
+ inv H0.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. lia.
+ inv H2.
  exploit field_offset_rec_in_range; eauto.
  exploit layout_field_range; eauto. lia.
+ eapply IHfld; eauto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Lemma field_offset_prefix:
  forall env id ofs bf fld2 fld1,
  field_offset env id fld1 = OK (ofs, bf) ->
  field_offset env id (fld1 ++ fld2) = OK (ofs, bf).
Proof.
  intros until fld1. unfold field_offset. generalize 0 as pos.
  induction fld1 as [|m fld1]; simpl; intros.
- discriminate.
- destruct (ident_eq id (name_member m)); auto.
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned_gen:
  forall env id fld ofs bf ty,
  field_offset env id fld = OK (ofs, bf) -> field_type id fld = OK ty ->
  (layout_alignment env ty bf | ofs).
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
  field_offset env id fld = OK (ofs, Full) -> field_type id fld = OK ty ->
  (alignof env ty | ofs).
Proof.
  intros. exploit field_offset_aligned_gen; eauto.
Qed.

(** [variant_field_offset env id ms] returns the byte offset (plus 4 bytes) and
    bitfield designator for accessing a member named [id] of a variant
    whose members are [ms].  The byte offset is always 0. *)

Definition variant_field_offset (env: composite_env) (id: ident) (ms: members) : res (Z * bitfield) :=
  if existsb (fun m => proj_sumbool (ident_eq id (name_member m))) ms then
    (* align all the members *)
    OK (align 32 (alignof_composite' env ms * 8) / 8 , Full)
  else Error (MSG "Unknown field " :: CTX id :: nil).


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
  auto. auto.
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
  do 5 f_equal.
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
     co_alignof co = align_attr (co_attr co) (alignof_composite env co.(co_sv) (co_members co));
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
  symmetry; rewrite B. f_equal. apply alignof_composite_stable; auto. 
  symmetry; rewrite C. f_equal. apply sizeof_composite_stable; auto.
  symmetry; rewrite D. apply rank_members_stable; auto.
Qed.

Lemma composite_of_def_consistent:
  forall env id su m a co orgs rels,
  composite_of_def env id su m a orgs rels = OK co ->
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
  forall id su m a defs env orgs rels,
  build_composite_env defs = OK env ->
  In (Composite id su m a orgs rels) defs ->
  exists co, env!id = Some co /\ co_members co = m /\ co_attr co = a /\ co_sv co = su /\ co_generic_origins co = orgs /\ co_origin_relations co = rels.
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
  In (Composite id (co_sv co) (co_members co) (co_attr co) (co_generic_origins co) (co_origin_relations co)) defs.
Proof.
  intros env0 defs0 id co.
  assert (REC: forall l env env',
    add_composite_definitions env l = OK env' ->
    env'!id = Some co ->
    env!id = Some co \/ In (Composite id (co_sv co) (co_members co) (co_attr co) (co_generic_origins co) (co_origin_relations co)) l).
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
- destruct a; simpl. destruct (composite_of_def env id su m a orgs org_rels); simpl.
  apply IHl1. 
  split; intros. discriminate. destruct H as (env' & A & B); discriminate.
Qed.

Lemma composite_eq:
  forall su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1
         su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2 orgs1 orgs2 rels1 rels2,
  su1 = su2 -> m1 = m2 -> a1 = a2 -> sz1 = sz2 -> al1 = al2 -> r1 = r2 -> orgs1 = orgs2 -> rels1 = rels2 ->
  Build_composite orgs1 rels1 su1 m1 a1 sz1 al1 r1 pos1 al2p1 szal1 = Build_composite orgs2 rels2 su2 m2 a2 sz2 al2 r2 pos2 al2p2 szal2.
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
  composite_of_def env id (co_sv co) (co_members co) (co_attr co) (co_generic_origins co) (co_origin_relations co) = OK co.
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
  co_attr co1 = co_attr co2 ->
  co_generic_origins co1 = co_generic_origins co2 ->
  co_origin_relations co1 = co_origin_relations co2 ->
  co1 = co2.
Proof.
  intros. destruct H, H0. destruct co1, co2; simpl in *. apply composite_eq; congruence.
Qed.

Lemma composite_of_def_stable:
  forall (env env': composite_env)
         (EXTENDS: forall id co, env!id = Some co -> env'!id = Some co)
         id su m a co orgs rels,
  env'!id = None ->
  composite_of_def env id su m a orgs rels = OK co ->
  composite_of_def env' id su m a orgs rels = OK co.
Proof.
  intros. 
  unfold composite_of_def in H0. 
  destruct (env!id) eqn:E; try discriminate.
  destruct (complete_members env m) eqn:CM; try discriminate.
  transitivity (composite_of_def env' id (co_sv co) (co_members co) (co_attr co) (co_generic_origins co) (co_origin_relations co)).
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
- destruct a. destruct (composite_of_def env1 id su m a) as [x|e] eqn:EQ; try discriminate.
  simpl in ACD.
  generalize EQ. unfold composite_of_def at 1. 
  destruct (env1!id) eqn:E1; try congruence.
  destruct (complete_members env1 m) eqn:CM1; try congruence. 
  intros EQ1.
  simpl. destruct (in_dec ident_eq id (map name_composite_def l0)); simpl.
+ eapply IHl; eauto.
* intros. rewrite PTree.gsspec in H0. destruct (peq id0 id); auto.
  inv H0.
  exploit list_in_map_inv; eauto. intros ([id' su' m' a' orgs' org_rels'] & P & Q).
  assert (X: Composite id su m a orgs org_rels = Composite id' su' m' a' orgs' org_rels').
  { eapply UNIQUE. auto. auto. rewrite <- P; auto. }
  inv X.
  exploit build_composite_env_charact; eauto. intros (co' & U & V & W & X & Y & Z). 
  assert (co' = co).
  { apply composite_consistent_unique with env2.
    apply composite_consistent_stable with env0; auto. 
    eapply build_composite_env_consistent; eauto.
    apply composite_consistent_stable with env1; auto.
    inversion EQ1; constructor; auto. 
    inversion EQ1; auto.
    inversion EQ1; auto.
    inversion EQ1; auto.
    inversion EQ1; auto.
    inversion EQ1; auto. }
  subst co'. apply AGREE0; auto. 
* intros. rewrite AGREE2. destruct (in_dec ident_eq id0 (map name_composite_def l0)); auto. 
  rewrite PTree.gsspec. destruct (peq id0 id); auto. subst id0. contradiction.
+ assert (E2: env2!id = None).
  { rewrite AGREE2. rewrite pred_dec_false by auto. auto. }
  assert (E3: composite_of_def env2 id su m a orgs org_rels = OK x).
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
