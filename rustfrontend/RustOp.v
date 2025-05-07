Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Rusttypes.
Require Import Errors Maps.
Require Archi.

Local Open Scope error_monad_scope.

(** Arithmetic and logical operators for the Rust languages *)

(* Redefine some classify_* functions from Cop *)

Definition classify_bool (ty: type) : classify_bool_cases :=
  match ty with
  | Tint _ _ => bool_case_i
  | Tfloat F64 => bool_case_f
  | Tfloat F32 => bool_case_s
  | Tlong _ => bool_case_l
  | _ => bool_default
  end.

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned => notint_case_i Unsigned
  | Tint _ _ => notint_case_i Signed
  | Tlong si => notint_case_l si
  | _ => notint_default
  end.

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned => neg_case_i Unsigned
  | Tint _ _ => neg_case_i Signed
  | Tfloat F64 => neg_case_f
  | Tfloat F32 => neg_case_s
  | Tlong si => neg_case_l si
  | _ => neg_default
  end.


Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
  match ty1, ty2 with
  | Tint I32 Unsigned , Tint _ _ => bin_case_i Unsigned
  | Tint _ _, Tint I32 Unsigned => bin_case_i Unsigned
  | Tint _ _ , Tint _ _ => bin_case_i Signed
  | Tlong Signed , Tlong Signed  => bin_case_l Signed
  | Tlong _ , Tlong _ => bin_case_l Unsigned
  | Tlong sg , Tint _ _ => bin_case_l sg
  | Tint _ _, Tlong sg => bin_case_l sg
  | Tfloat F32, Tfloat F32 => bin_case_s
  | Tfloat _, Tfloat _ => bin_case_f
  | Tfloat F64, (Tint _ _ | Tlong _) => bin_case_f
  | (Tint _ _ | Tlong _), Tfloat F64 => bin_case_f
  | Tfloat F32, (Tint _ _ | Tlong _) => bin_case_s
  | (Tint _ _ | Tlong _), Tfloat F32 => bin_case_s
  | _, _ => bin_default
  end.


Definition classify_shift (ty1: type) (ty2: type) :=
  match ty1, ty2 with
  | Tint I32 Unsigned, Tint _ _ => shift_case_ii Unsigned
  | Tint _ _, Tint _ _ => shift_case_ii Signed
  | Tint I32 Unsigned , Tlong _  => shift_case_il Unsigned
  | Tint _ _ , Tlong _  => shift_case_il Signed
  | Tlong s , Tint _ _  => shift_case_li s
  | Tlong s , Tlong _  => shift_case_ll s
  | _,_  => shift_default
  end.

(* sem_cast follows that in Cop.v *)


Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  (* remove non-numeric to numeric cast *)
  match tto, tfrom with
  | Tunit, Tunit => cast_case_void
  (* To [_Bool] *)
  | Tint IBool _ , Tint _ _ => cast_case_i2bool
  | Tint IBool _ , Tlong _ => cast_case_l2bool
  | Tint IBool _ , Tfloat F64 => cast_case_f2bool
  | Tint IBool _ , Tfloat F32 => cast_case_s2bool
  (* To [int] other than [_Bool] *)
  (** FIXME  *)
  | Tint sz2 si2 , Tint _ _  => cast_case_i2i sz2 si2
      (* if Archi.ptr64 then cast_case_i2i sz2 si2 *)
      (* else if intsize_eq sz2 I32 then cast_case_pointer *)
      (* else cast_case_i2i sz2 si2 *)
  | Tint sz2 si2 , Tlong _  => cast_case_l2i sz2 si2
  | Tint sz2 si2 , Tfloat F64  => cast_case_f2i sz2 si2
  | Tint sz2 si2 , Tfloat F32  => cast_case_s2i sz2 si2
  (* To [long] *)
  (** FIXME  *)
  | Tlong _ , Tlong _  => cast_case_l2l
      (* if Archi.ptr64 then cast_case_pointer else cast_case_l2l *)
  | Tlong _ , Tint sz1 si1  => cast_case_i2l si1
  | Tlong si2 , Tfloat F64  => cast_case_f2l si2
  | Tlong si2 , Tfloat F32  => cast_case_s2l si2
  (* To [float] *)
  | Tfloat F64 , Tint sz1 si1  => cast_case_i2f si1
  | Tfloat F32 , Tint sz1 si1  => cast_case_i2s si1
  | Tfloat F64 , Tlong si1  => cast_case_l2f si1
  | Tfloat F32 , Tlong si1  => cast_case_l2s si1
  | Tfloat F64 , Tfloat F64  => cast_case_f2f
  | Tfloat F32 , Tfloat F32  => cast_case_s2s
  | Tfloat F64 , Tfloat F32  => cast_case_s2f
  | Tfloat F32 , Tfloat F64  => cast_case_f2s
  (* To pointer types *)
  | Treference _ _ _ , Treference _ _ _ => cast_case_pointer
  | Tbox ty1, Tbox ty2 =>
      (* We do not allow casting box type with different inner type *)
      if type_eq ty1 ty2 then cast_case_pointer else cast_case_default
  (* To struct or union types *)
  | Tstruct _ id2 , Tstruct _ id1  => cast_case_struct id1 id2
  | Tvariant _ id2 , Tvariant _ id1  => cast_case_union id1 id2
  (* Catch-all *)
  | _, _ => cast_case_default
  end.


Definition sem_cast (v: val) (t1 t2: type) : option val :=
  match classify_cast t1 t2 with
  | cast_case_pointer =>
      match v with
      | Vptr _ _ => Some v
      | _ => None
      end
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
  | cast_case_s2s =>
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end
  | cast_case_s2f =>
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end
  | cast_case_f2s =>
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end
  | cast_case_i2f si1 =>
      match v with
      | Vint i => Some (Vfloat (cast_int_float si1 i))
      | _ => None
      end
  | cast_case_i2s si1 =>
      match v with
      | Vint i => Some (Vsingle (cast_int_single si1 i))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
          match cast_single_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_i2bool =>
      match v with
      | Vint n =>
          Some(Vint(if Int.eq n Int.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_s2bool =>
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2f si1 =>
      match v with
      | Vlong i => Some (Vfloat (cast_long_float si1 i))
      | _ => None
      end
  | cast_case_l2s si1 =>
      match v with
      | Vlong i => Some (Vsingle (cast_long_single si1 i))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
          match cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_struct id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_union id1 id2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 then Some v else None
      | _ => None
      end
  | cast_case_void =>
      match v with
      | Vint i =>
          if Int.eq i Int.zero then
            (* Tunit *)
            Some (Vint Int.zero)
          else None
      | _ => None
      end
  | cast_case_default =>
      None
  end.

Inductive val_casted : val -> type -> Prop :=
| val_casted_unit:
    val_casted (Vint Int.zero) Tunit 
| val_casted_int: forall sz si n,
    cast_int_int sz si n = n ->
    val_casted (Vint n) (Tint sz si)
| val_casted_float: forall n,
    val_casted (Vfloat n) (Tfloat F64)
| val_casted_single: forall n,
    val_casted (Vsingle n) (Tfloat F32)
| val_casted_long: forall si n,
    val_casted (Vlong n) (Tlong si)
| val_casted_box: forall b ofs ty,
    val_casted (Vptr b ofs) (Tbox ty)
| val_casted_ref: forall b ofs ty org mut,
    val_casted (Vptr b ofs) (Treference org mut ty)
| val_casted_struct: forall id orgs b ofs,
    val_casted (Vptr b ofs) (Tstruct orgs id)
| val_casted_enum: forall id orgs b ofs,
    val_casted (Vptr b ofs) (Tvariant orgs id).

Lemma val_casted_dec: forall v ty, {val_casted v ty} + {~ val_casted v ty}.
Proof.
  destruct ty; destruct v; try (right; intro CAST; inv CAST; fail); try (left; econstructor; fail).
  - destruct (Int.eq_dec i Int.zero); subst.
    left. econstructor.
    right. intro. inv H. congruence.
  - destruct (Int.eq_dec (cast_int_int i s i0) i0).
    left. econstructor; auto.
    right. intro. inv H. congruence.
  - destruct f.
    right. intro. inv H.
    left. constructor.
  - destruct f.
    left. constructor.
    right. intro. inv H.
Qed.
    
Inductive val_casted_list: list val -> typelist -> Prop :=
  | vcl_nil:
      val_casted_list nil Tnil
  | vcl_cons: forall v1 vl ty1 tyl,
      val_casted v1 ty1 -> val_casted_list vl tyl ->
      val_casted_list (v1 :: vl) (Tcons ty1 tyl).


(* move to RustOp *)
Lemma val_casted_to_ctype: forall ty v,
    val_casted v ty ->
    Cop.val_casted v (to_ctype ty).
Proof.
  destruct ty; intros v CAST; simpl in *; inv CAST; econstructor.
  unfold cast_int_int. auto.
  auto.
Qed.

Lemma val_casted_list_to_ctype: forall tyl vl,
    val_casted_list vl tyl ->
    Cop.val_casted_list vl (to_ctypelist tyl).
Proof.
  induction tyl; simpl; intros vl CAST; inv CAST; econstructor; eauto.
  eapply val_casted_to_ctype. auto.  
Qed.

Lemma val_casted_inject: forall ty v1 v2 j,
    val_casted v1 ty ->
    Val.inject j v1 v2 ->
    val_casted v2 ty.
Proof.
  destruct ty; intros v1 v2 j CAST INJ; inv CAST; inv INJ; econstructor; auto.
Qed.

Lemma val_casted_inject_list: forall tyl vl1 vl2 j,
    val_casted_list vl1 tyl ->
    Val.inject_list j vl1 vl2 ->
    val_casted_list vl2 tyl.
Proof.
  induction tyl; intros vl1 vl2 j CAST INJ; inv CAST; inv INJ; econstructor; eauto.
  eapply val_casted_inject; eauto.
Qed.


Ltac DestructCases :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: match ?x with _ => _ end = _ |- _ ] => destruct x eqn:?; DestructCases
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCases
  | [H: None = Some _ |- _ ] => discriminate H
  | [H: @eq intsize _ _ |- _ ] => discriminate H || (clear H; DestructCases)
  | [ |- val_casted (Vint (if ?x then Int.zero else Int.one)) _ ] =>
       try (constructor; destruct x; reflexivity)
  | [ |- val_casted (Vint _) (Tint ?sz ?sg) ] =>
       try (constructor; apply (cast_int_int_idem sz sg))
  | _ => idtac
  end.


Lemma cast_val_is_casted:
  forall v ty ty' v' , sem_cast v ty ty' = Some v' -> val_casted v' ty'.
Proof.
  unfold sem_cast; intros.
  destruct ty, ty'; simpl in H; DestructCases; try constructor; auto.  
Qed.

  
Ltac TrivialInject :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
  | [ |- exists v2', Some ?v = Some v2' /\ _ ] => exists v; split; auto
  (* | [H: Int.eq ?i1 ?i2 = true |- _ ] => *)
  (*     generalize (Int.eq_spec i1 i2); rewrite H; intros; subst; *)
  (*     clear H; TrivialInject *)
  (* | [ H:  match match ?i0 with IBool  => _ | _ => _ end with ?v4 => ?v5 | _ => _ end = _ |- Some _ ] => destruct i0; simpl in *; TrivialInject *)
  | _ => idtac
  end.

Lemma sem_cast_to_ctype_inject: forall f v1 v1' v2 t1 t2 m,
    sem_cast v1 t1 t2 = Some v2 ->
    Val.inject f v1 v1' ->
    exists v2', Cop.sem_cast v1' (to_ctype t1) (to_ctype t2) m = Some v2' /\ Val.inject f v2 v2'.
Proof.
  Transparent Archi.ptr64.
  unfold sem_cast; unfold Cop.sem_cast; intros; destruct t1; simpl in *; TrivialInject.  
  - destruct t2; simpl in H; destruct v1; inv H0;
      try (destruct i; simpl in *);
           try (destruct f0; simpl in *); TrivialInject.
    generalize (Int.eq_spec {| Int.intval := intval; Int.intrange := intrange |} Int.zero). rewrite Heqb. intros. rewrite H. econstructor.
  - destruct t2; inv H0; simpl in *;
     try (destruct i; simpl in *);
          try (destruct f0; simpl in *);
               try (destruct i0; simpl in *);
               TrivialInject.
  -  destruct t2; inv H0; simpl in *; TrivialInject; try(destruct i0; destruct (Archi.ptr64); simpl in *; TrivialInject; simpl in *);
    try (destruct (intsize_eq I8 I32); TrivialInject; inv e);
    try (destruct (intsize_eq I16 I32); TrivialInject; inv e);
    try (destruct f0; simpl in *; TrivialInject);
    try (destruct i; simpl in *; TrivialInject).
  - destruct t2; inv H0; simpl in *; 
    try(destruct i);  
    try(destruct Archi.ptr64 );
    try (destruct f0; simpl in *);
    try (destruct f1; simpl in *);
    TrivialInject. 
    (* econstructor. eauto. auto.     *)
  - destruct t2; inv H0; simpl in *;
    try (destruct f0);
    try (destruct i); 
    try (destruct f1); TrivialInject. 
  - destruct t2; inv H0; simpl in *;
      try(destruct i; destruct (Archi.ptr64));
       try (destruct f0); try (destruct type_eq); TrivialInject.
    econstructor. eauto. auto.
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64));
    try (destruct f0); TrivialInject. 
    econstructor; eauto; TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64));
    try (destruct f0); TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
  - destruct t2; inv H0; simpl in *;
    try(destruct i0; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2.
  - destruct t2; inv H0; simpl in *;
    try(destruct i0; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2.
Qed. 


Lemma sem_cast_id: forall v1 v2 ty1 ty2 m,
    sem_cast v1 ty1 ty2 = Some v2 ->
    Cop.sem_cast v1 (to_ctype ty1) (to_ctype ty2) m = Some v2.
Proof.
  intros.
  exploit cast_val_is_casted. eauto. intros CAST.
  exploit (sem_cast_to_ctype_inject inject_id v1 v1 v2); eauto.
  eapply val_inject_id. inv CAST; econstructor.
  instantiate (1 := m).
  intros (v2' & A1 & A2). inv A2; eauto.
  inv H0. rewrite Ptrofs.add_zero in A1. auto.
  inv CAST.
Qed.

