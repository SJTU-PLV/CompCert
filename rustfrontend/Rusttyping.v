Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Ctypes Cop Ctyping.
Require Import Globalenvs.
Require Import Rusttypes RustOp Rustlight Rustlightown.
Require Import Smallstep RustIR RustIRown.
Require Import Errors Maps.
Require Archi.

Import ListNotations.
Local Open Scope error_monad_scope.

(* To move *)
Definition type_unop (op: unary_operation) (ty: Rusttypes.type) : res type :=
  match op with
  | Onotbool =>
      match classify_bool ty with
      | bool_default => Error (msg "operator !")
      | _ => OK (Tint IBool Signed )
      end
  | Onotint =>
      match classify_notint ty with
      | notint_case_i sg => OK (Tint I32 sg )
      | notint_case_l sg => OK (Tlong sg )
      | notint_default   => Error (msg "operator ~")
      end
  | Oneg =>
      match classify_neg ty with
      | neg_case_i sg => OK (Tint I32 sg )
      | neg_case_f => OK (Tfloat F64 )
      | neg_case_s => OK (Tfloat F32 )
      | neg_case_l sg => OK (Tlong sg )
      | neg_default   => Error (msg "operator prefix -")
      end
  | Oabsfloat =>
      match classify_neg ty with
      | neg_default   => Error (msg "operator __builtin_fabs")
      | _             => OK (Tfloat F64 )
      end
  end.



Definition binarith_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg)
  | bin_case_l sg => OK (Tlong sg)
  | bin_case_f => OK (Tfloat F64 )
  | bin_case_s => OK (Tfloat F32 )
  | bin_default   => Error (msg m)
  end.

Definition binarith_int_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_case_i sg => OK (Tint I32 sg)
  | bin_case_l sg => OK (Tlong sg)
  | _ => Error (msg m)
  end.

Definition shift_op_type (ty1 ty2: type) (m: string): res type :=
  match classify_shift ty1 ty2 with
  | shift_case_ii sg | shift_case_il sg => OK (Tint I32 sg)
  | shift_case_li sg | shift_case_ll sg => OK (Tlong sg)
  | shift_default => Error (msg m)
  end.

Definition comparison_type (ty1 ty2: type) (m: string): res type :=
  match classify_binarith ty1 ty2 with
  | bin_default => Error (msg m)
  | _ => OK (Tint I32 Signed)
  end.

Definition type_binop (op: binary_operation) (ty1 ty2: type) : res type :=
  match op with
  | Oadd => binarith_type ty1 ty2 "operator +"
  | Osub => binarith_type ty1 ty2 "operator infix -"
  | Omul => binarith_type ty1 ty2 "operator infix *"
  | Odiv => binarith_type ty1 ty2 "operator /"
  | Omod => binarith_int_type ty1 ty2 "operator %"
  | Oand => binarith_int_type ty1 ty2 "operator &"
  | Oor => binarith_int_type ty1 ty2 "operator |"
  | Oxor => binarith_int_type ty1 ty2 "operator ^"
  | Oshl => shift_op_type ty1 ty2 "operator <<"
  | Oshr => shift_op_type ty1 ty2 "operator >>"
  | Oeq => comparison_type ty1 ty2 "operator =="
  | One => comparison_type ty1 ty2 "operator !="
  | Olt => comparison_type ty1 ty2 "operator <"
  | Ogt => comparison_type ty1 ty2 "operator >"
  | Ole => comparison_type ty1 ty2 "operator <="
  | Oge => comparison_type ty1 ty2 "operator >="
  end.

Ltac DestructCasesOK :=
  match goal with
  | [H: match match ?x with _ => _ end with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCasesOK
  | [H: match match ?x with _ => _ end with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCasesOK
  | [H: match ?x with _ => _ end = OK _ |- _ ] => destruct x eqn:?; DestructCasesOK
  | [H: match ?x with _ => _ end = Some _ |- _ ] => destruct x eqn:?; DestructCasesOK
  | [H: Some _ = Some _ |- _ ] => inv H; DestructCasesOK
  | [H: None = Some _ |- _ ] => discriminate
  | [H: OK _ = OK _ |- _ ] => inv H; DestructCasesOK
  | [H: Error _ = OK _ |- _ ] => discriminate
  | _ => idtac
  end.

Lemma classify_binarith_to_ctype: forall ty1 ty2 bc,
    classify_binarith ty1 ty2 = bc ->
    bc <> bin_default ->
    Cop.classify_binarith (to_ctype ty1) (to_ctype ty2) = bc.
Proof.
  intros. unfold classify_binarith in H.
  unfold Cop.classify_binarith.
  destruct ty1; destruct ty2; simpl in *; DestructCases; try congruence; auto.
Qed.

  
Lemma binarith_type_to_ctype: forall ty1 ty2 ty msg,
    binarith_type ty1 ty2 msg = OK ty ->
    Ctyping.binarith_type (to_ctype ty1) (to_ctype ty2) msg = OK (to_ctype ty).
Proof.
  intros. unfold binarith_type, classify_binarith in H.
  unfold Ctyping.binarith_type, Cop.classify_binarith.  
  destruct ty1; destruct ty2; simpl in *; DestructCasesOK; try congruence; auto.
Qed.

Lemma classify_shift_to_ctype: forall ty1 ty2 bc,
    classify_shift ty1 ty2 = bc ->
    bc <> shift_default ->
    Cop.classify_shift (to_ctype ty1) (to_ctype ty2) = bc.
Proof.
  intros. unfold classify_shift in H.
  unfold Cop.classify_shift.
  destruct ty1; destruct ty2; simpl in *; DestructCases; try congruence; auto.
  all: try destruct i0; auto.
  subst. destruct i; auto.
Qed.

Lemma classify_cmp_to_ctype: forall ty1 ty2 bc,
    classify_binarith ty1 ty2 = bc ->
    bc <> bin_default ->
    Cop.classify_cmp (to_ctype ty1) (to_ctype ty2) = cmp_default.
Proof.
  intros. unfold classify_binarith in H.
  unfold classify_cmp.
  destruct ty1; destruct ty2; simpl in *; DestructCases; try congruence; auto.
  destruct i0; auto.
  destruct i; auto. destruct i; auto.
Qed.

  
(** * Syntactic type checking  *)

Definition type_deref (ty: type) : res (type * variance) :=
  match ty with
  (* Only support box type to be dereferenced for now *)
  | Tbox tyelt => OK (tyelt, Covariant)
  (* We only suppor Invariant for nested shared reference for now *)
  | Treference _ mut tyelt => OK (tyelt, Invariant)
  | _ => Error (msg "type_deref error")
  end.

Lemma type_deref_some: forall ty1 ty2 v,
    type_deref ty1 = OK (ty2, v) ->
    ty1 = Tbox ty2 \/ (exists r mut, ty1 = Treference r mut ty2).
Proof.
  destruct ty1; intros; simpl in *; try congruence.
  left. inv H. auto.
  right. inv H. eauto.
Qed.


(* Some simple type checking (move to Rusttyping.v) *)

(* We do not support array type and function type in the variables for now *)
Definition valid_type (ty: type) : bool :=
  match ty with
  | Tarray _ _
  | Tfunction _ _ _ _ _ => false
  | _ => true
  end.


Definition not_composite (ty: type) : bool :=
  match ty with
  | Tstruct _ _
  | Tvariant _ _ => false
  | _ => true
  end.

(* check if a type is copyable *)

Definition is_box (ty: type) :=
  match ty with
  | Tbox _ => true
  | _ => false
  end.  

Definition is_reference (ty: type) :=
  match ty with
  | Treference _ _ _ => true
  | _ => false
  end.


Definition is_mutable_ref (ty: type) :=
  match ty with
  | Treference _ Mutable _ => true
  | _ => false
  end.

Definition is_immutable_ref (ty: type) :=
  match ty with
  | Treference _ Immutable _ => true
  | _ => false
  end.

Definition is_copyable (ty: type) : bool :=
  negb (move_type ty).

(* A place is movable if it is not constructed via reference *)
Fixpoint is_movable (p: place) : bool :=
  match p with
  | Pderef p1 _ =>
      is_movable p1 && is_box (typeof_place p1)
  | _ => true
  end.

Fixpoint is_mutable_place (p: place) : bool :=
  match p with
  | Plocal _ _ => true
  | Pderef p1 _ =>
      negb (is_immutable_ref (typeof_place p1)) && is_mutable_place p1
  | Pfield p1 _ _ 
  | Pdowncast p1 _ _ =>
      is_mutable_place p1
  end.

Definition typenv := PTree.t type.

Section TYPING.

Variable te: typenv.
Variable ce: composite_env.

Inductive wt_place : place -> Prop :=
| wt_local: forall id ty
    (WT1: te ! id = Some ty)
    (VTY: valid_type ty = true),
    wt_place (Plocal id ty)
| wt_deref: forall p ty v
    (WT1: wt_place p)
    (WT2: type_deref (typeof_place p) = OK (ty, v)),
    (* (VTY: valid_type ty = true), *)
    wt_place (Pderef p ty)
| wt_field: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tstruct orgs id)
    (WT3: ce ! id = Some co)
    (WT4: place_field_type co fid orgs = OK ty)
    (WT5: co.(co_sv) = Struct),
    wt_place (Pfield p fid ty)
| wt_downcast: forall p ty fid co orgs id
    (WT1: wt_place p)
    (WT2: typeof_place p = Tvariant orgs id)
    (WT3: ce ! id = Some co)
    (WT4: place_field_type co fid orgs = OK ty)
    (WT5: co.(co_sv) = TaggedUnion),
    wt_place (Pdowncast p fid ty).

(* We only support deref scalar/box/ref values for now and do not
support memory copying the struct/enum. *)
Definition access_by_value (ty: type) :=
  match access_mode ty with
  | By_value _ => true
  | _ => false
  end.

Inductive wt_pexpr: pexpr -> Prop :=
| wt_Eunit:
  wt_pexpr Eunit
| wt_Econst_int: forall n sz si,
    wt_pexpr (Econst_int n (Tint sz si))
| wt_Econst_float: forall f,
    wt_pexpr (Econst_float f (Tfloat Ctypes.F64))
| wt_Econst_single: forall f,
    wt_pexpr (Econst_single f (Tfloat Ctypes.F32))
| wt_Econst_long: forall n si,
    wt_pexpr (Econst_long n (Tlong si))
| wt_Eplace: forall p
    (WTP1: wt_place p)
    (COPY: is_copyable (typeof_place p) = true),
    (* (BYVAL: access_by_value (typeof_place p) = true), *)
    wt_pexpr (Eplace p (typeof_place p))
| wt_Ecktag: forall p fid orgs id
    (WTP1: typeof_place p = Tvariant orgs id)
    (WTP2: wt_place p),
    wt_pexpr (Ecktag p fid)
| wt_Eref: forall p org mut
    (WTP1: wt_place p),
    wt_pexpr (Eref org mut p (Treference org mut (typeof_place p)))
| wt_Eunop: forall uop pe ty
    (WTP1: wt_pexpr pe)
    (WTP2: type_unop uop (typeof_pexpr pe) = OK ty),
    wt_pexpr (Eunop uop pe ty)
| wt_Ebinop: forall bop pe1 pe2 ty
    (WTP1: wt_pexpr pe1)
    (WTP2: wt_pexpr pe2)
    (** FIXME: we use a very restrictive type checking for binary operation *)
    (WTP2: type_binop bop (typeof_pexpr pe1) (typeof_pexpr pe2) = OK ty),
    wt_pexpr (Ebinop bop pe1 pe2 ty).
    

Inductive wt_expr: expr -> Prop :=
| wt_move_place: forall p
    (WT1: wt_place p)
    (MOVE: is_movable p = true),
    (* (BYVAL: access_by_value (typeof_place p) = true), *)
    wt_expr (Emoveplace p (typeof_place p))
| wt_pure_expr: forall pe
    (SCALAR: scalar_type (typeof_pexpr pe) || is_reference (typeof_pexpr pe) = true)
    (WT1: wt_pexpr pe),
    wt_expr pe
.

Definition wt_exprlist al : Prop :=
  (* We do not support passing struct/enum via function arguments for
  now as it would introduce complicated inout parameters mechanism *)
  Forall (fun e => wt_expr e /\ access_by_value (typeof e) = true) al.

(* We should ensure that in an assignment, when source and target
types are reference/box/struct/enum, their types must have the same
structure but their regions can be different. For other types, there
should be no need to check that they are equal (as we may have type
cast), but for simplicity, we check that they are equal. *)

Inductive wt_stmt: statement -> Prop :=
| wt_Sskip: wt_stmt Sskip
| wt_Sassign: forall p e
    (WT1: wt_place p)
    (WT2: wt_expr e)
    (MUT: is_mutable_place p = true)
    (TEQ: type_eq_except_origins (typeof e) (typeof_place p) = true),
    (* Require the type of p equal to the type of e? *)
    wt_stmt (Sassign p e)
| wt_Sassign_variant: forall p id fid e co fty orgs
    (WT1: wt_place p)
    (WT2: wt_expr e)
    (WT3: ce ! id = Some co)
    (* used to prove assign_loc_variant_sound *)
    (WT4: co.(co_sv) = TaggedUnion)
    (MUT: is_mutable_place p = true)
    (PTY: typeof_place p = Tvariant orgs id)
    (FTY: place_field_type co fid orgs = OK fty)
    (TEQ: type_eq_except_origins (typeof e) fty = true),
    wt_stmt (Sassign_variant p id fid e)
| wt_Sbox: forall p e ty
    (WT1: wt_place p)
    (WT2: wt_expr e)
    (WT3: typeof_place p = Tbox ty)
    (* used to prove wt_fooprint *)
    (SZEQ: sizeof ce ty = sizeof ce (typeof e))
    (SZCK: 0 < sizeof ce (typeof e) <= Ptrofs.max_unsigned)
    (MUT: is_mutable_place p = true)
    (TEQ: type_eq_except_origins (typeof e) ty = true),
    wt_stmt (Sbox p e)
| wt_Sstoragelive: forall id,
    wt_stmt (Sstoragelive id)
| wt_Sstoragedead: forall id,
    wt_stmt (Sstoragedead id)
| wt_Sdrop: forall p
    (WT1: wt_place p)
    (MOVE: is_movable p = true),
    wt_stmt (Sdrop p)
| wt_Scall: forall p al id ty orgs rels tyl rty cc
    (WT1: wt_place p)
    (WT2: wt_exprlist al)
    (WT3: ty = Tfunction orgs rels tyl rty cc)
    (MUT: is_mutable_place p = true)
    (TEQ: type_eq_except_origins rty (typeof_place p) = true),
    (* We only support this kind of function call *)
    wt_stmt (Scall p (Eglobal id ty) al)
| wt_Sifthenelse: forall e s1 s2
    (WT1: wt_expr e)
    (WT2: wt_stmt s1)
    (WT3: wt_stmt s2),    
    wt_stmt (Sifthenelse e s1 s2)
| wt_Sreturn: forall p
    (WT1: wt_place p)
    (WT2: not_composite (typeof_place p) = true),
    wt_stmt (Sreturn p)
| wt_Ssequence: forall s1 s2
    (WT1: wt_stmt s1)
    (WT2: wt_stmt s2),
    wt_stmt (Ssequence s1 s2)
| wt_Sloop: forall s
    (WT1: wt_stmt s),
    wt_stmt (Sloop s)
| wt_Sbreak:
  wt_stmt Sbreak
| wt_Scontinue:
  wt_stmt Scontinue        
.

End TYPING.

Coercion env_to_tenv (e: env) : typenv :=
  PTree.map1 snd e.


Lemma get_tenv_some: forall e id ty,
    (env_to_tenv e) ! id = Some ty ->
    exists b, e ! id = Some (b, ty).
Proof.
  intros. unfold env_to_tenv in H. erewrite PTree.gmap1 in H.
  unfold option_map in H. destruct (e!id) eqn: A; try congruence.
  destruct p. simpl in H. inv H. eauto.
Qed.

Lemma sizeof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> size_chunk chunk = sizeof ce ty.
Proof.
  unfold Rusttypes.access_mode; intros.
  assert (size_chunk chunk = sizeof ce ty).
  {
    destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; auto.
  }
  lia.
Qed.

Lemma alignof_by_value:
  forall ce ty chunk,
  Rusttypes.access_mode ty = Ctypes.By_value chunk -> (align_chunk chunk | alignof ce ty).
Proof.
  unfold Rusttypes.access_mode; intros.
  destruct ty; try destruct i; try destruct s; try destruct f; inv H; auto;
    unfold Mptr; simpl; destruct Archi.ptr64; try apply Z.divide_refl.
  exists 2. auto.
  exists 2. auto.
Qed.

Lemma wt_place_wt_local: forall p (e: env) ce,
    wt_place e ce p ->
    exists b ty, e ! (local_of_place p) = Some (b, ty).
Proof.
  induction p; intros.
  - inv H. simpl. unfold env_to_tenv in WT1. rewrite PTree.gmap1 in WT1.
    destruct (e!i) eqn: A. inv WT1. destruct p. eauto.
    inv WT1.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
  - inv H. simpl. eauto.
Qed.

Fixpoint typeof_cont_call (ttop: type) (k: cont) : type :=
  match k with
  | Kcall p _ _ _ _ =>
      typeof_place p
  | Kstop => ttop
  | Kseq _ k
  | Kloop _ k
  (* impossible? *)
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k => typeof_cont_call ttop k
  end.


(** Typing of functions and programs *)

Fixpoint bind_vars (te: typenv) (l: list (ident * type)) : typenv :=
  match l with
  | nil => te
  | (id, ty) :: l' =>
      bind_vars (PTree.set id ty te) l'
  end.

Lemma bind_vars_app: forall l1 l2 le,
    bind_vars (bind_vars le l1) l2 = bind_vars le (l1 ++ l2).
Proof.
  induction l1; simpl; auto.
  intros. destruct a; auto.
Qed.

Lemma alloc_variables_bind_vars_eq: forall l ce le1 m1 le2 m2,
    alloc_variables ce le1 m1 l le2 m2 ->
    bind_vars (env_to_tenv le1) l = (env_to_tenv le2).
Proof.
  induction l; intros; simpl in *. inv H. auto.
  inv H. exploit IHl; eauto.
  intros. unfold env_to_tenv in *.
  rewrite <- H. f_equal.
  eapply PTree.extensionality.
  intros. rewrite PTree.gsspec.
  destruct peq. subst.
  rewrite PTree.gmap1. rewrite PTree.gss. auto.
  rewrite !PTree.gmap1. rewrite PTree.gso; eauto.
Qed.


Inductive wt_function (ce: composite_env) : function -> Prop :=
  | wt_function_intro: forall f
      (WTS1: wt_stmt (bind_vars (bind_vars (PTree.empty _) f.(fn_params)) f.(fn_vars)) ce f.(fn_body)),
      wt_function ce f.

Inductive wt_fundef (ce: composite_env) : fundef -> Prop :=
| wt_fundef_internal: forall f,
    wt_function ce f ->
    wt_fundef ce (Internal f)
| wt_fundef_external: forall ef targs tres cc orgs rels,
    (* (ef_sig ef).(sig_res) = rettype_of_type tres -> *)
    wt_fundef ce (External orgs rels ef targs tres cc).

Inductive wt_program : program -> Prop :=
| wt_program_intro: forall p,
    (forall id fd,
        In (id, Gfun fd) p.(prog_defs) ->
        wt_fundef p.(prog_comp_env) fd) ->
    wt_program p.

Section PRESERVATION.

Variable prog: program.
Hypothesis WTPROG: wt_program prog.
Variable se: Genv.symtbl.
Let ge := globalenv se prog.
Let L := semantics prog se.

Variable sg: rust_signature.
(* Well-typed continuation and state *)

Inductive wt_cont : typenv -> function -> cont -> Prop :=
| wt_Kstop: forall f te
    (WT1: wt_call_cont Kstop f.(fn_return)),
    wt_cont te f Kstop
| wt_Kseq: forall s k f te
    (WT1: wt_stmt te ge s)
    (WT2: wt_cont te f k),
    wt_cont te f (Kseq s k)
| wt_Kloop: forall s k te f
    (WT1: wt_stmt te ge s)
    (WT2: wt_cont te f k),
    wt_cont te f (Kloop s k)
| wt_Kdropplace: forall f st ps (e: env) own k
    (WT1: wt_cont e f k),
    wt_cont e f (Kdropplace f st ps e own k)
| wt_Kdropcall: forall f id st v e k membs
    (WT1: wt_cont e f k),
    wt_cont e f (Kdropcall id v st membs k)
| wt_Kcall: forall k p f f' le own te
    (WT1: wt_call_cont (Kcall p f' le own k) f.(fn_return)),
    wt_cont te f (Kcall p f' le own k)

with wt_call_cont : cont -> type -> Prop :=
| wt_call_Kstop:
  wt_call_cont Kstop (rs_sig_res sg)
| wt_call_Kcall: forall p f (le: env) own k rty
    (WT1: wt_cont le f k)
    (WT2: wt_place le ge p)
    (WT3: type_eq_except_origins rty (typeof_place p) = true),
    (* For simplicity, we do not consider casting in function call *)
  wt_call_cont (Kcall p f le own k) rty
.


Inductive wt_state : state -> Prop :=
| wt_regular_state: forall f s k (e: env) own m
    (WT1: wt_stmt e ge s)
    (WT2: wt_cont e f k),
    wt_state (State f s k e own m)
| wt_callstate: forall vf fd orgs rels tyl rty cc k m vl
    (FIND: Genv.find_funct ge vf = Some fd)
    (FTY: type_of_fundef fd = Tfunction orgs rels tyl rty cc)
    (WT1: wt_call_cont k rty),
    wt_state (Callstate vf vl k m)
| wt_returnstate: forall k rty m v
    (WT1: wt_call_cont k rty),
    wt_state (Returnstate v k m)
| wt_dropplace: forall f st drops k own m (e: env)
    (WT1: wt_cont e f k),
    wt_state (Dropplace f st drops k e own m)
| wt_dropstate: forall id v st membs k m f te
    (WT1: wt_cont te f k),
    wt_state (Dropstate id v st membs k m)
.

Hint Constructors wt_cont wt_stmt wt_state: ty.

Lemma wt_call_cont_type_eq: forall k ty1,
    wt_call_cont k ty1 ->
    type_eq_except_origins ty1 (typeof_cont_call (rs_sig_res sg) k) = true.
Proof.
  induction 1; intros; simpl in *; auto.
  eapply type_eq_except_origins_refl.
Qed.

Lemma is_wt_call_cont:
  forall te f k,
    is_call_cont k -> wt_cont te f k -> wt_call_cont k f.(fn_return).
Proof.
  intros. inv H0; simpl in H; try contradiction; auto.
Qed.

Lemma wt_cont_call_cont: forall k le f ck,
    wt_cont le f k ->
    call_cont k = Some ck ->
    wt_cont le f ck.
Proof.
  induction 1; intros CC; simpl in *; auto; try (inv CC; econstructor; eauto).
Qed.

Lemma call_cont_wt_call_cont:
  forall te f k ck,
    call_cont k = Some ck ->
    wt_cont te f k -> wt_call_cont ck f.(fn_return).
Proof.
  intros. eapply (is_wt_call_cont te).
  eapply call_cont_correct. eauto.
  eapply wt_cont_call_cont; eauto.
Qed.

(* The function found in the globalenv is well-typed *)

Lemma find_funct_wt: forall vf fd,
    Genv.find_funct ge vf = Some fd ->
    wt_fundef ge fd.
Proof.
  intros. simpl in *. inv WTPROG.
  eapply Genv.find_funct_prop; eauto.
  intros. eapply H0; eauto.
Qed.  

Lemma wt_initial_state: forall s q,
    rsq_sg q = sg ->
    initial_state ge q s ->
    wt_state s.
Proof.
  intros s q SGEQ INIT.
  inv INIT.
  exploit find_funct_wt; eauto.
  intros WTF. inv WTF.
  econstructor; eauto.
  assert (RTY: tres = (rs_sig_res sg)).
  { simpl in SGEQ. destruct sg. simpl. inv SGEQ. auto. }
  subst. econstructor.
Qed.

Lemma wt_state_step_preservation: forall s1 t s2,
    wt_state s1 ->
    Step L s1 t s2 ->
    wt_state s2.
Proof.
  intros s1 t s2 WTST STEP; inv STEP; inv WTST.
  all: try eauto with ty.
  - inv SDROP; eauto with ty.
  - inv SDROP; eauto with ty; inv WT1; eauto with ty.
  - inv WT1. simpl in *. inv H.
    econstructor; eauto.
    econstructor; eauto.
  - exploit find_funct_wt; eauto.
    intros WTF. simpl in *.
    unfold ge in FIND0. rewrite FIND in FIND0. inv FIND0.
    inv WTF. inv H0.
    inv ENTRY. exploit alloc_variables_bind_vars_eq; eauto.
    intros BINDEQ. rewrite bind_vars_app in *.
    econstructor; eauto.
    rewrite <- BINDEQ. eauto.    
    inv WT1.
    econstructor. destruct f. simpl in *. inv FTY. econstructor.
    econstructor. destruct f. simpl in *. inv FTY. econstructor; eauto.
  - inv WT1. econstructor.
    eapply call_cont_wt_call_cont; eauto.
  - inv WT1. econstructor; eauto. econstructor.
  - inv WT1; eauto with ty.    
  - inv WT2; eauto with ty.
  - inv WT2; eauto with ty.
  - inv WT2; eauto with ty.
  - inv WT1; eauto with ty.
    destruct b; eauto with ty.
  - inv WT1; eauto with ty.
  - inv WT2; eauto with ty.
  - inv WT2; eauto with ty.
Qed.

Lemma wt_state_external_preservation: forall s1 q,
    wt_state s1 ->
    at_external ge s1 q ->
    forall r s2, after_external s1 r s2 ->
            wt_state s2.
Proof.
  intros. inv H0. inv H. inv H1.
  econstructor; eauto.
Qed.

    
End PRESERVATION.

(** Type checking algorithm *)

Section COMP_ENV.

Variable ce: composite_env.


Definition type_field (ce: composite_env) (ty: type) (fid: ident) : res type :=
  match ty with
  | Tstruct orgs id =>
      match ce ! id with
      | Some co =>
          match co_sv co with
          | Struct =>
              place_field_type co fid orgs
          | _ => Error (msg "not struct in field type")
          end
      | None => Error (msg "no composite")
      end
  | _ => Error (msg "wrong struct type")                  
  end.

Definition type_downcast (ce: composite_env) (ty: type) (fid: ident) : res type :=
  match ty with
  | Tvariant orgs id =>
      match ce ! id with
      | Some co =>
          match co_sv co with
          | TaggedUnion =>
              place_field_type co fid orgs
          | _ => Error (msg "not variant in downcast type")
          end
      | None => Error (msg "no composite")
      end
  | _ => Error (msg "wrong enum type")                  
  end.


Section TENV.
Variable te: typenv.
  
  Fixpoint type_check_place (p: place) : res unit :=
    match p with
    | Plocal id ty1 =>
        match te ! id with
        | Some ty2 =>
            if type_eq ty1 ty2 && valid_type ty1 then
              OK tt
            else
              Error [CTX id; MSG " has wrong type"]
        | _ =>
            Error [CTX id; MSG " is not declared"]
        end
    | Pderef p ty =>
        do _ <- type_check_place p;
        do (ty1, _) <- type_deref (typeof_place p);
        if type_eq ty ty1 then
          OK tt
        else
          Error (msg "deref has wrong type")
    | Pfield p fid fty =>
        do _ <- type_check_place p;
        do fty1 <- type_field ce (typeof_place p) fid;
        if type_eq fty fty1 then
          OK tt
        else
          Error [CTX (local_of_place p); MSG " wrong field type"]
    | Pdowncast p fid fty =>
        do _ <- type_check_place p;
        do fty1 <- type_downcast ce (typeof_place p) fid;
        if type_eq fty fty1 then
          OK tt
        else
          Error [CTX (local_of_place p); MSG " wrong downcast type"]
    end.

Fixpoint type_check_pexpr (pe: pexpr) : res unit :=
  match pe with
  | Eunit => OK tt
  | Econst_int _ ty =>
      match ty with
      | Tint sz si => OK tt
      | _ => Error (msg "Econst_int type error")
      end
  | Econst_float _ ty =>
      match ty with
      | Tfloat Ctypes.F64 => OK tt
      | _ => Error (msg "Econst_float type error")
      end
  | Econst_single _ ty =>
      match ty with
      | Tfloat Ctypes.F32 => OK tt
      | _ => Error (msg "Econst_single type error")
      end
  | Econst_long _ ty =>
      match ty with
      | Tlong _ => OK tt
      | _ => Error (msg "Econst_long type error")
      end
  | Eplace p ty =>
      do _ <- type_check_place p;
      if is_copyable (typeof_place p) then
        if type_eq ty (typeof_place p) then
          OK tt
          (* if access_by_value (typeof_place p) then *)
          (*   OK tt *)
          (* else *)
          (*   Error (msg "Eplace type is not accessed by value") *)
        else
          Error (msg "Eplace type error")
      else Error (msg "Eplace copying a non-copyable place")
  | Ecktag p fid =>
      match typeof_place p with
      | Tvariant _ _ =>
          type_check_place p
      | _ =>
          Error (msg "Ecktag type error")
      end
  | Eref org1 mut1 p ty =>
      do _ <- type_check_place p;
      if type_eq ty (Treference org1 mut1 (typeof_place p)) then
        OK tt
      else       
        Error (msg "Eref type error")
  | Eunop uop pe ty =>
      do _ <- type_check_pexpr pe;
      do ty1 <- type_unop uop (typeof_pexpr pe);
      if type_eq ty ty1 then
        OK tt
      else
        Error (msg "Eunop type error")
  | Ebinop bop pe1 pe2 ty =>
      do _ <- type_check_pexpr pe1;
      do _ <- type_check_pexpr pe2;
      do ty1 <- type_binop bop (typeof_pexpr pe1) (typeof_pexpr pe2);
      if type_eq ty ty1 then
        OK tt
      else
        Error (msg "Ebinop type error")
  | Eglobal _ _ =>
      Error (msg "Global variables are restricted to be used")
  end.

Definition type_check_expr (e: expr) : res unit :=
  match e with
  | Emoveplace p ty =>
      do _ <- type_check_place p;      
      (** We should allow move out scalar type place?  *)
      (* if scalar_type (typeof_place p) then *)
      (*   Error (msg "Cannot move scalar type") *)
      (* else *)
      if is_movable p then
        if type_eq ty (typeof_place p) then
          OK tt
          (* if access_by_value (typeof_place p) then *)
          (*   OK tt *)
          (* else *)
          (*   Error (msg "Emoveplace type is not accessed by value") *)
        else 
          Error (msg "Emoveplace type error")
      else 
        Error (msg "Emoveplace move out a non-movable place")
  | Epure pe =>
      (* The type check here must ensure that the evaluation of pure
      expr must produce value with empty footprint (e.g., reference,
      scalar type) *)
      let ety := (typeof_pexpr pe) in
      if scalar_type ety || is_reference ety then
        type_check_pexpr pe
      else
        Error (msg "Neither scalar type or reference type in pure expression")
  end.

Fixpoint type_check_exprlist (l: list expr) : res unit :=
  match l with
  | nil => OK tt
  | e :: l' =>
      do _ <- type_check_expr e;
      if access_by_value (typeof e) then
        type_check_exprlist l'
      else
        Error (msg "type_check_exprlist: do not support passing struct/enum as arguments for now")      
  end.

Fixpoint type_check_stmt (stmt: statement) : res unit :=
  match stmt with
  | Sskip => OK tt
  | Sassign p e =>
      do _ <- type_check_expr e;
      do _ <- type_check_place p;
      if is_mutable_place p then
        if type_eq_except_origins (typeof e) (typeof_place p) then
          OK tt
        else Error (msg "assign: LHS and RHS type differs")             
      else Error (msg "Sassign: modify a not mutable place")
  | Sassign_variant p id fid e =>
      do _ <- type_check_expr e;
      do _ <- type_check_place p;
      if is_mutable_place p then
        (* p must have variant type *)
        match typeof_place p with
        | Tvariant orgs id1 =>
            if ident_eq id1 id then              
              match ce!id with
              | Some co =>
                  match co_sv co with
                  | TaggedUnion => 
                      do fty <- place_field_type co fid orgs;
                      if type_eq_except_origins (typeof e) fty then
                        OK tt
                      else
                        Error (msg "assign_variant: LHS and RHS type differs")
                  | _ => Error (msg "assign_variant: the composite is not variant")
                  end
              | _ => Error (msg "assign_variant type error")
              end
            else Error [CTX (local_of_place p);  MSG " assign_variant: variants id are not equal"]
        | _ => Error [CTX (local_of_place p);  MSG " assign_variant: the type of place is not variant"]
        end              
      else Error (msg "Sassign_variant: modify a not mutable place")
  | Sbox p e =>
      do _ <- type_check_expr e;
      do _ <- type_check_place p;
      if is_mutable_place p then
        match typeof_place p with
        | Tbox ty =>
            if type_eq_except_origins (typeof e) ty
               && Z.ltb 0 (sizeof ce (typeof e))
               && Z.leb (sizeof ce (typeof e)) Ptrofs.max_unsigned then
              OK tt
            else
              Error (msg "size error in Sbox")
        | _ =>
            Error (msg "type error in Sbox")
        end
      else Error (msg "Sbox: modify a not mutable place")
  | Sstoragelive _ | Sstoragedead _ => OK tt
  | Sdrop p =>
      do _ <- type_check_place p;
      (* For now we do not allow drop(p) where [p: &mut Box<T>]? *)
      if is_movable p then
        OK tt
      else Error (msg "Type check error: dropping a non-movable place")
  | Scall p a al =>
      do _ <- type_check_place p;
      do _ <- type_check_exprlist al;
      if is_mutable_place p then
        match a with
        | Epure (Eglobal id (Tfunction _ _ _ rty _)) =>
            if type_eq_except_origins rty (typeof_place p) then
              OK tt
            else
              Error (msg "return type is not equal to the type of place which receives the return value")
        | _ =>
            Error (msg "callee is not a global variable")
        end
      else 
        Error (msg "Type check error: mutabting a non-mutable place in Scall")
  | Sifthenelse e s1 s2 =>
      do _ <- type_check_expr e;
      do _ <- type_check_stmt s1;
      type_check_stmt s2
  | Sreturn p =>
      do _ <- type_check_place p;
      if not_composite (typeof_place p) then
        OK tt
      else
        Error (msg "return composites is not supported")
  | Ssequence s1 s2 =>
      do _ <- type_check_stmt s1;
      type_check_stmt s2
  | Sloop s =>
      type_check_stmt s
  | Sbreak | Scontinue => OK tt
  end.

End TENV.

End COMP_ENV.

(** Soundness of type checking  *)

Lemma type_field_inv ce: forall p fid fty,
    type_field ce (typeof_place p) fid = OK fty ->
    exists id orgs co, 
      typeof_place p = Tstruct orgs id
      /\ ce ! id = Some co
      /\ co_sv co = Struct
      /\ place_field_type co fid orgs = OK fty.
Proof.
  unfold type_field.
  intros. 
  destruct (typeof_place p) eqn: PTY; try congruence.
  destruct (ce!i) eqn: CO; try congruence.
  destruct (co_sv c) eqn: SV; try congruence.
  repeat eexists; eauto.
Qed.

Lemma type_downcast_inv ce: forall p fid fty,
    type_downcast ce (typeof_place p) fid = OK fty ->
    exists id orgs co, 
      typeof_place p = Tvariant orgs id
      /\ ce ! id = Some co
      /\ co_sv co = TaggedUnion
      /\ place_field_type co fid orgs = OK fty.
Proof.
  unfold type_downcast.
  intros. 
  destruct (typeof_place p) eqn: PTY; try congruence.
  destruct (ce!i) eqn: CO; try congruence.
  destruct (co_sv c) eqn: SV; try congruence.
  repeat eexists; eauto.
Qed
.

Lemma type_check_place_sound: forall ce te p,
    type_check_place ce te p = OK tt ->
    wt_place te ce p.
Proof.
  induction p; intros; simpl in *.
  - destruct (te!i) eqn: A1; try congruence.
    destruct (type_eq t t0 && valid_type t) eqn: A2; try congruence.
    eapply andb_true_iff in A2 as (A3 & A4).
    destruct type_eq in A3; simpl in A3; try congruence. subst.
    econstructor; eauto.
  - monadInv H.
    edestruct type_field_inv as (id & orgs & co & A1 & A2 & A3 & A4); eauto.
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto. 
  - monadInv H.    
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto.
  - monadInv H.
    edestruct type_downcast_inv as (id & orgs & co & A1 & A2 & A3 & A4); eauto.
    destruct type_eq; try congruence. subst.
    destruct x.
    econstructor; eauto. 
Qed.

Lemma type_check_pexpr_sound: forall ce te pe,
    type_check_pexpr ce te pe = OK tt ->
    wt_pexpr te ce pe.
Proof.
  induction pe; intros; simpl in *; try (econstructor; eauto; fail); try (destruct t; try congruence; try (destruct f0; try congruence); econstructor; fail).
  - monadInv H.
    destruct (is_copyable (typeof_place p)) eqn: COPY; try congruence. 
    destruct type_eq in EQ0; try congruence. subst.
    (* destruct (access_by_value (typeof_place p)) eqn: BYVAL; try congruence. *)
    econstructor.
    destruct x.
    eapply type_check_place_sound; eauto. auto. (* auto. *)
  - destruct (typeof_place p) eqn: TYP; try congruence.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
  - monadInv H.
    destruct type_eq in EQ0; try congruence. subst.
    destruct x.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
  - monadInv H.
    destruct type_eq in EQ2; try congruence. subst.
    destruct x.
    econstructor; eauto.
  - monadInv H.    
    destruct type_eq in EQ3; try congruence. subst.
    destruct x. destruct x0.
    econstructor; eauto.
Qed.

Lemma type_check_expr_sound: forall ce te e,
    type_check_expr ce te e = OK tt ->
    wt_expr te ce e.
Proof.
  destruct e; intros.
  - inv H. monadInv H1.    
    destruct is_movable eqn: TYP in EQ0; try congruence.
    destruct type_eq in EQ0; try congruence. subst.
    (* destruct (access_by_value (typeof_place p)) eqn: BYVAL; try congruence. *)
    destruct x.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
  - inv H.
    destruct scalar_type eqn: TYP in H1; simpl in H1; try congruence.
    econstructor; auto. rewrite TYP. auto.
    eapply type_check_pexpr_sound; eauto.
    destruct is_reference eqn: RTY in H1; simpl in H1; try congruence.
    econstructor; auto. rewrite TYP, RTY. auto.    
    eapply type_check_pexpr_sound; eauto.
Qed.

Lemma type_check_exprlist_sound: forall ce te l,
    type_check_exprlist ce te l = OK tt ->
    wt_exprlist te ce l.
Proof.
  induction l; simpl; intros.
  econstructor.
  monadInv H. destruct x.
  destruct (access_by_value (typeof a)) eqn: BYVAL; try congruence.
  econstructor; eauto.
  split.
  eapply type_check_expr_sound; eauto. auto.
  eapply IHl; eauto.
Qed.

Lemma type_check_stmt_sound: forall ce te s,
    type_check_stmt ce te s = OK tt ->
    wt_stmt te ce s.
Proof.
  induction s; simpl in *; intros CK; try (econstructor; eauto; fail).
  - monadInv CK. 
    destruct is_mutable_place eqn: MUT in EQ2; try congruence.
    destruct type_eq_except_origins eqn: TEQ in EQ2; try congruence.
    destruct x. destruct x0.
    econstructor; auto.
    eapply type_check_place_sound; eauto.
    eapply type_check_expr_sound; eauto.
  - monadInv CK. 
    destruct is_mutable_place eqn: MUT in EQ2; try congruence.
    destruct (typeof_place p) eqn: PTY in EQ2; try congruence.
    destruct (ident_eq i1 i) eqn: IDEQ in EQ2; try congruence; subst.
    destruct x. destruct x0.
    destruct (ce!i) eqn: CO; try congruence.
    destruct (co_sv c) eqn: SV; try congruence.
    monadInv EQ2.
    destruct type_eq_except_origins eqn: TEQ in EQ3; try congruence.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
    eapply type_check_expr_sound; eauto.
  - monadInv CK. 
    destruct is_mutable_place eqn: MUT in EQ2; try congruence.
    destruct x. destruct x0.
    destruct (typeof_place p) eqn: PTY; try congruence.
    destruct andb eqn: CK in EQ2; try congruence.
    rewrite !andb_true_iff in CK.
    rewrite Z.ltb_lt in CK.
    rewrite Z.leb_le in CK.
    (* rewrite Z.eqb_eq in CK. *)
    destruct CK as ((A1 & A2) & A3).
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
    eapply type_check_expr_sound; eauto.
    symmetry.
    eapply type_eq_sizeof_eq. auto.
  - monadInv CK. 
    destruct is_movable eqn: MOVE in EQ0; try congruence.
    destruct x.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
  - destruct (type_check_place ce te p) eqn: A1; simpl in CK; try congruence.
    destruct (type_check_exprlist ce te l) eqn: A2; simpl in CK; try congruence.
    destruct is_mutable_place eqn: MUT in CK; try congruence.
    destruct e; try congruence.
    destruct p0; try congruence.
    destruct t; try congruence.
    destruct u. destruct u0.
    destruct type_eq_except_origins eqn: TEQ in CK; try congruence.
    econstructor; eauto.
    eapply type_check_place_sound; eauto.
    eapply type_check_exprlist_sound; eauto.
  - monadInv CK. destruct x.
    econstructor; eauto.
  - monadInv CK. destruct x. destruct x0.
    econstructor; eauto.
    eapply type_check_expr_sound; eauto.
  - monadInv CK.
    destruct not_composite eqn: COM in EQ0; try congruence.
    destruct x. econstructor; eauto.
    eapply type_check_place_sound; eauto.
Qed.
    
(** End of syntactic type checking  *)

(** Some properties of is_prefix of well-typed places *)

Lemma projections_contain_app_one_inv: forall l1 l2 ph,
    projections_contain l1 (l2 ++ [ph]) = true ->
    l1 = l2 ++ [ph] \/ projections_contain l1 l2 = true.
Proof.
  induction l1; intros; simpl in *; auto.
  destruct l2; simpl in *.
  + destruct projection_eq; subst.
    * destruct l1; simpl in H; try congruence. auto.
    * congruence.
  + destruct projection_eq; subst.
    * exploit IHl1; eauto.
      intros [A|B].
      -- subst. left. auto.
      -- auto.
    * congruence.
Qed.

Lemma path_of_place_nil: forall p id,
    path_of_place p = (id, nil) ->
    exists ty, p = Plocal id ty.
Proof.
  induction p; intros id A; simpl in *.
  - inv A; eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    exploit app_eq_nil. eapply H1. intros (A1 & A2). inv A2.
Qed.  

Lemma path_of_place_field: forall p id fid l,
    path_of_place p = (id, l ++ [proj_field fid]) ->
    exists p' fty,
      p = Pfield p' fid fty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id fid l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. subst.
    eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
Qed.

Lemma path_of_place_deref: forall p id l ,
    path_of_place p = (id, l ++ [proj_deref]) ->
    exists p' ty,
      p = Pderef p' ty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.    
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. 
    eauto.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
Qed.

Lemma path_of_place_downcast: forall p id fid l,
    path_of_place p = (id, l ++ [proj_downcast fid]) ->
    exists p' fty,
      p = Pdowncast p' fid fty
      /\ path_of_place p' = (id, l).
Proof.
  induction p; intros id fid l A; simpl in *.
  - inv A. exploit app_eq_nil. symmetry. eapply H1.
    intros (A1 & A2). inv A2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.    
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2.
  - destruct (path_of_place p) eqn: P. inv A.
    eapply app_inj_tail in H1 as (B1 & B2). inv B2. subst.
    eauto.
Qed.

Lemma path_of_wt_place_eq: forall le ce p1 p2,
    wt_place le ce p1 ->
    wt_place le ce p2 ->
    path_of_place p1 = path_of_place p2 ->
    p1 = p2.
Proof.
  induction p1; intros p2 WT1 WT2 PEQ; simpl in *; destruct (path_of_place p2) eqn: P2; try (destruct (path_of_place p1) eqn: P1).
  - inv PEQ.
    eapply path_of_place_nil in P2 as (ty & A1). subst.
    inv WT1. inv WT2. rewrite WT0 in WT1. inv WT1. auto.
  - inv PEQ. eapply path_of_place_field in P2 as (p' & fty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
    rewrite WT5 in WT9. inv WT9. auto.
  - inv PEQ. eapply path_of_place_deref in P2 as (p' & ty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT4. inv WT4. auto.
  - inv PEQ. eapply path_of_place_downcast in P2 as (p' & fty & A1 & A2).
    subst. inv WT1. inv WT2.
    exploit IHp1. eapply WT0. eapply WT1. eauto. intros. subst.
    rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
    rewrite WT5 in WT9. inv WT9. auto.
Qed.

(** is_prefix and is_prefix_type are equivalent under two well-type places *)
Lemma is_prefix_wt: forall ce le p2 p1,
    wt_place le ce p1 ->
    wt_place le ce p2 ->
    is_prefix p1 p2 = true ->
    is_prefix_type p1 p2 = true.
Proof.
  induction p2; intros p1 WT1 WT2 PRE; simpl in *.
  - destr_prefix. inv POP0.
    destruct l; simpl in PRE1; try congruence.
    eapply path_of_place_nil in POP as (ty & A1). subst.
    inv WT1. inv WT2.
    rewrite WT0 in WT1. inv WT1.
    unfold is_prefix_type.
    destruct place_eq; try congruence. auto.    
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit projections_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_field in POP as (p' & fty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
      rewrite WT5 in WT9. inv WT9.
      eapply orb_true_iff. left.
      destruct place_eq; try congruence; auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      destruct ident_eq; try congruence; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit projections_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_deref in POP as (p' & ty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT4. inv WT4.
      eapply orb_true_iff. left.
      eapply proj_sumbool_is_true. auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      rewrite proj_sumbool_is_true; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
  - inv WT2.
    destr_prefix.
    destruct (path_of_place p2) eqn: POP2. inv POP0.
    exploit projections_contain_app_one_inv. eapply PRE1.
    intros [A|B].
    + subst. eapply path_of_place_downcast in POP as (p' & fty & A1 & A2).
      subst. inv WT1.
      exploit path_of_wt_place_eq. eapply WT0. eapply WT2.
      rewrite POP2. rewrite A2. auto. intros. subst.
      rewrite WT3 in WT7. inv WT7. rewrite WT4 in WT8. inv WT8.
      rewrite WT5 in WT9. inv WT9.
      eapply orb_true_iff. left.
      eapply proj_sumbool_is_true. auto.
    + exploit IHp2. eapply WT1. eapply WT0.
      unfold is_prefix. rewrite POP. rewrite POP2. rewrite B.
      rewrite proj_sumbool_is_true; auto.
      intros PRE2.
      eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. simpl.       
      unfold is_prefix_type in PRE2.
      eapply orb_true_iff in PRE2.
      destruct PRE2 as [A1|A1]; try apply proj_sumbool_true in A1; subst; auto.
Qed.      
  
