Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop Ctypes.
Require Import Values Globalenvs Memory.
Require Import Events.
Require Import Invariant Smallstep SmallstepLinkingSafe.
Require Import HashMap.
Require Import LinkedList RustOp Rusttypes Rustlight Rustlightown.

Local Open Scope error_monad_scope.
Import ListNotations.


Section CLOSURES.

Context {genv: Type}.
Context {state: Type}.

Variable step: genv -> state -> trace -> state -> Prop.
Variable numf: state -> nat.

Inductive starNf (ge: genv): nat -> state -> trace -> state -> Prop :=
  | starNf_refl: forall s,
      starNf ge O s E0 s
  | starNf_step: forall n s t t1 s' t2 s''
      (STEP: step ge s t1 s')
      (STAR: starNf ge n s' t2 s'')
      (TRACE: t = t1 ** t2)
      (FEQ: numf s = numf s'),
      starNf ge (S n) s t s''.

Remark starNf_star:
  forall ge n s t s', starNf ge n s t s' -> star step ge s t s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark starNf_step_right ge: forall n s t t1 s' t2 s'',
    starNf ge n s t1 s' -> step ge s' t2 s'' -> t = t1 ** t2 ->
    numf s' = numf s'' ->
    starNf ge (S n) s t s''.
Admitted.

End CLOSURES.


(* The kripke world used in proving partial safety *)
Record hmap_world :=
  { 
    hmap_callee: ident + ident;         (* remember the called
    function (inl is in linked_list and inr is in the C module) to
    specify the post condition when returning the current module. How
    to generalize it? *)
    hmap_senv: Genv.symtbl;
    hmap_hash_range : int }.


(* pre-post conditions of hash function *)

Inductive hash_pre_cond_args r : list Values.val -> Prop :=
| hash_pre_cond_args_intro: forall k
    (GTZ: Int.ltu Int.zero r = true)
    (CASTED1: val_casted (Vint k) type_int32s)
    (CASTED1: val_casted (Vint r) type_int32u),
    hash_pre_cond_args r [Vint k; Vint r].

Inductive hash_post_cond_retv range : Values.val -> Prop :=
| hash_post_cond_retv_intro: forall r    
    (INRAN: Int.ltu r range = true),
    hash_post_cond_retv range (Vint r).

(** Pre/Post-conditions parameterized by the function name *)
Definition linked_list_args_pre_conds r (f: ident) : list Values.val -> Prop :=
  if ident_eq f hash then
    hash_pre_cond_args r
  else fun _ => True.

Definition linked_list_retv_post_conds r (f: ident) : Values.val -> Prop :=
  if ident_eq f hash then
    hash_post_cond_retv r
  else fun _ => True.

Definition length_of_args (f: ident) : nat :=
  if ident_eq f find then
    2
  else
    if ident_eq f hash then
      2     
  else O.

(* Initial preservation and progress *)
Inductive vq_hash_map (w: hmap_world) : rust_query -> Prop :=
(* incoming call of linked_list (i.e., the outgoing call of hmap) *)
| vq_hash_map_intro1: forall b f targs tres tcc vargs m orgs rels fid
    (FINDF: Genv.find_funct_ptr (globalenv w.(hmap_senv) linked_list_mod) b = Some (Internal f))
    (NFHMAP: Genv.is_internal (Genv.globalenv w.(hmap_senv) hash_map_prog) (Vptr b Ptrofs.zero) = false)
    (TYF: type_of_function f = Tfunction orgs rels targs tres tcc)
    (NOTDROP: fn_drop_glue f = None)
    (CASTED: val_casted_list vargs targs)
    (SYM: Genv.invert_symbol w.(hmap_senv) b = Some fid)
    (PRECOND: linked_list_args_pre_conds w.(hmap_hash_range) fid vargs)
    (FIDEQ: w.(hmap_callee) = inl fid)
    (LEN: length_of_args fid = length vargs),
    vq_hash_map w (rsq (Vptr b Ptrofs.zero) (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m)
(* outgoing call (which is specific to the definition of the C
module..). For now, we only support calling the process function from
Rust side. Other functions in the C module are static. *)
| vq_hash_map_intro2: forall b f targs tres tcc vargs m orgs rels fid
    (FINDF: Genv.find_funct_ptr (Genv.globalenv w.(hmap_senv) hash_map_prog) b = Some (Ctypes.Internal f))
    (NFLINK: Genv.is_internal (globalenv w.(hmap_senv) linked_list_mod) (Vptr b Ptrofs.zero)= false)
    (TYF: Clight.type_of_function f = Ctypes.Tfunction (to_ctypelist targs) (to_ctype tres) tcc)
    (CASTED: val_casted_list vargs targs)
    (SYM: Genv.invert_symbol w.(hmap_senv) b = Some fid)
    (** we only permit process function be called from Rust *)
    (ONLYPROCESS: fid = process)
    (PRECOND: linked_list_args_pre_conds w.(hmap_hash_range) fid vargs)
    (FIDEQ: w.(hmap_callee) = inr fid)
    (LEN: length_of_args fid = length vargs),
    vq_hash_map w (rsq (Vptr b Ptrofs.zero) (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m).
    
Inductive vr_hash_map (w: hmap_world) : rust_reply -> Prop :=
(* return from linked_list module *)
| vr_hash_map_intro1: forall v m fid
    (FIDEQ: w.(hmap_callee) = inl fid)
    (POSTCOND: linked_list_retv_post_conds w.(hmap_hash_range) fid v),
    vr_hash_map w (rsr v m)
(* return from hash_map module *)
| vr_hash_map_intro2: forall v m fid
    (FIDEQ: w.(hmap_callee) = inr fid),
    vr_hash_map w (rsr v m)
.

Definition wf_senv se :=
  forall id,
    if in_dec ident_eq id ((prog_defs_names linked_list_mod) ++ (prog_defs_names hash_map_prog))
    then
      exists b, Genv.find_symbol se id = Some b
    else True.

Definition hmap_inv : invariant li_rs :=
  {| inv_world := hmap_world;
    symtbl_inv w se := w.(hmap_senv) = se
                       /\ wf_senv se;
    query_inv w q := vq_hash_map w q;
    reply_inv w r := vr_hash_map w r |}.

