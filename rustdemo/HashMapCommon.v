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
Require Import LanguageInterface.
Require Import MoveCheckingDomain.

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
Proof.
  induction n; intros until s''; intros STAR STEP TC NUM.
  - inv STAR. econstructor; eauto. econstructor.
    rewrite E0_right. reflexivity.
  - inv STAR. econstructor. eauto.
    eapply IHn; eauto. eapply Eapp_assoc. auto.
Qed.

End CLOSURES.


(* (* The kripke world used in proving partial safety *) *)
(* Record hmap_world := *)
(*   {  *)
(*     hmap_callee: ident + ident;         (* remember the called *)
(*     function (inl is in linked_list and inr is in the C module) to *)
(*     specify the post condition when returning the current module. How *)
(*     to generalize it? *) *)
(*     hmap_senv: Genv.symtbl; *)
(*     hmap_hash_range : int }. *)


(* (* pre-post conditions of hash function *) *)

(* Inductive hash_pre_cond_args r : list Values.val -> Prop := *)
(* | hash_pre_cond_args_intro: forall k *)
(*     (GTZ: Int.ltu Int.zero r = true) *)
(*     (CASTED1: val_casted (Vint k) type_int32s) *)
(*     (CASTED1: val_casted (Vint r) type_int32u), *)
(*     hash_pre_cond_args r [Vint k; Vint r]. *)

(* Inductive hash_post_cond_retv range : Values.val -> Prop := *)
(* | hash_post_cond_retv_intro: forall r     *)
(*     (INRAN: Int.ltu r range = true), *)
(*     hash_post_cond_retv range (Vint r). *)

(* (** Pre/Post-conditions parameterized by the function name *) *)
(* Definition linked_list_args_pre_conds r (f: ident) : list Values.val -> Prop := *)
(*   if ident_eq f hash then *)
(*     hash_pre_cond_args r *)
(*   else fun _ => True. *)

(* Definition linked_list_retv_post_conds r (f: ident) : Values.val -> Prop := *)
(*   if ident_eq f hash then *)
(*     hash_post_cond_retv r *)
(*   else fun _ => True. *)

(* (* Initial preservation and progress *) *)
(* Inductive vq_hash_map (w: hmap_world) : rust_query -> Prop := *)
(* (* incoming call of linked_list (i.e., the outgoing call of hmap) *) *)
(* | vq_hash_map_intro1: forall b f targs tres tcc vargs m orgs rels fid *)
(*     (FINDF: Genv.find_funct_ptr (globalenv w.(hmap_senv) linked_list_mod) b = Some (Internal f)) *)
(*     (NFHMAP: Genv.is_internal (Genv.globalenv w.(hmap_senv) hash_map_prog) (Vptr b Ptrofs.zero) = false) *)
(*     (TYF: type_of_function f = Tfunction orgs rels targs tres tcc) *)
(*     (NOTDROP: fn_drop_glue f = None) *)
(*     (CASTED: val_casted_list vargs targs) *)
(*     (SYM: Genv.invert_symbol w.(hmap_senv) b = Some fid) *)
(*     (PRECOND: linked_list_args_pre_conds w.(hmap_hash_range) fid vargs) *)
(*     (FIDEQ: w.(hmap_callee) = inl fid) *)
(*     (LEN: length_of_args fid = length vargs), *)
(*     vq_hash_map w (rsq (Vptr b Ptrofs.zero) (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m) *)
(* (* outgoing call (which is specific to the definition of the C *)
(* module..). For now, we only support calling the process function from *)
(* Rust side. Other functions in the C module are static. *) *)
(* | vq_hash_map_intro2: forall b f targs tres tcc vargs m orgs rels fid *)
(*     (FINDF: Genv.find_funct_ptr (Genv.globalenv w.(hmap_senv) hash_map_prog) b = Some (Ctypes.Internal f)) *)
(*     (NFLINK: Genv.is_internal (globalenv w.(hmap_senv) linked_list_mod) (Vptr b Ptrofs.zero)= false) *)
(*     (TYF: Clight.type_of_function f = Ctypes.Tfunction (to_ctypelist targs) (to_ctype tres) tcc) *)
(*     (CASTED: val_casted_list vargs targs) *)
(*     (SYM: Genv.invert_symbol w.(hmap_senv) b = Some fid) *)
(*     (** we only permit process function be called from Rust *) *)
(*     (ONLYPROCESS: fid = process) *)
(*     (TARGSEQ: targs = (Tcons (Tbox type_int32s) Tnil)) *)
(*     (TRESEQ: tres = Tbox type_int32s) *)
(*     (PRECOND: linked_list_args_pre_conds w.(hmap_hash_range) fid vargs) *)
(*     (FIDEQ: w.(hmap_callee) = inr fid) *)
(*     (LEN: length_of_args fid = length vargs), *)
(*     vq_hash_map w (rsq (Vptr b Ptrofs.zero) (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m). *)
    
(* Inductive vr_hash_map (w: hmap_world) : rust_reply -> Prop := *)
(* (* return from linked_list module *) *)
(* | vr_hash_map_intro1: forall v m fid *)
(*     (FIDEQ: w.(hmap_callee) = inl fid) *)
(*     (POSTCOND: linked_list_retv_post_conds w.(hmap_hash_range) fid v), *)
(*     vr_hash_map w (rsr v m) *)
(* (* return from hash_map module *) *)
(* | vr_hash_map_intro2: forall v m fid *)
(*     (FIDEQ: w.(hmap_callee) = inr fid), *)
(*     vr_hash_map w (rsr v m) *)
(* . *)

(* Definition wf_senv se := *)
(*   forall id, *)
(*     if in_dec ident_eq id ((prog_defs_names linked_list_mod) ++ (prog_defs_names hash_map_prog)) *)
(*     then *)
(*       exists b, Genv.find_symbol se id = Some b *)
(*     else True. *)

(* Definition hmap_inv : invariant li_rs := *)
(*   {| inv_world := hmap_world; *)
(*     symtbl_inv w se := w.(hmap_senv) = se *)
(*                        /\ wf_senv se; *)
(*     query_inv w q := vq_hash_map w q; *)
(*     reply_inv w r := vr_hash_map w r |}. *)

(** Safety interfaces for hmap.c and list.rs:

    ⟦hmap.c⟧ ⊩ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc
             ↠ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q}

    ⟦hmap.s⟧ ⊩ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_rc⋅R_ca
             ↠ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} ⋅ R_ca

    ⟦list.rs⟧ ⊩ {process ↦ ⊤, hmap_process ↦ ⊥}
             ↠ {find_process ↦ ⊤, hash ↦ P}

    ⟦list.s⟧ ⊩ {process ↦ ⊤, hmap_process ↦ ⊥} ⋅ (I_rs⋅R_ra) ⇒ (I_rs⋅R_rc⋅R_ca)
             ↠ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_ra

    ⟦list.s⟧ ⊩ {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} ⋅ R_ca
             ↠ {find_process ↦ ⊤, hash ↦ P} ⋅ I_rs⋅R_ra
             
    Note that list.rs impossibly calls hmap_process, so the ⊥
    interface can be refined to anything.

    {find_process ↦ ⊤, hash ↦ P}: hmap_ext_inv

    {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q}: hmap_int_inv

    {process ↦ ⊤, hmap_process ↦ ⊥}: list_ext_inv
 *)


Record hmap_world_ext :=
  {
    hmap_callee_ext: ident; (* remember the called function *)
    hmap_senv_ext: Genv.symtbl;
    hmap_hash_range_ext : int }.

Definition wf_senv se :=
  forall id,
    if in_dec ident_eq id (prog_defs_names hash_map_prog ++ prog_defs_names linked_list_mod)
    then
      exists b, Genv.find_symbol se id = Some b
    else True.


(** Pre- and Post- conditions for hash function *)

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

Inductive vq_hash (w: hmap_world_ext) : rust_query -> Prop :=
(* incoming call of linked_list (i.e., the outgoing call of hmap) *)
| vq_hash_intro: forall vf targs tres tcc vargs m orgs rels
    (* For safety of initial_state *)
    (FINDF: Genv.find_funct (globalenv w.(hmap_senv_ext) linked_list_mod) vf = Some (Internal hash_func))
    (CASTED: val_casted_list vargs targs)
    (TYF: type_of_function hash_func = Tfunction orgs rels targs tres tcc)
    (PRECOND: hash_pre_cond_args w.(hmap_hash_range_ext) vargs)
    (CALLEE: hmap_callee_ext w = hash),
    vq_hash w (rsq vf (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m).

Inductive vr_hash (w: hmap_world_ext) : rust_reply -> Prop :=
(* return from linked_list module *)
| vr_hash_intro: forall v m
    (POSTCOND: hash_post_cond_retv w.(hmap_hash_range_ext) v),
    vr_hash w (rsr v m).

Inductive vq_find (w: hmap_world_ext) : rust_query -> Prop :=
(* incoming call of linked_list (i.e., the outgoing call of hmap) *)
| vq_find_intro: forall vf targs tres tcc vargs m orgs rels
    (* For safety of initial_state *)
    (FINDF: Genv.find_funct (globalenv w.(hmap_senv_ext) linked_list_mod) vf = Some (Internal find_func))
    (CASTED: val_casted_list vargs targs)
    (TYF: type_of_function find_func = Tfunction orgs rels targs tres tcc)
    (LEN: length vargs = 2%nat)
    (CALLEE: hmap_callee_ext w = find),
    vq_find w (rsq vf (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m).



(** External interface for hmap.c  *)
Definition rsq_inv_hmap_ext (w: hmap_world_ext) (q: rust_query) (fid: ident) : Prop :=
  if ident_eq fid find then
    (* Although find does not have pre-and post conditions, we need to
    consider the length of arguements and the signature *)
    vq_find w q
  else if ident_eq fid hash then
         vq_hash w q 
       else False.

Definition rsr_inv_hmap_ext (w: hmap_world_ext) (r: rust_reply) (fid: ident) : Prop :=
  if ident_eq fid find then
    True
  else if ident_eq fid hash then
         vr_hash w r 
       else False.


(* Pre-conditions of rust query composed of the conditions of each
function *)
Definition rsq_inv {W: Type} (w: W) (q: rust_query) se (fn_pred: W -> rust_query -> ident -> Prop) : Prop :=
  match rsq_vf q with
  | Vptr b ofs =>
      if Ptrofs.eq_dec ofs Ptrofs.zero then
        match Genv.invert_symbol se b with
        | Some id =>
            fn_pred w q id
        | _ => False
        end
      else
        False
  | _ => False
  end.

Definition rsr_inv {W: Type} (w: W) (r: rust_reply) callee (fn_pred: W -> rust_reply -> ident -> Prop) : Prop :=
  fn_pred w r callee.
  
(* Safety interfaces for external calls of hmap.c, i.e., {find_process ↦ ⊤, hash ↦ P} *)
Definition hmap_ext_inv : invariant li_rs :=
  {| inv_world := hmap_world_ext;
    symtbl_inv w se := w.(hmap_senv_ext) = se
                       (* wf_xx_senv is used to ensure the safety of
                       function call (see eval_Eglobal) *)
                       /\ wf_senv se;
    query_inv w q := rsq_inv w q (hmap_senv_ext w) rsq_inv_hmap_ext;
    reply_inv w r := rsr_inv w r (hmap_callee_ext w) rsr_inv_hmap_ext|}.


(* External interface of linked list *)

Record list_world_ext :=
  {
    list_callee_ext: ident; (* remember the called function *)
    list_senv_ext: Genv.symtbl;
  }.



Inductive vq_process (w: list_world_ext) : rust_query -> Prop :=
| vq_process_intro: forall vf targs tres tcc vargs m orgs rels
    (* For safety of initial_state *)
    (FINDF: Genv.find_funct (Genv.globalenv w.(list_senv_ext) hash_map_prog) vf = Some (Ctypes.Internal process_func))
    (TYF: Clight.type_of_function process_func = Ctypes.Tfunction (to_ctypelist targs) (to_ctype tres) tcc)
    (CASTED: val_casted_list vargs targs)
    (TARGSEQ: targs = (Tcons (Tbox type_int32s) Tnil))
    (TRESEQ: tres = Tbox type_int32s)    
    (LEN: length vargs = 1%nat)
    (CALLEE: list_callee_ext w = process),
    vq_process w (rsq vf (mksignature orgs rels (type_list_of_typelist targs) tres tcc (prog_comp_env linked_list_mod)) vargs m).


Definition rsq_inv_list_ext (w: list_world_ext) (q: rust_query) (fid: ident) : Prop :=
  if ident_eq fid process then
    (* process ↦ ⊤. We need to consider the length of arguments and signature *)
    vq_process w q
  else if ident_eq fid hmap_process then
         (* {hmap_process ↦ ⊥} *)
         False
       else False.

Definition rsr_inv_list_ext (w: list_world_ext) (r: rust_reply) (fid: ident) : Prop :=
  if ident_eq fid process then
    (* process ↦ ⊤ *)
    True
  else if ident_eq fid hmap_process then
         (* {hmap_process ↦ ⊥} *)
         False
       else False.

(* {process ↦ ⊤, hmap_process ↦ ⊥}  *)
Definition list_ext_inv: invariant li_rs := 
  {| inv_world := list_world_ext;
    symtbl_inv w se := w.(list_senv_ext) = se
                       (* wf_senv is used to ensure the safety of
                       function call in C and Rust sides (see eval_Eglobal) *)
                       /\ wf_senv se;
    query_inv w q := rsq_inv w q (list_senv_ext w) rsq_inv_list_ext;
    reply_inv w r := rsr_inv w r (list_callee_ext w) rsr_inv_list_ext|}.

(* Incoming interface for hmap. *)

Record hmap_world_int :=
  {
    hmap_list_ext: list_world_ext;
    hmap_rs_own: rs_own_world;
  }.

Local Open Scope inv_scope.

Definition cq_inv_hmap_int (w: hmap_world_int) (q: c_query) (fid: ident) : Prop :=
  if ident_eq fid process then
    (* process ↦ ⊤⋅I_rs⋅R_rc. ⊤ requires us to consider the length of
    argument and signature *)
    query_inv ((list_ext_inv @@ rs_own) @! cc_rust_c)
      (w.(hmap_list_ext), (w.(hmap_list_ext).(list_senv_ext), w.(hmap_rs_own)), tt) q
  else if ident_eq fid hmap_process then
         (* TODO *)
         True
       else False.

Definition cr_inv_hmap_int (w: hmap_world_int) (r: c_reply) (fid: ident) : Prop :=
  if ident_eq fid process then
    (* process ↦ ⊤⋅I_rs⋅R_rc *)
    reply_inv ((list_ext_inv @@ rs_own) @! cc_rust_c)
      (w.(hmap_list_ext), (w.(hmap_list_ext).(list_senv_ext), w.(hmap_rs_own)), tt) r
  else if ident_eq fid hmap_process then
         (* TODO *)
         True
       else False.

(* Pre-conditions of rust query composed of the conditions of each
function *)
Definition cq_inv {W: Type} (w: W) (q: c_query) se (fn_pred: W -> c_query -> ident -> Prop) : Prop :=
  match cq_vf q with
  | Vptr b ofs =>
      if Ptrofs.eq_dec ofs Ptrofs.zero then
        match Genv.invert_symbol se b with
        | Some id =>
            fn_pred w q id
        | _ => False
        end
      else
        False
  | _ => False
  end.

Definition cr_inv {W: Type} (w: W) (r: c_reply) callee (fn_pred: W -> c_reply -> ident -> Prop) : Prop :=
  fn_pred w r callee
.

(* Safety interfaces for incoming calls of hmap.c,
   i.e., {process ↦ ⊤⋅I_rs⋅R_rc, hmap_process ↦ Q} *)
Definition hmap_int_inv : invariant li_c :=
  {| inv_world := hmap_world_int;
    symtbl_inv w se := (list_senv_ext (hmap_list_ext w)) = se
                       (* wf_xx_senv is used to ensure the safety of
                       function call (see eval_Eglobal) *)
                       /\ wf_senv se;
    query_inv w q := cq_inv w q (list_senv_ext (hmap_list_ext w)) cq_inv_hmap_int;
    reply_inv w r := cr_inv w r (list_callee_ext (hmap_list_ext w)) cr_inv_hmap_int|}.


Definition length_of_args (f: ident) : nat :=
  if ident_eq f find then
    2
  else
    if ident_eq f hash then
      2
    else if ident_eq f process then
           1
  else O.
  
