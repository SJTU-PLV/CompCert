Require Import Coqlib.
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown MoveChecking BorrowCheck.
Require Import Wfsimpl.
Require Import Separation.

Import ListNotations.

Definition spure := Separation.pure.

Definition STrue := spure True.

(** Try to define the sem_wt_loc/val as a coherence relation between
footprint and the memory. We try to define it using massert which
explicitly encode separation. *)

(** Definition of footprint *)

(* A tree structured footprint (maybe similar to some separation logic
algebra) *)
Inductive footprint : Type :=
| fp_emp                      (* empty footprint *)
| fp_scalar (ty: type) (v: val)       (* type must be scalar type. *)
| fp_box (b: block) (sz: Z) (fp: footprint) (* A heap block storing values that occupy footprint fp *)
(* (field ident, field type, field offset,field footprint) *)
| fp_struct (id: ident) (fpl: list (ident * Z * footprint))
(* orgs are not used for now but it is used to relate to the type *)
| fp_enum (id: ident) (orgs: list origin) (tag: Z) (fid: ident) (ofs: Z) (fp: footprint)
| fp_ref (ty: type) (phs: paths) (* reference to an owner at [phs] with type [ty] *)
.

Local Open Scope sep_scope.


(** Unused for now *)
Fixpoint mconj_list (l: list massert) : massert :=
  match l with
  | nil => STrue
  | a :: l' =>
      a ** (mconj_list l')
  end.

Inductive Forall_sep {A : Type} (P : A -> massert -> Prop) : list A -> massert -> Prop :=
    Forall_sep_nil : Forall_sep P nil STrue
  | Forall_sep_cons : forall (x : A) (l : list A) mass1 mass2,
      P x mass1 -> 
      Forall_sep P l mass2 -> 
      Forall_sep P (x :: l) (mass1 ** mass2).

(* We cannot write Forall (fun ... => sem_wt_loc ... in sem_wt_struct)
which would report error that sem_wt_loc does not occur positively, so
we define it here to make sem_wt_loc occurs positively in
sem_wt_struct case *)
Inductive fields_sep (b: block) (ofs: Z) (P: footprint -> block -> Z -> massert -> Prop) : list (ident * Z * footprint) -> massert -> Prop :=
| fields_sep_nil: fields_sep b ofs P nil STrue
| fields_sep_cons: forall fid fofs ffp l mass1 mass2
    (IND: fields_sep b ofs P l mass2)
    (FWT: P ffp b (ofs + fofs) mass1),
    fields_sep b ofs P ((fid, fofs, ffp) :: l) (mass1 ** mass2).

Section COMP_ENV.

Variable ce: composite_env.

(** * Definitions of semantics typedness *)

Definition alignof_comp (id: ident) :=
  match ce ! id with
  | Some co => co_alignof co
  | None => 1
  end.

Definition sizeof_comp (id: ident) :=
  match ce ! id with
  | Some co => co_sizeof co
  | None => 0
  end.

Inductive sem_wt_loc : footprint -> block -> Z -> massert -> Prop :=
| sem_wt_emp: forall b ofs,
    (* This location is not tracked *)
    sem_wt_loc fp_emp b ofs (spure True)
| sem_wt_scalar: forall ty b ofs chunk v
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk),
    sem_wt_loc (fp_scalar ty v) b ofs (hasvalue chunk b ofs v)
| sem_wt_box: forall b ofs fp b1 sz1 v mass
    (WTVAL: sem_wt_val (fp_box b1 sz1 fp) v mass),
    sem_wt_loc (fp_box b1 sz1 fp) b ofs ((hasvalue Mptr b ofs v) ** mass)
| sem_wt_struct: forall b ofs fpl id mass
    (FWT: fields_sep b ofs sem_wt_loc fpl mass),
    sem_wt_loc (fp_struct id fpl) b ofs mass
| sem_wt_enum: forall fp b ofs tagz fid fofs id orgs mass1 mass2
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: mass1 = hasvalue Mint32 b ofs (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc fp b (ofs + fofs) mass2),
    sem_wt_loc (fp_enum id orgs tagz fid fofs fp) b ofs (mass1 ** mass2)


with sem_wt_val : footprint -> val -> massert -> Prop :=
| wt_val_scalar: forall ty v,
    sem_wt_val (fp_scalar ty v) v (spure True)
| wt_val_box: forall b fp sz mass1 mass2
    (WTLOC: sem_wt_loc fp b 0 mass1)
    (** TODO: support negative range  *)
    (MASS: mass2 = range b (- size_chunk Mptr) sz
                   ** contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz)))
                   ** mass1)
    (* sz > 0 is used to make sure extcall_ext_free succeeds and sz <=
    max_unsigned is used to provent overflow when traversing some
    field offsets *)
    (RANGE: 0 < sz <= Ptrofs.max_unsigned),
    sem_wt_val (fp_box b sz fp) (Vptr b Ptrofs.zero) mass2
| wt_val_struct: forall b ofs id fpl mass1 mass2
    (WTLOC: sem_wt_loc (fp_struct id fpl) b (Ptrofs.unsigned ofs) mass1)
    (AL: (alignof_comp id | Ptrofs.unsigned ofs))
    (* The permission of the location is readable to make sure
    assign_loc has no memory error. *)
    (** TODO: does this value owns the location of the pointed struct?
    Or should we support share permission? What if we allow copying
    composite types? *)
    (PERM: mass2 = range b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id)),
    (** mass1 and mass2 are overlapped!! *)
    sem_wt_val (fp_struct id fpl) (Vptr b ofs) (mconj mass1 mass2)
| wt_val_enum: forall b ofs fp tagz fid fofs id orgs mass1 mass2
    (WTLOC: sem_wt_loc (fp_enum id orgs tagz fid fofs fp) b (Ptrofs.unsigned ofs) mass1)
    (AL: (alignof_comp id | Ptrofs.unsigned ofs))
    (PERM: mass2 = range b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id)),
    sem_wt_val (fp_enum id orgs tagz fid fofs fp) (Vptr b ofs) (mconj mass1 mass2).



Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPscalar: forall ty v, P (fp_scalar ty v))
  (HPbox: forall (b : block) sz (fp : footprint), P fp -> P (fp_box b sz fp))
  (HPstruct: forall id fpl, (forall fid ofs fp, In (fid, ofs, fp) fpl -> P fp) -> P (fp_struct id fpl))
  (HPenum: forall id orgs (tag : Z) fid ofs (fp : footprint), P fp -> P (fp_enum id orgs tag fid ofs fp))
  (HPref: forall ty ref_owner, P (fp_ref ty ref_owner)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as ((fid1 & ofs1) & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid ofs fp H). 
  - apply HPenum. apply strong_footprint_ind.
  - apply HPref. 
Qed.
    
End FP_IND.

(* Footprint used in interface (for now, it is just defined by
support) *)
Definition flat_footprint : Type := list block.

(* Function used to flatten a footprint  *)
Fixpoint footprint_flat (fp: footprint) : flat_footprint :=
  match fp with
  | fp_emp => nil
  | fp_scalar _ _ => nil
  | fp_ref _ _ => nil
  | fp_box b _ fp' =>
      b :: footprint_flat fp'
  | fp_struct _ fpl =>
      flat_map (fun '(_, _, fp) => footprint_flat fp) fpl
  | fp_enum _ _ _ _ _ fp =>
      footprint_flat fp
  end.

Definition footprint_disjoint (fp1 fp2: footprint) :=
  list_disjoint (footprint_flat fp1) (footprint_flat fp2).

Inductive footprint_disjoint_list : list footprint -> Prop :=
| fp_disjoint_nil: footprint_disjoint_list nil
| fp_disjoint_cons: forall fp fpl,
      list_disjoint (footprint_flat fp) (flat_map footprint_flat fpl) ->
      footprint_disjoint_list fpl ->
      footprint_disjoint_list (fp::fpl)
.

(* Definition of footprint map where each element represents the
footprint of a local variable or the footprint of the memory location
passed by reference from the caller (TODO: this part may be put at
another local environment) *)

Definition fp_map := PTree.t footprint.

(* A footprint in a function frame *)

Definition flat_fp_map (fpm: fp_map) : flat_footprint :=
  flat_map (fun elt => footprint_flat (snd elt)) (PTree.elements fpm).

(* Definiton of footprint for stack frames *)

(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* The footprint in a module *)

Inductive fp_frame : Type :=
| fpf_emp
(* we need to record the footprint of the stack *)
| fpf_func (e: env) (fpm: fp_map) (fpf: fp_frame)
(* use this to record the structure of footprint in dropplace state, rfp is the footprint of the place being dropped *)
(** We may not need fpf_dropplace. We can prove some invariant for the
places in drop_place_state, e.g., their footprint in fpm is not
shallowly fp_emp and etc. *)
(* | fpf_dropplace (e: env) (fpm: fp_map) (rfp: footprint) (fpf: fp_frame) *)
(* record the footprint in a drop glue: fpl are the footprint of the
members to be dropped (the first element of fpl is the current dropped
footprint); (b, ofs) is the address of this composite. *)
| fpf_drop (b: block) (ofs: Z) (fpl: list (ident * Z * footprint)) (fpf: fp_frame)
.

Inductive coherent_var (fpm: fp_map) (elt: (ident * (block * type))) : massert -> Prop :=
| coherent_var_intro: forall id b ty mass fp
    (ELTEQ: elt = (id, (b, ty)))
    (VARFP: fpm ! id = Some fp)
    (MASS: sem_wt_loc fp b 0 mass),
    coherent_var fpm elt mass.

(* The separation predicate for (local env, footprint map) *)
Inductive coherent_fpm (e: env) (fpm: fp_map) : massert -> Prop :=
| coherent_fpm_intro: forall mass
    (ALLSEP: Forall_sep (coherent_var fpm) (PTree.elements e) mass),
    coherent_fpm e fpm mass.


(* coherent relation between the tree-shaped footprint structure and
the concrete memory *)
Inductive coherent_fpf : fp_frame -> massert -> Prop :=
| coherent_fpf_emp: coherent_fpf fpf_emp (STrue)
| coherent_fpf_func: forall e fpm fpf mass1 mass2
    (COH1: coherent_fpm e fpm mass1)
    (COH2: coherent_fpf fpf mass2),
    coherent_fpf (fpf_func e fpm fpf) (mass1 ** mass2)
| coherent_fpf_drop: forall fpf fpl b ofs mass1 mass2
    (COH1: fields_sep b ofs sem_wt_loc fpl mass1)
    (COH2: coherent_fpf fpf mass2),
    coherent_fpf (fpf_drop b ofs fpl fpf) (mass1 ** mass2).

Inductive coherent (m: mem) (fpf: fp_frame) : Prop :=
| coherent_intro: forall mass
    (COH: coherent_fpf fpf mass)
    (MPRED: m |= mass),
    coherent m fpf.

(** Next step:   *)
