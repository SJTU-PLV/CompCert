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

Fixpoint mconj_list (l: list massert) : massert :=
  match l with
  | nil => spure True
  | a :: l' =>
      a ** (mconj_list l')
  end.

(* We cannot write Forall (fun ... => sem_wt_loc ... in sem_wt_struct)
which would report error that sem_wt_loc does not occur positively, so
we define it here to make sem_wt_loc occurs positively in
sem_wt_struct case *)
Inductive fields_sep (b: block) (ofs: Z) (P: footprint -> block -> Z -> massert -> Prop) : list (ident * Z * footprint) -> massert -> Prop :=
| fields_sep_nil: fields_sep b ofs P nil (spure True)
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
