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
| fp_struct (id: ident) (fpl: list (ident * (Z * footprint)))
(* orgs are not used for now but it is used to relate to the type *)
| fp_enum (id: ident) (* (orgs: list origin) *) (tag: Z) (fid: ident) (ofs: Z) (fp: footprint)
| fp_ref (b: block) (ofs: Z) (phs: paths) (* reference to an owner at [phs] with type [ty] *)
.

Definition ffpty : Type := ident * (Z * footprint).

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
Inductive fields_sep (b: block) (ofs: Z) (P: footprint -> block -> Z -> massert -> Prop) : list ffpty -> massert -> Prop :=
| fields_sep_nil: fields_sep b ofs P nil STrue
| fields_sep_cons: forall fid fofs ffp l mass1 mass2
    (IND: fields_sep b ofs P l mass2)
    (FWT: P ffp b (ofs + fofs) mass1),
    fields_sep b ofs P ((fid, (fofs, ffp)) :: l) (mass1 ** mass2).

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
| sem_wt_ref: forall b1 b2 ofs1 ofs2 phs,
    sem_wt_loc (fp_ref b2 ofs2 phs) b1 ofs1 (hasvalue Mptr b1 ofs1 (Vptr b2 (Ptrofs.repr ofs2)))
| sem_wt_box: forall b ofs fp b1 sz1 v mass
    (WTVAL: sem_wt_val (fp_box b1 sz1 fp) v mass),
    sem_wt_loc (fp_box b1 sz1 fp) b ofs ((hasvalue Mptr b ofs v) ** mass)
| sem_wt_struct: forall b ofs fpl id mass
    (FWT: fields_sep b ofs sem_wt_loc fpl mass),
    sem_wt_loc (fp_struct id fpl) b ofs mass
| sem_wt_enum: forall fp b ofs tagz fid fofs id mass1 mass2
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: mass1 = hasvalue Mint32 b ofs (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc fp b (ofs + fofs) mass2),
    sem_wt_loc (fp_enum id tagz fid fofs fp) b ofs (mass1 ** mass2)


with sem_wt_val : footprint -> val -> massert -> Prop :=
| wt_val_scalar: forall ty v,
    sem_wt_val (fp_scalar ty v) v (spure True)
| wt_val_box: forall b fp sz mass1 mass2
    (WTLOC: sem_wt_loc fp b 0 mass1)
    (** TODO: support negative range  *)
    (MASS: mass2 = (mconj (range b (- size_chunk Mptr) sz)
                      (* note that (-8, sz) is overlapped with mass1
                      and the following contains_neg*)
                      ((contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz)))))
                      ** mass1))
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
| wt_val_enum: forall b ofs fp tagz fid fofs id mass1 mass2
    (WTLOC: sem_wt_loc (fp_enum id tagz fid fofs fp) b (Ptrofs.unsigned ofs) mass1)
    (AL: (alignof_comp id | Ptrofs.unsigned ofs))
    (PERM: mass2 = range b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id)),
    sem_wt_val (fp_enum id tagz fid fofs fp) (Vptr b ofs) (mconj mass1 mass2).



Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPscalar: forall ty v, P (fp_scalar ty v))
  (HPbox: forall (b : block) sz (fp : footprint), P fp -> P (fp_box b sz fp))
  (HPstruct: forall id fpl, (forall fid ofs fp, In (fid, (ofs, fp)) fpl -> P fp) -> P (fp_struct id fpl))
  (HPenum: forall id (tag : Z) fid ofs (fp : footprint), P fp -> P (fp_enum id tag fid ofs fp))
  (HPref: forall b ofs ref_owner, P (fp_ref b ofs ref_owner)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as (fid1 & ofs1 & fp1).  simpl in H. destruct H.
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
  | fp_ref _ _ _ => nil
  | fp_box b _ fp' =>
      b :: footprint_flat fp'
  | fp_struct _ fpl =>
      flat_map (fun '(_, (_, fp)) => footprint_flat fp) fpl
  | fp_enum _ _ _ _ fp =>
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

Definition fenv := PTree.t (block * Z * type).

(** Footprint map which records the footprint starting from stack
blocks (denoted by variable names). It represents the ownership chain
from a stack block. *)

(* The footprint in a module *)

Inductive fp_frame : Type :=
| fpf_emp
(* we need to record the footprint of the stack. Can we just use one
local environment to record the location of local variables and
locations passed by reference from the caller? *)
| fpf_func (e: fenv) (fpm: fp_map) (fpf: fp_frame)
(* use this to record the structure of footprint in dropplace state, rfp is the footprint of the place being dropped *)
(** We may not need fpf_dropplace. We can prove some invariant for the
places in drop_place_state, e.g., their footprint in fpm is not
shallowly fp_emp and etc. *)
(* | fpf_dropplace (e: env) (fpm: fp_map) (rfp: footprint) (fpf: fp_frame) *)
(* record the footprint in a drop glue: fpl are the footprint of the
members to be dropped (the first element of fpl is the current dropped
footprint); (b, ofs) is the address of this composite. *)
| fpf_drop (b: block) (ofs: Z) (fpl: list (ffpty)) (fpf: fp_frame)
.

Inductive coherent_var (fpm: fp_map) (elt: (ident * (block * Z * type))) : massert -> Prop :=
| coherent_var_intro: forall id b ofs ty mass fp
    (ELTEQ: elt = (id, (b, ofs, ty)))
    (* What if fpm contains more variables than local env? *)
    (VARFP: fpm ! id = Some fp)
    (MASS: sem_wt_loc fp b 0 mass),
    (* local variables are freeable (defined by range) *)
    coherent_var fpm elt (mconj mass (range b ofs (sizeof ce ty))).

(* The separation predicate for (local env, footprint map) *)
Inductive coherent_fpm (e: fenv) (fpm: fp_map) : massert -> Prop :=
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

End COMP_ENV.

(** Functions for getting and updating the footprint map. *)

(* [set_footprint] and [set_footprint_map] set some footprint [fp] to
the path (id, phl); [get_footprint] gets footprint from a footprint
with a path and [get_loc_footprint_map] gets footprint and the
location storing this footprint; [clear_footprint(_map)] set the
footprint at the path [phl] to fp_emp; We also need to distinguish
getting footprint through owner path and arbitary path (i.e., paths
containing dereference reference), so we define [get_footprint(_map)
to get the footprint from arbitary path which uses a function
[get_owner_loc_footprint_(map)]] which gets footprint from only owner
paths. This distinguishment may not be needed for set functions as we
can ensure that we only set owner paths?  *)

(** TODO: it would be better to use list_find and its properties from stdpp. *)
Definition find_field {A: Type} (id: ident) (l: list (ident * A)) : option (ident * A) :=
  find (fun '(id', _) => if ident_eq id id' then true else false) l. 

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

Definition set_field_fp (fid: ident) (vfp: footprint) (fpl: list (ffpty)) : list ffpty :=
  set_field fid (fun '(fofs, ffp) => (fofs, vfp)) fpl.

(* set footprint [v] in the path [ph] of footprint [fp] *)
Fixpoint set_footprint (phl: list path) (v: footprint) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some v
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b sz fp1 =>
          match set_footprint l v fp1 with
          | Some fp2 =>
              Some (fp_box b sz fp2)
          | None => None
          end
      | ph_field fid, fp_struct id fpl =>
          match find_field fid fpl with
          | Some (fid1, (fofs, ffp)) =>
              match set_footprint l v ffp with
              | Some ffp1 =>
                  Some (fp_struct id (set_field_fp fid ffp1 fpl)) 
              | None => None
              end
          | None => None
          end
      (* TODO: remove pty in ph_downcast *)
      | ph_downcast _ fid (* fty *), fp_enum id tagz fid1 fofs1 fp1 =>
          (** Type safe checking *)
          if ident_eq fid fid1 then
            match set_footprint l v fp1 with
            | Some fp2 =>
                Some (fp_enum id tagz fid1 fofs1 fp2)
            | None => None
            end
          else None
      | _, _ => None
      end
  end.

Definition set_footprint_map (ps: paths) (v: footprint) (fpm: fp_map) : option fp_map :=
  let (id, phl) := ps in
  match fpm!id with
  | Some fp1 =>
      match set_footprint phl v fp1 with
      | Some fp2 =>
          Some (PTree.set id fp2 fpm)
      | None =>
          None
      end
  | None => None
  end.


Fixpoint get_owner_loc_footprint (phl: list path) (fp: footprint) (b: block) (ofs: Z) : option (block * Z * footprint) :=
  match phl with
  | nil => Some (b, ofs, fp)
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_owner_loc_footprint l fp1 b 0
      | ph_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, (fofs, fp1)) =>
              get_owner_loc_footprint l fp1 b (ofs + fofs)
          | None => None
          end
      | ph_downcast _ fid1 (* fty1 *), fp_enum id _ fid2 fofs fp1 =>
          if ident_eq fid1 fid2  then
            get_owner_loc_footprint l fp1 b (ofs + fofs)
          else None
      | _, _  => None
      end
  end.

(* non-loc version: use it to get some internal footprint *)
Fixpoint get_owner_footprint (phl: list path) (fp: footprint) : option footprint :=
  match phl with
  | nil => Some fp
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_owner_footprint l fp1
      | ph_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, (fofs, fp1)) =>
              get_owner_footprint l fp1
          | None => None
          end
      | ph_downcast pty fid1 (* fty1 *), fp_enum id _ fid2 fofs fp1 =>
          if ident_eq fid1 fid2 then
            get_owner_footprint l fp1
          else
            None
      | _, _  => None
      end
  end.


Definition get_owner_loc_footprint_map (e: fenv) (ps: paths) (fpm: fp_map) : option (block * Z * footprint) :=
  let (id, phl) := ps in
  match e!id, fpm!id with
  | Some (b, ofs, ty), Some fp =>
      get_owner_loc_footprint phl fp b ofs
  | _, _ => None
  end.

Fixpoint clear_footprint_rec (fp: footprint) : footprint :=
  match fp with
  | fp_scalar _ _
  | fp_box _ _ _
  | fp_enum _ _ _ _ _
  | fp_ref _ _ _
  | fp_emp => fp_emp
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, (fofs, ffp)) => (fid, (fofs, clear_footprint_rec ffp))) fpl)
  end.

Definition clear_footprint_map (e: fenv) (ps: paths) (fpm: fp_map) : option fp_map :=
  match get_owner_loc_footprint_map e ps fpm with
  | Some (_, _, fp1) =>
      set_footprint_map ps (clear_footprint_rec fp1) fpm
  | None => None
  end.

(* Get location and footprint through paths which may contains
dereference of reference *)

Fixpoint get_loc_footprint (fe: fenv) (fpm: fp_map) (phl: list path) (fp: footprint) (b: block) (ofs: Z) : option (block * Z * footprint) :=
  match phl with
  | nil => Some (b, ofs, fp)
  | ph :: l =>
      match ph, fp with
      | ph_deref, fp_box b _ fp1 =>
          get_owner_loc_footprint l fp1 b 0
      | ph_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, (fofs, fp1)) =>
              get_loc_footprint fe fpm l fp1 b (ofs + fofs)
          | None => None
          end
      | ph_downcast _ fid1 (* fty1 *), fp_enum id _ fid2 fofs fp1 =>
          if ident_eq fid1 fid2  then
            get_loc_footprint fe fpm l fp1 b (ofs + fofs)
          else None
      | ph_deref, fp_ref b1 ofs1 phs1 =>
          match get_owner_loc_footprint_map fe phs1 fpm with
          | Some (b2, ofs2, fp2) =>
              (* If this reference is valid, (b1, ofs1) should be
              equal to (b2, ofs2) *)
              get_loc_footprint fe fpm l fp2 b2 ofs2
          | None => None
          end
      | _, _  => None
      end
  end.

Definition get_loc_footprint_map (fe: fenv) (ps: paths) (fpm: fp_map) : option (block * Z * footprint) :=
  let (id, phl) := ps in
  match fe!id, fpm!id with
  | Some (b, ofs, ty), Some fp =>
      get_loc_footprint fe fpm phl fp b ofs
  | _, _ => None
  end.


(** ** Typing of the footprint: used to make sure the footprint is well-formed *)


Section COMP_ENV.

Variable ce: composite_env.

Fixpoint wt_path (ty: type) (phl: list path) : res type :=
  match phl with
  | nil => OK ty
  | ph :: phl1 =>
      do ty1 <- 
           match ph with
           | ph_deref => type_deref ty
           | ph_field fid => type_field ce ty fid
           | ph_downcast _ fid => type_downcast ce ty fid
           end;
      wt_path ty1 phl1
  end.


(* Definition of wt_footprint (well-typed footprint). Intuitively, it
says that the footprint is an abstract form of the syntactic type. *)
Inductive wt_footprint : type -> footprint -> Prop :=
| wt_fp_emp: forall ty
    (* It means that the location with this type is not initialized or
        this location is scalar type. We require that [ty] is not
        structure because we do not want to dynamically unpack the
        struct when setting footprint (e.g., by set_loc_footprint) to
        some field of this struct. But to ensure this properties, we
        need to carefully set fp_emp to place with structure type. *)
    (WF: forall orgs id, ty <> Tstruct orgs id),
    wt_footprint ty fp_emp
| wt_fp_scalar: forall ty v
    (WF: scalar_type ty = true),
    wt_footprint ty (fp_scalar ty v)
| wt_fp_struct: forall orgs id fpl co
    (CO: ce ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (** TODO: combine WT1 andp WT2 elegantly. WT1 is used in getting
    the sub-field's footprint. WT2 is used in proving the properties
    of sub-field's footprint *)
    (WT1: forall fid fty,
        place_field_type co fid orgs = OK fty ->
        (* For simplicity, use find_field instead of In predicate *)
        exists ffp fofs,
          find_field fid fpl = Some (fid, (fofs, ffp))
          /\ field_offset ce fid co.(co_members) = OK fofs
          (* bound condition *)
          /\ wt_footprint fty ffp)
    (WT2: forall fid fofs ffp,
        find_field fid fpl = Some (fid, (fofs, ffp)) ->
        exists fty,
          place_field_type co fid orgs = OK fty
          /\ field_offset ce fid co.(co_members) = OK fofs
          /\ wt_footprint fty ffp)
    (* make sure that the flattened footprint list has the same order
    as that of the members. If we can ensure that name_members are
    norepeated, then so are the field_idents. *)
    (FLAT: field_idents fpl = name_members (co_members co)),
    wt_footprint (Tstruct orgs id) (fp_struct id fpl)
| wt_fp_enum: forall orgs id tagz fid fty fofs fp co
    (CO: ce ! id = Some co)
    (ENUM: co_sv co = TaggedUnion)
    (TAG: list_nth_z co.(co_members) tagz = Some (Member_plain fid fty))
    (* avoid some norepet properties *)
    (FTY: place_field_type co fid orgs = OK fty)
    (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs)
    (WT: wt_footprint fty fp),
    wt_footprint (Tvariant orgs id) (fp_enum id tagz fid fofs fp)
| wt_fp_box: forall ty b fp
    (* this is ensured by bm_box *)
    (WT: wt_footprint ty fp),
    (* It is used to make sure that dropping any location within a
    block does not cause overflow *)
    wt_footprint (Tbox ty) (fp_box b (sizeof ce ty) fp)
| wt_fp_ref: forall ty b ofs phs org mut,
    (** Do we need to prove that phs is well-typed path? *)
    wt_footprint (Treference org mut ty) (fp_ref b ofs phs).

Definition wt_footprint_list tyl fpl :=
  list_forall2 wt_footprint tyl fpl.

End COMP_ENV.


(** Initialize a footprint with fp_emp based on the type of this footprint *)

Definition members_to_fields_fp_emp ce (ms: members) (f: type -> footprint): list ffpty :=
  map (fun '(Member_plain fid fty) =>
         match field_offset ce fid ms with
         | OK fofs =>
             (fid, (fofs, f fty))
         | Error _ => (* we can prove that it is impossible *)
             (fid, (0, fp_emp))
         end) ms.

Fixpoint type_to_empty_footprint_rec (ce: composite_env) (rank: nat) (ty: type) : footprint :=
  match rank with
  | O => fp_emp
  | S r =>      
      match ty with
      | Tstruct _ id =>
          match ce ! id with
          | Some co =>
              let fields := members_to_fields_fp_emp ce (co_members co) (type_to_empty_footprint_rec ce r) in
              fp_struct id fields
          | None => fp_emp
          end
      | _ => fp_emp
      end
  end.

Definition type_to_empty_footprint (ce: composite_env) (ty: type) : footprint :=
  type_to_empty_footprint_rec ce (rank_type ce ty) ty.

Lemma type_to_empty_footprint_rec_eq: forall ce ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    type_to_empty_footprint_rec ce (rank_type ce ty1) ty1 = type_to_empty_footprint_rec ce (rank_type ce ty2) ty2.
Admitted.

Lemma type_to_empty_footprint_eq: forall ce ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    type_to_empty_footprint ce ty1 = type_to_empty_footprint ce ty2.
Proof.
  intros. eapply type_to_empty_footprint_rec_eq. auto.
Qed.

(** We need that ce is consistent so that if ty is struct then ce
contains this struct *)
Lemma type_to_empty_footprint_wt: forall ce ty,
    complete_type ce ty = true ->
    wt_footprint ce ty (type_to_empty_footprint ce ty).
Admitted.

