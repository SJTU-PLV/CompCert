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
| fp_emp (sz: Z) (al: Z)      (* empty footprint. We need to record its size and align *)
| fp_scalar (chunk: memory_chunk) (v: val)       (* scalar type. *)
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

Lemma Forall_sep_app {A: Type} : forall (l1 l2: list A) P mass,
    Forall_sep P (l1 ++ l2) mass <-> 
      (exists mass1 mass2, Forall_sep P l1 mass1 /\ Forall_sep P l2 mass2 /\ mass = mass1 ** mass2).
Admitted.

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
| sem_wt_emp: forall b ofs sz al
    (* This location is not initialized, but it should be aligned
    properly and have enough permission *)
    (AL: (al | ofs)),
    sem_wt_loc (fp_emp sz al) b ofs (range b ofs (ofs + sz))
| sem_wt_scalar: forall b ofs chunk v,
    (* (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk), *)
    (* hasvalue already contain the align requirement *)
    sem_wt_loc (fp_scalar chunk v) b ofs (hasvalue chunk b ofs v)
| sem_wt_ref: forall b1 b2 ofs1 ofs2 phs,
    sem_wt_loc (fp_ref b2 ofs2 phs) b1 ofs1 (hasvalue Mptr b1 ofs1 (Vptr b2 (Ptrofs.repr ofs2)))
| sem_wt_box: forall b ofs fp b1 sz1 v mass
    (WTVAL: sem_wt_val (fp_box b1 sz1 fp) v mass),
    sem_wt_loc (fp_box b1 sz1 fp) b ofs ((hasvalue Mptr b ofs v) ** mass)
| sem_wt_struct: forall b ofs fpl id mass
    (FWT: fields_sep b ofs sem_wt_loc fpl mass)
    (AL: (alignof_comp id | ofs)),
    sem_wt_loc (fp_struct id fpl) b ofs (mconj mass (range b ofs (ofs + sizeof_comp id)))
| sem_wt_enum: forall fp b ofs tagz fid fofs id mass1 mass2
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: mass1 = hasvalue Mint32 b ofs (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc fp b (ofs + fofs) mass2)
    (AL: (alignof_comp id | ofs)),
    sem_wt_loc (fp_enum id tagz fid fofs fp) b ofs (mconj (mass1 ** mass2) (range b ofs (ofs + sizeof_comp id)))


with sem_wt_val : footprint -> val -> massert -> Prop :=
| wt_val_scalar: forall chunk v
    (* We should ensure that the value in the footprint is loaded from memory *)
    (VEQ: v = Val.load_result chunk v),
    sem_wt_val (fp_scalar chunk v) v (spure True)
| wt_val_ref: forall phs b ofs,
    sem_wt_val (fp_ref b ofs phs) (Vptr b (Ptrofs.repr ofs)) (spure True)
| wt_val_box: forall b fp sz mass1 mass2
    (WTLOC: sem_wt_loc fp b 0 mass1)
    (* contains_neg implies that this location can be freed *)
    (MASS: mass2 = (contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz))))
                     ** mass1),
    (* sz > 0 is used to make sure extcall_ext_free succeeds and sz <=
    max_unsigned is used to provent overflow when traversing some
    field offsets *)
    (* (RANGE: 0 < sz <= Ptrofs.max_unsigned), *)
    sem_wt_val (fp_box b sz fp) (Vptr b Ptrofs.zero) mass2
| wt_val_struct: forall b ofs id fpl mass
    (WTLOC: sem_wt_loc (fp_struct id fpl) b (Ptrofs.unsigned ofs) mass),
    (* (AL: (alignof_comp id | Ptrofs.unsigned ofs)) *)
    (* (* The permission of the location is readable to make sure *)
    (* assign_loc has no memory error. *) *)
    (* (** TODO: does this value owns the location of the pointed struct? *)
    (* Or should we support share permission? What if we allow copying *)
    (* composite types? *) *)
    (* (PERM: mass2 = range b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id)), *)
    (** mass1 and mass2 are overlapped!! *)
    sem_wt_val (fp_struct id fpl) (Vptr b ofs) mass
| wt_val_enum: forall b ofs fp tagz fid fofs id mass
    (WTLOC: sem_wt_loc (fp_enum id tagz fid fofs fp) b (Ptrofs.unsigned ofs) mass),
    (* (AL: (alignof_comp id | Ptrofs.unsigned ofs)) *)
    (* (PERM: mass2 = range b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id)), *)
    sem_wt_val (fp_enum id tagz fid fofs fp) (Vptr b ofs) mass.


Lemma fields_sep_equiv: forall fpl b ofs P mass,
    fields_sep b ofs P fpl mass <->
      Forall_sep (fun '(fid, (fofs, ffp)) => P ffp b (ofs + fofs)) fpl mass.
Proof.
  induction fpl; intros.
  - split; intros.
    + inv H. econstructor.
    + inv H. econstructor.
  - split; intros.
    + inv H. econstructor; eauto. 
      eapply IHfpl. auto.
    + inv H. destruct a. destruct p. econstructor; eauto. 
      eapply IHfpl. auto.
Qed.

Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: forall sz al, P (fp_emp sz al))
  (HPscalar: forall chunk v, P (fp_scalar chunk v))
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
  | fp_emp _ _ => nil
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

Coercion fenv_to_tenv (fe: fenv) : typenv := PTree.map1 snd fe.

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
    (MASS: sem_wt_loc fp b ofs mass),
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


Lemma find_field_some {A: Type}: forall fid fid1 fpl (a: A),
    find_field fid fpl = Some (fid1, a) ->
    fid = fid1 /\ In (fid, a) fpl.
Proof.
  intros. unfold find_field in H.
  exploit find_some. eauto. intros (A1 & B).
  destruct ident_eq in B; try congruence.
  subst. auto.
Qed.

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

Definition get_owner_footprint_map (ps: paths) (fpm: fp_map) : option footprint :=
  let (id, phl) := ps in
  match fpm!id with
  | Some fp =>
      get_owner_footprint phl fp
  | _ => None
  end.


Definition get_owner_loc_footprint_map (e: fenv) (ps: paths) (fpm: fp_map) : option (block * Z * footprint) :=
  let (id, phl) := ps in
  match e!id, fpm!id with
  | Some (b, ofs, ty), Some fp =>
      get_owner_loc_footprint phl fp b ofs
  | _, _ => None
  end.

Fixpoint clear_footprint_rec ce (fp: footprint) : footprint :=
  match fp with
  | fp_scalar chunk _ => fp_emp (size_chunk chunk) (align_chunk chunk)
  | fp_box _ _ _ => fp_emp (size_chunk Mptr) (align_chunk Mptr)
  | fp_enum id _ _ _ _ => fp_emp (sizeof_comp ce id) (alignof_comp ce id)
  | fp_ref _ _ _ => fp_emp (size_chunk Mptr) (align_chunk Mptr)
  | fp_emp sz al => fp_emp sz al
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, (fofs, ffp)) => (fid, (fofs, clear_footprint_rec ce ffp))) fpl)
  end.

Definition clear_footprint_map ce (e: fenv) (ps: paths) (fpm: fp_map) : option fp_map :=
  match get_owner_loc_footprint_map e ps fpm with
  | Some (_, _, fp1) =>
      set_footprint_map ps (clear_footprint_rec ce fp1) fpm
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

(* Useful tactic to destruct get_loc_footprint *)
(* Ltac destr_fp_enum fp ty := *)
(*   destruct fp; try congruence; *)
(*   destruct ty; try congruence; *)
(*   destruct ident_eq; try congruence; *)
(*   destruct list_eq_dec; try congruence; *)
(*   destruct ident_eq; try congruence; subst. *)

(* Ltac destr_fp_enum_simpl fp := *)
(*   destruct fp; try congruence; *)
(*   destruct ident_eq; try congruence; *)
(*   destruct list_eq_dec; try congruence; *)
(*   destruct ident_eq; try congruence; subst. *)

Ltac destr_fp_field fp H :=
  let A1 := fresh "A" in
  let A2 := fresh "A" in
  let p := fresh "p" in
  let FIND := fresh "FIND" in
  destruct fp; try congruence;
  destruct find_field as [p|] eqn: FIND; try congruence;
  repeat destruct p; simpl in H;
  exploit find_field_some; eauto; intros (A1 & A2); subst.


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

Definition wt_paths (te: typenv) (phs: paths) : res type :=
  let (id, phl) := phs in
  match te ! id with
  | Some ty =>
      wt_path ty phl
  | None =>
      Error (msg "no local type")
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
    wt_footprint ty (fp_emp (sizeof ce ty) (alignof ce ty))
| wt_fp_scalar: forall ty v chunk
    (WF: scalar_type ty = true)
    (MODE: access_mode ty = Ctypes.By_value chunk),
    wt_footprint ty (fp_scalar chunk v)
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

(* Properties of fields_sep *)

Lemma fields_sep_split: forall b ofs fofs fid ffp l mass P,
    fields_sep b ofs P l mass ->
    In (fid, (fofs, ffp)) l ->
    exists mass1 mass2 mass3, 
      P ffp b (ofs + fofs) mass2 
      /\ mass = mass1 ** mass2 ** mass3.
  (* use Forall_sep properties to prove fields_sep properties *)
Admitted.


(** Initialize a footprint with fp_emp based on the type of this footprint *)

Definition members_to_fields_fp_emp ce (ms: members) (f: type -> footprint): list ffpty :=
  map (fun '(Member_plain fid fty) =>
         match field_offset ce fid ms with
         | OK fofs =>
             (fid, (fofs, f fty))
         | Error _ => (* we can prove that it is impossible *)
             (fid, (0, (fp_emp 0 0)))
         end) ms.

Fixpoint type_to_empty_footprint_rec (ce: composite_env) (rank: nat) (ty: type) : footprint :=
  match rank with
  | O => fp_emp (sizeof ce ty) (alignof ce ty)
  | S r =>      
      match ty with
      | Tstruct _ id =>
          match ce ! id with
          | Some co =>
              let fields := members_to_fields_fp_emp ce (co_members co) (type_to_empty_footprint_rec ce r) in
              fp_struct id fields
          (* impossible *)
          | None => fp_emp 0 0
          end
      | _ => fp_emp (sizeof ce ty) (alignof ce ty)
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

(** Properties of footprint that ensured by move checking *)

Fixpoint shallow_init (fp: footprint) : bool :=
  match fp with
  | fp_emp _ _ => false
  | fp_struct _ fpl =>
      forallb (fun '(_, (_, ffp)) => shallow_init ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      shallow_init ffp
  | _ => true
  end.

Fixpoint deep_init (fp: footprint) : bool :=
  match fp with
  | fp_emp _ _ => false
  | fp_struct _ fpl =>
      forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      deep_init ffp
  | fp_box _ _ fp1 =>
      deep_init fp1
  | _ => true
  end.

(* use it to replace mmatch of the original proofs *)
Definition move_check_inv (own: own_env) (fpm: fp_map) : Prop :=
  forall p fp,
    get_owner_footprint_map (path_of_place p) fpm = Some fp ->
    is_init own p = true ->
    shallow_init fp = true 
    /\ (is_full (own_universe own) p = true ->
       deep_init fp = true).

(** An important lemma: if a place pass [must_movable] then the
footprint stored in the path of this place is deeply init. *)

Lemma movable_place_deep_init: forall ce fp fpm own p init uninit universe
    (POWN: must_movable ce init uninit universe p false = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: get_owner_footprint_map (path_of_place p) fpm = Some fp),
    deep_init fp = true.
Admitted.

(* May be combined with the above lemma *)
Lemma movable_place_shallow_init: forall ce fp fpm own p init uninit universe
    (POWN: must_movable ce init uninit universe p true = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: get_owner_footprint_map (path_of_place p) fpm = Some fp),
    shallow_init fp = true.
Admitted.

(** Basic rules for coherent relation (e.g., store and load rules) *)

(** TODO: move it to Separation.v  *)

Lemma massert_eqv_pure_l: forall P,
    massert_eqv P (Separation.pure True ** P).
Proof.
  intros. split.
  red; split; [intros; eapply sep_pure; auto|simpl; intros; destruct H; try contradiction; auto].
  red. split. intros. eapply sep_pure in H. destruct H; auto.
  intros. simpl. auto.
Qed.

Lemma massert_eqv_pure_r: forall P,
    massert_eqv P (P ** Separation.pure True).
Proof.
  intros. etransitivity.
  eapply massert_eqv_pure_l.
  eapply sep_comm.
Qed.  

Lemma contains_range: forall chunk b ofs P,
    massert_imp (contains chunk b ofs P) (range b ofs (ofs + size_chunk chunk)).
Admitted.

Lemma mconj_comm: forall P Q, massert_eqv (mconj P Q) (mconj Q P).
Proof. 
  intros. split.
  - red. split. intros. simpl in *. destruct H; auto.
    intros. simpl in *. destruct H; auto.
  - red. split. intros. simpl in *. destruct H; auto.
    intros. simpl in *. destruct H; auto.
Qed.

Lemma mconj_proj1_massert: forall P Q , massert_imp (mconj P Q) P.
Proof.
  intros. red. split.
  - intros. eapply sep_pick1 with (Q:= STrue).
    eapply mconj_proj1. erewrite <- massert_eqv_pure_r. eauto.
  - intros. simpl. left. auto.
Qed.

Lemma mconj_proj2_massert: forall P Q , massert_imp (mconj P Q) Q.
Proof.
  intros. 
  etransitivity. eapply mconj_comm. eapply mconj_proj1_massert.
Qed.

Lemma massert_imp_proj1: forall P Q , massert_imp (P ** Q) P.
Proof.
  intros. red. split.
  - intros. eapply sep_proj1. eauto.
  - intros. simpl. left. auto.
Qed.

Lemma massert_imp_proj2: forall P Q , massert_imp (P ** Q) Q.
Proof.
  intros. red. split.
  - intros. eapply sep_proj2. eauto.
  - intros. simpl. right. auto.
Qed.

Lemma store_range_rule: forall chunk m b ofs v (spec: val -> Prop) P,
    m |= range b ofs (ofs + size_chunk chunk) ** P ->
    (align_chunk chunk | ofs) ->
    spec (Val.load_result chunk v) ->
    exists m',
      Mem.store chunk m b ofs v = Some m' /\ m' |= contains chunk b ofs spec ** P.
Proof.
Admitted.


Definition sizeof_footprint ce (fp: footprint) : Z :=
  match fp with
  | fp_emp sz _ => sz
  | fp_scalar chunk _ => size_chunk chunk
  | fp_box _ _ _ => size_chunk Mptr
  | fp_enum id _ _ _ _ => sizeof_comp ce id
  | fp_struct id _ => sizeof_comp ce id
  | fp_ref _ _ _ => size_chunk Mptr      
  end.

Definition alignof_footprint ce (fp: footprint) : Z :=
  match fp with
  | fp_emp _ al => al
  | fp_scalar chunk _ => align_chunk chunk
  | fp_box _ _ _ => align_chunk Mptr
  | fp_enum id _ _ _ _ => alignof_comp ce id
  | fp_struct id _ => alignof_comp ce id
  | fp_ref _ _ _ => align_chunk Mptr      
  end.


Lemma wt_footprint_size_eq ce : forall ty fp,
    wt_footprint ce ty fp ->
    sizeof ce ty = sizeof_footprint ce fp.
Admitted.

Lemma wt_footprint_align_eq ce : forall ty fp,
    wt_footprint ce ty fp ->
    alignof ce ty = alignof_footprint ce fp.
Admitted.


Definition fp_match_chunk fp chunk : Prop :=
  match fp with
  | fp_emp sz al =>
      sz = size_chunk chunk /\ al = align_chunk chunk
  | fp_scalar chunk1 _ =>
      chunk1 = chunk
  | fp_box _ _ _
  | fp_ref _ _ _ => chunk = Mptr
  | fp_struct _ _
  | fp_enum _ _ _ _ _ => False
  end.


Lemma fp_match_chunk_size ce: forall fp chunk,
    fp_match_chunk fp chunk ->
    sizeof_footprint ce fp = size_chunk chunk.
Proof.
  destruct fp; simpl; intros; try contradiction; subst; auto.
  destruct H. auto.
Qed.  


Lemma fp_match_chunk_align ce: forall fp chunk,
    fp_match_chunk fp chunk ->
    alignof_footprint ce fp = align_chunk chunk.
Proof.
  destruct fp; simpl; intros; try contradiction; subst; auto.
  destruct H. auto.
Qed.

Lemma sem_wt_loc_valid_access ce: forall fp b ofs mass m p chunk
    (WTLOC: sem_wt_loc ce fp b ofs mass)
    (MPRED: m |= mass)
    (FPMAT: fp_match_chunk fp chunk),
    Mem.valid_access m chunk b ofs p.
Proof.
  induction fp using strong_footprint_ind; intros; red; inv WTLOC; simpl in FPMAT; try contradiction.
  - destruct FPMAT. subst. split.
    + red. intros. eapply MPRED. eauto.
    + auto. 
  - admit.
  - admit.
  - admit.
Admitted.

(* Storing a semantically well-typed value into a location with
   range permission can result in that this location becomes a
   semantically well-typed location. *)
Lemma store_sem_wt_val ce: forall fp mass MP chunk v b ofs m1
    (WTVAL: sem_wt_val ce fp v mass)
    (MPRED: m1 |= range b ofs (ofs + size_chunk chunk) ** mass ** MP)
    (AL: (align_chunk chunk | ofs))
    (MATCH: fp_match_chunk fp chunk),
    exists m2 mass', 
      Mem.store chunk m1 b ofs v = Some m2
      /\ sem_wt_loc ce fp b ofs mass'
      /\ m2 |= mass' ** MP. 
Proof.
  intros.
  destruct fp; inv WTVAL; inv MATCH.
  - eapply store_range_rule with (spec:= (fun v' : val => v' = Val.load_result chunk v)) (v:= v) in MPRED; auto.
    destruct MPRED as (m2 & STORE & MPRED). rewrite <- VEQ in *.
    exists m2, (hasvalue chunk b ofs v). split; auto.
    split; auto.
    econstructor. rewrite sep_swap in MPRED. eapply sep_proj2 in MPRED. 
    auto.
  - admit.
  - admit.
Admitted.



Lemma sem_wt_loc_split_range ce: forall fp mass b ofs
      (WTLOC: sem_wt_loc ce fp b ofs mass),
  (* We cannot prove their equivalence as mass may contain the value
  spec in this location which cannot be expressed by range. *)
  exists mass', massert_imp mass (range b ofs (ofs + sizeof_footprint ce fp) ** mass').
Proof.
  induction fp using strong_footprint_ind; intros; inv WTLOC.
  - exists STrue. eapply massert_eqv_pure_r.
  - exists STrue. etransitivity. eapply contains_range.
    eapply massert_eqv_pure_r.
  - exists mass0. setoid_rewrite contains_range. reflexivity. 
  - exists STrue. etransitivity. eapply mconj_proj2_massert.
    eapply massert_eqv_pure_r.
  - exists STrue. etransitivity. eapply mconj_proj2_massert.
    eapply massert_eqv_pure_r.
  - exists STrue. etransitivity. eapply contains_range.
    eapply massert_eqv_pure_r.
Qed.

Lemma store_sem_wt_loc ce: forall fp vfp b ofs mass1 mass2 v m1 MP chunk
    (WTLOC: sem_wt_loc ce fp b ofs mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (AL: (align_chunk chunk | ofs))
    (MPRED: m1 |= mass1 ** mass2 ** MP)
    (MAT1: fp_match_chunk fp chunk)
    (MAT2: fp_match_chunk vfp chunk),
    exists m2 mass3, 
      Mem.store chunk m1 b ofs v = Some m2      
      /\ sem_wt_loc ce vfp b ofs mass3
      /\ m2 |= mass3 ** MP.
Proof.
  intros. eapply store_sem_wt_val; eauto.
  (* prove a lemma that extract the range from sem_wt_loc *)
  eapply sem_wt_loc_split_range in WTLOC as (mass1' & MIMP).
  eapply sep_imp. eapply MPRED. 
  erewrite fp_match_chunk_size in MIMP; eauto.
  etransitivity. eapply MIMP. eapply massert_imp_proj1.
  reflexivity.
Qed.  

  (** TODO: we should split the range massert from sem_wt_loc and then
  drop the remaining sem_wt_val, using sem_wt_loc_split. I think this
  property is also useful in moving from a sem_wt_val. But in this
  case, we cannot know what value is stored in the sem_wt_loc *)

 
Lemma store_coherent_var: forall phl m ce mass1 mass2 v vfp fp1 pfp chunk b1 ofs1 b2 ofs2 MP
    (WTLOC: sem_wt_loc ce fp1 b1 ofs1 mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (MPRED: m |= mass1 ** mass2 ** MP)
    (* id may denote an external owner? *)
    (GFP: get_owner_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, pfp))
    (* The following properties should be derived from wt_footprint *)
    (AL: (align_chunk chunk | ofs2))
    (MAT1: fp_match_chunk pfp chunk)
    (MAT2: fp_match_chunk vfp chunk),
    exists m1 fp2 mass3,
      Mem.store chunk m b2 ofs2 v = Some m1
      /\ set_footprint phl vfp fp1 = Some fp2
      /\ sem_wt_loc ce fp2 b1 ofs1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  induction phl; intros.
  - inv GFP. 
    exploit store_sem_wt_loc; eauto.
    intros (m2 & mass3 & STORE & WTLOC1 & MPRED1).
    exists m2, vfp, mass3. split; try split; auto. 
  - simpl in GFP. destruct a; try congruence.
    + destruct fp1; try congruence. 
      inv WTLOC. inv WTVAL0.
      set (MP1 := hasvalue Mptr b1 ofs1 (Vptr b Ptrofs.zero)) in *.
      set (MP2 := contains_neg Mptr b (- size_chunk Mptr) (eq (Vptrofs (Ptrofs.repr sz)))) in *.
      (* prove it with commutative lemmas of sepconj *)
      assert (MPRED1: m|= mass1 ** mass2 ** (MP ** MP1 ** MP2)) by admit.
      exploit IHphl; eauto. intros (m1 & fp2 & mass3 & A1 & A2 & A3 & A4).
      exists m1, (fp_box b sz fp2), (MP1 ** MP2 ** mass3).
      do 3 (try apply conj); eauto.
      * simpl. rewrite A2. reflexivity.
      * econstructor; eauto. econstructor; eauto.
      * admit.
    + destr_fp_field fp1 GFP.
      inv WTLOC.
      exploit fields_sep_split; eauto. intros (mass1 & mass3 & mass4 & B1 & B2). subst.
      (* A big problem is that how to ensure storing value to a
      sub-field do not change the range massert of the whole struct?
      We should also split the range massert into subfiles !!
      Something like (mconj mass1 range1) ** (mconj mass2 range2) **
      (mconj mass3 range3). This require us to prove a stronger
      fields_sep_split! *)


(* We prove a strong version, i.e., the store operation can always success *)
Lemma store_coherent_fpm: forall phl m ce fe fpm mass1 mass2 v vfp pfp ty chunk b ofs id MP
    (COH: coherent_fpm ce fe fpm mass1)
    (WTVAL: sem_wt_val ce vfp v mass2)
    (MPRED: m |= mass1 ** mass2 ** MP)
    (* id may denote an external owner? We reduce all store for
    reference into store for their referred owner *)
    (GFP: get_owner_loc_footprint_map fe (id, phl) fpm = Some (b, ofs, pfp))
    (* TODO: maybe we need wf_env to ensure that all footprint in fpm
    is wt_footprint *)
    (* (WT: wt_paths ce fe (id, phl) = OK ty) *)
    (* (CK: access_mode ty = Ctypes.By_value chunk), *)
    (** We may just require that the (size, align) of pfp is equal to
    the (size, align) of the chunk. Maybe all the store rules can be
    reduced to storebytes? *)
    
    exists m1 fpm1 mass3,
Mem.store_storebytes Mem.storebytes_store
      Mem.store chunk m b ofs v = Some m1
      /\ set_footprint_map (id, phl) vfp fpm = Some fpm1
      /\ coherent_fpm ce fe fpm1 mass3
      /\ m1 |= mass3 ** MP.
Proof.
  intros. simpl in GFP, WT. simpl.
  destruct (fe ! id) as [((b1 & ofs1) & ty1)|] eqn: A; try congruence.
  setoid_rewrite PTree.gmap1 in WT. rewrite A in WT. simpl in WT.
  destruct (fpm ! id) as [fp|] eqn: B; try congruence.
  (* We should split the footprint for the id from mass1 *)
  exploit PTree.elements_remove. eapply A. intros (l1 & l2 & C1 & C2). 
  inv COH. rewrite C1 in ALLSEP. 
  erewrite Forall_sep_app in ALLSEP. 
  destruct ALLSEP as (mass11 & mass12 & D1 & D2 & D3). subst.
  inv D2. inv H1. inv ELTEQ.
  rewrite B in VARFP. inv VARFP.  
  (* apply store_coherent_var *)
  
