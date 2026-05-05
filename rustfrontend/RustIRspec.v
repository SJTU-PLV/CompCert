Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepSafe.
Require Import Listmisc.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rusttyping Rustlight.
Require Import Rustlightown RustIR.
Require Import LanguageInterface.
Require Import InitDomain.
Require Import Memory.
Require Import BorrowCheckDomain BorrowCheckPolonius.
Require Import Separation.

Import ListNotations.

Local Open Scope error_monad_scope.

Section WT_PATH.

Variable ce: composite_env.

Fixpoint wt_projections (ty: type) (phl: list projection) : res type :=
  match phl with
  | nil => OK ty
  | ph :: phl1 =>
      do ty1 <- 
           match ph with
           | proj_deref => do (ty1, _) <- type_deref ty; OK ty1
           | proj_field fid => type_field ce ty fid
           | proj_downcast fid => type_downcast ce ty fid
           end;
      wt_projections ty1 phl1
  end.

Definition wt_path (te: typenv) (phs: path) : res type :=
  let (id, phl) := phs in
  match te ! id with
  | Some ty =>
      wt_projections ty phl
  | None =>
      Error (msg "no local type")
  end.

Fixpoint wt_projections_variance (ty: type) (phl: list projection) (v: variance) : res (type * variance):=
  match phl with
  | nil => OK (ty, v)
  | ph :: phl1 =>
      match ph with
      | proj_deref => 
          do (ty1, v1) <- type_deref ty;
          wt_projections_variance ty1 phl1 (join_variance v v1)          
      | proj_field fid => 
          do fty <- type_field ce ty fid;
          wt_projections_variance fty phl1 v
      | proj_downcast fid => 
          do fty <- type_downcast ce ty fid;
          wt_projections_variance fty phl1 v
      end
  end.

Definition wt_path_variance (te: typenv) (phs: path) : res (type * variance) :=
  let (id, phl) := phs in
  match te ! id with
  | Some ty =>
      wt_projections_variance ty phl Covariant
  | None =>
      Error (msg "no local type")
  end.

End WT_PATH.

Definition alignof_comp ce (id: ident) :=
  match ce ! id with
  | Some co => co_alignof co
  | None => 1
  end.

Definition sizeof_comp ce (id: ident) :=
  match ce ! id with
  | Some co => co_sizeof co
  | None => 0
  end.


(* Definition of Adt *)

(** Define the semantic interpretation of abstract data type written
in unsafe module *)

Record massert_rel_functional (P: massert -> Prop) : Prop :=
  { mass_rel_left_total: exists mp, P mp;
    mass_rel_right_unique: forall mp1 mp2, P mp1 -> P mp2 -> massert_eqv mp1 mp2; }.

(* Adt instrumented with information of memory locations *)
Record Adt_mem : Type := {
    mem_repr: Type;
    repr_inv: mem_repr -> Prop;         (* representation invariant *)
    mem_exposed_borrow: mem_repr -> list (ident * ((block * Z * Z) * type));
    (* layout *)
    adt_size : Z;
    adt_align: Z;
    
    mem_pred: mem_repr -> block -> Z -> massert -> Prop; (* How it locates in the memory *)
    
    (* Propertis of mem_pred, e.g., it is total and deterministic *)
    mem_pred_functional: forall r b ofs, massert_rel_functional (mem_pred r b ofs);
    
    (* mem_pred implies that the location is freeable if the exposed
    borrowable subparts are also freeable, which is used in freeing
    the block of this object *)
    (* mem_pred_range: forall r b ofs MP, *)
    (*   mem_pred r b ofs MP -> *)
    (*   massert_imp (MP ** range_list (map (compose fst snd) (mem_exposed_borrow r))) (range b ofs (ofs + adt_size)); *)
    
    (* exposed_borrow_consistent: forall r, *)
    (*   map fst (mem_exposed_borrow r) = exposed_borrow mem_pure_adt (mem_to_pure_repr r); *)

  }.

Definition adt_mem_env : Type := ident -> Adt_mem.

Section SPEC.

(* I think this environment is a premise for the whole borrow checking
proof and the RustIRspec. When we want to use the borow checking
proof, we must provide its instance. *)
Context {ame: adt_mem_env}.

(** RustIR functional specification. *)

(* Function environment *)

Definition views := list path.

(* A tree structured footprint (maybe similar to some separation logic
algebra). *)
Inductive footprint : Type :=
| fp_emp  (* empty footprint. It is required because we want moved out
  the whole location and then set fp_emp to the original location *)
| fp_uninit (sz al: Z) (*  Uninitialized footprint. We need to record its size and align *)
| fp_scalar (chunk: memory_chunk) (v: val)  (* scalar type. *)
| fp_box (b: block) (* (sz: Z) *) (fp: footprint) (* A heap block storing values that occupy footprint fp. We do not record size here because if fp is fp_emp the size is meaningless and wt_footprint cannot be defined for Box(Adt) *)
(* (field ident, field type, field offset,field footprint) *)
| fp_struct (id: ident) (fpl: list (ident * ((Z * Z) * footprint)))
(* orgs are not used for now but it is used to relate to the type *)
| fp_enum (id: ident) (tagz: Z) (fid: ident) (fofs: Z) (ffp: footprint)
| fp_ref (mut: mutkind) (b: block) (ofs: Z) (ph: option path) (vs: views) (* reference to an owner at [phs]. We also record the reborrowed paths
  of ph. If this fp_ref (Some ph) has been converted to fp_ref None,
  it means that it has been invalidated by the dynamic borrow check or
  it has been moved from. The dynamic borrow check should maintian an
  invariant that if some sv_ref is valid, then the path it points to
  must also valid. The main reason we do not convert fp_ref to
  fp_uninit like move operation does is because if we convert it to
  fp_uninit, then some deep_init footprint would become not
  deep_init. *)
| fp_object (id: ident) (obj: (mem_repr (ame id))) (exposed: list (ident * ((block * Z) * type * footprint)))
.

(* Induction principle for footprint *)
Section FP_IND.

Variable (P: footprint -> Prop)
  (HPemp: P fp_emp)
  (HPuninit: forall sz al, P (fp_uninit sz al))
  (HPscalar: forall chunk v, P (fp_scalar chunk v))
  (HPbox: forall (b : block) (fp : footprint), P fp -> P (fp_box b fp))
  (HPstruct: forall id fpl, (forall fid base fofs ffp, In (fid, ((base, fofs), ffp)) fpl -> P ffp) -> P (fp_struct id fpl))
  (HPenum: forall id (tag : Z) fid fofs (ffp : footprint), P ffp -> P (fp_enum id tag fid fofs ffp))
  (HPref: forall mut b ofs ref_owner vs, P (fp_ref mut b ofs ref_owner vs))
  (HPobj: forall id obj bors, (forall fid b ofs ffp, In (fid, (b, ofs, ffp)) bors -> P ffp) -> P (fp_object id obj bors)).

Fixpoint strong_footprint_ind t: P t.
Proof.
  destruct t.
  - apply HPemp.
  - apply HPuninit.
  - apply HPscalar.
  - eapply HPbox. specialize (strong_footprint_ind t); now subst.
  - eapply HPstruct. induction fpl.
    + intros. inv H.
    + intros. destruct a as (fid1 & ofs1 & fp1).  simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
        (* now subst. *)
      * apply (IHfpl fid base fofs ffp H). 
  - apply HPenum. apply strong_footprint_ind.
  - apply HPref. 
  - eapply HPobj. induction exposed.
    + intros. inv H.
    + intros. destruct a as (fid1 & ((b1 & ofs1) & fp1)). simpl in H. destruct H.
      * specialize (strong_footprint_ind fp1). inv H. apply strong_footprint_ind.
      * apply (IHexposed fid b ofs ffp H). 
Qed.
    
End FP_IND.

(* It is used to define the invariant for the dynamic borrow check *)
Definition fp_graph := PTree.t footprint.

(* The [option origin] is used to indicate that this "variable" is
local var/param (None) or a name for some locations passed by
reference (Some org where org is the generic region of this location) *)
Definition fp_map := PTree.t (block * Z * option origin * type * footprint).

Definition empty_fpm := PTree.empty (block * Z * option origin * type * footprint).

Implicit Type fpm : fp_map.

Definition fpm_to_env (fpm: fp_map) : env := 
  PTree.map_filter1 (fun '(b, _, optr, ty, _) =>
                       match optr with
                       | Some r => None
                       | None => Some (b, ty)
                       end) fpm.

Coercion fpm_to_fpg (fpm: fp_map) : fp_graph :=
  PTree.map1 snd fpm.


(** Shallow init and Deep init which should be statically checked by
the move checking *)

Fixpoint shallow_init (fp: footprint) : bool :=
  match fp with
  | fp_emp
  (* Here is the difference *)
  | fp_uninit _ _ => false
  | fp_struct _ fpl =>
      forallb (fun '(_, (_, ffp)) => shallow_init ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      shallow_init ffp
  (* We cannot simply say that fp1 is not fp_emp because when we pass
  some field of fp1 to caller, its original footprint would be set to
  fp_emp, but we cannot owns the whole block anymore. *)
  | _ => true
  end.

(* All level footprint are not fp_emp *)
Fixpoint deep_init (fp: footprint) : bool :=
  match fp with
  | fp_emp
  (* Here is the difference *)
  | fp_uninit _ _ => false
  | fp_struct _ fpl =>
      forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      deep_init ffp
  | fp_box _ fp1 =>
      deep_init fp1
  | _ => true
  end.

(** Functions for getting and updating the footprint map. *)

Definition sizeof_footprint ce (fp: footprint) : Z :=
  match fp with
  | fp_emp => 0
  | fp_uninit sz _ => sz
  | fp_scalar chunk _ => size_chunk chunk
  | fp_box _ _ => size_chunk Mptr
  | fp_enum id _ _ _ _ => sizeof_comp ce id
  | fp_struct id _ => sizeof_comp ce id
  | fp_ref _ _ _ _ _ => size_chunk Mptr
  | fp_object id _ _ => adt_size (ame id)
  end.

Definition alignof_footprint ce (fp: footprint) : Z :=
  match fp with
  | fp_emp => 0
  | fp_uninit _ al => al
  | fp_scalar chunk _ => align_chunk chunk
  | fp_box _ _ => align_chunk Mptr
  | fp_enum id _ _ _ _ => alignof_comp ce id
  | fp_struct id _ => alignof_comp ce id
  | fp_ref _ _ _ _ _ => align_chunk Mptr
  | fp_object id _ _ => adt_align (ame id)
  end.


(** Initialize a footprint with fp_uninit based on the type of this footprint *)

(* pattern (fid, ((base, fofs), ffp): base is the end of the last
field's offset (it is 0 if this field is the first field). The
interval [base, fofs) is used to align this field but we need to
specify its permission, for which we record it in the footprint. *)
Definition ffpty : Type := ident * ((Z * Z) * footprint).


Section COMP_ENV.

Variable ce: composite_env.

(** Move it to Rusttypes.v  *)

(* We define a new field_offset which returns the starting offset of a
field that does not consider the alignment. *)

Fixpoint field_noalign_offset_rec (env: composite_env) (id: ident) (ms: members) (pos: Z)
                          {struct ms} : res (Z * Z) :=
  match ms with
  | nil => Error (MSG "Unknown field " :: CTX id :: nil)
  | m :: ms =>
      if ident_eq id (name_member m)
      then do fofs <- layout_field env pos m;
           OK (pos, fofs)
      else field_noalign_offset_rec env id ms (next_field env pos m)
  end.

Definition field_noalign_offset (env: composite_env) (id: ident) (ms: members) : res (Z * Z) :=
  field_noalign_offset_rec env id ms 0.

End COMP_ENV.

Definition members_to_fields_fp_uninit ce (ms: members) (f: type -> footprint): list ffpty :=
  map (fun '(Member_plain fid fty) =>
         match field_noalign_offset ce fid ms with
         | OK (base, fofs) =>
             (fid, ((base, fofs), f fty))
         | Error _ => (* we can prove that it is impossible *)
             (fid, ((0, 0), (fp_uninit 0 0)))
         end) ms.

Fixpoint type_to_uninit_footprint_rec (ce: composite_env) (rank: nat) (ty: type) : footprint :=
  match rank with
  | O => fp_uninit (sizeof ce ty) (alignof ce ty)
  | S r =>
      match ty with
      | Tstruct _ id =>
          match ce ! id with
          | Some co =>
              let fields := members_to_fields_fp_uninit ce (co_members co) (type_to_uninit_footprint_rec ce r) in
              fp_struct id fields
          (* impossible *)
          | None => fp_uninit 0 0
          end
      | _ => fp_uninit (sizeof ce ty) (alignof ce ty)
      end
  end.

Definition type_to_uninit_footprint (ce: composite_env) (ty: type) : footprint :=
  type_to_uninit_footprint_rec ce (rank_type ce ty) ty.


(* Operations for the footprint environment *)

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

Definition set_field_fp {L: Type} (fid: ident) (vfp: footprint) (fpl: list (ident * (L * footprint))) : list (ident * (L * footprint)) :=
  set_field fid (fun '(l, ffp) => (l, vfp)) fpl.

(* set footprint [v] in the path [ph] of footprint [fp] *)
Fixpoint set_footprint (phl: list projection) (v: footprint) (fp: footprint) : res footprint :=
  match phl with
  | nil => OK v
  | ph :: l =>
      match ph, fp with
      | proj_deref, fp_box b fp1 =>
          do fp2 <- set_footprint l v fp1;
          OK (fp_box b fp2)
      | proj_field fid, fp_struct id fpl =>
          match find_field fid fpl with
          | Some (fofs, ffp) =>
              do ffp1 <- set_footprint l v ffp;
              OK (fp_struct id (set_field_fp fid ffp1 fpl)) 
          | None => Error nil
          end
      | proj_field fid, fp_object id obj exposed =>
          match find_field fid exposed with
          | Some ((b, ofs), ffp) =>
              do ffp1 <- set_footprint l v ffp;
              OK (fp_object id obj (set_field_fp fid ffp1 exposed))
          | None => Error nil
          end                  
      | proj_downcast fid, fp_enum id tagz fid1 fofs1 fp1 =>
          (** Type safe checking *)
          if ident_eq fid fid1 then
            do fp2 <- set_footprint l v fp1;
            OK (fp_enum id tagz fid1 fofs1 fp2)
          else Error nil
      | _, _ => Error nil
      end
  end.

Definition set_footprint_map (ps: path) (v: footprint) (fpm: fp_map) : res fp_map :=
  let (id, phl) := ps in
  match fpm!id with
  | Some (a, fp1) =>
      do fp2 <- set_footprint phl v fp1;
      OK (PTree.set id (a, fp2) fpm)
  | None => Error nil
  end.

(* Definition not_fp_emp (fp: footprint) : bool := *)
(*   match fp with *)
(*   | fp_emp => false *)
(*   | _ => true *)
(*   end. *)

Fixpoint get_owner_loc_footprint (phl: list projection) (fp: footprint) (b: block) (ofs: Z) : res (block * Z * footprint) :=
  match phl with
  | nil => OK (b, ofs, fp)
  | ph :: l =>
      match ph, fp with
      | proj_deref, fp_box b fp1 =>
          (* if not_fp_emp fp1 then *)
            (* We can only deference box pointer that is not moved from *)
          get_owner_loc_footprint l fp1 b 0
          (* else *)
          (*   (* The location pointed by this pointer may not be valid *) *)
          (*   Error nil *)
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some ((base, fofs), fp1) =>
              get_owner_loc_footprint l fp1 b (ofs + fofs)
          | None => Error nil
          end
      | proj_field fid, fp_object id obj fpl =>
          match find_field fid fpl with
          | Some (b, ofs, ty, fp1) =>
              get_owner_loc_footprint l fp1 b ofs
          | None => Error nil
          end
      | proj_downcast fid1 (* fty1 *), fp_enum id _ fid2 fofs fp1 =>
          if ident_eq fid1 fid2  then
            get_owner_loc_footprint l fp1 b (ofs + fofs)
          else Error nil
      | _, _  => Error nil
      end
  end.

(* Why we need this? Because in the definition of invariant, we need
to ignore the memory locations information *)
Fixpoint get_owner_footprint (phl: list projection) (fp: footprint) : res footprint :=
  match phl with
  | nil => OK fp
  | ph :: l =>
      match ph, fp with
      | proj_deref, fp_box b fp1 =>
          get_owner_footprint l fp1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (fofs, fp1) =>
              get_owner_footprint l fp1
          | None => Error nil
          end
      | proj_field fid, fp_object id obj fpl =>
          match find_field fid fpl with
          | Some (b, ofs, fp1) =>
              get_owner_footprint l fp1
          | None => Error nil
          end
      | proj_downcast fid1 (* fty1 *), fp_enum id _ fid2 fofs fp1 =>
          if ident_eq fid1 fid2 then
            get_owner_footprint l fp1
          else
            Error nil
      | _, _  => Error nil
      end
  end.

Definition get_owner_loc_footprint_map (ps: path) (fpm: fp_map) : res (block * Z * footprint) :=
  let (id, phl) := ps in
  match fpm!id with
  | Some (b, ofs, ty, _, fp) =>
      get_owner_loc_footprint phl fp b ofs
  | _ => Error nil
  end.


Definition get_owner_footprint_map (ps: path) (fpg: fp_graph) : res footprint :=
  let (id, phl) := ps in
  match fpg!id with
  | Some fp =>
      get_owner_footprint phl fp
  | _ => Error nil
  end
.


(* In our setting, moving from a value is clearing its inner
footprint. Like RustBelt, for some type [own τ], after moving from a
value of this type produce, the original location of this type becomes
[own ⊥]. *)
Fixpoint clear_footprint_rec (ce: composite_env) (fp: footprint) : footprint :=
  match fp with
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, (r, ffp)) => (fid, (r, clear_footprint_rec ce ffp))) fpl)
  | _ => fp_uninit (sizeof_footprint ce fp) (alignof_footprint ce fp)
  end.
  (* match fp with *)
  (* | fp_scalar _ _ *)
  (* (* What about moving a reference? *) *)
  (* | fp_uninit _ _ *)
  (* | fp_object _ _ _               (* impossible?*) *)
  (* | fp_emp => fp *)
  (* | fp_box b fp1 => fp_box b fp_emp *)
  (* | fp_ref mut b ofs _ vs => *)
  (*     (* Move from a reference would disallow its usage *) *)
  (*     fp_ref mut b ofs None vs *)
  (* | fp_enum id tagz fid fofs ffp => fp_enum id tagz fid fofs (clear_footprint_rec ffp) *)
  (* | fp_struct id fpl => *)
  (*     fp_struct id (map (fun '(fid, (fofs, ffp)) => (fid, (fofs, clear_footprint_rec ffp))) fpl) *)
  (* end. *)


Definition clear_footprint_map (ce: composite_env) (ps: path) (fpm: fp_map) : res fp_map :=
  do (_, fp) <- get_owner_loc_footprint_map ps fpm;
  set_footprint_map ps (clear_footprint_rec ce fp) fpm.
  
Fixpoint clear_footprint_map_list (ce: composite_env) (l: list path) (fpm: fp_map) : res fp_map :=
  match l with
  | nil => OK fpm
  | ph :: l1 =>
      do fpm1 <- clear_footprint_map ce ph fpm;
      clear_footprint_map_list ce l1 fpm1
  end.


(* Get location and footprint through paths which may contains
dereference of reference *)

Definition append_proj (pj: projection) (ph: path) :=
  (fst ph, snd ph ++ [pj]).

(* To get the location of arbitary path, we divide it into two steps:
first we use [get_owner_path] to obtain the path of these projections
in the tree and second we use [get_owner_loc_footprint] to obtain the
actual memory address and its footprint. *)
Fixpoint get_owner_path (fpg: fp_graph) (ph: path) (phl: list projection) (fp: footprint) (alias: list path) : res (path * views) :=
  match phl with
  | nil => OK (ph, ph :: alias)
  | pj :: l =>
      let ph1 := append_proj pj ph in
      let alias1 := map (append_proj pj) alias in
      match pj, fp with
      | proj_deref , fp_box _ fp1 =>          
          get_owner_path fpg ph1 l fp1 alias1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_owner_path fpg ph1 l ffp alias1
          | None => Error nil
          end
      | proj_field fid, fp_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_owner_path fpg ph1 l ffp alias1
          | None => Error nil
          end
      | proj_downcast fid1, fp_enum _ _ fid2 _ fp1 =>
          if ident_eq fid1 fid2 then
            get_owner_path fpg ph1 l fp1 alias1
          else
            Error nil
      | proj_deref, fp_ref mut _ _ (Some ph2) rebor =>
          do fp2 <- get_owner_footprint_map ph2 fpg;
          (* dynamic computation of reborrow paths based on the
          supporting prefix technique of the borrow checker *)
          let alias2 := match mut with
                        | Mutable => (ph1 :: rebor ++ alias1)
                        (* ph1 and alias1 cannot modify the content in
                        ph2, so they are not added in the reborrow
                        paths *)
                        | Immutable => rebor
                        end in
          get_owner_path fpg ph2 l fp2 alias2
      | _, _  => Error nil
      end
  end.

(* This actually can be used to define "reachability" *)
Definition get_owner_path_map (ps: path) (fpg: fp_graph) : res (path * views) :=
  let (id, phl) := ps in
  match fpg!id with
  | Some fp =>
      get_owner_path fpg (id, nil) phl fp nil
  | _ => Error nil
  end.

(* For temporary footprint, we want to skip this footprint and find a
reachable path from this footprint to an owner path at fpg *)
(** Important TODO: maybe we should not use borrow_check_inv_snapshot
method to write invariant for temporary footprint and use this
get_reachable_path to derive the views of reachable path from
temporary footprint *)
Fixpoint get_reachable_path (fpg: fp_graph) (phl: list projection) (fp: footprint) : res (path * views) :=
  match phl with
  | nil => Error nil
  | pj :: l =>      
      match pj, fp with
      | proj_deref , fp_box _ fp1 =>          
          get_reachable_path fpg l fp1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_reachable_path fpg l ffp
          | None => Error nil
          end
      | proj_field fid, fp_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_reachable_path fpg l ffp
          | None => Error nil
          end
      | proj_downcast fid1, fp_enum _ _ fid2 _ fp1 =>
          if ident_eq fid1 fid2 then
            get_reachable_path fpg l fp1
          else
            Error nil
      | proj_deref, fp_ref mut _ _ (Some ph2) rebor =>
          do fp2 <- get_owner_footprint_map ph2 fpg;
          get_owner_path fpg ph2 l fp2 rebor
      | _, _  => Error nil
      end
  end.


(* Get the target footprint from a source footprint and a path
traversing the footprint. The result of this function should be the
same as the resulted evaluated from the combination of get_owner_path
and get_owner_footprint_map. Why we need this function because
sometime the starting point at [fp] does not belong to any
local/external variables *)

Fixpoint get_reachable_footprint (fpg: fp_graph) (phl: list projection) (fp: footprint) : res footprint :=
  match phl with
  | nil => OK fp
  | pj :: l =>
      match pj, fp with
      | proj_deref , fp_box _ fp1 =>          
          get_reachable_footprint fpg l fp1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_reachable_footprint fpg l ffp
          | None => Error nil
          end
      | proj_field fid, fp_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              get_reachable_footprint fpg l ffp
          | None => Error nil
          end
      | proj_downcast fid1, fp_enum _ _ fid2 _ fp1 =>
          if ident_eq fid1 fid2 then
            get_reachable_footprint fpg l fp1
          else
            Error nil
      | proj_deref, fp_ref mut _ _ (Some ph2) rebor =>
          do fp2 <- get_owner_footprint_map ph2 fpg;
          get_reachable_footprint fpg l fp2
      | _, _  => Error nil
      end
  end.

Definition get_reachable_footprint_map (fpg: fp_graph) (ph: path) : res footprint :=
  let (id, phl) := ph in
  match fpg!id with
  | Some fp =>
      get_reachable_footprint fpg phl fp
  | _ => Error nil
  end.


(* To also extract the type, use this function *)
Fixpoint get_owner_footprint_type ce (phl: list projection) (ty: type) (fp: footprint) : res (type * footprint) :=
  match phl with
  | nil => OK (ty, fp)
  | ph :: l =>
      match ph, fp with
      | proj_deref , fp_box _ fp1 =>
          do (ty1, _) <- type_deref ty;
          get_owner_footprint_type ce l ty1 fp1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, fp1) =>
              do fty <- type_field ce ty fid;
              get_owner_footprint_type ce l fty fp1
          | None => Error nil
          end
      (* Get the object's exposed borrowable value *)
      | proj_field fid, fp_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, fty1, fp1) =>
              get_owner_footprint_type ce l fty1 fp1
          | None => Error nil
          end
      | proj_downcast fid1, fp_enum _ _ fid2 _ fp1 =>
          if ident_eq fid1 fid2 then
              do fty <- type_field ce ty fid1;
            get_owner_footprint_type ce l fty fp1
          else
            Error nil
      | _, _  => Error nil
      end
  end.


Definition get_owner_footprint_type_map ce (ph: path) (fpm: fp_map) : res (type * footprint) :=
  let (id, pj) := ph in
  match fpm ! id with
  | Some (_, _, _, ty, fp) =>
      get_owner_footprint_type ce pj ty fp
  | None =>
      Error nil
  end.


(* We dynamically check that if one footprint is being overwritten, it
should not denote some unreleased resource, otherwise if some
reference pointed to this leak resource, but borrow check only check
assignment as shallow write, then we cannot maintain the invariant *)
Fixpoint fp_is_dropped (fp: footprint) : bool :=
  match fp with
  | fp_box _ _ => false
  | fp_enum id _ fid _ fp1 =>
      (fp_is_dropped fp1)
  | fp_struct id fpl =>
      (forallb (fun '(fid, (_, ffp)) => fp_is_dropped ffp) fpl) 
  | _ => true
  end.

(* Fixpoint fp_is_dropped (fp: footprint) : bool := *)
(*   match fp with *)
(*   | fp_box _  => negb (not_fp_emp fp1) *)
(*   | fp_enum id _ fid _ fp1 => *)
(*       (fp_is_dropped fp1) *)
(*   | fp_struct id fpl => *)
(*       (forallb (fun '(fid, (_, ffp)) => fp_is_dropped ffp) fpl)  *)
(*   | _ => true *)
(*   end. *)

Definition check_path_is_dropped (fpm: fp_map) (ph: path) : res bool :=
  do fp <- get_owner_footprint_map ph fpm;
  OK (fp_is_dropped fp).

(* Note that for example we split drop( p where p: Box<Box<i32>>) into
drop( *p) and drop(p) in the drop elaboration pass, so for fp_box to
be dropped we should ensure that its point-to footprint has been
dropped. *)
Definition check_path_is_droppable (fpm: fp_map) (ph: path) : res bool :=
  do fp <- get_owner_footprint_map ph fpm;
  match fp with
  | fp_box _ fp1 =>
      (* There is no need to check that fp1 has beed dropped or not
      since we do not guarantee no memory leak *)
      OK true
  | fp_struct _ _
  | fp_enum _ _ _ _ _ =>
      OK (deep_init fp)
  | _ => OK false
  end.

Fixpoint check_path_is_dropped_list (fpm: fp_map) (l: list path) : res bool :=
  match l with
  | nil => OK true
  | ph :: l1 =>
      do fg1 <- check_path_is_dropped fpm ph;
      do fg2 <- check_path_is_dropped_list fpm l1;
      OK (fg1 && fg2)
  end.


(** Borrow check operations *)

(* We access ph1, to see whether ph2 in the views is conflict with ph1 *)
Definition relevant_path (ph1: path) (am: access_mode_bor) (ph2: path) :=
  is_prefix_strict_path ph2 ph1 || 
    match am with
    | Ashallow => is_shallow_prefix_path ph1 ph2
    (* Note that all the path [ph2] in the views are mutable path, so if
  ph1 is a prefix of ph2 than ph1 must be the supporting prefix of
  ph2 *)
    | Adeep => is_prefix_path ph1 ph2
    end.
        
(* access ph: note that access ph by write/read is irrelevant because
all the path in views are mutable path *)
Definition conflict_view (ph: path) (am : access_mode_bor) (vs: views) : bool :=
  existsb (relevant_path ph am) vs.

Fixpoint invalidate_conflict_ref (ph: path) (ak: access_kind) (am : access_mode_bor) (fp: footprint) : footprint :=
  match fp with
  | fp_ref mut b ofs ph1 vs =>
      let ph1' := if conflict_access ak mut && conflict_view ph am vs then None else ph1 in
      fp_ref mut b ofs ph1' vs
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, (r, ffp)) => (fid, (r, invalidate_conflict_ref ph ak am ffp))) fpl)
  | fp_enum id tag fid fofs fp1 =>
      fp_enum id tag fid fofs (invalidate_conflict_ref ph ak am fp1)
  | fp_box b fp1 =>
      fp_box b (invalidate_conflict_ref ph ak am fp1)
  | _ => fp
  end.

Definition invalidate_conflict_ref_fpm (ph: path) (ak: access_kind) (am : access_mode_bor) (fpm: fp_map) : fp_map :=
  PTree.map1 (fun '(b, ofs, r, ty, fp) => (b, ofs, r, ty, invalidate_conflict_ref ph ak am fp)) fpm.

Fixpoint invalidate_conflict_ref_fpm_list (l: list path) (ak: access_kind) (am : access_mode_bor) (fpm: fp_map) : fp_map :=
  match l with
  | nil => fpm
  | ph :: l1 =>
      invalidate_conflict_ref_fpm_list l1 ak am (invalidate_conflict_ref_fpm ph ak am fpm)
  end.

(** Kill loans *)

(* We need to remove set of paths, i.e., views from the current views
because overwrite a path would kill all the views of this path. *)
Definition kill_paths (kill: views) (vs: views) : views :=
  filter (fun ph1 => negb (existsb (fun ph => is_prefix_path ph ph1) kill)) vs.


Fixpoint kill_paths_ref (kill: views) (fp: footprint) : footprint :=
  match fp with
  | fp_ref mut b ofs ph1 vs =>
      fp_ref mut b ofs ph1 (kill_paths kill vs)
  | fp_struct id fpl =>
      fp_struct id (map (fun '(fid, (r, ffp)) => (fid, (r, kill_paths_ref kill ffp))) fpl)
  | fp_enum id tag fid fofs fp1 =>
      fp_enum id tag fid fofs (kill_paths_ref kill fp1)
  | fp_box b fp1 =>
      fp_box b (kill_paths_ref kill fp1)
  | _ => fp
  end.

Definition kill_paths_ref_fpm (kill: views) (fpm: fp_map) : fp_map :=
  PTree.map1 (fun '(b, ofs, r, ty, fp) => (b, ofs, r, ty, kill_paths_ref kill fp)) fpm.

(* Only used in function return, to kill the loans reborrowed from
local variables/parameters *)
Fixpoint kill_vars_ref_fpm (l: list ident) (fpm: fp_map) : fp_map :=
  match l with
  | nil => fpm
  | id :: l1 =>
      kill_vars_ref_fpm l1 (kill_paths_ref_fpm ((id, nil) :: nil) fpm)
  end.

(* Operations for the function call and return *)

(** Some generic operations for adding and collecting paths from fpm or sv_map *)

Definition add_ref_path_views (ph: path) (vs: views) (r: origin) (ty: type) (l: list (path * (views * origin * type))) : list (path * (views * origin * type)):=
  if existsb (fun ph1 => is_prefix_path ph1 ph) (map fst l) then
    l
  else
    (* We keep the non-prefix paths *)
    let l1 := filter (fun '(ph1, (_, _, _)) => negb (is_prefix_path ph ph1)) l in
    (ph, (vs, r, ty)) :: l.

Definition lex_ord_lt := lex_ord lt lt.

Lemma remove_first_length_lt {A B: Type} eqA : forall (l1: list A) (l2 l2': list B) x 
    (InH: In x l1),
    lex_ord_lt (length (remove eqA x l1), length l2)  (length l1, length l2').
Proof.
  intros. eapply lex_ord_left.
  eapply remove_length_lt. auto.
Qed.


Lemma lex_lt_cons_snd {A B: Type} : forall (l1: list A) (l2 l2': list B) x
    (EQ: l2' = x :: l2),
    lex_ord_lt (length l1, length l2)  (length l1, length l2').
Proof.
  intros. rewrite EQ.
  eapply lex_ord_right. simpl. 
  econstructor.
Qed.

(* Recursively collect ref paths. The actual definition of get_paths
depends on the definition of structured memory. The returned list of
paths are the view of the reference which points to the owner path. We
need to remember it so that we can abstract it, pass it to callee and
then recover from the returned abstract view and recover to the
concrete views. [get_paths] gets the paths that a reference points to
along with the views of this reference. It may be not useful to
parametrize the get_paths as we can just use the result from the
RustIRspec to construct the footprint that are passed to the callee
instead of using footprint's specific get_paths function. *)
Fixpoint collect_ref_paths_generic (get_paths: path -> type -> res (list (path * (views * origin * type)))) (collected: list (path * (views * origin * type))) (to_visit: list (path * (views * origin * type))) (not_visited: list path) (ACC: Acc lex_ord_lt (length not_visited, length to_visit)) {struct ACC} : res (list (path * (views * origin * type))) :=
  (match to_visit as to_visit0 return (to_visit = to_visit0) -> res (list (path * (views * origin * type))) with
  | nil => fun _ => OK collected
  | (ph, (vs, r, ty)) :: to_visit1 =>
      fun eqH =>
        (** TODO: it may be better to use filter instead of remove  *)
        match in_dec path_eq ph not_visited with
        | left InH =>
            let not_visited1 := (remove path_eq ph not_visited) in
            let collected1 := add_ref_path_views ph vs r ty collected in
            do new_paths <- get_paths ph ty;
            let ACC1 := Acc_inv ACC (remove_first_length_lt path_eq not_visited (new_paths ++ to_visit1) to_visit ph InH) in
            collect_ref_paths_generic get_paths collected1 (new_paths ++ to_visit1) not_visited1 ACC1
        (* This ph has been visited so we skip it *)
        | right _ =>
            let ACC1 := Acc_inv ACC (lex_lt_cons_snd not_visited to_visit1 to_visit (ph, (vs, r, ty)) eqH) in
            collect_ref_paths_generic get_paths collected to_visit1 not_visited ACC1
        end
  end) eq_refl.

Lemma lex_ord_lt_acc_intro {A B: Type} : forall (l1: list A) (l2: list B),
    Acc lex_ord_lt (length l1, length l2).
Proof. 
  intros.
  eapply wf_lex_ord. all: eapply Nat.lt_wf_0.
Qed.

Definition suffix_projections (phl1 phl2: list projection) : list projection :=
  skipn (length phl1) phl2.

(* We do not return (option path) to simplify the semantics. Note that
our final goal is to prove no UB in this semantics, so we need to
ensure that None case is impossible *)
Definition generate_new_suffix_path (l: list (ident * path)) (ph: path) : res path :=
  match find (fun '(_, ph1) => is_prefix_path ph1 ph) l with
  | Some (idx, ph1) =>
      let pj := suffix_projections (snd ph1) (snd ph) in
      OK (idx, pj)
  | None => Error nil
  end.

(* The reverse operaiton of generate_new_suffix_path *)
(* ph= (id, pj) is the returned path where id can be seen as the index
of the l *)
Definition recover_ref_path (l: list (ident * path)) (ph: path) : res path :=
  let (id, pj) := ph in
  match find (fun '(id1, _) => ident_eq id id1) l with
  | Some (id1, ph1) =>
      (* ph1 is the path in the caller's svm, the actual path of ph
      should be defined as appending the projecitons of ph into the
      projetions of ph1 *)
      OK ((fst ph1, snd ph1 ++ pj))
  | None =>
      Error nil
end.
  (* match nth_error l (pred (Pos.to_nat id)) with *)
  (* | Some ph1 => *)
  (*     (* ph1 is the path in the caller's svm, the actual path of ph *)
  (*     should be defined as appending the projecitons of ph into the *)
  (*     projetions of ph1 *) *)
  (*     OK ((fst ph1, snd ph1 ++ pj)) *)
  (* | None => *)
  (*     Error nil *)
  (* end. *)


(** Implementation dependent operations *)


(* collect the owner paths stored in the leaf nodes that are fp_ref *)
Fixpoint collect_footprint_ref_paths (fp: footprint) : list path :=
  match fp with
  | fp_struct _ fpl =>
      flat_map  (fun '(_, (_, ffp)) => collect_footprint_ref_paths ffp) fpl
  | fp_enum _ _ _ _ ffp =>
      collect_footprint_ref_paths ffp
  | fp_box _ fp1 =>
      collect_footprint_ref_paths fp1
  | fp_ref _ _ _ (Some ph) _  =>
      ph :: nil
  | _ => nil
  end.

(* Similar to collect_sval_ref_paths, we also return the projections
of the reference path. It is only used in collect_sval_ref_paths_types *)
Fixpoint collect_footprint_ref_paths_projections (pj: list projection) (fp: footprint) : list (path * views * list projection) :=
  match fp with
  | fp_struct _ fpl =>
      flat_map  (fun '(fid, (_, ffp)) => collect_footprint_ref_paths_projections (pj ++ [proj_field fid]) ffp) fpl
  | fp_enum _ _ fid _ ffp =>
      collect_footprint_ref_paths_projections (pj ++ [proj_downcast fid]) ffp 
  | fp_box _ fp1 =>
      collect_footprint_ref_paths_projections (pj ++ [proj_deref]) fp1
  | fp_ref _ _ _ (Some ph) vs =>
      (ph, vs, pj) :: nil
  (* We assume that object cannot have referenece to the current environment *)
  (* | sv_object *)
  | _ => nil
  end.

(* collect all the unvisited owner path *)
Definition collect_fpm_ref_paths (fpm: fp_map) : list path :=
  let fpl := map (fun '(_, (_, _, _, _, fp)) => fp) (PTree.elements fpm) in
  flat_map collect_footprint_ref_paths fpl.




Definition collect_ref_type_region ce (ty: type) (pj: list projection) : res (origin * type) :=
    do ty1 <- wt_projections ce ty pj;
    match ty1 with
    | Treference r _ ty2 =>
        OK (r, ty2)
    | _ => Error nil
    end.

(** TODO: there may be no need to compute the type when collecting the
inout parameters path. We can build a substitution function to
substitute the type computed from get_owner_footprint_type at the
inout parameter path. *)
Definition collect_footprint_ref_paths_types ce (ty_fp: type * footprint) : res (list (path * (views * origin * type))) :=
  let (ty, fp) := ty_fp in
  let l := collect_footprint_ref_paths_projections nil fp in
  mmap (fun '(ph, vs, pj) => do (r, ty1) <- collect_ref_type_region ce ty pj;
                          OK (ph, (vs, r, ty1))) l.

Definition get_owner_footprint_map_ref_paths ce (fpm: fp_map) (ph: path) ty : res (list (path * (views * origin * type))) :=
  do fp <- get_owner_footprint_map ph fpm;
  collect_footprint_ref_paths_types ce (ty, fp).


(* We need to ensure that all the returned paths are disjoint, its
located note contain deep_init sval, and form a closure. The types of
the argument come from function signature, meaning that they contain
generic regions. *)
Definition collect_fpm_args_ref_paths ce (fpm: fp_map) (args: list (type * footprint)) : res (list (ident * (path * (views * origin * type)))) :=
  let not_visited := collect_fpm_ref_paths fpm in
  do l <- mmap (collect_footprint_ref_paths_types ce) args;
  let to_visit := concat l in
  do collected_paths <- collect_ref_paths_generic (get_owner_footprint_map_ref_paths ce fpm) nil to_visit not_visited (lex_ord_lt_acc_intro _ _);
  let idxl := map Pos.of_nat (seq O (length collected_paths)) in  
  OK (combine idxl collected_paths).
  

Fixpoint generate_new_suffix_path_footprint (process_views: path -> views -> views) (l: list (ident * path)) (fp: footprint) : res footprint :=
  match fp with
  | fp_ref mut b ofs (Some ph) vs =>
      do ph1 <- generate_new_suffix_path l ph;
      (* We can directly use ph1 as the abstract view for callee? *)
      OK (fp_ref mut b ofs (Some ph1) (process_views ph1 vs))
  | fp_box b fp1 =>
      do fp1' <- generate_new_suffix_path_footprint process_views l fp1;
      OK (fp_box b fp1')
  | fp_struct id fpl =>
      do fpl1 <- (mmap (fun '(fid, (r, ffp)) => 
                            do ffp1 <- generate_new_suffix_path_footprint process_views l ffp;
                            OK (fid, (r, ffp1))) fpl);
      OK (fp_struct id fpl1)
  | fp_enum id tag fid fofs ffp =>
      do ffp1 <- generate_new_suffix_path_footprint process_views l ffp;
      OK (fp_enum id tag fid fofs ffp1)
  | fp_object id obj fpl =>
      do fpl1 <- (mmap (fun '(fid, (r, ffp)) => 
                            do ffp1 <- generate_new_suffix_path_footprint process_views l ffp;
                            OK (fid, (r, ffp1))) fpl);
      OK (fp_object id obj fpl1)
  | _ => OK fp
  end.

Definition rename_path (substs: PTree.t ident) (ph: path) : res path :=
  let (id, pjl) := ph in
  match substs ! id with
  | Some id1 => OK (id1, pjl)
  | None => Error nil
  end.

Definition rename_views (substs: PTree.t ident) (vs: list path) : res views :=
  mmap (rename_path substs) vs.
  (* flat_map (fun ph1 => match recover_ref_path l ph1 with *)
  (*                   | OK ph2 => ph2 :: nil *)
  (*                   | _ => nil *)
  (*                   end) phl. *)


Fixpoint subst_list_idents (substs: PTree.t ident) (l: list ident) : res (list ident) :=
  match l with
  | nil => OK nil
  | id :: l1 =>
      match substs ! id with
      | Some id1 =>
          do l2 <- subst_list_idents substs l1;
          OK (id1 :: l1)
      | None =>
          Error nil
      end
  end.
  

(* It has some similarity with generate_new_suffix_path_footprint but
I do not know how to generalize it for now *)
Fixpoint rename_path_footprint (substs: PTree.t ident) (fp: footprint) : res footprint :=
  match fp with
  | fp_ref mut b ofs (Some ph) vs =>
      do ph1 <- rename_path substs ph;
      do vs1 <- rename_views substs vs;
      (* We can directly use ph1 as the abstract view for callee? *)
      OK (fp_ref mut b ofs (Some ph1) vs1)
  | fp_box b fp1 =>
      do fp1' <- rename_path_footprint substs fp1;
      OK (fp_box b fp1')
  | fp_struct id fpl =>
      do fpl1 <- (mmap (fun '(fid, (r, ffp)) => 
                            do ffp1 <- rename_path_footprint substs ffp;
                            OK (fid, (r, ffp1))) fpl);
      OK (fp_struct id fpl1)
  | fp_enum id tag fid fofs ffp =>
      do ffp1 <- rename_path_footprint substs ffp;
      OK (fp_enum id tag fid fofs ffp1)
  | fp_object id obj fpl =>
      do fpl1 <- (mmap (fun '(fid, (r, ffp)) => 
                            do ffp1 <- rename_path_footprint substs ffp;
                            OK (fid, (r, ffp1))) fpl);
      OK (fp_object id obj fpl1)
  | _ => OK fp
  end.



(* Collect the svals that are passed via reference to the environment *)
Definition collect_fpm_passed_ref_footprint (process_views: path -> views -> views) (fpm: fp_map) (l: list (ident * path)) : res (list (block * Z * footprint)) :=
  mmap (fun '(id, ph) => do (bofs, fp) <- get_owner_loc_footprint_map ph fpm;
                     do fp1 <- generate_new_suffix_path_footprint process_views l fp;
                     OK (bofs, fp1)) l.

Definition collect_fpm_return_ref_footprint (fpm: fp_map) (substs: PTree.t ident) : res fp_map :=
  (* let phs := map (fun '(s, t) => (s, (t, nil))) substs in *)
  let fpm1 := PTree.map_filter1 
                (fun '(b, ofs, opt_r, ty, fp) =>
                   match opt_r with
                   | Some r =>
                       match rename_path_footprint substs fp with
                       | OK fp1 =>
                           Some (b, ofs, Some r, ty, fp1)
                       | _ => None
                       end
                   | None => None
                   end) fpm in
  let flat_fpm1 := PTree.elements fpm1 in
  do rename_ids <- subst_list_idents substs (map fst flat_fpm1);
  OK (PTree_Properties.of_list (combine rename_ids (map snd flat_fpm1))).
    
  (* mfold_left (fun m '(s, t) =>  *)
  (*               match fpm ! s with *)
  (*               | Some (b, ofs, Some r, ty, fp) => *)
  (*                   do fp1 <- generate_new_suffix_path_footprint process_views phs fp; *)
                    
  (*                   OK (PTree.set t (b, ofs, Some r, ty, fp1) m) *)
  (*               | _ => Error nil *)
  (*               end) substs empty_fpm. *)


(* set sv_bot to the location that passed via reference *)
Fixpoint clear_fpm_passed_ref_sval (fpm: fp_map) (l: list path) : res fp_map :=
  match l with
  | nil => OK fpm
  | ph :: phl =>
      
      do fpm1 <- set_footprint_map ph fp_emp fpm;
      clear_fpm_passed_ref_sval fpm1 phl
  end.


(* The output parameters contain two parts: one for the normal
arguments and the others are the memory locations passed via
reference *)
Definition generate_call_parameters ce (fpm: fp_map) (args: list (type * footprint)) : res (list footprint * fp_map * list (ident * (path * (views * origin * type)))) :=
  do extern_paths <- collect_fpm_args_ref_paths ce fpm args;  
  let collected_paths := (map (fun '(id, (ph, _)) => (id, ph)) extern_paths) in
  do args1 <- mmap (generate_new_suffix_path_footprint (fun ph _ => ph :: nil) collected_paths) (map snd args);
  do inout_loc_footprints <- collect_fpm_passed_ref_footprint (fun ph _ => ph :: nil) fpm collected_paths;
  (* collect (origin, type) for the inout arguments *)
  let inout_params := map (fun '(r, ty, (b, ofs, fp)) => (b, ofs, Some r, ty, fp)) (combine (map (fun '(_, (_, (_, r, ty))) => (r, ty)) extern_paths) inout_loc_footprints) in
  let inout_fpm := PTree_Properties.of_list (combine (map fst collected_paths) inout_params) in
  OK (args1, inout_fpm, extern_paths).

(* Definition normalize_returned_views (phs: list (ident * path)) (_: path) (vs: views) : views := *)
(*   (* If we cannot find the path in phs, it means that it is a local *)
(*   path of the callee and we can just ignore it. *) *)
(*   flat_map (fun ph => match generate_new_suffix_path phs ph with *)
(*                    | OK ph1 => ph1 :: nil *)
(*                    | _ => nil *)
(*                    end) vs. *)

(* For funciton return, we need to reset the path name of the external
reference location to its normalized forms (i.e., the ordinal in the
list passed by caller). We can reuse the generate_new_suffix_path_sval
to do this work. *)
Definition generate_return_parameters (fpm: fp_map) (retv: footprint) (substs: PTree.t ident) : res (footprint * fp_map) :=
  do retv1 <- rename_path_footprint substs retv;
  do inout_fpm <- collect_fpm_return_ref_footprint  fpm substs;
  OK (retv1, inout_fpm).


  (* let phs := map (fun '(s, t) => (s, (t, nil))) substs in *)
  (* do retv1 <- generate_new_suffix_path_footprint (normalize_returned_views phs) phs retv; *)
  (* do inout_fpm <- collect_fpm_return_ref_footprint (normalize_returned_views phs) fpm substs; *)
  (* OK (retv1, inout_fpm). *)

  (* let phs := map (fun id => (id, nil)) ns in *)
  (* do retv1 <- generate_new_suffix_path_footprint (normalize_returned_views phs) phs retv; *)
  (* do out_params <- collect_fpm_return_ref_footprint (normalize_returned_views phs) fpm ns; *)
  (* OK (retv1, out_params). *)


(* When receive return value/input arguments from environment, the
current function should recover the normalized names that are passed
to environment (or generate new names to avoid name conflict with the
current variable names at function entry). These two kinds of
operations can be done using recover_sval_ref_paths. *)
Fixpoint recover_footprint_ref_paths (process_views: views -> views) (l: list (ident * path)) (fp: footprint)  : res footprint :=
  match fp with
  | fp_ref mut b ofs (Some ph) vs =>
      (* There may be view from the callee local paths (e.g., by
      returning a reborrowed path), which should be ignored when
      recovering the concrete views. *)
      do ph1 <- recover_ref_path l ph;
      OK (fp_ref mut b ofs (Some ph1) (process_views vs))
  | fp_box b fp1 =>
      do fp1' <- recover_footprint_ref_paths process_views l fp1;
      OK (fp_box b fp1')
  | fp_struct id fpl =>
      do fpl1 <- mmap (fun '(fid, (r, ffp)) => 
                        do ffp1 <- recover_footprint_ref_paths process_views l ffp;
                        OK (fid, (r, ffp1))) fpl;
      OK (fp_struct id fpl1)
  | fp_enum id tag fid fofs ffp =>
      do ffp1 <- recover_footprint_ref_paths process_views l ffp;
      OK (fp_enum id tag fid fofs ffp1)
  | fp_object id obj fpl =>
      do fpl1 <- mmap (fun '(fid, (r, ffp)) => 
                        do ffp1 <- recover_footprint_ref_paths process_views l ffp;
                        OK (fid, (r, ffp1))) fpl;
      OK (fp_object id obj fpl1)
  | _ =>
      OK fp
  end.

(* The id in ph is the index of the views *)
Definition recover_views_from_abstract_path (l: list views) (ph: path) : views :=
  let (id, pj) := ph in
  match nth_error l (Init.Nat.pred (Pos.to_nat id)) with
  | Some vs => (map (fun ph1 => (fst ph1, snd ph1 ++ pj)) vs)
  | None => nil
  end.
  
Definition recover_views (l: list views) (vs: views) : views :=
  flat_map (recover_views_from_abstract_path l) vs.

(* When the caller receives the returned sval and the
reference-passed sval list, it updates their reference paths and
then putback to the svm. The caller should guarantee that the external
svals are normalized into the form same as those passed by the
caller *)
Definition receive_return_footprint (fpm: fp_map) (l: list (ident * path * views)) (retv: footprint) (inout_fpm: fp_map) : res (footprint * fp_map) :=
  let phl := map fst l in
  let vsl := map snd l in
  do retv1 <- recover_footprint_ref_paths (recover_views vsl) phl retv;
  do fpm1 <- mfold_left (fun acc '(id, ph) => 
                          match inout_fpm ! id with
                          | Some (b, ofs, r, ty, fp) =>
                              do fp1 <- recover_footprint_ref_paths (recover_views vsl) phl fp;
                              set_footprint_map ph fp1 acc
                          | _ => Error nil
                          end) phl fpm;
(* set_footprint_map ph fp acc) phs_externs fpm; *)
  OK (retv1, fpm1).

 
Definition receive_incoming_params (substs: PTree.t ident) (args: list footprint) (inout_fpm: fp_map) : res (list footprint * fp_map) :=
  do args1 <- mmap (rename_path_footprint substs) args;
  do inout_fpm1 <- collect_fpm_return_ref_footprint inout_fpm substs;
  OK (args1, inout_fpm1).
 
Fixpoint clear_fpm_passed_ref_footprint (fpm: fp_map) (l: list path) : res fp_map :=
  match l with
  | nil => OK fpm
  | ph :: phl =>
     do fpm1 <- set_footprint_map ph fp_emp fpm;
     clear_fpm_passed_ref_footprint fpm1 phl
  end.

Section SEMANTICS.

(** ** Global environment  *)

Definition rustir_defmap := PTree.t (globdef fundef type).

Record genv := { genv_genv:> Genv.t fundef type; genv_defmap :> rustir_defmap ; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv:= Genv.globalenv se p; genv_defmap := prog_defmap p ; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.

(** ** Evaluation of expressions *)

Section EXPR.
  
Definition access_mode_chunk (ty: type) : res memory_chunk :=
  match access_mode ty with
  | By_value chunk => OK chunk
  | _ => Error nil
  end.

(* We also do dynamic borrow checking *)
Fixpoint eval_pexpr (fpm: fp_map) (pe: pexpr) : res (footprint * fp_map) :=
  match pe with
  | Eunit => OK (fp_scalar Mint32 (Vint Int.zero), fpm)               
  | Econst_int i ty => 
      do chunk <- access_mode_chunk ty;
      OK (fp_scalar chunk (Vint i), fpm)
  | Econst_float f ty => 
      do chunk <- access_mode_chunk ty;
      OK (fp_scalar chunk (Vfloat f), fpm)
  | Econst_single f ty => 
      do chunk <- access_mode_chunk ty;
      OK (fp_scalar chunk (Vsingle f), fpm)
  | Econst_long i ty => 
      do chunk <- access_mode_chunk ty;
      OK (fp_scalar chunk (Vlong i), fpm)
  | Eunop op a t =>
      do (v1, fpm1) <- eval_pexpr fpm a;
      match v1 with
      | fp_scalar _ v2 =>
          match sem_unary_operation op v2 t with
          | Some v3 =>
              do chunk <- access_mode_chunk t;
              OK (fp_scalar chunk v3, fpm1)
          | None =>
              Error nil
          end
      | _ => Error nil
      end
  | Ebinop op a1 a2 t =>
      do (v1, fpm1) <- eval_pexpr fpm a1;
      do (v2, fpm2) <- eval_pexpr fpm1 a2;
      match v1, v2 with
      | fp_scalar _ v1', fp_scalar _ v2' =>
          match sem_binary_operation_rust op v1' (typeof_pexpr a1) v2' (typeof_pexpr a2) with
          | Some v =>
              do chunk <- access_mode_chunk t;
              OK (fp_scalar chunk v, fpm2)
          | None =>
              Error nil
          end
      | _, _ => Error nil
      end
  | Eplace p ty =>
      (* We first do invalidation and then get the footprint because
      we do not want to do invalidate on the footprint we get. *)
      let fpm1 := invalidate_conflict_ref_fpm p ARead Adeep fpm in
      do (ph, _) <- get_owner_path_map p fpm1;
      do (_, fp) <- get_owner_loc_footprint_map ph fpm1;
      OK (fp, fpm1)
  | Ecktag p fid =>
      let fpm1 := invalidate_conflict_ref_fpm p ARead Ashallow fpm in
      do (ph, _) <- get_owner_path_map p fpm1;
      do (_, fp) <- get_owner_loc_footprint_map ph fpm1;
      match fp with
      | fp_enum _ _ fid1 _ _ =>
          (* refer to how rustc handles Discriminant operation
          (rustc_borrowck/src/lib.rs#L1550) *)
          OK (fp_scalar Mint8unsigned (Val.of_bool (ident_eq fid fid1)), fpm1)
      | _ => Error nil
      end
  | Eref _ mut p _ =>
      let ak := mut_to_access_kind mut in
      let fpm1 := invalidate_conflict_ref_fpm p ak Adeep fpm in
      do (ph, vs) <- get_owner_path_map p fpm1;
      do (bofs, _) <- get_owner_loc_footprint_map ph fpm1;
      let (b, ofs) := bofs in
      OK (fp_ref mut b ofs (Some ph) vs, fpm1)
  | _ => Error nil
  end.


Definition eval_expr (ce: composite_env) (fpm: fp_map) (e: expr) : res (footprint * fp_map) :=
  match e with
  | Emoveplace p _ =>
      (* The main reason we first do invalidation and then get the
      location is because we do not want to do invalidation on the
      footprint we get from the owner. The invalidation is used to
      simulate the deep access like creating a reference of this path.
      But the difficulty may be the proof of no invalid fp_ref in
      [fp]? Maybe in the static borrow checking, we can show that all
      reachable path of [p] is live so we cannot invalidate their
      fp_ref? No matter whether the fp_ref is reachable from [p]? *)
      let fpm1 := invalidate_conflict_ref_fpm p AWrite Adeep fpm in
      do (_, fp) <- get_owner_loc_footprint_map p fpm1;
      do fpm2 <- clear_footprint_map ce p fpm1;
      OK (fp, fpm2)
  | Epure pe =>
      eval_pexpr fpm pe
  end.


(* Fixpoint eval_exprlist (svm: sv_map) (al: list expr) (tyl: typelist) : res (list sval * sv_map) := *)
(*   match al, tyl with *)
(*   | nil, Tnil => OK (nil, svm) *)
(*   | a :: al1, Tcons ty tyl1 => *)
(*       do v1 <- eval_expr svm a; *)
(*       do svm1 <- move_place_option svm (moved_place a); *)
(*       do v1' <- sem_cast v1 (typeof a) ty; *)
(*       do (vl, svm2) <- eval_exprlist svm1 al1 tyl1; *)
(*       OK (v1' :: vl, svm2) *)
(*   | _, _ => Error nil *)
(*   end. *)

Fixpoint eval_exprlist ce (fpm: fp_map) (al: list expr) (* (tyl: typelist) *) : res (list footprint * fp_map) :=
  match al with
  | nil => OK (nil, fpm)
  | a :: al1 =>
      do (fp1, fpm1) <- eval_expr ce fpm a;
      (** We do not support sem_cast for now to simplify the proof, may
      be we need to do some restricted type checking *)
      (* do v1' <- sem_cast v1 (typeof a) ty; *)
      do (fpl, fpm2) <- eval_exprlist ce fpm1 al1;
      OK (fp1 :: fpl, fpm2)
  (* | _ => Error nil *)
  end.


End EXPR.

(** ** Program states *)

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: place -> function -> list (ident * (path * (views * origin * type))) -> PTree.t ident -> fp_map -> cont -> cont
.


(* Return from dropstate, dropplace and dropinsert is UB *)
Fixpoint call_cont (k: cont) : option cont :=
  match k with
  | Kseq _ k => call_cont k
  | Kloop _ k => call_cont k
  | _ => Some k
  end.


Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ => True
  | _ => False
  end.


Fixpoint typeof_cont_call (ttop: type) (k: cont) : type :=
  match k with
  | Kcall p _ _ _ _ _ =>
      typeof_place p
  | Kstop => ttop
  | Kseq _ k
  | Kloop _ k => typeof_cont_call ttop k
  end.

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (alpha: PTree.t ident)         (* used to record the new idents for the in-out parameters *)
    (fpm: fp_map)
    (sup: Mem.sup) : state
| Callstate
    (fun_id: ident)
    (args: list footprint)
    (* (inout: list (block * Z * origin * type * footprint)) *)
    (inout: fp_map)
    (sup: Mem.sup)
    (k: cont): state
| Returnstate
    (retv: footprint)
    (* (rety: type)   *)
    (* The return type may contain generic regions of the returned
    function *)
    (* (inout: list (block * Z * origin * type * footprint)) *)
    (inout: fp_map)
    (sup: Mem.sup)
    (k: cont): state.


(* Initialize of function *)

(* Copy from memory *)

Fixpoint find_max_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => Pos.max hd (find_max_pos tl)
  end.

Fixpoint npos (n: nat) (p: positive) : list positive :=
  match n with
  | O => nil
  | S n' =>
      p :: (npos n' (Pos.succ p))
  end.

Fixpoint alloc_vars ce (fpm: fp_map) (l: list (ident * type)) (sup: Mem.sup) : (fp_map * Mem.sup) :=
  match l with
  | nil => (fpm, sup)
  | (id, ty) :: l1 =>
      let b := Mem.fresh_block sup in
      alloc_vars ce (PTree.set id (b, 0, None, ty, type_to_uninit_footprint ce ty) fpm) l1 (Mem.sup_incr sup)
  end.

Fixpoint bind_params (fpm: fp_map) (l: list (ident * type)) (vl: list footprint) : res fp_map :=
  match l, vl with
  | nil, nil => OK fpm
  | (id, ty) :: l1, v :: vl1 =>
      do fpm1 <- set_footprint_map (id, nil) v fpm;
      bind_params fpm1 l1 vl1
  | _, _ => Error nil
  end.

Fixpoint bind_inout_params (fpm: fp_map) (l: list ident) (vl: list (block * Z * origin * type * footprint)) : res fp_map :=
  match l, vl with
  | nil, nil => OK fpm
  | id :: l1, (b, ofs, r, ty, v) :: vl1 =>
      let fpm1 := PTree.set id (b, ofs, Some r, ty, v) fpm in
      bind_inout_params fpm1 l1 vl1
  | _, _ => Error nil
  end.

(* We should assume that the types in inout_params contain generic
regions instead of the local regions from the caller. *)
Definition function_entry ce (f: function) (args: list footprint) (inout_fpm: fp_map) (sup: Mem.sup) : res (PTree.t ident * fp_map * Mem.sup) :=
  let names := field_idents (fn_params f ++ fn_vars f) in
  let fresh_var := Pos.succ (find_max_pos names) in
  let inout_params := PTree.elements inout_fpm in
  let fresh_vars := npos (length inout_params) fresh_var in
  let substs1 := PTree_Properties.of_list (combine fresh_vars (map fst inout_params)) in
  let substs2 := PTree_Properties.of_list (combine (map fst inout_params) fresh_vars) in
  (* Substitute the old name in args and in_params with the fresh names *)
  (* let fresh_paths := map (fun id => (id, (id, nil))) fresh_vars in *)
  do (args1, inout_fpm1) <- receive_incoming_params substs2 args inout_fpm;
  (* allocate the variables and paramters *)
  let (fpm1, sup1) := alloc_vars ce inout_fpm1 (f.(fn_params) ++ f.(fn_vars)) sup in
  (* set the value to the map *)
  do fpm2 <- bind_params fpm1 (fn_params f) args1;
  (* do fpm3 <- bind_inout_params fpm2 fresh_vars inout_params1; *)
  OK (substs1, fpm2, sup1).

Definition var_to_path (v: ident * type) : path := (fst v, nil).

Definition vars_to_paths (l: list (ident * type)) : list path :=
  map var_to_path l.



Definition before_write_place ce (fpm1: fp_map) (p: place) : res (path * views * fp_map) :=
  do (ph, vs) <- get_owner_path_map p fpm1;
  (* This property should be guaranteed by the correct insertion of
    drop. Since we have no way to express this guarantee provided by
    RustIRgen/Drop Elaboration, we must encode it into the
    semantics. *)
  do is_dropped <- check_path_is_dropped fpm1 ph;
  if is_dropped then
    (* Before overwrite the target location, we should first set it to
    fp_uninit so that the original fp_ref in this location is removed
    and we can establish invariant before overwriting a new
    value. Maybe in high-level spec without views at fp_ref, we can
    remove this extra operation because the cleared place would be
    immediately assigned with value. *)
    do fpm2 <- clear_footprint_map ce ph fpm1;
    (* To make the views at each reference precise. Note that we
    should also kill the loans in the evaluated value (e.g., consider
    x = &mut *x. Therefore we return the views of p. *)
    OK (ph, vs, kill_paths_ref_fpm vs fpm2)
  else Error nil.

Definition eval_assign ce (fpm1: fp_map) (p: place) (e: expr) : res (path * footprint * fp_map) :=
  do (vfp, fpm2) <- eval_expr ce fpm1 e;
  let fpm3 := invalidate_conflict_ref_fpm p AWrite Ashallow fpm2 in
  do (ph_vs, fpm4) <- before_write_place ce fpm3 p;
  let (ph, vs) := ph_vs in
  (* We also need to do invalidation on vfp? I think we cannot create
  some reference which borrows prefix of shallow children parts of the
  written place ,e.g., [*a = &mut a] or [a.f = &mut a]. But anyway,
  the static borrow checking would check this situation, therefore we
  need to do invalidation on the evaluated footprint. *)
  let vfp1 := invalidate_conflict_ref p AWrite Ashallow vfp in
  OK (ph, (kill_paths_ref vs vfp1), fpm4).


Section SMALLSTEP.

Variable ge: genv.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e (p: place) vfp fpm1 fpm2 fpm3 ph ns k sup
    (EVAL: eval_assign ge fpm1 p e = OK (ph, vfp, fpm2))    
    (ASS: set_footprint_map ph vfp fpm2 = OK fpm3),
    step (State f (Sassign p e) k ns fpm1 sup) E0 (State f Sskip k ns fpm3
 sup)
| step_assign_variant: forall f e (p: place) k fpm1 fpm2 fpm3 vfp co fid enum_id orgs ph fty ns sup fofs tag
    (EVAL: eval_assign ge fpm1 p e = OK (ph, vfp, fpm2))
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK fty)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* (CAST: sem_cast v (typeof e) fty = OK v1) *)
    (ASS: set_footprint_map ph (fp_enum enum_id tag fid fofs vfp) fpm2 = OK fpm3),
    step (State f (Sassign_variant p enum_id fid e) k ns fpm1 sup) E0 (State f Sskip k ns fpm3 sup)
| step_box: forall f e (p: place) k ty fpm1 fpm2 fpm3 vfp ph ns sup
    (EVAL: eval_assign ge fpm1 p e = OK (ph, vfp, fpm2))
    (TYP: typeof_place p = Tbox ty)
    (* (CAST: sem_cast v (typeof e) ty = OK v1) *)
    (ASS: set_footprint_map ph (fp_box (Mem.fresh_block sup) vfp) fpm2 = OK fpm3),
    step (State f (Sbox p e) k ns fpm1 sup) E0 (State f Sskip k ns fpm3 (Mem.sup_incr sup))
(* big-step drop semantics: just like a move operation. But we need to
check that the footprint in the dropped place is deeply owned, which
encodes the guarantee provided by the Drop elaboration, i.e., it only
keeps the drop statement for the place that is init. *)
| step_drop: forall fpm1 fpm2 fpm3 k f (p: place) ns sup
    (* We must ensure that p is an owner, otherwise dropping [*p where
    p:&mut Box<i32>] and then not reassigning a new value into [*p]
    would break memory safety. Because [p] may be created from
    reborrowing [q] and [q] can be used after dropping [*p] without
    reassignment. We should use [drop_and_replace( *p, v)] to perform
    drop on [*p]. *)
    (* (EVALP: get_owner_loc p fpm1 = OK (ph, vs)) *)
    (INVP: invalidate_conflict_ref_fpm p AWrite Adeep fpm1 = fpm2)
    (* Properties ensured by Drop elaboration, which we encode into
    the semantics *)
    (DEEP_INIT: check_path_is_droppable fpm2 p = OK true)
    (DROP: clear_footprint_map ge p fpm2 = OK fpm3),
    step (State f (Sdrop p) k ns fpm1 sup) E0 (State f Sskip k ns fpm3 sup)
| step_storagelive: forall f k ns fpm id sup,
    step (State f (Sstoragelive id) k ns fpm sup) E0 (State f Sskip k ns fpm sup)
| step_storagedead: forall f k ns fpm1 fpm2 id sup
    (* The insertion of drop should ensure that before storagedead,
    the resource of variable is released. But why do we need this? Is
    it necessary to the proof? Or is it because we will set it to
    uninit and kill the loans related to this variable so there should
    not be memory leak? *)
    (CKDROP: check_path_is_dropped fpm1 (id, nil) = OK true)
    (* To maintain the invariant, we need to clear all the dead
    sv_ref, so we set it to sv_bot. *)
    (CLR: clear_footprint_map ge (id, nil) fpm1 = OK fpm2),
    step (State f (Sstoragedead id) k ns fpm1 sup) E0 (State f Sskip k ns fpm2 sup)
| step_call: forall f ty al k tyargs fd cconv tyres p orgs org_rels fun_id fpm1 fpm2 args args1 inout_params ns phl sup
    (CASE: classify_fun ty = fun_case_f tyargs tyres cconv)
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (EVAL: eval_exprlist ge fpm1 al = OK (args, fpm2))
    (NOT_DROP: function_not_drop_glue fd)
    (* Collect the footprint that is passed via reference *)
    (REF_OUT: generate_call_parameters ge fpm2 (combine (type_list_of_typelist tyargs) args) = OK (args1, inout_params, phl)),
    step (State f (Scall p (Eglobal fun_id ty) al) k ns fpm1 sup) E0 (Callstate fun_id args1 inout_params sup (Kcall p f phl ns fpm2 k))
| step_internal_function: forall fun_id vargs inout_params k fpm1 f ns sup1 sup2
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry ge f vargs inout_params sup1 = OK (ns, fpm1, sup2)),
    step (Callstate fun_id vargs inout_params sup1 k) E0 (State f f.(fn_body) k ns fpm1 sup2)

| step_return_1: forall p vfp vfp1 vfp2 fpm1 fpm2 fpm3 fpm4 f k ck ns out_params sup
    (CONT: call_cont k = Some ck)
    (* Should we move out the return varibales so that the borrow
    check can tell that the inout params cannot point to this return
    variable's reachable locations? *)
    (EVAL: eval_expr ge fpm1 (Emoveplace p (typeof_place p)) = OK (vfp, fpm2))
    (* perform shallow write for variables/parameters *)
    (FREE: invalidate_conflict_ref_fpm_list (map (fun '(id, _) => (id,nil)) (f.(fn_vars) ++ f.(fn_params))) AWrite Ashallow fpm1 = fpm2)
    (* kill loans reborrowed from variables/parameters *)
    (KILL: kill_paths_ref_fpm (vars_to_paths (f.(fn_vars) ++ f.(fn_params))) fpm2 = fpm3)
    (* set all the variables/parameters to fp_uninit to align with the
    operation of kill loans *)
    (CLR: clear_footprint_map_list ge (vars_to_paths (f.(fn_vars) ++ f.(fn_params))) fpm3 = OK fpm4)
    (* (CAST: sem_cast v (typeof_place p) f.(fn_return) = OK v1) *)
    (* Rename the external footprint to match the use of the names
    passed in this function. How to ensure that all the above
    operation is not related to vfp? We need to kill all the loans
    created from reborrowing the variables/parameters in the return
    value (e.g., consider [return &mut *x] where x points to an in-out
    parameters *)
    (RETV: (kill_paths_ref (vars_to_paths (f.(fn_vars) ++ f.(fn_params))) vfp) = vfp1)
    (NORMALIZE: generate_return_parameters fpm4 vfp1 ns = OK (vfp2, out_params)),
    (** How to know in advance that all the reference in out
    parameters are not fp_uninit? It is ensured by check_dangle? *)
    step (State f (Sreturn p) k ns fpm1 sup) E0 (Returnstate vfp2 out_params sup ck)

| step_returnstate: forall (p: place) v v1 fpm1 fpm2 fpm3 fpm4 f k inout_fpm phl ph ns vs sup
    (* We need to first putback the ref-passed location and the do the
    assignment because p may locate in those ref-passed locations *)
    (PUTBACK: receive_return_footprint fpm1 (map (fun '(id, (ph, (vs, _, _))) => (id, ph, vs)) phl) v inout_fpm = OK (v1, fpm2))
    (EVALP: before_write_place ge fpm2 p = OK (ph, vs, fpm3))    
    (* (CASTED: sval_casted v1 (typeof_place p)) *)
    (ASS: set_footprint_map ph (kill_paths_ref vs v1) fpm3 = OK fpm4),
    step (Returnstate v inout_fpm sup (Kcall p f phl ns fpm1 k)) E0 (State f Sskip k ns fpm4 sup)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m sup,
    step (State f (Ssequence s1 s2) k e m sup)
      E0 (State f s1 (Kseq s2 k) e m sup)
| step_skip_seq: forall f s k e m sup,
    step (State f Sskip (Kseq s k) e m sup)
      E0 (State f s k e m sup)
| step_continue_seq: forall f s k e m sup,
    step (State f Scontinue (Kseq s k) e m sup)
      E0 (State f Scontinue k e m sup)
| step_break_seq: forall f s k e m sup,
    step (State f Sbreak (Kseq s k) e m sup)
      E0 (State f Sbreak k e m sup)
| step_ifthenelse:  forall f a s1 s2 k e m m1 v1 b sup
    (* there is no receiver for the moved place, so it must be a pure
    expression *)
    (EVAL: eval_pexpr m a = OK (fp_scalar Mint8unsigned v1, m1)),
    bool_val v1 (typeof a) = Some b ->
    step (State f (Sifthenelse (Epure a) s1 s2) k e m sup)
      E0 (State f (if b then s1 else s2) k e m1 sup)
| step_loop: forall f s k e m sup,
    step (State f (Sloop s) k e m sup)
      E0 (State f s (Kloop s k) e m sup)
| step_skip_or_continue_loop:  forall f s k e m x sup,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e m sup)
      E0 (State f s (Kloop s k) e m sup)
| step_break_loop:  forall f s k e m sup,
    step (State f Sbreak (Kloop s k) e m sup)
      E0 (State f Sskip k e m sup)
.

(** Language interfaces for the RustIR specification *)

Record rust_spec_query :=
  rspec_q {
    rspec_fid: ident;
    rspec_sg: rust_signature;
    rspec_args: list footprint;
    rspec_in_fpm: fp_map;
    rspec_q_sup: Mem.sup;
  }.

Record rust_spec_reply :=
  rspec_r {
    rspec_retval: footprint;
    (* rspec_rety: type; *)
    rspec_out_fpm: fp_map;
    rspec_r_sup: Mem.sup;
  }.

Definition li_rs_spec : language_interface :=
  {|
    query := rust_spec_query;
    reply := rust_spec_reply;
    entry _ := Vundef;
  |}.


(** Open semantics *)

Inductive initial_state: (query li_rs_spec) -> state -> Prop :=
| initial_state_intro: forall f targs tres tcc vargs orgs org_rels fun_id inout_fpm sup
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (TYF: type_of_function f = Tfunction orgs org_rels targs tres tcc)
    (* This function must not be drop glue *)
    (NOTDROP: f.(fn_drop_glue) = None),
    (* how to prove it? *)
    (* (CAST: sval_casted_list vargs targs), *)
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rspec_q fun_id (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs inout_fpm sup)
      (Callstate fun_id vargs inout_fpm sup Kstop).


Inductive at_external: state -> (query li_rs_spec) -> Prop :=
| at_external_intro: forall fun_id name args k targs tres cconv orgs org_rels in_params sup
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv))),
    at_external (Callstate fun_id args in_params sup k) (rspec_q fun_id (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args in_params sup).

Inductive after_external: state -> (reply li_rs_spec) -> state -> Prop:=
| after_external_intro: forall fun_id args k in_params out_params v sup1 sup2,
    after_external
      (Callstate fun_id args in_params sup1 k)
      (rspec_r v out_params sup2)
      (Returnstate v out_params sup2 k).

Inductive final_state: state -> (reply li_rs_spec) -> Prop:=
| final_state_intro: forall v out_params sup,
    final_state (Returnstate v out_params sup Kstop) (rspec_r v out_params sup).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

End SPEC.


(* Define here just for simplicity *)
Section TYPE_PRESERVATION.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).


Variable prog: program.
Hypothesis WTPROG: wt_program prog.
Variable se: Genv.symtbl.
Let ge := globalenv se prog.
Let L := @semantics ame prog se.

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
| wt_Kcall: forall k p f f' fpm te substs inout_paths
    (WT1: wt_call_cont (Kcall p f' inout_paths substs fpm k) f.(fn_return)),
    wt_cont te f (Kcall p f' inout_paths substs fpm k)

with wt_call_cont : cont -> type -> Prop :=
| wt_call_Kstop:
  wt_call_cont Kstop (rs_sig_res sg)
| wt_call_Kcall: forall p f (fpm: fp_map) substs inout_paths k rty
    (WT1: wt_cont (fpm_to_env fpm) f k)
    (WT2: wt_place (fpm_to_env fpm) ge p)
    (WT3: type_eq_except_origins rty (typeof_place p) = true),
    (* For simplicity, we do not consider casting in function call *)
  wt_call_cont (Kcall p f inout_paths substs fpm k) rty
.


Inductive wt_state : state -> Prop :=
| wt_regular_state: forall f s k substs fpm sup
    (WT1: wt_stmt (fpm_to_env fpm) ge s)
    (WT2: wt_cont (fpm_to_env fpm) f k),
    wt_state (State f s k substs fpm sup)
| wt_callstate: forall fid fd orgs rels tyl rty cc k fpl inout_fpm sup
    (FINDF: ge.(genv_defmap) ! fid = Some (Gfun fd))
    (FTY: type_of_fundef fd = Tfunction orgs rels tyl rty cc)
    (WT1: wt_call_cont k rty),
    wt_state (Callstate fid fpl inout_fpm sup k)
| wt_returnstate: forall k rety inout_fpm sup v
    (WT1: wt_call_cont k rety),
    wt_state (Returnstate v inout_fpm sup k)
.

(* Hint Constructors wt_cont wt_stmt wt_state: spec_ty. *)

(* Lemma wt_call_cont_type_eq: forall k ty1, *)
(*     wt_call_cont k ty1 -> *)
(*     type_eq_except_origins ty1 (typeof_cont_call (rs_sig_res sg) k) = true. *)
(* Proof. *)
(*   induction 1; intros; simpl in *; auto. *)
(*   eapply type_eq_except_origins_refl. *)
(* Qed. *)

(* Lemma is_wt_call_cont: *)
(*   forall te f k, *)
(*     is_call_cont k -> wt_cont te f k -> wt_call_cont k f.(fn_return). *)
(* Proof. *)
(*   intros. inv H0; simpl in H; try contradiction; auto. *)
(* Qed. *)

(* Lemma wt_cont_call_cont: forall k le f ck, *)
(*     wt_cont le f k -> *)
(*     call_cont k = Some ck -> *)
(*     wt_cont le f ck. *)
(* Proof. *)
(*   induction 1; intros CC; simpl in *; auto; try (inv CC; econstructor; eauto). *)
(* Qed. *)

(* Lemma call_cont_wt_call_cont: *)
(*   forall te f k ck, *)
(*     call_cont k = Some ck -> *)
(*     wt_cont te f k -> wt_call_cont ck f.(fn_return). *)
(* Proof. *)
(*   intros. eapply (is_wt_call_cont te). *)
(*   eapply call_cont_correct. eauto. *)
(*   eapply wt_cont_call_cont; eauto. *)
(* Qed. *)

(* (* The function found in the globalenv is well-typed *) *)

(* Lemma find_funct_wt: forall vf fd, *)
(*     Genv.find_funct ge vf = Some fd -> *)
(*     wt_fundef ge fd. *)
(* Proof. *)
(*   intros. simpl in *. inv WTPROG. *)
(*   eapply Genv.find_funct_prop; eauto. *)
(*   intros. eapply H0; eauto. *)
(* Qed.   *)

Lemma wt_initial_state: forall s q,
    rspec_sg q = sg ->
    initial_state ge q s ->
    wt_state s.
Proof.
(*   intros s q SGEQ INIT. *)
(*   inv INIT. *)
(*   exploit find_funct_wt; eauto. *)
(*   intros WTF. inv WTF. *)
(*   econstructor; eauto. *)
(*   assert (RTY: tres = (rs_sig_res sg)). *)
(*   { simpl in SGEQ. destruct sg. simpl. inv SGEQ. auto. } *)
(*   subst. econstructor. *)
(* Qed. *)
Admitted.

Lemma wt_state_step_preservation: forall s1 t s2,
    wt_state s1 ->
    Step L s1 t s2 ->
    wt_state s2.
Proof.
  intros s1 t s2 WTST STEP; inv STEP; inv WTST.
  all: try eauto with ty.
(*   - inv SDROP; eauto with ty. *)
(*   - inv SDROP; eauto with ty; inv WT1; eauto with ty. *)
(*   - inv WT1. simpl in *. inv H. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*   - exploit find_funct_wt; eauto. *)
(*     intros WTF. simpl in *. *)
(*     unfold ge in FIND0. rewrite FIND in FIND0. inv FIND0. *)
(*     inv WTF. inv H0. *)
(*     inv ENTRY. exploit alloc_variables_bind_vars_eq; eauto. *)
(*     intros BINDEQ. rewrite bind_vars_app in *. *)
(*     econstructor; eauto. *)
(*     rewrite <- BINDEQ. eauto.     *)
(*     inv WT1. *)
(*     econstructor. destruct f. simpl in *. inv FTY. econstructor. *)
(*     econstructor. destruct f. simpl in *. inv FTY. econstructor; eauto. *)
(*   - inv WT1. econstructor. *)
(*     eapply call_cont_wt_call_cont; eauto. *)
(*   - inv WT1. econstructor; eauto. econstructor. *)
(*   - inv WT1; eauto with ty.     *)
(*   - inv WT2; eauto with ty. *)
(*   - inv WT2; eauto with ty. *)
(*   - inv WT2; eauto with ty. *)
(*   - inv WT1; eauto with ty. *)
(*     destruct b; eauto with ty. *)
(*   - inv WT1; eauto with ty. *)
(*   - inv WT2; eauto with ty. *)
(*   - inv WT2; eauto with ty. *)
(* Qed. *)
Admitted.

Lemma wt_state_external_preservation: forall s1 q,
    wt_state s1 ->
    at_external ge s1 q ->
    forall r s2, after_external s1 r s2 ->
            wt_state s2.
Proof.
  intros. inv H0. inv H. inv H1.
  econstructor; eauto.
Qed.

    
End TYPE_PRESERVATION.
