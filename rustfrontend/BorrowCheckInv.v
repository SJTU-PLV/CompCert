Require Import Coqlib.
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight.
Require Import RustOp RustIR Rusttyping.
Require Import Errors.
Require Import Listmisc.
Require Import BorrowCheckDomain.
Require Import Rustlightown RustIRspec.

Import ListNotations.

Local Open Scope error_monad_scope.


Ltac destr_path_of_place p :=
  destruct (path_of_place p) as (?pid & ?phl) eqn: ?POP.

Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation fp_graph := (@fp_graph ame).
Notation get_owner_path_map := (@get_owner_path_map ame).

(* Section COMP_ENV. *)

(* Variable ce: composite_env. *)

(* Fixpoint mutable_projections (ty: type) (phl: list projection) : bool := *)
(*   match phl with *)
(*   | nil => true *)
(*   | ph :: phl1 => *)
(*       match ph with *)
(*       | proj_deref =>  *)
(*           if is_immutable_ref ty then  *)
(*             false *)
(*           else  *)
(*             match type_deref ty with *)
(*             | OK ty1 => mutable_projections ty1 phl1 *)
(*             | _ => false *)
(*             end *)
(*       | proj_field fid =>  *)
(*           match type_field ce ty fid with *)
(*           | OK ty1 => mutable_projections ty1 phl1 *)
(*           | _ => false *)
(*           end *)
(*       | proj_downcast fid =>  *)
(*           match type_downcast ce ty fid with *)
(*           | OK ty1 => mutable_projections ty1 phl1 *)
(*           | _ => false *)
(*           end *)
(*       end *)
(*   end. *)


(* Definition mutable_path (fpm: fp_map) (ph: path) : bool := *)
(*   let (id, phl) := ph in *)
(*   match fpm ! id with *)
(*   | Some (_, _, _, ty, _) => *)
(*       mutable_projections ty phl *)
(*   | None => *)
(*       false *)
(*   end. *)

(* End COMP_ENV. *)

Fixpoint mutable_path_footprint (fpg: fp_graph) (phl: list projection) (fp: footprint) : res bool :=
  match phl with
  | nil => OK true
  | pj :: l =>
      match pj, fp with
      | proj_deref , fp_box _ fp1 =>          
          mutable_path_footprint fpg l fp1
      | proj_field fid, fp_struct _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              mutable_path_footprint fpg l ffp
          | None => Error nil
          end
      | proj_field fid, fp_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, ffp) =>
              mutable_path_footprint fpg l ffp
          | None => Error nil
          end
      | proj_downcast fid1, fp_enum _ _ fid2 _ fp1 =>
          if ident_eq fid1 fid2 then
            mutable_path_footprint fpg l fp1
          else
            Error nil
      | proj_deref, fp_ref mut _ _ (Some ph2) rebor =>
          match mut with
          | Mutable =>
              do fp2 <- get_owner_footprint_map ph2 fpg;
              mutable_path_footprint fpg l fp2
          | Immutable =>
              OK false
          end
      | _, _  => Error nil
      end
  end.


Definition mutable_path (ph: path) (fpg: fp_graph) : res bool :=
  let (id, phl) := ph in
  match fpg!id with
  | Some fp =>
      mutable_path_footprint fpg phl fp
  | _ => Error nil
  end.


(* Maybe useful comment *)
(* For safety: all owner paths that have the ability to change the
   semantic typed of the stored value or permission of the location
   that the reference points to should be approximated by (i.e., they
   should appear as loans in the loan set of this region) the borrow
   check result. However, borrow checker checks more properties than
   safety. For example, borrow checker would check the stack
   discipline of multiple mutable borrows, which can be expressed by
   adding stacked borrow model into each owner path. These multiple
   mutable accesses cannot perform "full write" to the locations they
   point to. They can only perfom in-place write which would ensure
   the well-typedness of the new values. *)

(** Invariant: the views stored at each reference path can
precisely(?) capature all reachable paths (that are live and mutable)
to this reference path excluding the paths created by reborrowed from
this reference path. *)

Fixpoint all_splits {A} (l : list A) : list (list A * list A) :=
  match l with
  | nil => nil
  | x :: xs => (x::nil, xs) :: map (fun '(p,s) => (x::p, s)) (all_splits xs)
  end.


Definition dominators_of_owner_projections (l: list projection) : list (list projection * list projection) :=
  filter (fun '(_, s) => in_dec projection_eq proj_deref s) (all_splits l).


Inductive reachable_from_dominators (fpg: fp_graph) : path -> path -> Prop :=
| reachable_from_dominators_intro: forall id1 pjl1 id2 pjl dom_pjl suf_pjl vs,
    In (dom_pjl, suf_pjl) (dominators_of_owner_projections pjl) ->
    get_owner_path_map (id1, pjl1) fpg = OK ((id2, dom_pjl), vs) ->
    reachable_from_dominators fpg (id1, pjl1 ++ suf_pjl) (id2, pjl).
    
Definition fp_ref_views_adequate (fpg: fp_graph) (tgt: path) (vs: views) : Prop := 
  forall ph1, reachable_from_dominators fpg ph1 tgt ->
         mutable_path ph1 fpg = OK true ->
         In ph1 vs.

(* Note that the precision is conditional. It only holds for the valid
path. *)
Definition fp_ref_views_precise (fpg: fp_graph) (tgt: path) (vs: views) : Prop := 
  forall ph1 tgt1 vs1,
    In ph1 vs ->
    (* If it reaches a target? Consider invalidate some mutable
    path while reading some mutable path, but the views in the
    immutable reference do not change. We can kill this loan in the
    immutable reference maybe? But then the adequate property becomes
    non-trivial to be preserved under invalidation because we can
    reduce some path in the views. I think this should be related to
    actual kill loans operations. *)
    (* Actually, it is not definable because we need to do something
    like when invalidating a reference, we need to kill the loans
    related to this reference for other reference.  *)
    get_owner_path_map ph1 fpg = OK (tgt1, vs1) ->
    tgt = tgt1 /\ mutable_path ph1 fpg = OK true.

(* We cannot define stack discipline in the context of fp_map because
we need to show that all the temporary footprint does not point to the
same location? We need to define this property in the whole fp_graph
with temporary values. *)


Inductive views_order (fpg: fp_graph) (ph1 ph2: path) (vs1 vs2: views) : Prop :=
| views_order_immut_mut
    (IMMUTL: mutable_path ph1 fpg = OK false)
    (MUT: mutable_path ph2 fpg = OK true)
    (INCL: incl vs2 vs1)
    (NEQ: ~ list_equiv vs1 vs2):
  views_order fpg ph1 ph2 vs1 vs2
| views_order_mut_immut
    (IMMUTL: mutable_path ph2 fpg = OK false)
    (MUT: mutable_path ph1 fpg = OK true)
    (INCL: incl vs1 vs2)
    (NEQ: ~ list_equiv vs1 vs2):
  views_order fpg ph1 ph2 vs1 vs2
| views_order_mut_mut
    (IMMUTL: mutable_path ph1 fpg = OK true)
    (MUT: mutable_path ph2 fpg = OK true)
    (INCL: incl vs1 vs2 \/ incl vs2 vs1)
    (NEQ: ~ list_equiv vs1 vs2):
  views_order fpg ph1 ph2 vs1 vs2
| views_order_immut_immut
    (IMMUTL: mutable_path ph1 fpg = OK false)
    (MUT: mutable_path ph2 fpg = OK false):
  (* The relation between two immutable paths are not important?
  Because they cannot invalidate each other. *)
  views_order fpg ph1 ph2 vs1 vs2.

  
(* The paths that reach the same location should form a total order
chain. Should we enforce that the views of mutable path must be
smaller than those of immutable path? Because we have an invariant say
that all paths in the view is mutable path, then there must be no
mutable path whose views are greater than some immutable path? *)
Definition fp_graph_views_inv (fpg: fp_graph) : Prop :=
  forall ph1 ph2 tgt vs1 vs2,
    ph1 <> ph2 ->
    (* How to distinguish mutable and immutable path? *)
    get_owner_path_map ph1 fpg = OK (tgt, vs1) ->
    get_owner_path_map ph2 fpg = OK (tgt, vs2) ->
    views_order fpg ph1 ph2 vs1 vs2.

    (* (** In fact, there is no need to compare the views between two *)
    (* immutable path because they cannot affect each other.  *) *)
    (* (incl vs1 vs2 \/ incl vs2 vs1) *)
    (* (* If they are equivalent, then two paths must be immutable path. *)
    (* we create some immutable reference from a mutable path whose *)
    (* weight is in the middle, then the views of this path are not *)
    (* equivalent to the views of other immutable reference. But it is *)
    (* still be included in the views of other immutable reference? *) *)
    (* /\ (list_equiv vs1 vs2 -> *)
    (*    (mutable_path ph1 fpg = OK false /\ mutable_path ph2 fpg = OK false)). *)


(* Record alias_graph_views_inv (fpg: fp_graph) (ph: path) (vs: views) (tgt: path) : Prop := *)
(*   { alias_graph_views_precise: forall ph1, *)
(*       In ph1 vs -> *)
(*       exists vs1,  *)
(*         get_owner_path_map ph1 fpg = OK (tgt, vs1) *)
(*         /\ mutable_path ph1 fpg = OK true; *)
    
(*     alias_graph_views_owner: In tgt vs; *)

(*     (* all dominators path is included in vs *) *)
(*     (** It is not correct because ph may also reach tgt via the same *)
(*     dominators but ph1 may be created by reborrowing ph *) *)
(*     (* alias_graph_views_adequate: forall ph1, *) *)
(*     (*   reachable_from_dominators fpg ph1 tgt -> *) *)
(*     (*   mutable_path ph1 fpg = OK true -> *) *)
(*     (*   In ph1 vs; *) *)

(*     (* It actually requires two kinds of stack discipline: if ph is a *)
(*     mutable path, then there may be some paths that are on top of it, *)
(*     i.e., ph is included in its view. But if ph is an immutable path, *)
(*     we may need to say that all the mutable path to the same location *)
(*     is included in the views of ph? In fact, we can prove [~ In ph *)
(*     vs1] because all the path in the view must be mutable path using *)
(*     the borrow_check_views_inv. As a result, we can use the stack *)
(*     discipline of ph1 to prove that In ph1 vs which is a contradiction *)
(*     with ~In ph1 vs. *) *)
(*     alias_graph_views_stack_discipline: forall ph1 vs1, *)
(*       get_owner_path_map ph1 fpg = OK (tgt, vs1) -> *)
(*       mutable_path ph1 fpg = OK true -> *)
(*       ~ In ph1 vs -> *)
(*       In ph vs1;                (* If [ph] is a temporary path, then *)
(*       it cannot be in [vs1], which means that [ph1] must be in [vs], *)
(*       i.e., all the paths reachable to tgt is included in the views *)
(*       [vs] of [ph] *) *)

(*  }. *)

(* Definition borrow_check_views_inv (fpg: fp_graph) : Prop := *)
(*   forall ph tgt vs, *)
(*     get_owner_path_map ph fpg = OK (tgt, vs) -> *)
(*     (* It is ok that this path we consider is not a mutable path *) *)
(*     (* mutable_path ph fpg = OK true -> *) *)
(*     alias_graph_views_inv fpg ph vs tgt. *)

(** There are two invariants need to hold at each reference. The first
is that location stored in fp_ref is equal to the address of its
point-to owner path. The second is that the views stored in each
reference must contain all the paths which reach to the point-to
target via a dominator path. *)

Section FPM_ENV.

Variable fpm: fp_map.

(* We define a new field_offset which returns the starting offset of a
field that does not consider the alignment. *)

Inductive fp_ref_loc_wf_field (P: footprint -> Prop): ffpty -> Prop :=
| fp_ref_loc_wf_field_intro: forall fid base fofs ffp
    (WF_FIELD: P ffp),
    fp_ref_loc_wf_field P (fid, ((base, fofs), ffp)).

Inductive fp_ref_obj_exposed_wf (P: footprint -> Prop): (ident * (block * Z * type * footprint)) -> Prop :=
| fp_ref_obj_exposed_wf_intro: forall fid b lo ty ffp
    (WTFP: P ffp),
    fp_ref_obj_exposed_wf P (fid, ((b, lo), ty, ffp)).

Inductive fp_ref_loc_wf : footprint -> Prop :=
| fp_uninit_wf sz al: fp_ref_loc_wf (fp_uninit sz al)
| fp_scalar_wf chunk v: fp_ref_loc_wf (fp_scalar chunk v)
| fp_struct_wf: forall id fpl
    (MATCH: Forall (fp_ref_loc_wf_field fp_ref_loc_wf) fpl),
    fp_ref_loc_wf (fp_struct id fpl)        
| fp_enum_wf: forall id ffp fid fofs tag
    (WF: fp_ref_loc_wf ffp),
    fp_ref_loc_wf (fp_enum id tag fid fofs ffp)
| fp_ref_some_wf: forall ph b ofs fp vs mut 
    (* Reference consistency property *)
    (GLOC: get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp))
    (*TODO: there should be also an invariant about fp which says that fp is fully init, but it is unclear whether we should put it here. *)
    (* It is OK to just say that the views are adequate in fpm instead
    of fp_graph which contains the temporary value, because there
    cannot be some reference point to this temporary value which could
    break the adequate invariant after setting some temporary value to
    a path. *)
    (* This adequate property may be redundant for temporary value
    since the fp_ref_views_inv is stronger than this adequacy. But
    this proeprty is required for the reference inside the fp_map.  *)
    (ADEQUATE: fp_ref_views_adequate fpm ph vs)
    (PRECISE: fp_ref_views_precise fpm ph vs)
    (** TODO: we need to show that all path in vs are valid in fpm *),
    fp_ref_loc_wf (fp_ref mut b ofs (Some ph) vs)
| fp_ref_none_wf: forall b ofs vs mut,
    fp_ref_loc_wf (fp_ref mut b ofs None vs)
| fp_object_wf: forall id obj exposed
     (WF: Forall (fp_ref_obj_exposed_wf fp_ref_loc_wf) exposed),
    fp_ref_loc_wf (fp_object id obj exposed).

Definition fp_ref_loc_wf_list fpl :=
  Forall fp_ref_loc_wf fpl.

End FPM_ENV.

Definition fp_ref_loc_wf_fpm (fpm: fp_map) : Prop :=
  forall id b ofs r ty fp,
    fpm ! id = Some (b, ofs, r, ty, fp) ->
    fp_ref_loc_wf fpm fp.


(* Definition fpg_ref_type_inv ce (fpg: fp_graph) : Prop := *)
(*   forall ph1 ph2 vs2 ty1, *)
(*     get_owner_path_map ph1 fpg = OK (ph2, vs2) -> *)
(*     wt_path ce (fpg_to_tenv fpg) ph1 = OK ty1 -> *)
(*     exists ty2, wt_path ce (fpg_to_tenv fpg) ph2 = OK ty2 /\ type_eq_except_origins ty1 ty2 = true. *)


(* If a reference is live, then its value is the same as the location
of the owner it points to. We use fpg to represent the footprint map
with the temporary variables storing the temporary value evaluated by
the expression and fpm to compute the address.  *)
(* Definition fpm_ref_loc_inv (fpg: fp_graph) (fpm: fp_map) : Prop := *)
(*   forall ph1 ph2 b ofs mut vs, *)
(*     @get_owner_footprint_map ame ph1 fpg = OK (fp_ref mut b ofs (Some ph2) vs) -> *)
(*     exists fp, get_owner_loc_footprint_map ph2 fpm = OK (b, ofs, fp). *)


(* The invariant established and preserved by the borrow checking *)
Record borrow_check_inv (fpm: fp_map) : Prop :=
  { borrowck_views_inv: fp_graph_views_inv (fpm_to_fpg fpm);
    (** One alternative is to encode the location invariant of fp_ref
    into views invariant: for all reachable path, if we can compute
    its reached memory location, then this location must be equal to
    the owner location? One (big) problem is that get_owner_path is
    defined on fp_graph instead of fp_map, we cannot compute the
    target location of arbitary path? *)
    borrowck_fp_ref_loc_inv: fp_ref_loc_wf_fpm fpm; }.


(* Useful in the proof to store the evaluated value in a fresh temp *)
Definition fresh_PTree_ident {A: Type} (m: PTree.t A) : ident :=
  let names := map fst (PTree.elements m) in
  Pos.succ (Mem.find_max_pos names).

Definition fresh_PTree_idents {A: Type} (m: PTree.t A) (n: nat) : list ident :=
  let fresh_id := fresh_PTree_ident m in
  npos n fresh_id.

(* We need to establish invariant for some intermediate state which
contains some computed values (e.g., creating a reference) *)
Record borrow_check_inv_snapshot (fpm: fp_map) (fpg: fp_graph) (fpl: list footprint) : Prop :=
  { borrowck_views_inv_snapshot: fp_graph_views_inv fpg;
    borrowck_fp_ref_loc_inv_snapshot: fp_ref_loc_wf_fpm fpm;
    borrowck_fpl_wf: fp_ref_loc_wf_list fpm fpl}.

Definition borrow_check_fpm_vals_inv (fpm: fp_map) (vl: list footprint) : Prop :=
  let idl := fresh_PTree_idents fpm (length vl) in
  let fpg1 := PTree_Properties.of_list ((PTree.elements (fpm_to_fpg fpm)) ++ (combine idl vl)) in
  borrow_check_inv_snapshot fpm fpg1 vl.

Lemma borrow_check_fpg_vals_inv_empty: forall fpm,
    borrow_check_fpm_vals_inv fpm nil ->
    borrow_check_inv fpm.
Admitted.

(** ** Typing of the footprint: used to make sure the footprint is well-formed *)

Definition fpm_to_tenv (fpm: fp_map) : typenv :=
  PTree.map1 (fun '(b, ofs, r, ty, fp) => ty) fpm.

Section COMP_ENV.

Variable ce: composite_env.
Variable te: typenv.
(** Move it to Rusttypes.v  *)

(* We define a new field_offset which returns the starting offset of a
field that does not consider the alignment. *)


Inductive fp_match_field (co: composite) (P: type -> footprint -> Prop): ffpty -> member -> Prop :=
| fp_match_field_intro: forall fid base fofs ffp fty
    (FOFS: field_noalign_offset ce fid (co_members co) = OK (base, fofs))
    (WTFP: P fty ffp),
    fp_match_field co P (fid, ((base, fofs), ffp)) (Member_plain fid fty).

Inductive obj_exposed_wf (P: type -> footprint -> Prop): (ident * (block * Z * Z * type)) -> (ident * (block * Z * type * footprint)) -> Prop :=
| obj_exposed_wf_intro: forall fid b lo ty ffp
    (WTFP: P ty ffp),
    obj_exposed_wf P (fid, (b, lo, lo + sizeof ce ty, ty)) (fid, ((b, lo), ty, ffp)).


(* Definition of wt_footprint (well-typed footprint). Intuitively, it
says that the footprint is an abstract form of the syntactic type. *)
Inductive wt_footprint : type -> footprint -> Prop :=
(* fp_emp can only appear when we pass inout parameters to the
callee. In a well-formed footprint/fp_map, it should not appear. *)
(* | wt_fp_emp: forall ty, *)
(*     wt_footprint ty fp_emp *)
| wt_fp_uninit: forall ty
    (* It means that the location with this type is not initialized or
        this location is scalar type. We require that [ty] is not
        structure because we do not want to dynamically unpack the
        struct when setting footprint (e.g., by set_loc_footprint) to
        some field of this struct. But to ensure this properties, we
        need to carefully set fp_emp to place with structure type. *)
    (WF: forall orgs id, ty <> Tstruct orgs id),
    wt_footprint ty (fp_uninit (sizeof ce ty) (alignof ce ty))
| wt_fp_scalar: forall ty v chunk
    (WF: scalar_type ty = true)
    (MODE: access_mode ty = Ctypes.By_value chunk),
    wt_footprint ty (fp_scalar chunk v)
| wt_fp_struct: forall orgs id fpl co
    (CO: ce ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (MATCH: Forall2 (fp_match_field co wt_footprint) fpl (co_members co))
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
    wt_footprint (Tbox ty) (fp_box b fp)
(* | wt_fp_ref_some: forall ty b ofs ph org mut vs fp pty *)
(*     (** [ty] is equal to the type in [ph] *) *)
(*     (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK pty) *)
(*     (TYEQ: type_eq_except_origins ty pty = true) *)
(*     (** The memory location stored in this reference is equal to the *)
(*     location of [ph] *) *)
(*     (LOCEQ: get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp)),     *)
(*     wt_footprint (Treference org mut ty) (fp_ref mut b ofs (Some ph) vs) *)
| wt_fp_ref_some: forall ty b ofs org mut vs ph pty
    (WTPH: wt_path ce te ph = OK pty)
    (TYEQ: type_eq_except_origins ty pty = true),
    wt_footprint (Treference org mut ty) (fp_ref mut b ofs (Some ph) vs)
| wt_fp_ref_none: forall ty b ofs org mut vs,
    wt_footprint (Treference org mut ty) (fp_ref mut b ofs None vs)
| wt_fp_object: forall id obj exposed
    (WF: Forall2 (obj_exposed_wf wt_footprint) (mem_exposed_borrow (ame id) obj) exposed)
    (* The object always satisfies the representation invariant (this
    invariant should not depend on the properties of borrowable
    subparts) *)
    (REPR_INV: repr_inv (ame id) obj),
    wt_footprint (Tadt id) (fp_object id obj exposed)
.

Definition wt_footprint_list tyl fpl :=
  list_forall2 wt_footprint tyl fpl.

End COMP_ENV.

Definition wt_fpm ce (fpm: fp_map) : Prop :=
  forall id b ofs r ty fp,
    fpm ! id = Some (b, ofs, r, ty, fp) ->
    wt_footprint ce (fpm_to_tenv fpm) ty fp.


(** Properties of get/set footprint map  *)
Lemma get_owner_loc_footprint_map_wt ce: forall phl id fpm b ofs fp,
    get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, fp) ->
    wt_fpm ce fpm ->
    exists ty, wt_path ce (fpm_to_tenv fpm) (id, phl) = OK ty
          /\ wt_footprint ce (fpm_to_tenv fpm) ty fp
          /\ (alignof ce ty | ofs).
Admitted.

Lemma get_owner_loc_footprint_map_fp_ref_wf: forall phl id fpm b ofs fp,
    get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, fp) ->
    fp_ref_loc_wf_fpm fpm ->
    fp_ref_loc_wf fpm fp.
Admitted.


Lemma get_owner_path_map_inv: forall id phl (fpg: fp_graph) ph vs,
    get_owner_path_map (id, phl) fpg = OK (ph, vs) ->
    exists (fp: footprint),
      fpg ! id = Some fp
      /\ get_owner_path fpg (id, nil) phl fp nil = OK (ph, vs).
Admitted.

(* If a path can be reached via (phl1 ++ phl2) then this reachable
path can be divided into two parts: one is reached from phl1 and one
is reach from phl2 *)
Lemma get_owner_path_app_inv: forall phl1 phl2 ph1 ph3 sv1 vs1 vs3 (fpm: fp_map),
    get_owner_path fpm ph1 (phl1 ++ phl2) sv1 vs1 = OK (ph3, vs3) ->
    exists ph2 vs2 sv2,
      get_owner_path fpm ph1 phl1 sv1 vs1 = OK (ph2, vs2) 
      /\ get_owner_footprint_map ph2 fpm = OK sv2 
      /\ get_owner_path fpm ph2 phl2 sv2 vs2 = OK (ph3, vs3).
Admitted.

Lemma get_owner_path_for_owner: forall (fpm: fp_map) ph fp,
    get_owner_footprint_map ph fpm = OK fp ->
    (* Since ph is an owner path, vs must only contain [ph] itself *)
    get_owner_path_map ph fpm = OK (ph, ph :: nil).
Admitted.

Lemma get_owner_loc_footprint_map_eq: forall (fpm: fp_map) ph b ofs fp,
    get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp) ->
    get_owner_footprint_map ph fpm = OK fp.
Admitted.

Lemma get_owner_loc_footprint_map_app: forall id phl1 phl2 b1 ofs1 fp1 b2 ofs2 fp2 (fpm: fp_map),
    get_owner_loc_footprint_map (id, phl1) fpm = OK (b1, ofs1, fp1) ->
    get_owner_loc_footprint phl2 fp1 b1 ofs1 = OK (b2, ofs2, fp2) ->         
    get_owner_loc_footprint_map (id, phl1 ++ phl2) fpm = OK (b2, ofs2, fp2).
Admitted.

(** Misc for invalidate_conflict_ref and kill_paths *)

Lemma get_owner_loc_footprint_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ak am b ofs fp,
    get_owner_loc_footprint_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK (b, ofs, fp) ->
    exists fp', get_owner_loc_footprint_map ph1 fpm = OK (b, ofs, fp')
           /\ invalidate_conflict_ref ph2 ak am fp' = fp.
Admitted.

Lemma get_owner_path_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ak am ph vs,
    get_owner_path_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK (ph, vs) ->
    get_owner_path_map ph1 fpm = OK (ph, vs).
Admitted.


(** Proof of the preservation of borrow check invariant *)

Section BORROWCK_INV.

Variable prog: program.
Hypothesis WTPROG: wt_program prog.
(* Variable w: rs_own_world. *)
Variable se: Genv.symtbl.
Variable sg: rust_signature.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
(* Let L := semantics prog se. *)
Let ge := globalenv se prog.
(* composite environment *)
Let ce := ge.(genv_cenv).

Let wt_state := @wt_state ame prog se sg.

Inductive borrowck_inv_cont: cont -> Prop :=
| borrowck_inv_cont_Kstop: borrowck_inv_cont Kstop
| borrowck_inv_cont_Kseq: forall s k
    (CONT: borrowck_inv_cont k),
    borrowck_inv_cont (Kseq s k)
| borrowck_inv_cont_Kloop: forall s k
    (CONT: borrowck_inv_cont k),
    borrowck_inv_cont (Kloop s k)
| borrowck_inv_cont_Kcall: forall k fpm inout_paths substs p f
    (CONT: borrowck_inv_cont k)
    (* We may require some invariant about that all views in
    inout_paths must cover all reachable path of the inout_path in
    fpm?  *)
    (BOR_INV: borrow_check_inv fpm),
    borrowck_inv_cont (Kcall p f inout_paths substs fpm k).


Inductive borrowck_inv : state -> Prop :=
| borrowck_inv_regular_states: forall f s k substs fpm sup
    (BOR_INV: borrow_check_inv fpm)
    (CONT: borrowck_inv_cont k),
    borrowck_inv (State f s k substs fpm sup)
| borrowck_inv_callstates: forall fid fpl inout_fpm sup k fd orgs org_rels tyargs tyres cconv
    (FINDF: ge.(genv_defmap) ! fid = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (BOR_INV: borrow_check_fpm_vals_inv inout_fpm fpl)
    (CONT: borrowck_inv_cont k),
    (* (WTFP: list_forall2 (wt_footprint ce (fpm_to_tenv inout_fpm)) (type_list_of_typelist tyargs) fpl), *)
    borrowck_inv (Callstate fid fpl inout_fpm sup k)
| borrowck_inv_returnstates: forall rfp inout_fpm sup k rety
    (* The regions in the return type computed from cont are different
    from those in rety but it is not related to proving the invariant
    preservation. It is only related to proving the
    over-approximation? *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = rety)
    (* (WTFP: wt_footprint ce (fpm_to_tenv inout_fpm) rety rfp) *)
    (BOR_INV: borrow_check_fpm_vals_inv inout_fpm [rfp])
    (CONT: borrowck_inv_cont k),
    borrowck_inv (Returnstate rfp inout_fpm sup k).

Ltac unfold_eval_assign :=
  match goal with
  | [H : context G [eval_assign] |- _ ] =>
      unfold eval_assign in H; monadInv H;
      match goal with
      | [H1 : context G [before_write_place _ _ _ = OK (?a, ?b)] |- _ ] =>
          destruct a as ((?tgt_id & ?tgt_phl) & ?vs)
      end
  end.

Ltac unfold_before_write_place :=
  match goal with
  | [H : context G [before_write_place] |- _ ] =>
      unfold before_write_place in H; monadInv H;
      match goal with
      | [H1 : context G [check_path_is_dropped _ _ = OK ?b],
            H2: context [(if ?b then _ else _) = OK _]    
         |- _ ] =>              
          destruct b; try monadInv H2
      end
  end.

(** The smallest operations that preserve the borrow check invariant  *)

Definition invalidate_conflict_ref_fpg (ph: path) (ak: access_kind) (am : access_mode_bor) (fpg: fp_graph) : fp_graph :=
  PTree.map1 (invalidate_conflict_ref ph ak am) fpg.


(* Definition dummy_origin : ident := 1%positive. *)

Definition access_kind_to_mut (ak: access_kind) : mutkind :=
  match ak with
  | AWrite => Mutable
  | ARead => Immutable
  end.

Coercion access_kind_to_mut : access_kind >-> mutkind.

(* Thinking of its sufficiency to prove the borrow check invariant:
the key point is to prove the stack discipline in the invariant. I
think the two premises about the reachability in the borrow check
invariant and the stack discipline field can be applied to this
lemma? *)
Lemma invalidate_conflict_ref_fpm_views_largest: forall phl1 id1 ak am (fpg1 fpg2: fp_graph)
  (* Should we ensure that the mutability of (id1, phl1) (id2, phl2)
  match the access kind? How to dynamically check that all the deep
  path of (id1, phl1) is mutable? Maybe we do not need to check that
  because we do not actually use this path to do something, we just
  check the views of this path. When the path is immutable but the
  access is write, the views are still computed to be mutable paths
  (by the definition of get_owner_path) *)
  (* Note: Do we need other invariants to prove this lemma, such as
  precision? I think we need the precision property? Because when we
  accumulate the view, we should ensure that it can actually reaches
  the target location we want otherwise the set of views are not
  comparable! But in fact, the stack property before invalidation
  can give us this guarantee? Because when these two path can reach
  a target in fpg2 then they must reach the same target with the
  same views at fpg1. Then we can apply the stack property of
  fpg1. The remaining thing is to prove that vs3 includes vs2 is
  impossible? How? We can show that all the path in vs3 is not
  relevant to the path in vs2 (or more specifically, (id2,phl2))?
  The key part here is how to show that when accumulating the path
  from traversing (id3, phl3), the irrelevant relation between the
  path is maintained? I think it is correct because when some path
  is already irrelevant to (id2, phl2) then if we append some
  projection on it, it must be also irrelevant to (id2, phl2). There
  is still a problem, we use (id1, phl1) to do the invalidation so
  how to argue that vs3 has no relevant path of (id2, phl2)? We just
  know that vs3 has no relevant path of (id1, phl1). We can prove
  that (id2, phl2) is relevant to (id1, phl1) (remember that we are
  accessing (id1, phl1), so when it is shallow access, (id2, phl2)
  is prefix of (id1,phl1)) and the path in vs3 is not relevant to
  (id1,phl1), then this path must be not relevant to (id2, phl2). *)
  (VIEWS_INV: fp_graph_views_inv fpg1)
  (** TODO: define the spec of invalidae_conflict_ref_fpg for fpg2
  instead of mentioning fpg1 here *)
  (INVALID: fpg2 = invalidate_conflict_ref_fpg (id1, phl1) ak am fpg1)
  phl2 id2 phl3 id3 vs2 vs3 tgt 
  (* We want to say that the views of (id2, phl2) are the largest
  view to its location *)
  (CONFLICT: relevant_path (id1, phl1) am (id2, phl2) = true)
  (* Any two paths which reach the same target loaction, the views
  of (id2, phl2) must include the views of the other *)
  (BEFORE: get_owner_path_map (id2, phl2) fpg2 = OK (tgt, vs2))
  (AFTER: get_owner_path_map (id3, phl3) fpg2 = OK (tgt, vs3))
  (PH_NEQ: (id2, phl2) <> (id3, phl3)),
    match ak with
    | AWrite =>
        (* Should we also prove that (id3, phl3) must be a mutable path? *)
        incl vs3 vs2 /\ ~ list_equiv vs2 vs3
    | ARead =>
        (mutable_path (id3, phl3) fpg2 = OK true -> incl vs3 vs2)
        (* If (id3, phl3) is not a mutable path, we do not know the
        relation between vs2 and vs3 but we must ensure that that
        are comparable. Is it necessary to compare the views between
        immutable path? Because there is not way to invalidate other
        views by immutable access (But this should be ensured by the
        compatibility between access_kind and the mutablibity of the
        access path?) *)
        (* /\ (incl vs3 vs2 \/ incl vs2 vs3) *)
    end.
Admitted.


(* Deep access of a path, which creates a temporary reference. This
reference can be seen as a normal reference, or it can be used to
extract the point-to footprint to act as a move operation. The
access_kind is irrelevant because we need to prove that the views of
all reachable path from this accessed path cover all the mutable
path. *)
Lemma borrow_check_inv_deep_access: forall phl id (fpm1 fpm2: fp_map) fpl vs tgt b ofs fp ak
    (BOR_INV: borrow_check_fpm_vals_inv fpm1 fpl)
    (* wt_fpm ce fpm1 -> *)
    (* wt_footprint_list ce fpm1 tyl fpl -> *)
    (* wt_path ce (fpm_to_tenv fpm1) (id, phl) = OK ty -> *)
    (REACH: get_owner_path_map (id, phl) fpm1 = OK (tgt, vs))
    (GET: get_owner_loc_footprint_map tgt fpm1 = OK (b, ofs, fp))
    (* Maybe we need to show that the mutability of (id,phl) is
    compatible with ak *)
    (INVALID: fpm2 = invalidate_conflict_ref_fpm (id, phl) ak Adeep fpm1),
    (** We also need to invalidate fpl because some reference in fpl
    may be created by deeply accessing (id,phl)! This scenario is
    ruled out by the static borrow checking! *)
    borrow_check_fpm_vals_inv fpm2 ((fp_ref ak b ofs (Some tgt) vs) :: (map (invalidate_conflict_ref (id, phl) ak BorrowCheckDomain.Adeep) fpl)).
    (* /\ wt_footprint_list ce fpm2 ((Treference dummy_origin mut ty) :: tyl) ((fp_ref mut b ofs (Some tgt) vs) :: fpl) *)
    (* /\ wt_fpm ce fpm2. *)
Proof.
  intros. 
  (* We need to ignore how to prove the properties of using arbitary
  fresh idents for temporary footprints. We reduce the proof to the
  form that all the idents of fpl are the same as the ids after
  inserting the new fp_ref. *)
  (* We need to show that if we perform invalidation directly on the
  fp_graph, the result is the same? *)
  (* Therefore, we can prove it using following steps: (1) we prove
  the properties derived from the deep access (i.e., all reachable
  path of this deeply accessed path have views that contain the views
  of all the reachable path to the same location); (2) we prove that
  with the above properties, we can extract this deep access path to a
  new temporary value. *)
  (* 1. The invariant is preserved by the invalidation process  *)
  assert (BOR_INV1: borrow_check_fpm_vals_inv fpm2 (map (invalidate_conflict_ref (id, phl) ak Adeep) fpl)) by admit.
  inv BOR_INV.
  set (fpg1 := ((PTree_Properties.of_list
                  (PTree.elements (fpm_to_fpg fpm1) ++
                     combine (fresh_PTree_idents fpm1 (Datatypes.length fpl)) fpl)))) in *.  
  inv BOR_INV1.
  set (fpm2 := (invalidate_conflict_ref_fpm 
                  (id, phl) ak Adeep fpm1)) in *.
  set (fpl2 := (map
                  (invalidate_conflict_ref 
                     (id, phl) ak Adeep) fpl)) in *.
  set (fpg2 := ((PTree_Properties.of_list
                  (PTree.elements (fpm_to_fpg fpm2) ++
                     combine (fresh_PTree_idents fpm2 (Datatypes.length fpl2)) fpl2)))) in *.
  assert (FPG2: fpg2 = invalidate_conflict_ref_fpg (id, phl) ak Adeep fpg1) by admit.
  (* 2. apply invalidate_conflict_ref_fpm_views_largest to show the
  property of [vs] *)
  generalize (invalidate_conflict_ref_fpm_views_largest phl id ak Adeep fpg1 fpg2 borrowck_views_inv_snapshot0 FPG2).
  intros VS_TOP.
  econstructor.
  (* For now, ignore how to chose the new id *)
  set (fresh_id := fresh_PTree_ident fpg2).
  replace ((PTree_Properties.of_list
       (PTree.elements (fpm_to_fpg fpm2) ++
        combine
          (fresh_PTree_idents fpm2
             (Datatypes.length (fp_ref ak b ofs (Some tgt) vs :: fpl2)))
          (fp_ref ak b ofs (Some tgt) vs :: fpl2)))) with (PTree.set fresh_id (fp_ref ak b ofs (Some tgt) vs) fpg2) by admit.
  red.
  (* Note: By case analysis, if both ph1 and ph2 do not include
  fresh_id, then we use the invariant for fpg2; if ph1 or ph2 includes
  fresh_id, then we use the property of
  invalidate_conflict_ref_fpm_views_largest; if both ph1 and ph2
  include fresh_id, then we may use the stack invariant in fpg2 to
  show that the views created from traversing tgt to the tgt0 have
  linear order.*)
  admit.
  admit.
  admit.
Admitted.

(* Move out the footprint pointed by the fp_ref in the temporary
values and then use this footprint to replace the fp_ref to simulate
the move operation.  *)
(* Note: Do case analysis. When two paths do not go through the
temporary reference, then we use the invariant of fpm1; when one of
them goes through this reference, the view of the path that does not
go through this reference must be the same as that before moving, so
we can construct a path in fpm1 that goes through the reference and
use the invariant of fpm1; when both two path go through the moved out
footprint, then we just construct their original path in fpm1 with the
reference. *)
Lemma borrow_check_inv_replace_move: forall (fpm1 fpm2: fp_map) fpl tgt b ofs fp,
    borrow_check_fpm_vals_inv fpm1 ((fp_ref Mutable b ofs (Some tgt) [tgt]) :: fpl) ->
    (* wt_fpm ce fpm1 -> *)
    (* wt_footprint_list ce fpm1 ((Treference r Mutable ty) :: tyl) ((fp_ref Mutable b ofs (Some tgt) vs) :: fpl) -> *)
    get_owner_loc_footprint_map tgt fpm1 = OK (b, ofs, fp) ->
    clear_footprint_map ce tgt fpm1 = OK fpm2 ->
    borrow_check_fpm_vals_inv fpm2 (fp :: fpl).
    (* /\ wt_footprint_list ce fpm2 (ty :: tyl) (fp :: fpl) *)
    (* /\ wt_fpm ce fpm2. *)
Admitted.

(* The borrow check invariant preserves when we drop any of the
temporary footprint value. *)
Lemma borrow_check_inv_drop: forall n (fpm: fp_map) fpl,
    borrow_check_fpm_vals_inv fpm fpl ->
    (* wt_fpm ce fpm -> *)
    (* wt_footprint_list ce fpm tyl fpl -> *)
    borrow_check_fpm_vals_inv fpm (list_delete n fpl).
    (* /\ wt_footprint_list ce fpm (list_delete n tyl) (list_delete n fpl) *)
    (* /\ wt_fpm ce fpm. *)
Admitted.

(* Moving out a footprint: proved by borrow_check_inv_deep_access and
borrow_check_inv_replace_move *)
Lemma borrow_check_inv_move: forall (fpm1 fpm2 fpm3: fp_map) fpl tgt b ofs fp,
    borrow_check_fpm_vals_inv fpm1 fpl ->
    (* wt_fpm ce fpm1 -> *)
    (* wt_footprint_list ce fpm1 tyl fpl -> *)
    (* wt_path ce (fpm_to_tenv fpm1) tgt = OK ty -> *)
    (* In a move operastion, we first do deep access (simulate
    creating a reference) and then move out the footprint after the
    invalidation process. But note that in
    borrow_check_inv_deep_access, we first get the owner path and then
    do the invalidation. It does not matter because getting the owner
    path of an owner is irrelevant to the invalidation procee. *)
    fpm2 = invalidate_conflict_ref_fpm tgt AWrite BorrowCheckDomain.Adeep fpm1 ->
    get_owner_loc_footprint_map tgt fpm2 = OK (b, ofs, fp) ->
    clear_footprint_map ce tgt fpm2 = OK fpm3 ->
    borrow_check_fpm_vals_inv fpm3 (fp :: (map (invalidate_conflict_ref tgt AWrite BorrowCheckDomain.Adeep) fpl)).
    (* /\ wt_footprint_list ce fpm3 (ty :: tyl) (fp :: fpl) *)
    (* /\ wt_fpm ce fpm3. *)
Proof.
  intros. subst.
  destruct tgt as (tid & tphl).
  (* The location gotten before invalidation is the same *)
  exploit get_owner_loc_footprint_map_after_invalidate_ref. eauto.
  intros (fp' & A1 & A2).
  exploit get_owner_path_for_owner.
  eapply get_owner_loc_footprint_map_eq. eauto.
  intros GPH.
  exploit borrow_check_inv_deep_access; eauto.
  instantiate (1 := AWrite). 
  intros B1.  
  eapply borrow_check_inv_replace_move; eauto. 
Qed.  


(* Why is it so complicated? When we do shallow write on a path, we
should also simultaneously kill the loans related to this paths and
set the footprint of this path to fp_uninit othewise the invariant may
be broken? Because when we set fp_uninit to some path, we should
either invalidate the path point to the reachable path of this to-set
path or kill the loans related to those reachable path? *)
Lemma borrow_check_inv_shallow_write: forall (fpm1 fpm2 fpm3 fpm4: fp_map) id phl fpl vs tgt,
    borrow_check_fpm_vals_inv fpm1 fpl ->
    (* wt_footprint_list ce fpm1 tyl fpl -> *)
    (* wt_fpm ce fpm1 -> *)
    (** Adhoc: we first do invalidation because we need to match the
    static borrow checking *)
    fpm2 = invalidate_conflict_ref_fpm (id, phl) AWrite BorrowCheckDomain.Ashallow fpm1 ->
    get_owner_path_map (id, phl) fpm2 = OK (tgt, vs) ->
    (* If we do not check this property, then some path may point to
    the descendant of tgt which cannot be invalidated by the shallow
    access *)
    check_path_is_dropped fpm2 tgt = OK true ->    
    (* This clearing operation is used to align with the kill loans operation. *)
    clear_footprint_map ce tgt fpm2 = OK fpm3 ->
    fpm4 = kill_paths_ref_fpm vs fpm3 ->
    borrow_check_fpm_vals_inv fpm4 (map (kill_paths_ref vs) (map (invalidate_conflict_ref (id, phl) AWrite BorrowCheckDomain.Ashallow) fpl)).
    (* /\ wt_footprint_list ce fpm4 tyl (map (kill_paths_ref vs) fpl) *)
    (* /\ wt_fpm ce fpm4. *)
Proof.
  intros. subst.
  unfold borrow_check_fpm_vals_inv in *.
  simpl in *.
  destruct H as [Hviews Hloc Hvals].
  econstructor.
  - admit.
  - admit.
  - admit.
Admitted.

(* We can move the footprint from temporary variables to a path whose
footprint is fp_emp or has been cleared by clear_footprint_map, and
the invariant preserves. *)
Lemma borrow_check_inv_set_fp: forall (fpm1 fpm2: fp_map) fpl tgt fp,
    borrow_check_fpm_vals_inv fpm1 (fp :: fpl) ->
    (* wt_fpm ce fpm1 -> *)
    (* wt_footprint_list ce fpm1 (ty :: tyl) (fp :: fpl) -> *)
    check_path_is_dropped fpm1 tgt = OK true ->
    set_footprint_map tgt fp fpm1 = OK fpm2 ->
    (* wt_path ce (fpm_to_tenv fpm1) tgt = OK ty -> *)
    borrow_check_fpm_vals_inv fpm2 fpl.
    (* /\ wt_footprint_list ce fpm2 tyl fpl *)
    (* /\ wt_fpm ce fpm2. *)
Admitted.

(* moving from a place preserves the borrow checking invariant
under the successful checking. But what is the effect of checking
for pure expr? *)
Lemma eval_expr_preserve_borchk_inv: forall (fpm1 fpm2: fp_map) e vfp
    (INV: borrow_check_inv fpm1)
    (* (WTFPM: wt_fpm ce fpm1) *)
    (* (WTEXPR: wt_expr (fpm_to_env fpm1) ce e) *)
    (EVAL: eval_expr ce fpm1 e = OK (vfp, fpm2)),
    borrow_check_fpm_vals_inv fpm2 [vfp].
    (* /\ wt_fpm ce fpm2 *)
    (* /\ wt_footprint ce fpm2 (typeof e) vfp. *)
Proof.
  destruct e; intros.
  (* moveplace *)
  - simpl in EVAL.
    monadInv EVAL. destruct x as (b & ofs).
    (* inv WTEXPR.  *)
Admitted.

(** Misc (TODO: we should categorize these lemmas to structure the
proof better) *)

Lemma clear_footprint_map_is_dropped: forall phl id (fpm1 fpm2: fp_map),
    clear_footprint_map ce (id, phl) fpm1 = OK fpm2 ->
    check_path_is_dropped fpm2 (id, phl) = OK true.
Admitted.

Lemma kill_paths_ref_fpm_preserve_is_dropped: forall phl id (fpm: fp_map) vs,
    check_path_is_dropped fpm (id, phl) = OK true ->
    check_path_is_dropped (kill_paths_ref_fpm vs fpm) (id, phl) = OK true.
Admitted.


(* step preservation *)

(* It is not very usefule because we need to prove the preservation of
borrowck_inv in the simulation proof between RustIRspec and
RustIRown *)

(* Lemma step_preservation: forall s1 t s2, *)
(*     RustIRspec.step ge s1 t s2 -> *)
(*     borrowck_inv s1 -> *)
(*     wt_state s1 -> *)
(*     borrowck_inv s2 /\ wt_state s2. *)
(* Proof. *)
(*   intros s1 t s2 STEP INV WTST.  *)
(*   exploit (@wt_state_step_preservation ame); eauto. intros WTST1. *)
(*   split; auto. *)
(*   inv STEP; inv INV; inv WTST. *)
(*   (* Sassign *) *)
(*   - inv WT1. *)
(*     unfold_eval_assign. inv EQ2. *)
(*     unfold_before_write_place.       *)
(*     destr_path_of_place p. *)
(*     (* evaluate expr preserves borrow check invariant. We should write *)
(*     it in a separated lemma *) *)
(*     exploit eval_expr_preserve_borchk_inv; eauto. *)
(*     intros (BORCK_INV1 & WTFPM1 & WTFP1). *)
(*     (* shallow write preserves borrow check invariant *) *)
(*     exploit borrow_check_inv_shallow_write; eauto. *)
(*     econstructor. eauto. econstructor. *)
(*     intros (BORCK_INV2 & WTFP2 & WTFPM2). *)
(*     (* set footprint to the assginee preserves the invariant *) *)
(*     (* assert (WTPH1: wt_path *) *)
(*     exploit borrow_check_inv_set_fp; eauto. *)
(*     eapply kill_paths_ref_fpm_preserve_is_dropped. *)
(*     eapply clear_footprint_map_is_dropped; eauto.     *)
(*     admit.  (* We cannot prove that the type of the tgt path is *)
(*     (typeof e) but we can prove that its type is equal to (typeof e) *)
(*     modulo the regions. *) *)
(*     intros (BORCK_INV3 & WTFP3 & WTFPM3). *)
(*     econstructor; eauto. *)
(* Admitted. *)
   

End BORROWCK_INV.

End ADT_ENV.

Global Hint Resolve get_owner_loc_footprint_map_wt
  get_owner_loc_footprint_map_fp_ref_wf
  get_owner_path_map_inv
  get_owner_path_for_owner
  get_owner_loc_footprint_map_eq
  get_owner_loc_footprint_map_app: fpmap.
