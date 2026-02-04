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
Require Import BorrowCheck.
Require Import MoveCheckingFootprint1.
(* Unsupported for now *)
(* Require Import StkBorPermission RustIRbor. *)
Require Import RustIRspec.
Require Import BorrowCheckDomain RegionLiveness.

Import ListNotations.

Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation ae := (fun id => (ame id).(mem_pure_adt)).
Notation sval := (@sval ae).
Notation sv_map := (@sv_map ae).


Section COMP_ENV.

Variable ce: composite_env.

Fixpoint mutable_projections (ty: type) (phl: list projection) : bool :=
  match phl with
  | nil => true
  | ph :: phl1 =>
      match ph with
      | proj_deref => 
          if is_immutable_ref ty then 
            false
          else 
            match type_deref ty with
            | OK ty1 => mutable_projections ty1 phl1
            | _ => false
            end
      | proj_field fid => 
          match type_field ce ty fid with
          | OK ty1 => mutable_projections ty1 phl1
          | _ => false
          end
      | proj_downcast fid => 
          match type_downcast ce ty fid with
          | OK ty1 => mutable_projections ty1 phl1
          | _ => false
          end
      end
  end.


Definition mutable_path (svm: sv_map) (ph: path) : bool :=
  let (id, phl) := ph in
  match svm ! id with
  | Some (_, ty, sv) =>
      mutable_projections ty phl
  | None =>
      false
  end.

End COMP_ENV.

Definition is_live_path (live: RegionSet.t) (te: typenv) (ph: path) : bool :=
  let (id, phl) := ph in
  match te ! id with
  | Some ty =>
      forallb (fun r => RegionSet.mem r live) (origins_of_type ty)
  | None =>
      false
  end.

(* We also need to know that generic region this path locates
at....  *)
Definition extern_loc_region (svm: sv_map) (ph: path) : option origin :=
  let (id, pj) := ph in
  match svm ! id with
  | Some (r, _, _) =>
      r
  | _ => None
  end.

(* [ln] is a prefix of [ph] *)
Definition loan_approx (svm: sv_map) (ln: loan) (ph: path) : Prop :=
  match ln, extern_loc_region svm ph with
  | Lintern _ p, None =>
      (* TODO: maybe we should use path uniformly *)
      let (id1, pj1) := path_of_place p in
      let (id2, pj2) := ph in
      id1 = id2 /\ projections_contain pj1 pj2 = true
  | Lextern org1, Some org2 =>
      org1 = org2 
  | _, _ => False
  end.

(* ph is the location the reference points to *)
Definition alias_graph_approx_loans ce (live: RegionSet.t) (ls: LoanSet.t) (svm: sv_map) (vs: views) (ph: path) : Prop :=
  forall vph vs1,
    In vph vs ->
    is_live_path live (svm_to_tenv svm) vph = true ->
    mutable_path ce svm vph = true ->
    get_owner_path_sv_map vph svm = OK (ph, vs1) ->
    exists ln, 
      LoanSet.In ln ls ->
      loan_approx svm ln vph.


Definition sound_loan_analysis ce (live: RegionSet.t) (le: LOrgEnv.t) (svm: sv_map) : Prop :=
  forall rph ph vs mut ty ls r,
    get_owner_sval_map rph svm = OK (sv_ref mut ph vs) ->
    wt_path ce (svm_to_tenv svm) rph = OK (Treference r mut ty) ->
    LOrgEnv.get r le = Live ls ->
    alias_graph_approx_loans ce live ls svm vs ph.

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

Definition alias_graph_views_sufficient ce (live: RegionSet.t) (svm: sv_map) : Prop :=
  forall rph ph vs mut,
    (* Do we need to say that rph must be live? *)
    get_owner_sval_map rph svm = OK (sv_ref mut ph vs) ->
    (** TODO: The deref of rph must be not in [vs], otherwise we
    cannot prove the premise of not In in the following conclusion. *)    
    forall ph1 vs1,
      get_owner_path_sv_map ph1 svm = OK (ph, vs1) ->
      is_live_path live (svm_to_tenv svm) ph1 = true ->
      mutable_path ce svm ph1 = true ->
      (* The views of ph1, i.e., vs1 does not contain reborrowed path
      of rph *)
      ~ In (append_proj proj_deref rph) vs1 ->
      In ph1 vs.

(** Type invariants: the reference type must be equal to the type it
points to *)

Definition svm_ref_inv ce (live: RegionSet.t) (svm: sv_map) : Prop :=
  forall ph1 ph2 ph3 vs2 vs3 r mut ty1,
    get_owner_path_sv_map ph1 svm = OK (ph2, vs2) ->
    get_owner_sval_map ph2 svm = OK (sv_ref mut ph3 vs3) ->
    is_live_path live (svm_to_tenv svm) ph1 = true ->
    wt_path ce (svm_to_tenv svm) ph1 = OK (Treference r mut ty1) ->
    exists ty2, wt_path ce (svm_to_tenv svm) ph2 = OK ty2 /\ type_eq_except_origins ty1 ty2 = true.


(** Footprint can be seen as a rich form of structured value in
RustIRspec, which contains extra permission information. We can use
[fp_to_sval] to remove this information. *)


(* Translate footprint to structured value *)
Fixpoint fp_to_sval (fp: footprint) : sval :=
  match fp with
  | fp_emp
  | fp_uninit _ _ => sv_bot
  | fp_scalar _ v => sv_scalar v
  | fp_box _ fp1 => sv_box (fp_to_sval fp1)
  | fp_struct id fpl => sv_struct id (map (fun '(fid, (_, ffp)) => (fid, fp_to_sval ffp)) fpl)
  | fp_enum id _ fid _ ffp => sv_enum id fid (fp_to_sval ffp)
  | fp_ref mut _ _ ph vs => sv_ref mut ph vs 
  | fp_object id obj exposed => sv_object id (mem_to_pure_repr (ame id) obj) (map (fun '(fid, (_,
ty, ffp)) => (fid, (ty, fp_to_sval ffp))) exposed)
  end.

Definition fpm_to_svm (fpm: fp_map) : sv_map :=
  PTree.map1 (fun '(_, r, ty, fp) => (r, ty, fp_to_sval fp)) fpm.

(* If a reference is live, then its value is the same as the location
of the owner it points to *)
Definition fpm_ref_inv (live: RegionSet.t) (fpm: fp_map) : Prop :=
  forall ph1 ph2 ph3 b0 ofs0 b ofs mut vs2 vs,
    get_owner_path_sv_map ph1 (fpm_to_svm fpm) = OK (ph2, vs2) ->
    get_owner_loc_footprint_map ph2 fpm = Some (b0, ofs0, fp_ref mut b ofs ph3 vs) ->
    is_live_path live fpm ph1 = true ->
    exists fp, get_owner_loc_footprint_map ph3 fpm = Some (b, ofs, fp).


(* The invariant established and preserved by the borrow checking *)
Record borrow_check_inv ce (live: RegionSet.t) (le: LOrgEnv.t) (svm: sv_map) (fpm: fp_map) : Prop :=
  { borrowck_approximation: sound_loan_analysis ce live le svm;
    borrowck_sufficient_views: alias_graph_views_sufficient ce live svm;
    borrowck_svm_ref_inv: svm_ref_inv ce live svm;
    borrowck_fpm_ref_inv: fpm_ref_inv live fpm; }.

End ADT_ENV.

Coercion fp_to_sval : footprint >-> sval.
Coercion fpm_to_svm : fp_map >-> sv_map.


(* Old version of the borrow check invariant which contains properties about stacked borrow

Definition loan_approx (fpm: fp_map) (l: loan) (ph: path) : Prop :=
  match l, extern_loc_region fpm ph with
  | Lintern _ p, None =>
      (* TODO: use path uniformly *)
      let (id1, pj1) := path_of_place p in
      let (id2, pj2) := ph in
      id1 = id2 /\ projections_contain pj1 pj2 = true
  | Lextern org1, Some org2 =>
      org1 = org2 
  | _, _ => False
  end.


(* ph is the location the stack resides in *)
Inductive borstk_approx_loans ce (live: RegionSet.t) (orgst: LOrgSt.t) (fpm: fp_map) (stk: BorStkPerm.t) (ph: path) (it: BorStkPerm.item) : Prop :=
| borstk_approx_loans_intro: forall stk1 stk2 ls,
    orgst = Live ls ->
    (* The item is in the stack. What about the uniqueness of this item? *)
    (** We should prove that all suffix of stk containing it :: stk2
    also satisfies this property *)
    stk = stk1 ++ it :: stk2 ->
    (* all valid Unique items in stk2 are approximated by ls *)
    (forall b ofs ph1 ph2 fp pj,
        In (BorStkPerm.Unique (b, ofs)) stk2 ->
        (* ph2 is a node in the footprint tree *)
        get_owner_loc_footprint_map ph2 fpm = Some (b, ofs, fp) ->
        (* ph2 is reachable via an arbitary path [ph1] *)
        get_owner_path_map ph1 fpm = Some ph2 ->
        (* We should know how ph2 reaches ph; the projections should
        have the form [proj_deref; proj_field/downcast^*] *)
        get_owner_path fpm ph2 pj fp = Some ph ->
        (* ph1 is mutable *)
        mutable_path ce fpm ph1 = true ->
        (* ph1 is live *)
        is_live_path live fpm ph1 = true ->
        (* The conclusion is that ls contains a loan that is prefix of
        [ph1; proj_deref]. TODO: what if the location of this stk is
        within some fields? *)
        exists ln, 
          LoanSet.In ln ls 
          (* If ph1 is from external locations then ln must be
          Lextern('a) where 'a is the region of this external
          location; otherwise ln is a prefix of ph1. We use
          loan_of_path to compute the loan of this path (imagine that
          it is borrow?) *)
          /\ loan_approx fpm ln ph2) ->
    borstk_approx_loans ce live orgst fpm stk ph it.
  
Local Open Scope map_scope.

Definition stkbor_ref_inv ce (live: RegionSet.t) (le: LOrgEnv.t) (fpm: fp_map) (stk_mem: bor_stacks) :=
  forall ph1 ph2 org mut ty, 
    wt_path ce fpm ph1 = OK (Treference org mut ty) ->
    (* ph1 is a live path *)
    is_live_path live fpm ph1 = true ->
    get_owner_path_map ph1 fpm = Some ph2 ->
    (* The footprint at ph2 is fp_ref *)
    forall rb rofs ph3, 
      get_owner_footprint_map ph2 fpm = Some (fp_ref rb rofs ph3) ->
      forall del,
        0 <= del < sizeof ce ty ->
        exists stk, 
          stk_mem # rb ## (rofs + del) = Some stk
          (** Since path ph2 is live, it must appear in the
              stack at (rb, rofs + del). *)
          /\ borstk_approx_loans ce live (LOrgEnv.get org le) fpm stk ph3 (BorStkPerm.to_item mut (rb,rofs)).


Definition stkbor_box_inv (live: RegionSet.t) (le: LOrgEnv.t) (fpm: fp_map) (stk_mem: bor_stacks) :=
  forall ph b sz fp,
    get_owner_footprint_map ph fpm = Some (fp_box b sz fp) ->
    not_fp_emp fp = true ->
    forall del,
      0 <= del < sz ->
      exists stk, 
        (* The last element of the borrow stack of a heap block must
        be the box pointer itself *)
        stk_mem # b ## del = Some (stk ++ [BorStkPerm.Unique (b,0)]).

(* If a reference is live, then its value is the same as the location
of the owner it points to *)
Definition fpm_ref_inv (live: RegionSet.t) (fpm: fp_map) : Prop :=
  forall ph1 b ofs ph2,
    get_owner_footprint_map ph1 fpm = Some (fp_ref b ofs ph2) ->
    is_live_path live fpm ph1 = true ->
    exists fp, get_owner_loc_footprint_map ph2 fpm = Some (b, ofs, fp). 

(* The invariant established and preserved by the borrow checking *)
Record borrow_check_inv ce (live: RegionSet.t) (le: LOrgEnv.t) (fpm: fp_map) (stk_mem: bor_stacks) : Prop :=
  { borrowck_stkbor_ref: stkbor_ref_inv ce live le fpm stk_mem;
    borrowck_stkbor_box: stkbor_box_inv live le fpm stk_mem;
    borrowck_fpm_ref: fpm_ref_inv live fpm }.

*) 
