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

(* For now, I have no idea how to define a more simpler version of
computing the mutablity of a path. If we add mutablity information
into the path itselt, the tree path in the footprint is not unique
anymore, I don't know if there is any problem there. *)
Definition mutable_path (fpm: fp_map) (ph: path) : bool :=
  let (id, phl) := ph in
  match fpm ! id with
  | Some (_, _, ty, _, _) =>
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
Definition extern_loc_region (fpm: fp_map) (ph: path) : option origin :=
  let (id, pj) := ph in
  match fpm ! id with
  | Some (_, _, _, opt_reg, _) =>
      opt_reg
  | _ => None
  end.

(* ph is the location the reference points to *)
Inductive alias_graph_approx_loans ce (live: RegionSet.t) (orgst: LOrgSt.t) (svm: sv_map) (ph: path) : Prop :=
| alias_graph_approx_loans_intro: forall stk1 stk2 ls,
    orgst = Live ls ->
    (* For safety: all owner paths that have the ability to change the
    semantic typed of the stored value or permission of the location
    that the reference points to should be approximated by (i.e., they
    should appear as loans in the loan set of this region) the borrow
    check result. However, borrow checker checks more properties than
    safety, which is not expressed in this invariant (in order to make
    our proof more simpler and we only care safety for now). For
    example, borrow checker would check the stack discipline of
    multiple mutable borrows, which can be expressed by adding stacked
    borrow model into each owner path. These multiple mutable accesses
    cannot perform "full write" to the locations they point to. They
    can only perfom in-place write which would ensure the
    well-typedness of the new values. *)
    forall phl ph1, 
      dominator_paths ce live svm ph phl ->
      In ph1 phl ->
      
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

(* aliasing invariant which can be defined only on the structured value map *)
Definition borchk_ref_alias_inv ce (live: RegionSet.t) (le: LOrgEnv.t) (svm: sv_map) :=
  forall ph1 ph2 org mut ty, 
    wt_path ce fpm ph1 = OK (Treference org mut ty) ->
    (* ph1 is a live path *)
    is_live_path live fpm ph1 = true ->
    get_owner_path_sv_map ph1 svm = Some ph2 ->
    (* The footprint at ph2 is fp_ref *)
    forall rb rofs ph3, 
      get_owner_sval_map ph2 svm = Some (sv_ref ph3) ->
      alias_graph_approx_loans ce live (LOrgEnv.get org le) svm stk ph3.



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
