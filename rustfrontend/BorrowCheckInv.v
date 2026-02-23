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
Require Import Rustlightown RustIRspec.

Import ListNotations.

Local Open Scope error_monad_scope.

Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
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
    

Record alias_graph_views_inv (fpg: fp_graph) (ph: path) (vs: views) (tgt: path) : Prop :=
  { alias_graph_views_precise: forall ph1,
      In ph1 vs ->
      exists vs1, 
        get_owner_path_map ph1 fpg = OK (tgt, vs1)
        /\ mutable_path ph1 fpg = OK true;
    
    alias_graph_views_owner: In tgt vs;

    (* all dominators path is included in vs *)
    alias_graph_views_adequate: forall ph1,
      reachable_from_dominators fpg ph1 tgt ->
      mutable_path ph1 fpg = OK true ->
      In ph1 vs;

    alias_graph_views_stack_discipline: forall ph1 vs1,
      get_owner_path_map ph1 fpg = OK (tgt, vs1) ->
      mutable_path ph1 fpg = OK true ->
      ~ In ph1 vs ->
      In ph vs1;                (* If [ph] is a temporary path, then
      it cannot be in [vs1], which means that [ph1] must be in [vs],
      i.e., all the paths reachable to tgt is included in the views
      [vs] of [ph] *)

 }.

Definition borrow_check_views_inv (fpg: fp_graph) : Prop :=
  forall ph tgt vs,
    get_owner_path_map ph fpg = OK (tgt, vs) ->
    mutable_path ph fpg = OK true ->
    alias_graph_views_inv fpg ph vs tgt.

(** Type invariants: the reference type must be equal to the type it
points to *)


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
Record borrow_check_inv (fpg: fp_graph) : Prop :=
  { borrowck_views_inv: borrow_check_views_inv fpg; }.
    (* borrowck_fpg_ref_type_inv: fpg_ref_type_inv ce fpm; *)
    (* borrowck_fpm_ref_loc_inv: fpm_ref_loc_inv fpm fpm; }. *)


(* Useful in the proof to store the evaluated value in a fresh temp *)
Definition fresh_PTree_ident {A: Type} (m: PTree.t A) : ident :=
  let names := map fst (PTree.elements m) in
  Pos.succ (Mem.find_max_pos names).

Definition fresh_PTree_idents {A: Type} (m: PTree.t A) (n: nat) : list ident :=
  let fresh_id := fresh_PTree_ident m in
  npos n fresh_id.

Definition borrow_check_fpg_vals_inv (fpg: fp_graph) (vl: list footprint) : Prop :=
  let idl := fresh_PTree_idents fpg (length vl) in
  let fpg1 := PTree_Properties.of_list ((PTree.elements fpg) ++ (combine idl vl)) in
  borrow_check_inv fpg.



(** ** Typing of the footprint: used to make sure the footprint is well-formed *)

Definition fpm_to_tenv (fpm: fp_map) : typenv :=
  PTree.map1 (fun '(b, ofs, r, ty, fp) => ty) fpm.

Section COMP_ENV.

Variable ce: composite_env.
Variable fpm: fp_map.
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
| wt_fp_ref_some: forall ty b ofs ph org mut vs fp pty
    (** [ty] is equal to the type in [ph] *)
    (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK pty)
    (TYEQ: type_eq_except_origins ty pty = true)
    (** The memory location stored in this reference is equal to the
    location of [ph] *)
    (LOCEQ: get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp)),    
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
    wt_footprint ce fpm ty fp.


(** Proof of the preservation of borrow check invariant *)

Section BORROWCK_INV.

Variable prog: program.
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
    (WTFPM: wt_fpm ce fpm)
    (* We may require some invariant about that all views in
    inout_paths must cover all reachable path of the inout_path in
    fpm?  *)
    (BOR_INV: borrow_check_inv fpm),
    borrowck_inv_cont (Kcall p f inout_paths substs fpm k).


Inductive borrowck_inv : state -> Prop :=
| borrowck_inv_regular_states: forall f s k substs fpm sup
    (WTFPM: wt_fpm ce fpm)
    (BOR_INV: borrow_check_inv fpm)
    (CONT: borrowck_inv_cont k),
    borrowck_inv (State f s k substs fpm sup)
| borrowck_inv_callstates: forall fid fpl inout_fpm sup k fd orgs org_rels tyargs tyres cconv
    (FINDF: ge.(genv_defmap) ! fid = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (WTFPM: wt_fpm ce inout_fpm)
    (BOR_INV: borrow_check_fpg_vals_inv inout_fpm fpl)
    (CONT: borrowck_inv_cont k)
    (WTFP: list_forall2 (wt_footprint ce inout_fpm) (type_list_of_typelist tyargs) fpl),
    borrowck_inv (Callstate fid fpl inout_fpm sup k)
| borrowck_inv_returnstates: forall rfp inout_fpm sup k rety
    (* The regions in the return type computed from cont are different
    from those in rety but it is not related to proving the invariant
    preservation. It is only related to proving the
    over-approximation? *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = rety)
    (WTFP: wt_footprint ce inout_fpm rety rfp)
    (WTFPM: wt_fpm ce inout_fpm)
    (BOR_INV: borrow_check_fpg_vals_inv inout_fpm [rfp])
    (CONT: borrowck_inv_cont k),
    borrowck_inv (Returnstate rfp inout_fpm sup k).

(* step preservation *)

Lemma step_preservation: forall s1 t s2,
    RustIRspec.step ge s1 t s2 ->
    borrowck_inv s1 ->
    wt_state s1 ->
    borrowck_inv s2 /\ wt_state s2.
Proof.



End ADT_ENV.
