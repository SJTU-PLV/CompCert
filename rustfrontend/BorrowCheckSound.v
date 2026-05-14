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
Require Import UnionFindDelete.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import RustIRspec.
Require Import Errors.
Require Import Listmisc.
(* move checking *)
Require Import InitDomain InitAnalysis.
Require Import MoveChecking.
(* borrow checking *)
Require Import RegionLiveness BorrowCheckDomain.
Require Import BorrowCheckPolonius BorrowCheck BorrowCheckInv.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope positive_scope.
Local Open Scope Z_scope.

Definition enc_reg (frame: frame_idx) (r: origin) :=
  prod_encode frame r.

Definition append_projs (phl: list projection) (ph: path) :=
  (fst ph, snd ph ++ phl).

(** Move to other files. Properties of wt_path  *)

Lemma wt_projections_append ce: forall phl1 phl2 ty1 ty2 ty3,
    wt_projections ce ty1 phl1 = OK ty2 ->
    wt_projections ce ty2 phl2 = OK ty3 ->
    wt_projections ce ty1 (phl1 ++ phl2) = OK ty3.
Admitted.


Lemma wt_path_append ce: forall ph phl ty1 ty2 te,
    wt_path ce te ph = OK ty1 ->
    wt_projections ce ty1 phl = OK ty2 ->
    wt_path ce te (append_projs phl ph) = OK ty2.
Admitted.

Lemma wt_path_append_inv ce: forall ph phl ty2 te,
    wt_path ce te (append_projs phl ph) = OK ty2 ->
    exists ty1,  wt_path ce te ph = OK ty1 
            /\ wt_projections ce ty1 phl = OK ty2.
Admitted.

Lemma wt_projections_has_variance ce: forall phl ty1 ty2 va1,
    wt_projections ce ty1 phl = OK ty2 ->
    exists va2, wt_projections_variance ce ty1 phl va1 = OK (ty2, va2).
Admitted.


Lemma wt_path_has_variance ce: forall ph ty te,
    wt_path ce te ph = OK ty ->
    exists va, wt_path_variance ce te ph = OK (ty, va).
Admitted.


Lemma wt_path_variance_append ce: forall ph phl ty1 ty2 te va1 va2,
    wt_path_variance ce te ph = OK (ty1, va1) ->
    wt_projections_variance ce ty1 phl va1 = OK (ty2, va2) ->
    wt_path_variance ce te (append_projs phl ph) = OK (ty2, va2).
Admitted.

Lemma wt_path_variance_append_inv ce: forall ph phl ty2 te va2,
    wt_path_variance ce te (append_projs phl ph) = OK (ty2, va2) ->
    exists ty1 va1, 
      wt_path_variance ce te ph = OK (ty1, va1)
      /\ wt_projections_variance ce ty1 phl va1 = OK (ty2, va2).    
Admitted.

Lemma wt_projections_variance_imply ce: forall phl ty va ty1 va1,
    wt_projections_variance ce ty phl va = OK (ty1, va1) ->
    wt_projections ce ty phl = OK ty1.
Admitted.


Lemma wt_path_variance_imply ce: forall ph ty1 va1 te,
    wt_path_variance ce te ph = OK (ty1, va1) ->
    wt_path ce te ph = OK ty1.
Admitted.


Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation cont := (@cont ame).
Notation state := (@state ame).
Notation get_owner_path_map := (@get_owner_path_map ame).

Section BORROW_CHECK.

Variable prog: program.
(* Variable w: rs_own_world. *)
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Let L := @semantics ame prog se.
Let ge := globalenv se prog.

(* composite environment *)
Let ce := ge.(genv_cenv).

(* Definition mod_sg := match w with *)
(*                     | rsw sg _ _ _ => sg *)
(*                     end. *)

(* Let wt_state := wt_state prog se mod_sg. *)

(* split move_check_program_spec into the following hypotheses to simplify the proof *)
Hypothesis CONSISTENT: composite_env_consistent ce.

Hypothesis COMP_RANGE: forall id co, ce ! id = Some co -> co_sizeof co <= Ptrofs.max_unsigned.
Hypothesis COMP_LEN: forall id co, ce ! id = Some co -> list_length_z (co_members co) <= Int.max_unsigned.
Hypothesis COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)).
(* Hypothesis FUN_CHECK:  forall id fd, *)
(*     In (id, Gfun fd) prog.(prog_defs) -> *)
(*     move_check_fundef_spec ce fd. *)

(* Result of the init analysis and the result of the move checking *)

Let INIT_AN : Type := (PMap.t IM.t * PMap.t IM.t * PathsMap.t).

Let move_check_stmt_spec (ae: INIT_AN) body cfg s ts := match_stmt get_init_info ae (move_check_stmt ce) (check_cond_expr ce) body cfg s ts.

(* Result of the loans-flow analysis and the result of the borrow
checking *)

Let LOANS_AN : Type := (PMap.t RegionSet.t * PMap.t LoansEnv.t).

Let borrow_check_stmt_spec (ae: LOANS_AN) regs f cfg s ts := match_stmt (get_borck_result regs f cfg) ae (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg s ts.

(** Over-approximation of the borrow analysis. Note that this
definition is not specific to which borrow checking algorithms you
use, e.g., NLL or Polonius, because we just use their final result of
the compuation, i.e., both of them compute active loans at each point
of the program. *)


Definition mutability_match (ref_mut loan_mut: mutkind) : Prop :=
  match ref_mut, loan_mut with
  | Mutable, Mutable => True
  (* If this reference is immutable reference, than we do not need to
  care the how we create this loan *)
  | Immutable, _ => True
  | _, _ => False
  end.

Definition ext_views_map := PTree.t PathSet.t.

Section FRAME.

Variable frame: frame_idx.

(* frame is the current frame id; [ph] is the dynamic access path
whose id is (fid, var_id) *)
Definition loan_approx (orgm: ext_views_map) (ln: loan) (mut: mutkind) (fid: frame_idx) (ph: path) : Prop :=  
  if Pos.eqb fid frame then
    match ln with
    | Lintern loan_mut p =>
        path_of_place p = ph /\ loan_mut = mut
      (* (** Note: mut is the precise mutability of the reference we are focusing. *) *)
      (* (* TODO: maybe we should use path uniformly *) *)
      (* let (id1, pj1) := path_of_place p in *)
      (* let (id2, pj2) := ph in *)
      (* id1 = id2 /\ projections_contain pj1 pj2 = true /\ mut = loan_mut *)
    | _ => False
    end
  else
    (* The state path starts from other frames so it should be abstracted by an extern loan *)
    match ln with
    | Lextern org =>
        exists vs, orgm ! org = Some vs 
              (* Since there is not way for us to make sph more
              precise (in dynamic transfer function, we do not compute
              actual spath), we do not need to say that there is a
              prefix of sph in vs *)
              /\ PathSet.In (enc_path fid ph, mut) vs
    | _ => False
    end.

Definition loans_approx_views (orgm: ext_views_map) (ls: LoanSet.t) (vs: PathSet.t) : Prop :=
  forall mut sph, PathSet.In (sph, mut) vs ->
             exists fid ph, dec_path sph = OK (fid, ph)
                       /\ exists ln, LoanSet.In ln ls /\ loan_approx orgm ln mut fid ph.

(* Definition fpm_to_orgm (fpm: fp_map) : PTree.t (option origin) := *)
(*   PTree.map1 (fun '(_,_,r,_,_) => r) fpm. *)

(* Why do we need region liveness here? *)
Definition sound_loan_approx (live: RegionSet.t) (le: LOrgEnv.t) (orgm: ext_views_map) (sphm: LOrgPhEnv.t) : Prop :=
  forall r (LIVE_REG: RegionSet.In r live),
    exists vs ls, 
      LOrgPhOptSt.eq (LOrgPhEnv.get (enc_reg frame r) sphm) (Some (LOrgPhSt.Live vs))
      /\ LOrgLnSt.eq (LOrgEnv.get r le) (LOrgLnSt.Live ls)
      /\ loans_approx_views orgm ls vs.

End FRAME.

Definition views_approx (phs: PathSet.t) (ref_mut: mutkind) (vs: views) : Prop :=
  forall ph, In ph vs ->
        exists aph mut, PathSet.In (aph, mut) phs
                   /\ mutability_match ref_mut mut
                   /\ is_prefix_path aph ph = true.

Definition sound_region_approx (phm: LOrgPhEnv.t) (fpm: fp_map) : Prop :=
  forall fid ph opt_ph vs mut b ofs r ty
    (* If we make these two get_xxx as assumptions, how can we use
    this approximation property to prove progress, i.e., how to prove
    these two assumptions. For example, when we prove the progress in
    eval_pexpr on Eplace, the two get functions can be proved to make
    progress by using induciton, this approximation property and
    property about "all owners pointed by reference is init" *)
    (* (GET_FP: get_owner_path_map ph fpm = OK (owner_ph, vs1)) *)
    (* (GET_FP: get_owner_footprint_map owner_ph fpm = OK (fp_ref mut b ofs opt_ph vs2)) *)
    (GET_FP: get_reachable_footprint_map fpm (enc_path fid ph) = OK (fp_ref mut b ofs opt_ph vs))
    (WTPH: wt_path ce (fpm_to_tenv fpm) (enc_path fid ph) = OK (Treference r mut ty)),
    match LOrgPhEnv.get (enc_reg fid r) phm with
    | Some (LOrgPhSt.Live phs) =>
        exists rph, opt_ph = Some rph
               /\ views_approx phs mut vs
    | _ => True
    end.

Definition sound_region_approx_footprint (fid: frame_idx) (phm: LOrgPhEnv.t) (fpm: fp_map) (fp: footprint) (ty: type) : Prop :=
  forall phl opt_ph vs mut b ofs r ty1
    (GET_FP: get_reachable_footprint fpm phl fp = OK (fp_ref mut b ofs opt_ph vs))
    (WT_PROJS: wt_projections ce ty phl = OK (Treference r mut ty1)),
    match LOrgPhEnv.get (enc_reg fid r) phm with
    | Some (LOrgPhSt.Live phs) =>
        exists rph, opt_ph = Some rph
               /\ views_approx phs mut vs
    | _ => True
    end.

Definition sound_region_approx_footprint_list (fid: frame_idx) (phm: LOrgPhEnv.t) (fpm: fp_map) (fpl: list footprint) (tyl: list type) : Prop :=
  Forall2 (sound_region_approx_footprint fid phm fpm) fpl tyl.


(* Old version of abstraction property *)
(* (* Why do we need region liveness here? *) *)
(* Definition sound_loan_analysis ce (live: RegionSet.t) (le: LOrgEnv.t) (fpm: fp_map) : Prop := *)
(*   forall ph opt_ph vs mut b ofs r ty *)
(*     (* If we make these two get_xxx as assumptions, how can we use *)
(*     this approximation property to prove progress, i.e., how to prove *)
(*     these two assumptions. For example, when we prove the progress in *)
(*     eval_pexpr on Eplace, the two get functions can be proved to make *)
(*     progress by using induciton, this approximation property and *)
(*     property about "all owners pointed by reference is init" *) *)
(*     (* (GET_FP: get_owner_path_map ph fpm = OK (owner_ph, vs1)) *) *)
(*     (* (GET_FP: get_owner_footprint_map owner_ph fpm = OK (fp_ref mut b ofs opt_ph vs2)) *) *)
(*     (GET_FP: get_reachable_footprint_map fpm ph = OK (fp_ref mut b ofs opt_ph vs)) *)
(*     (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK (Treference r mut ty)) *)
(*     (LIVE_REG: RegionSet.In r live), *)
(*     (* live region contains valid loans *) *)
(*     exists ls, LOrgSt.eq (LOrgEnv.get r le) (Live ls) *)
(*     (* Safety: this reference is not invalidated *) *)
(*     /\ (exists rph, opt_ph = Some rph) *)
(*     (* Approximation: all (mutable) paths in the vs2 are approximated *)
(*     in the loans map *) *)
(*     /\ loans_approx_views (fpm_to_orgm fpm) ls mut vs. *)


(* For temporary values *)
(* Definition sound_loan_analysis_footprint ce (le: LOrgEnv.t) (fpm: fp_map) (fp: footprint) (ty: type) : Prop := *)
(*   forall phl opt_ph vs mut b ofs r ty1 *)
(*     (GET_FP: get_reachable_footprint fpm phl fp = OK (fp_ref mut b ofs opt_ph vs)) *)
(*     (WT_PROJS: wt_projections ce ty phl = OK (Treference r mut ty1)), *)
(*     (* live region contains valid loans *) *)
(*     exists ls, LOrgSt.eq (LOrgEnv.get r le) (Live ls) *)
(*     (* Safety: this reference is not invalidated *) *)
(*     /\ (exists rph, opt_ph = Some rph) *)
(*     (* Approximation: all (mutable) paths in the vs are approximated *)
(*     in the loans map *) *)
(*     /\ loans_approx_views (fpm_to_orgm fpm) ls mut vs. *)
 
(* Definition sound_loan_analysis_footprint_list ce (le: LOrgEnv.t) (fpm: fp_map) (fpl: list footprint) (tyl: list type) : Prop := *)
(*   Forall2 (sound_loan_analysis_footprint ce le fpm) fpl tyl. *)

(** TODO  *)
(* Global Instance sound_loan_analysis_Proper: Proper (eq ==> RegionSet.eq ==> LOrgEnv.eq ==> eq ==> iff) sound_loan_analysis. *)
(* Admitted. *)

(* Global Instance sound_loan_analysis_footprint_Proper: Proper (eq ==> LOrgEnv.eq ==> eq ==> eq ==> eq ==>iff) sound_loan_analysis_footprint. *)
(* Admitted. *)

(* Global Instance sound_loan_analysis_footprint_list_Proper: Proper (eq ==> LOrgEnv.eq ==> eq ==> eq ==> eq ==>iff) sound_loan_analysis_footprint_list. *)
(* Admitted. *)


(** Over-approximation of equality relation in the loans map *)

Definition region_relation_wrt_variance (r1 r2: origin) (va1 va2: variance) (uf: UFD.t) :=
  if variance_eq va1 Covariant && variance_eq va2 Covariant then
    True
  else 
    UFD.sameclass uf r1 r2.


(* Why not define this soundness of region relations in
sound_loan_analysis? Because in sound_loan_analysis, we only consider
the fp_ref can be actually reached, but in the soundness of region
relations, we need to consider all the possibly reachable Treference
from the aliased location even if they are not actually reachable in
the current fpm *)
Definition sound_region_relations (phm: LOrgPhEnv.t) (fpm: fp_map) : Prop :=
  forall ph1 ph2 fid1 fid2 ph vs1 vs2 phl va1 va2 ty1 ty2 r1 r2 mut1 mut2
    (* Two paths reach the same locations *)
    (GET_PH1: get_owner_path_map (enc_path fid1 ph1) fpm = OK (ph, vs1))
    (GET_PH2: get_owner_path_map (enc_path fid2 ph2) fpm = OK (ph, vs2))    
    (WTPH1: wt_path_variance ce (fpm_to_tenv fpm) (append_projs phl (enc_path fid1 ph1)) = OK (Treference r1 mut1 ty1, va1))
    (WTPH2: wt_path_variance ce (fpm_to_tenv fpm) (append_projs phl (enc_path fid2 ph2)) = OK (Treference r2 mut2 ty2, va2)),
    (* (LIVE_REG1: RegionSet.In r1 live) *)
    (* (LIVE_REG2: RegionSet.In r2 live), *)
    region_relation_wrt_variance (enc_reg fid1 r1) (enc_reg fid2 r2) va1 va2 (LOrgPhEnv.uf phm).


Definition sound_region_relations_footprint (fid1: frame_idx) (phm: LOrgPhEnv.t) (fpm: fp_map) (fp: footprint) (ty: type) : Prop :=
  forall phl1 ph2 ph vs1 vs2 phl va1 va2 ty1 ty2 r1 r2 mut1 mut2 fid2
    (GET_PH1: get_reachable_path fpm phl1 fp = OK (ph, vs1))
    (GET_PH2: get_owner_path_map (enc_path fid2 ph2) fpm = OK (ph, vs2))
    (WTPH1: wt_projections_variance ce ty (phl1 ++ phl) Covariant = OK (Treference r1 mut1 ty1, va1))
    (WTPH2: wt_path_variance ce (fpm_to_tenv fpm) (append_projs phl (enc_path fid2 ph2)) = OK (Treference r2 mut2 ty2, va2)),
    (* (LIVE_REG2: RegionSet.In r2 live), *)
    region_relation_wrt_variance (enc_reg fid1 r1) (enc_reg fid2 r2) va1 va2 (LOrgPhEnv.uf phm).


(* An instance of sound_region_relations where we focus on a specific
   owner path [ph] and we have a reachable path with type [ty1] to
   this owner path (note that this reachable path can be not given
   here) *)
Definition sound_region_relations_path (fid1: frame_idx) (phm: LOrgPhEnv.t) (fpm: fp_map) (ph: path) (ty1: type) (va1: variance) := 
  forall ph2 vs2 phl r1 r2 mut1 mut2 va1' va2 ty1' ty2 fid2
    (GET_PH2: get_owner_path_map (enc_path fid2 ph2) fpm = OK (ph, vs2))
    (WTPH2: wt_path_variance ce (fpm_to_tenv fpm) (append_projs phl (enc_path fid2 ph2)) = OK (Treference r2 mut2 ty2, va2))
    (WTPH1: wt_projections_variance ce ty1 phl va1 = OK (Treference r1 mut1 ty1', va1')),
    (* (LIVE_REG1: RegionSet.In r1 live) *)
    (* (LIVE_REG2: RegionSet.In r2 live), *)
    region_relation_wrt_variance (enc_reg fid1 r1) (enc_reg fid2 r2) va1 va2 (LOrgPhEnv.uf phm).

Definition sound_region_relations_approx (generic_regions: list origin) (fid1: frame_idx) (live: RegionSet.t) (le: LOrgEnv.t) (sphm: LOrgPhEnv.t) : Prop :=
  forall r1 r2 fid2
    (LIVE_REG: RegionSet.In r1 live)
    (EQ12: UFD.sameclass (LOrgPhEnv.uf sphm) (enc_reg fid1 r1) (enc_reg fid2 r2)),
    if Pos.eqb fid1 fid2 then
      UFD.sameclass (LOrgEnv.uf le) r1 r2
    else
      exists gr, In gr generic_regions
            (** TODO: think carefully why we can say that this generic
            region is equivalent to (fid2,r2)?  *)
            /\ UFD.sameclass (LOrgPhEnv.uf sphm) (enc_reg (fid1-1)%positive gr) (enc_reg fid2 r2)
            /\ UFD.sameclass (LOrgEnv.uf le) r1 r2.

(** Over-approximation of the init analysis *)

Definition in_universe (w: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let universe := PathsMap.get id w in
  Paths.mem p universe.


Definition sound_init_analysis (fpm: fp_map) (init uninit universe: PathsMap.t) : Prop :=
  forall p fp, 
    in_universe universe p = true ->
    get_owner_footprint_map p fpm = OK fp ->
    (* if p is full then deep_init of fp is related to may_init and
       may_uninit, otherwise shallow_init of fp is related to them *)
    if is_full universe p then
      implb (deep_init fp) (may_init init uninit universe p) = true
      /\ implb (must_init init uninit universe p) (deep_init fp) = true
    else
      implb (shallow_init fp) (may_init init uninit universe p) = true
      /\ implb (must_init init uninit universe p) (shallow_init fp) = true.


(** state invariants *)

Inductive sound_cont: INIT_AN -> LOANS_AN -> function -> rustcfg -> cont -> cfg_kinfo -> Prop :=
| sound_Kstop: forall init_an loans_an f cfg nret
    (RET: cfg ! nret = Some Iend),
    sound_cont init_an loans_an f cfg Kstop (mk_cfg_kinfo nret None None nret)
| sound_Kseq: forall init_an loans_an f cfg s k pc next cont brk nret
    (MCK_STMT: move_check_stmt_spec init_an f.(fn_body) cfg s s (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt_spec loans_an (regset_fun f) f cfg s s (mk_cfg_info pc next cont brk nret))
    (MCONT: sound_cont init_an loans_an f cfg k (mk_cfg_kinfo next cont brk nret)),
    sound_cont init_an loans_an f cfg (Kseq s k) (mk_cfg_kinfo pc cont brk nret)
| sound_Kloop: forall init_an loans_an f cfg s k body_start loop_jump_node exit_loop nret contn brk
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MCK_STMT: move_check_stmt_spec init_an f.(fn_body) cfg s s (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (BORCK_STMT: borrow_check_stmt_spec loans_an (regset_fun f) f cfg s s (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (MCONT: sound_cont init_an loans_an f cfg k (mk_cfg_kinfo exit_loop contn brk nret)),
    sound_cont init_an loans_an f cfg (Kloop s k) (mk_cfg_kinfo loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
| sound_Kcall: forall init_an loans_an f1 cfg k nret f2 p fpm ns inout_params
    (MSTK: sound_stacks (Kcall p f2 inout_params ns fpm k))
    (RET: cfg ! nret = Some Iend),
    (* (WFOWN: wf_own_env e ce own), *)
    sound_cont init_an loans_an f1 cfg (Kcall p f2 inout_params ns fpm k) (mk_cfg_kinfo nret None None nret)

with sound_stacks : cont -> Prop :=
| sound_stacks_stop:
    sound_stacks Kstop
| sound_stacks_call: forall f nret cfg pc contn brk k p maybeInit maybeUninit universe entry mayinit mayuninit live loans_env LoansEnv mayinit0 mayuninit0 inout_params fpm ns
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k (mk_cfg_kinfo pc contn brk nret))
    (* may(un)init0 are the intermediate state of this function call
    statement before initializing p *)
    (MAY_INIT: mayinit = add_place universe p mayinit0)
    (MAY_UNINIT: mayuninit = remove_place p mayuninit0)
    (* we need to maintain this invariant for p's evaluation when
    function return *)
    (DOM: dominators_must_init mayinit0 mayuninit0 universe p = true)
    (** Invariant of the move checking. TODO: it is not correct
    because we may pass some reference passed locations out. Maybe we
    can label those locations instead of passing them out? *)
    (INIT_APPRO: sound_init_analysis fpm mayinit0 mayuninit0 universe)
    (* Invariant of the borrow checking *)
    (BORROW_APPRO: sound_loan_analysis ce (live!!pc) loans_env fpm),
    sound_stacks (Kcall p f inout_params ns fpm k).


Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s pc next cont brk nret k fpm live live_st LoansEnv loans_env ns sup
    (* The init and loans-flow analysis results *)
    (* (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe)) *)
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The result of move checking and borrow checking *)
    (* (MCK_STMT: move_check_stmt_spec (maybeInit, maybeUninit, universe) f.(fn_body) cfg s s (mk_cfg_info pc next cont brk nret)) *)
    (BORCK_STMT: borrow_check_stmt_spec (live, LoansEnv) (regset_fun f) f cfg s s (mk_cfg_info pc next cont brk nret))
    (* The init set and loans environment of the current pc *)
    (* (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit))) *)
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k (mk_cfg_kinfo next cont brk nret))
    (* Over-approximation of the move checking. *)
    (* (INIT_APPRO: sound_init_analysis fpm mayinit mayuninit universe) *)
    (* We use the liveness information before this pc instead of after this pc *)
    (LIVE_ST: RegionLiveness.transfer f cfg (regset_fun f) pc (live !! pc) = live_st)
    (* Over-approximation of the borrow checking *)
    (BORROW_APPRO: sound_loan_analysis ce live_st loans_env fpm),
    sound_state (State f s k ns fpm sup)
| sound_callstate: forall fun_id fd orgs org_rels tyargs tyres cconv args k inout_fpm sup
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun fd))
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (* (WTVAL_LIST: sem_wt_val_list ce fpl args VMP) *)
    (* Used in assign_loc_sound in function entry proof *)
    (* (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl) *)
    (STK: sound_stacks k),
    (** TODO: borrow check invariant is missing at function call *)
    (* also disjointness of fpl and fpf *)
    sound_state (Callstate fun_id args inout_fpm sup k)
| sound_returnstate: forall sg k retty rfp inout_fpm sup
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = retty)
    (* (WTFP: wt_footprint ce retty rfp) *)
    (STK: sound_stacks k),
    (** TODO: borrow check invariant is missing at function return *)
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)), *)
    sound_state (Returnstate rfp inout_fpm sup k)
.

(** Misc for invalidate_conflict_ref and kill_paths. TODO: merge with
the related lemmas in BorrowCheckInv.v *)

Ltac destr_if_with_name H name :=
  match type of H with
  | ((if ?x then _ else _) = _) =>
      destruct x eqn: name; try congruence
  | context G [(match ?x with | _ => _ end)] =>
      destruct x eqn: name; try congruence
  end.

Lemma get_reachable_footprint_append: forall phl1 phl2 fp1 fp2 fp3 (fpm: fp_map),
    get_reachable_footprint fpm phl1 fp1 = OK fp2 ->
    get_reachable_footprint fpm phl2 fp2 = OK fp3 ->
    get_reachable_footprint fpm (phl1 ++ phl2) fp1 = OK fp3.
Admitted.

  
(* get_reachable_footprint_map can be divided into get_owner_path_map
and then get_reachable_footprint *)
Lemma get_reachable_footprint_map_append: forall (fpm: fp_map) ph phl ph1 vs fp fp1,
    get_owner_path_map ph fpm = OK (ph1, vs) ->
    get_owner_footprint_map ph1 fpm = OK fp ->
    get_reachable_footprint fpm phl fp = OK fp1 ->
    get_reachable_footprint_map fpm (append_projs phl ph) = OK fp1.
Admitted.


Lemma get_owner_footprint_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ak am fp,
    get_owner_footprint_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK fp ->
    exists fp', get_owner_footprint_map ph1 fpm = OK fp'
           /\ invalidate_conflict_ref ph2 ak am fp' = fp.
Admitted.

Lemma get_owner_path_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ph vs ak am,
    get_owner_path_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK (ph, vs) ->
    get_owner_path_map ph1 fpm = OK (ph, vs).    
Admitted.


Lemma get_reachable_footprint_after_invalidate_ref: forall phl (fpm: fp_map) ph ak am fp fp1,
    get_reachable_footprint (invalidate_conflict_ref_fpm ph ak am fpm) phl (invalidate_conflict_ref ph ak am fp) = OK fp1 ->
    exists fp2, get_reachable_footprint fpm phl fp = OK fp2
           /\ invalidate_conflict_ref ph ak am fp2 = fp1.
Admitted.


Lemma get_reachable_footprint_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ak am fp,
    get_reachable_footprint_map (invalidate_conflict_ref_fpm ph2 ak am fpm) ph1 = OK fp ->
    exists fp', get_reachable_footprint_map fpm ph1 = OK fp'
           /\ invalidate_conflict_ref ph2 ak am fp' = fp.
Admitted.


Ltac destr_fp_map_elt p :=
  destruct p as ((((?b & ?ofs) & ?r) & ?ty) & ?fp).

Lemma fpm_to_orgm_after_invalidate_ref: forall (fpm: fp_map) ph ak am,
    fpm_to_orgm (invalidate_conflict_ref_fpm ph ak am fpm) = fpm_to_orgm fpm.
Proof.
  intros. unfold fpm_to_orgm, invalidate_conflict_ref_fpm. 
  eapply PTree.extensionality.
  intros. erewrite ! PTree.gmap1.
  destruct (fpm ! i); try destr_fp_map_elt p; auto.
Qed.

Lemma fpm_to_tenv_after_invalidate_ref: forall (fpm: fp_map) ph ak am,
    fpm_to_tenv (invalidate_conflict_ref_fpm ph ak am fpm) = fpm_to_tenv fpm.
Proof.
  intros. unfold fpm_to_tenv, invalidate_conflict_ref_fpm. 
  eapply PTree.extensionality.
  intros. erewrite ! PTree.gmap1.
  destruct (fpm ! i); try destr_fp_map_elt p; auto.
Qed.

Lemma fpm_to_orgm_after_set_footprint_map: forall (fpm1 fpm2: fp_map) ph fp,
    set_footprint_map ph fp fpm1 = OK fpm2 ->
    fpm_to_orgm fpm2 = fpm_to_orgm fpm1.
Proof.
Admitted.

Lemma fpm_to_tenv_after_set_footprint_map: forall (fpm1 fpm2: fp_map) ph fp,
    set_footprint_map ph fp fpm1 = OK fpm2 ->
    fpm_to_tenv fpm2 = fpm_to_tenv fpm1.
Proof.
Admitted.


Hint Resolve get_owner_footprint_map_after_invalidate_ref
             get_owner_path_map_after_invalidate_ref
             get_reachable_footprint_after_invalidate_ref
             get_reachable_footprint_map_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref
             fpm_to_orgm_after_set_footprint_map: invalidate_fp_ref.

Hint Rewrite get_owner_footprint_map_after_invalidate_ref
             get_owner_path_map_after_invalidate_ref
             get_reachable_footprint_after_invalidate_ref
             get_reachable_footprint_map_after_invalidate_ref
             fpm_to_orgm_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref
             fpm_to_orgm_after_set_footprint_map: invalidate_fp_ref.

(** Properties of operations on LOrgEnv.t  *)

Lemma loan_env_add_ge: forall le r ls,
    LOrgEnv.ge (loan_env_add le r ls) le.
Admitted.

Global Instance loan_env_add_Proper: Proper (LOrgEnv.eq ==> eq ==> LOrgSt.eq ==> LOrgEnv.eq) loan_env_add.
Proof.
  intros le1 le2 A r1 r2 B ls1 ls2 C.
  unfold loan_env_add. subst.
  eapply LOrgEnv_set_Proper; auto.
  eapply LOrgSt_lub_Proper; eauto.
  eapply A.
Qed.


(** invalidation of fp_ref preserves sound approximation invariant *)


(* Used to prove conflict_Proper *)
Lemma forallb_ext_In_perm :
  forall (A : Type) (f : A -> bool) (l1 l2 : list A),
    (forall x, In x l1 <-> In x l2) ->
    forallb f l1 = forallb f l2.
Proof.
  intros A f l1 l2 Heq.
  apply Bool.eq_true_iff_eq.
  rewrite !forallb_forall.
  split; intros. eapply H. eapply Heq. auto.
  intros. eapply H. eapply Heq. auto.
Qed.

Lemma LoanSet_InA_to_In :
  forall x l,
    SetoidList.InA LoanSet.E.eq x l <->
    In x l.
Proof.
  intros x l.
  split.
  - intros H. induction H.
    + left. auto.
    + right. auto.
  - intros H. 
    eapply SetoidList.In_InA; auto.
    eapply eq_equivalence.
Qed.

Global Instance conflict_Proper: Proper (eq ==> LoanSet.eq ==> eq ==> eq ==> eq) conflict.
Proof.
  unfold conflict.
  intros p1 p2 EQ1 ls1 ls2 EQ2 am1 am2 EQ3 ak1 ak2 EQ4. subst.
  rewrite !LoanSetFacts.for_all_b.
  erewrite forallb_ext_In_perm. reflexivity.
  split; intros. 
  eapply LoanSet_InA_to_In. eapply EQ2. 
  eapply LoanSet_InA_to_In in H. eapply H.
  eapply LoanSet_InA_to_In. eapply EQ2. 
  eapply LoanSet_InA_to_In in H. eapply H.
  intros a1 a2 EQ4. subst. auto.
  intros a1 a2 EQ4. subst. auto.
Qed.

Lemma illegal_access_false_implies: forall le p am ak r ls,
    illegal_access le p am ak = false ->
    LOrgSt.eq (LOrgEnv.get r le) (Live ls) ->
    conflict p ls am ak = false.
Proof.
  intros until ls. intros ILL.
  unfold illegal_access in ILL.
  erewrite PTree_Properties.exists_false in ILL. 
  unfold LOrgEnv.get.
  destruct (LOrgEnv.m le) ! (UnionFindDelete.UFD.repr (LOrgEnv.uf le) r) eqn: A; auto.  
  - intros EQ. destruct t; simpl in EQ; try contradiction. 
    eapply ILL in A. unfold illegal_access_in_origin_state in A. 
    destr_if_with_name A CON; try congruence.
    erewrite conflict_Proper; eauto. 
    eapply LoanSet.eq_sym; auto.
  - intros. inv H.
Qed.

(* p is the path we access and p1 is the path in views *)
Lemma loan_approx_conflict_loan_false_implies: forall p p1 am ak ln orgm ref_mut,
    conflict_access ak ref_mut = true ->
    conflict_loan p am ak ln = false ->
    loan_approx orgm ln ref_mut p1 ->
    relevant_path p am p1 = false.
Proof.
  intros until ref_mut. intros A1 A2 SOUND.
  red in SOUND. unfold conflict_loan in A2.
  destruct ln.
  - destruct (extern_loc_region orgm p1); try contradiction.
    destr_path_of_place p0. destruct p1 as (id2 & pj2) eqn: P1.
    destruct SOUND as (B1 & B2 & B3). subst.
    assert (C: conflict_access ak mut = true).
    { destruct ak; destruct ref_mut; simpl in A1; try congruence; destruct mut; simpl in B3; simpl; auto. }
    rewrite C in A2. 
    destruct (relevant_place p p0 am) eqn: C1; simpl in A2; try congruence.   
    (* C1 implies: p0 -> p (p0 is prefix of p) or p ->(am) p0 is false;
       B2 (the loans we analyze approximates the real view) implies: p0 -> (id2,phl) (p0 is prefix of (id2, phl), i.e., p1) *)
    destruct (is_prefix_strict_path (id2, pj2) p) eqn: PREFIX.
    (* we have p0 -> (id2, phl) -> p, which is contradict to [p0 -> p
    is false] implies by C1 *)
    + admit.
    + unfold relevant_path, relevant_place in *. 
      rewrite PREFIX.
      destruct (match am with
                | Ashallow => is_shallow_prefix_path p (id2, pj2)
                | Adeep => is_prefix_path p (id2, pj2)
                end) eqn: PRE_AM; auto.
      (* Since we have [p ->(am) p0 = false] and [p0 -> (id2, phl)], we
      have [p -> (am) (id2,phl) = false]. Prove by contradiction? If [p
      -> (am) (id2,phl) = true] and [p0 -> (id2, phl)] then we have
      either [p0 is prefix of p] or [p is support prefix of p0]. THe
      former case is contradict with [PREFIX] and the latter case is
      contradict with [p ->(am) p0 = false]. *)
      assert (CONTR: match am with
                     | Ashallow => is_shallow_prefix p p0
                     | Adeep => is_support_prefix p p0
                     end = true).
      { admit. }
      rewrite CONTR in C1. rewrite orb_true_r in C1. congruence.
  - destruct (extern_loc_region orgm p1); try contradiction. subst.
    (** TODO: p1 is an external access path, so p (which is a local
    place) cannot be prefix or decendant of p1. But this lemma does
    not give this premises. *)
    admit.

Admitted.

Lemma loans_approx_views_not_conflict: forall vs p am ak ref_mut ls orgm
  (SOUND: loans_approx_views orgm ls ref_mut vs)
  (CONFLICT: conflict p ls am ak = false),
    conflict_access ak ref_mut && conflict_view p am vs = false.
Proof.
  induction vs; intros.
  - simpl. ring.
  - unfold loans_approx_views, conflict, conflict_view in *. 
    exploit IHvs. intros. eapply SOUND. right. auto.
    eauto. intros A.
    (* Proof idea: the target is to prove that [relevant_path p am a =
    false]. We know for each loan in the loans set which approx
    (a::vs), there is no conflict loan w.r.t. p under am and ak. But
    [conflict_loan p am ak ln = false] may be derived from the fact
    that [conflict_access ak (mut of the relevant_place in ln)] is
    false (the opposite case is the normal case which may be proved by
    loan_approx). But we need to prove that it is impossible. How?
    First, we can only consider the case [conflict_access ak ref_mut =
    true]. Then, since [loan_approx orgm ln ref_mut a], there exists a
    relevant path in ln w.r.t. [p] must have matched mutability with
    [ref_mut]. It further means that there exists a relevant place in
    [ln] w.r.t. [p] must have matched mutability with [ref_mut], which
    can further derive that [conflict_access ak (mut of this
    relevant_place in ln)] is true. *)
    (* We first say that [conflict_access ak ref_mut] is true *)
    destruct (conflict_access ak ref_mut) eqn: C1; simpl in *; auto.
    rewrite A. rewrite orb_false_r.
    (* prove relevant_path p am a = false *)
    eapply negb_false_iff in CONFLICT.
    eapply LoanSet.for_all_2 in CONFLICT.
    2: { red. unfold Proper. reflexivity. }
    exploit (SOUND a). auto.    
    intros (ln & A1 & A2).
    eapply CONFLICT in A1. eapply negb_true_iff in A1.
    eapply loan_approx_conflict_loan_false_implies; eauto.
Qed. 



Lemma invalidate_conflict_ref_fpm_preserves_borchk_approx: forall fpm p am ak le live
    (SOUND: sound_loan_analysis ce live le fpm)
    (ILL_ACCESS: illegal_access le p am ak = false),
    sound_loan_analysis ce live le (invalidate_conflict_ref_fpm p ak am fpm).
Proof.
  intros. red. intros.
  (** The most important property we need to prove is that opt_ph in
  GET_FP may not be the same as the opt_ph in fpm because of the
  invalidation, but we need to prove that they are the same using the
  checking result of [illegal_access] *)  
  exploit (@get_reachable_footprint_map_after_invalidate_ref); eauto.
  intros (fp1 & GET_FP1 & INVREF).
  destruct fp1; inv INVREF.  
  (* use sound approximation in fpm to prove that ph0 is not invalid *)
  autorewrite with invalidate_fp_ref in *. 
  exploit SOUND; eauto. 
  intros (ls & A1 & (rph & A2) & A3). subst.
  exists ls. split; eauto.
  split; auto. 
  exists rph.
  exploit illegal_access_false_implies; eauto. intros CONFLICT_FALSE.
  erewrite loans_approx_views_not_conflict; eauto.
Qed.

Lemma sound_loan_analysis_footprint_reachable: forall le fpm fp ty fp1 ty1 phl1,
    sound_loan_analysis_footprint ce le fpm fp ty ->
    get_reachable_footprint fpm phl1 fp = OK fp1 ->
    wt_projections ce ty phl1 = OK ty1 ->
    sound_loan_analysis_footprint ce le fpm fp1 ty1.
Proof.
  intros. red. intros.
  eapply H. 
  eapply get_reachable_footprint_append; eauto.
  eapply wt_projections_append; eauto.
Qed.

Lemma invalidate_conflict_ref_preserves_borchk_approx: forall fp fpm p am ak le ty
    (SOUND: sound_loan_analysis_footprint ce le fpm fp ty)
    (ILL_ACCESS: illegal_access le p am ak = false),
    sound_loan_analysis_footprint ce le (invalidate_conflict_ref_fpm p ak am fpm) (invalidate_conflict_ref p ak am fp) ty.
Proof.
  intros. red.
  intros.
  exploit get_reachable_footprint_after_invalidate_ref; eauto.
  intros (fp' & A1 & A2).
  destruct fp'; inv A2.
  exploit SOUND; eauto.
  intros (ls1 & B1 & (rph & B2) & B3). subst.  
  exploit illegal_access_false_implies; eauto. intros CONFLICT_FALSE.
  erewrite loans_approx_views_not_conflict in *; eauto.
  exists ls1. repeat apply conj; eauto.
  autorewrite with invalidate_fp_ref. auto.
Qed.    


(* It should be straightforward *)
Lemma sound_loan_analysis_footprint_inside: forall live le fpm fp ph ty
  (SOUND: sound_loan_analysis ce live le fpm)
  (GET_FP: get_owner_footprint_map ph fpm = OK fp)
  (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK ty)
  (* all regions in ty are live *)
  (LIVE: Forall (fun r => RegionSet.In r live) (origins_of_type ty)),
    sound_loan_analysis_footprint ce le fpm fp ty.
Admitted.

(* It should be straightforward *)
Lemma sound_loan_analysis_after_clear_footprint_map: forall ph fpm1 fpm2 live le,
    sound_loan_analysis ce live le fpm1 ->
    clear_footprint_map ce ph fpm1 = OK fpm2 ->
    sound_loan_analysis ce live le fpm2.
Admitted.

(* It should be straightforward *)
Lemma sound_loan_analysis_footprint_after_clear_footprint_map: forall ph fpm1 fpm2 le fp ty,
    sound_loan_analysis_footprint ce le fpm1 fp ty ->
    clear_footprint_map ce ph fpm1 = OK fpm2 ->
    sound_loan_analysis_footprint ce le fpm2 fp ty.
Admitted.

(* It should be straightforward *)
Lemma loans_approx_views_monotonicity: forall ls1 ls2 orgm vs mut,
    loans_approx_views orgm ls1 mut vs ->
    LoanSetL.ge ls2 ls1 ->
    loans_approx_views orgm ls2 mut vs.
Admitted.
  
(* It should be straightforward *)
Lemma sound_loan_analysis_liveness_monotonicity: forall live1 live2 le fpm,
    sound_loan_analysis ce live2 le fpm ->
    RegionSet.Subset live1 live2 ->
    sound_loan_analysis ce live1 le fpm.
Admitted.

(* Sound over-approximation is preserved when we have a more
   abstracted domain (under LOrgEnv.ge). Formally, it is called
   "monotonicity with respect to the abstract order". *)
Lemma sound_loan_analysis_monotonicity: forall live le1 le2 fpm,
    LOrgEnv.ge le1 le2 ->
    sound_loan_analysis ce live le2 fpm ->
    sound_loan_analysis ce live le1 fpm.
Admitted.


Fixpoint fp_not_contain_ref (fp: footprint) : bool :=
  match fp with
  | fp_emp => true
  | fp_uninit _ _ => true
  | fp_scalar _ _ => true
  | fp_struct fid fpl =>
      forallb (fun '(_, (_, ffp)) => fp_not_contain_ref ffp) fpl
  | fp_box _ fp1 =>
      fp_not_contain_ref fp1 
  | fp_enum _ _ _ _ ffp =>
      fp_not_contain_ref ffp 
  | fp_ref _ _ _ _ _ => false
  | fp_object _ _ fpl =>
      forallb (fun '(_, (_, _, _, ffp)) => fp_not_contain_ref ffp) fpl
  end.

Lemma sound_loan_analysis_footprint_trivial: forall fp le fpm ty,
    fp_not_contain_ref fp = true ->
    sound_loan_analysis_footprint ce le fpm fp ty.
Admitted.

(** Important TODO: Sound approximation of aggregate_origin_states w.r.t. the views
collected from get_owner_path_map *)
Lemma sound_aggregate_origin_states: forall (p: place) le live fpm ph vs mut,
    sound_loan_analysis ce live le fpm ->
    get_owner_path_map p fpm = OK (ph, vs) ->
    exists ls, LOrgSt.eq 
            (LOrgSt.lub 
               (aggregate_origin_states le (support_origins p))
               (Live (LoanSet.singleton (Lintern mut p)))) 
            (Live ls)
          /\ loans_approx_views (fpm_to_orgm fpm) ls mut vs.
Admitted.

(** evaluation of expression preserves invariant *)

Lemma get_reachable_footprint_fp_ref_inv: forall phl (fpm: fp_map) mut b ofs ph vs fp,
    get_reachable_footprint fpm phl (fp_ref mut b ofs (Some ph) vs) = OK fp ->
    (fp = (fp_ref mut b ofs (Some ph) vs) /\ phl = nil)
    \/ (exists fp1 phl1, get_owner_footprint_map ph fpm = OK fp1
                   /\ phl = proj_deref :: phl1
                   /\ get_reachable_footprint fpm phl1 fp1 = OK fp).
Proof.
  destruct phl.
  - simpl; intros. inv H. eauto.
  - intros. simpl in H.
    destr_if_with_name H PROJ. monadInv H.
    right. eauto.
Qed.

Lemma eval_pexpr_preserves_borchk_approx: forall pe fpm1 fpm2 live le vfp
  (BORROW_APPROX: sound_loan_analysis ce live le fpm1)
  (EVAL: eval_pexpr fpm1 pe = OK (vfp, fpm2))
  (* It ensures that we do not invalidate some reference (which is
  live) incorrectly. *) 
  (BORROW_CHECK: check_pure_expr le pe = OK tt)
  (WT: wt_pexpr (fpm_to_env fpm1) ce pe),
    sound_loan_analysis ce live (transfer_pure_expr le pe) fpm2
    /\ sound_loan_analysis_footprint ce (transfer_pure_expr le pe) fpm2 vfp (typeof pe).
Proof.
  induction pe; intros.
  1-5: try (monadInv EVAL; simpl in BORROW_APPROX; split; [eauto| try eapply sound_loan_analysis_footprint_trivial; eauto]).
  (* Eplace *)
  - simpl in BORROW_CHECK. 
    destr_if_with_name BORROW_CHECK ILL.
    inv WT.
    monadInv EVAL. 
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx in BORROW_APPROX as BORROW_APPROX1; eauto.
    (* approximation property of the evaluated footprint *)
    destruct x1 as (b & ofs).
    exploit @get_owner_loc_footprint_map_after_invalidate_ref. eapply EQ1.
    intros (vfp1 & A1 & A2). subst.
    assert (SOUND_FP: sound_loan_analysis_footprint ce le (invalidate_conflict_ref_fpm p ARead Adeep fpm1) (invalidate_conflict_ref p ARead Adeep vfp1) (typeof_place p)).
    { eapply sound_loan_analysis_footprint_inside; eauto with fpmap.      
      (* wt_path *) admit.
      (* region liveness *) admit. }
    split; auto.
  (* cktag *)
  - monadInv EVAL. 
    destruct x2; try congruence. inv EQ2.
    simpl in BORROW_APPROX; split; [eauto| try eapply sound_loan_analysis_footprint_trivial; eauto].
    simpl in BORROW_CHECK.
    destr_if_with_name BORROW_CHECK ILL_ACCESS.
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx; eauto.
  (** Eref *)
  - simpl in BORROW_CHECK. 
    destr_if_with_name BORROW_CHECK ILL.
    inv WT.
    monadInv EVAL. 
    destruct x1 as (b & ofs). inv EQ2.
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx in BORROW_APPROX as BORROW_APPROX1; eauto.
    eapply sound_loan_analysis_liveness_monotonicity with (live1 := live) in BORROW_APPROX1 as BORROW_APPROX2; eauto. 
    2: admit.                   (* region liveness inclusion *)
    split.
    + eapply sound_loan_analysis_monotonicity with (le2:= le).
      eapply loan_env_add_ge. auto.
    + simpl.
      exploit sound_aggregate_origin_states; eauto. instantiate (1 := m).
      intros (ls & A1 & A2).
      set (fpm2 := (invalidate_conflict_ref_fpm p (mut_to_access_kind m) Adeep fpm1)) in *.
      (* (* well-typed property ensured by get_owner_path_map *) *)
      (* assert (WTPH: wt_path ce (fpm_to_tenv fpm2) x = OK (typeof_place p)) by admit. *)
      (* Two cases: 1. consider x0 or 2. consider the fp_ref reachable from x *)
      eapply sound_loan_analysis_footprint_Proper. reflexivity.
      eapply loan_env_add_Proper. eapply LOrgEnv.eq_refl. reflexivity. eauto.
      1-3: reflexivity.
      red. intros.
      exploit get_reachable_footprint_fp_ref_inv; eauto.
      intros [[B1 B2] | B2].
      * inv B1. inv WT_PROJS.        
        unfold loan_env_add.
        setoid_rewrite LOrgEnv.gsspec.
        rewrite peq_true. destruct (LOrgEnv.get r le) eqn: G.
        -- simpl. exists (LoanSet.union ls ls0). split.
           reflexivity. split; eauto.
           eapply loans_approx_views_monotonicity. eauto.
           eapply LoanSetL.ge_lub_left.
        -- simpl. exists ls. split. reflexivity. split; eauto.
      * destruct B2 as (fp1 & phl1 & G1 & G2 & G3).
        subst.
        (* use sound_loan_analysis *)
        exploit BORROW_APPROX1. eapply get_reachable_footprint_map_append; eauto.
        eapply wt_path_append.
        (* wt_place *)
        instantiate (1 := typeof_place p). admit.
        simpl in WT_PROJS. eauto.
        (* region liveness *)
        admit.
        intros (ls1 & C1 & (rph & C2) & C3). subst.
        unfold loan_env_add. setoid_rewrite LOrgEnv.gsspec.
        destruct peq.
        -- exists (LoanSet.union ls ls1). repeat apply conj; eauto. 
           assert (G: LOrgEnv.get o le = LOrgEnv.get r le).
           { unfold LOrgEnv.get. rewrite e. auto. }
           rewrite G. rewrite C1. reflexivity.
           eapply loans_approx_views_monotonicity. eauto.
           eapply LoanSetL.ge_lub_right.
        -- exists ls1. repeat apply conj; eauto. 
  (* Eunop *)
  - simpl in BORROW_CHECK.
    inv WT.
    monadInv EVAL. 
    destruct x; try congruence. 
    destr_if_with_name EQ0 UOP. monadInv EQ0.
    simpl in BORROW_APPROX; split; [eauto| try eapply sound_loan_analysis_footprint_trivial; eauto].
    eapply IHpe; eauto.
  (* Ebinop *)
  - simpl in BORROW_CHECK. monadInv BORROW_CHECK.
    inv WT.
    monadInv EVAL. 
    destr_if_with_name EQ4 FP1.
    destr_if_with_name EQ4 FP2. 
    destr_if_with_name EQ4 BINOP. monadInv EQ4.
    simpl in BORROW_APPROX; split; [eauto| try eapply sound_loan_analysis_footprint_trivial; eauto].
    eapply IHpe2 with (le := (transfer_pure_expr le pe1)); eauto.
    eapply IHpe1; eauto. destruct x; eauto. 
    (* evaluation does not change type env *)
    admit.
  - inv WT.
Admitted.


Lemma eval_expr_preserves_borchk_approx: forall e fpm1 fpm2 live le vfp
  (BORROW_APPROX: sound_loan_analysis ce live le fpm1)
  (EVAL: eval_expr ce fpm1 e = OK (vfp, fpm2))
  (* It ensures that we do not invalidate some reference (which is
  live) incorrectly. *) 
  (BORROW_CHECK: check_expr le e = OK tt)
  (WT: wt_expr (fpm_to_env fpm1) ce e),
    sound_loan_analysis ce live (transfer_expr le e) fpm2
    /\ sound_loan_analysis_footprint ce (transfer_expr le e) fpm2 vfp (typeof e).
Proof.
  intros. destruct e.  
  (* moveplace *)
  - simpl in EVAL. monadInv EVAL.
    destruct x.
    simpl in BORROW_CHECK.
    destr_if_with_name BORROW_CHECK ILL_ACCESS.
    inv WT.
    (** TODO: add premise about that p is a local place, which is used
    to prove that the invalidation of fp_ref is not because this
    reference contains an extern loans conflict with p *)
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx with (p:= p) (am:= Adeep) (ak:= AWrite) in BORROW_APPROX as BORROW_APPROX1; eauto.
    (* approximation property of the evaluated footprint *)
    exploit @get_owner_loc_footprint_map_after_invalidate_ref. eapply EQ.
    intros (vfp1 & A1 & A2). subst.
    (* sound_loan_analysis implies sound_loan_analysis_footprint for
    each internal footprint *)   
    assert (SOUND_FP: sound_loan_analysis_footprint ce le (invalidate_conflict_ref_fpm p AWrite Adeep fpm1) (invalidate_conflict_ref p AWrite Adeep vfp1) (typeof_place p)).
    { eapply sound_loan_analysis_footprint_inside; eauto with fpmap.      
      (* wt_path *) admit.
      (* region liveness *) admit. }
    (* sound approximation is preserved under clearing owner's footprint *)
    eapply sound_loan_analysis_after_clear_footprint_map in BORROW_APPROX1 as BORROW_APPROX2; eauto.
    eapply sound_loan_analysis_footprint_after_clear_footprint_map in SOUND_FP as SOUND_FP1; eauto.
  - eapply eval_pexpr_preserves_borchk_approx; eauto.
    inv WT. auto.
Admitted.


(** Important TODO  *)
Lemma before_write_place_sound: forall fpm1 fpm2 le1 live fp ty p ph vs
    (SOUND: sound_loan_analysis ce live le1 fpm1)
    (SOUND_FP: sound_loan_analysis_footprint ce le1 fpm1 fp ty)
    (WRITE: before_write_place ce fpm1 p = OK (ph, vs, fpm2)),
    sound_loan_analysis ce live (kill_loans le1 p) fpm2
    /\ sound_loan_analysis_footprint ce (kill_loans le1 p) fpm2 (kill_paths_ref vs fp) ty.
Admitted.


(** Important TODO: how can we split a reachable path into two parts
after setting a new footprint into the map?  *)
Lemma get_reachable_footprint_map_after_set: forall fpm1 fpm2 ph1 ph2 vfp fp,
    set_footprint_map ph1 vfp fpm1 = OK fpm2 ->
    get_reachable_footprint_map fpm2 ph2 = OK fp ->
    get_reachable_footprint_map fpm1 ph2 = OK fp
    (* We first traverse fpm1 until we reach ph1 and then we start
    from vfp to traverse fpm2 *)
    \/ exists id2 phl1 phl2 vs, 
        ph2 = (id2, phl1 ++ phl2)
        /\ get_owner_path_map (id2, phl1) fpm1 = OK (ph1, vs)
        /\ get_reachable_footprint fpm2 phl2 vfp = OK fp.
Admitted.

(** TODO: combine get_reachable_footprint and get_reachable_path?  *)
(* Similar to get_reachable_footprint_map_after_set but we focus on
the path here *)
Lemma get_owner_path_map_after_set: forall fpm1 fpm2 ph1 ph2 vfp ph vs,
    set_footprint_map ph1 vfp fpm1 = OK fpm2 ->
    get_owner_path_map ph2 fpm2 = OK (ph, vs) ->
    get_owner_path_map ph2 fpm1 = OK (ph, vs)
    (* We first traverse fpm1 until we reach ph1 and then we start
    from vfp to traverse fpm2 *)
    \/ exists id2 phl1 phl2 vs, 
        ph2 = (id2, phl1 ++ phl2)
        /\ get_owner_path_map (id2, phl1) fpm1 = OK (ph1, vs)
        /\ get_reachable_path fpm2 phl2 vfp = OK (ph, vs).
Admitted.


(** Important TODO  *)
(** How to prevent we cannot flow r_src to r_tgt twice? For example,
what if we have type like [&'a mut &'a mut i32]? So we can only know
the loans in r2 is greater than the joined loans? *)
Lemma flow_loans_projections_spec: forall phl ty_src ty_tgt le va va1 r1 r2 mut1 mut2 ty1 ty2,
    type_eq_except_origins ty_src ty_tgt = true ->
    wt_projections_variance ce ty_src phl va = OK (Treference r1 mut1 ty1, va1) ->
    (* The variance of target type is not important here because loans
    flow depends on the variance of source type *)
    wt_projections ce ty_tgt phl = OK (Treference r2 mut2 ty2) ->
    LOrgSt.ge (LOrgEnv.get r2 (flow_loans le ty_src ty_tgt va)) (LOrgSt.lub (LOrgEnv.get r1 le) (LOrgEnv.get r2 le))
    /\ match va1 with
      | Invariant =>
          UFD.sameclass (LOrgEnv.uf (flow_loans le ty_src ty_tgt va)) r1 r2
      | _ => True
      end.
Admitted.

(** Important TODO  *)

Lemma flow_loans_sound: forall fp le1 ty_src ty_tgt fk va_tgt fpm1 live1 live2 ph ph_ty fpm2
    (SOUND: sound_loan_analysis ce live1 le1 fpm1)
    (SOUND_FP: sound_loan_analysis_footprint ce le1 fpm1 fp ty_src)
    (REG_SOUND_FP: sound_region_relations_footprint ce live1 le1 fpm1 fp ty_src)
    (REG_SOUND: sound_region_relations ce live1 le1 fpm1)
    (* This property should be derived from before_write_place_sound *)
    (REG_SOUND_PH: sound_region_relations_path live1 le1 fpm1 ph ty_tgt va_tgt)
    (* What is the relation between live1 and live2? Can we just
    use ty1 and ty2 to define this relation? One important point
    is to say that if some region [r] is dead at [live1] but live
    at [live2], then there must be no other path that can reach
    the same location as [ph] must be a local path and we have
    invalidated all path that reborros [ph]. We should also prove
    that all regions in ty2 are either all live or all dead? *)
    (SET_FP: set_footprint_map ph fp fpm1 = OK fpm2)
    (GET_UNINIT: get_owner_footprint_map ph fpm1 = OK (type_to_uninit_footprint ce ty_tgt))
    (* type checking result *)
    (* ph_ty is used to relate other types that bypass ph *)
    (WTPH: wt_path ce (fpm_to_tenv fpm1) ph = OK ph_ty)
    (TYEQ1: type_eq_except_origins ph_ty ty_tgt = true)
    (TYEQ2: type_eq_except_origins ty_src ty_tgt = true)
    (WTFPM: wt_fpm ce fpm1)
    (* Because we are using types to simulate footprint assignment,
    this operation is sound only if the footprint matches the type *)
    (WTFP: wt_footprint ce (fpm_to_tenv fpm1) ty_src fp),
    sound_loan_analysis ce live2 (flow_loans le1 ty_src ty_tgt fk) fpm2
    /\ sound_region_relations ce live2 (flow_loans le1 ty_src ty_tgt fk) fpm2.
Proof.
  intros. split.
  - red. intros.
    destruct (RegionSet.mem r live1) eqn: LIVE_REG1.
    + eapply RegionSet.mem_2 in LIVE_REG1.
      exploit get_reachable_footprint_map_after_set; eauto.
      intros [A|(id1 & phl1 & phl2 & vs1 & A2 & A3 & A4)]; subst.
      (* Case 1: we do not touch the newly set footprint *)
      * erewrite fpm_to_orgm_after_set_footprint_map; eauto.
        erewrite fpm_to_tenv_after_set_footprint_map in WTPH0; eauto.
        exploit SOUND; eauto.
        intros (ls1 & B1 & (rph & B2) & B3). subst.
        (* easy: use flow_loans_monotonicity property *)
        assert (GE: exists ls2, (LOrgEnv.get r (flow_loans le1 ty_src ty_tgt fk)) = ls2 
                       /\ LOrgSt.ge ls2 (Live ls1)) by admit.
        admit.
      (* Case 2: we first reach the path that being set and then traverse the set footprint *)
      * assert (GET_FP1: get_reachable_footprint fpm1 phl2 fp = OK (fp_ref mut b ofs opt_ph vs)).
        (** This assertion is the most difficult part in proving the
      soundness of setting a footprint in an owner path because it
      relies on stack discipline invariant and the effect of shallow
      write (which is very subtle). *)
        admit.
        edestruct (wt_path_append_inv ce (id1,phl1) phl2) as (ty1 & WT1 & WT2); eauto.
        (* We should use sound_region_relations_path to relate [r] to
        the region in [ty_tgt] so that we can know how we update the
        loans in [r] in flow_loans (which only mention [ty_tgt]. *)
        (** How to know that we can get wt_projections_variance ty_tgt
      phl2? We should use wt_footprint and wt_fpm properties to say
      that (type_eq_except_origins ty1 ty_tgt) *)
        assert (TY_EQ1: type_eq_except_origins ty1 ty_tgt = true). admit.
        (* Since we can project ty1 we can also project ty_tgt and ty_src *)
        assert (PROJ_TY_TGT: exists r_tgt ty_tgt', wt_projections ce ty_tgt phl2 = OK (Treference r_tgt mut ty_tgt')) by admit.        
        destruct PROJ_TY_TGT as (r_tgt & ty_tgt' & PROJ_TY_TGT).
        assert (PROJ_TY_SRC: exists r_src ty_src', wt_projections ce ty_src phl2 = OK (Treference r_src mut ty_src')) by admit.
        destruct PROJ_TY_SRC as (r_src & ty_src' & PROJ_TY_SRC).
        (* Properties of the loans of r_src *)
        exploit SOUND_FP. eauto. eauto.
        intros (ls_src & B1 & (rph & B2) & B3). subst.
        exploit wt_path_has_variance. eapply WT1. intros (va1 & WTPH1).
        exploit wt_projections_has_variance. eapply WT2. instantiate (1 := va1).
        intros (va2 & WTPJ1).
        exploit wt_projections_has_variance. eapply PROJ_TY_TGT. instantiate (1 := va_tgt).
        intros (va_tgt' & PROJ_TY_TGT').
        (** TODO: Covariant here should adhere to fk  *)
        exploit wt_projections_has_variance. eapply PROJ_TY_SRC. instantiate (1 := Covariant).
        intros (va_src & PROJ_TY_SRC').
        (* Strategt: first show how loans of r_src are flowed into
        r_tgt by proving some properties of flow_loans; then use
        REG_SOUND_PH to derive the relation between r_tgt and r to
        show the properties of the loans in r *)
        exploit flow_loans_projections_spec. eapply TYEQ2. eauto. eauto. 
        instantiate (1 := le1).
        intros (C1 & C2).
        destruct (RegionSet.mem r_tgt live1) eqn: LIVE_REG2.
        -- eapply RegionSet.mem_2 in LIVE_REG2.
           erewrite (fpm_to_tenv_after_set_footprint_map fpm1 fpm2 ph) in *; eauto.
           exploit REG_SOUND_PH. eauto.
           eapply wt_path_variance_append. eapply WTPH1. eauto.
           eauto. auto. auto.
           intros REG_REL.
           unfold region_relation_wrt_variance in REG_REL.
           destr_if_with_name REG_REL VAR_EQ.
        (** Hard: What if both va_tgt' and va2 are Covariant? It only
        means that phl1 does not contain reference derefernce, so
        (id1, phl1) is equal to ph. "va_tgt' is Covariant" can further
        imply that the type [ph] is ty_tgt because if we get [ph] by
        traversing some deference of reference, we cannot get va_tgt
        is Covariant. So the only situtation is that the path of the
        assginee is an owner path. Then we have [ty_tgt = ty1] and
        then we have [r_tgt = r] *)
           ++ assert (HARD: r_tgt = r). admit.
              subst.
              admit.
           (* Since repr r_tgt = repr r, then this proof is the same as above *)
           ++ admit.           
        (** Hard: If r_tgt is not live at live1, it means that ph is a
        local variable because r_tgt is in ty_tgt. Then we can prove
        ph is a local variable. Our strategy here is to first show
        that (id1, phl1) must be the same as ph because fpm1 is
        constructed after invalidation w.r.t. shallow write on ph, so
        there must be no path reachable to ph. Then we can prove r =
        r_tgt so LIVE_REG1 is a contradiction. *)
        -- admit.
    (** If r is not live at live1, we should prove that ident of ph0
    must be the same as ph and ph must be a local variable because we
    do not allow overlapped regions in the types of different local
    variables. So GET_FP can be reduced to getting fp_ref from fp and
    then we can use SOUND_FP *)
    + admit.
  (* sound_region_relations *)
  - red. intros.
    exploit get_owner_path_map_after_set. eauto. eapply GET_PH1.
    intros G1.
    exploit get_owner_path_map_after_set. eauto. eapply GET_PH2.
    intros G2.
    erewrite (fpm_to_tenv_after_set_footprint_map fpm1 fpm2 ph) in *; eauto.    
    destruct (RegionSet.mem r1 live1) eqn: LIVE_REG1'.
    + eapply RegionSet.mem_2 in LIVE_REG1'.
      destruct (RegionSet.mem r2 live1) eqn: LIVE_REG2'.
      * eapply RegionSet.mem_2 in LIVE_REG2'.
        destruct G1 as [G1 | (id1 & phl11 & phl12 & vs11 & A12 & A13 & A14)].
        -- destruct G2 as [G2 | (id2 & phl21 & phl22 & vs21 & A22 & A23 & A24)].
           ++ exploit REG_SOUND. eapply G1. eapply G2.
              eapply WTPH1. eapply WTPH2. auto. auto.
              intros R.
              (* flow_loans does not change equality relation *)
              admit.
           ++ subst.
              (* strategy: we need to first establish the regions in
              the types of (id2, phl21) and the regions in ty_tgt
              using REG_SOUND_PH; then we can use REG_SOUND_FP to
              relate regions in (ph1 ++ phl) i.e., region [r1] and the
              regions in ty_src; then we can use the region relations
              established in flow_loans between ty_src and ty_tgt to
              relate regions in both of these types; then we can
              relate [r2] and its correspondence in ty_tgt *)              
              (* R1: r2 ~ r_tgt; R2: r1 ~ r_src; R3: r_src ~ r_tgt; 4. r1
              ~ r2 (derived from 1 to 3) *)
              assert (GET_FP1: get_reachable_path fpm1 phl22 fp = OK (ph0, vs21)).
              (** This assertion is the most difficult part in proving the
                  soundness of setting a footprint in an owner path because it
                  relies on stack discipline invariant and the effect of shallow
                  write (which is very subtle). *)              
              admit.
              exploit (wt_path_variance_append_inv ce (id2, phl21) (phl22 ++ phl)). 
              simpl. rewrite app_assoc. eapply WTPH2.
              intros (ty3 & va3 & WTPH21 & WTPH22).  
              (* This can be proved by wt_fpm *)
              assert (TY_EQ1: type_eq_except_origins ty3 ty_tgt = true). admit.
              (* Since we can project ty1 we can also project ty_tgt and ty_src *)
              assert (PROJ_TY_TGT: exists r_tgt ty_tgt' va_tgt', wt_projections_variance ce ty_tgt (phl22 ++ phl) va_tgt = OK (Treference r_tgt mut2 ty_tgt', va_tgt')) by admit.
              destruct PROJ_TY_TGT as (r_tgt & ty_tgt' & va_tgt' & PROJ_TY_TGT).
              assert (PROJ_TY_SRC: exists r_src ty_src' va_src', wt_projections_variance ce ty_src (phl22 ++ phl) Covariant = OK (Treference r_src mut2 ty_src', va_src')) by admit.
              destruct PROJ_TY_SRC as (r_src & ty_src' & va_src' & PROJ_TY_SRC). 
              destruct (RegionSet.mem r_tgt live1) eqn: LIVE_REG_TGT.
              ** eapply RegionSet.mem_2 in LIVE_REG_TGT.
                 exploit REG_SOUND_PH. eauto. 
                 eapply wt_path_variance_append. eapply WTPH21. eauto. eauto. auto. auto.
                 intros R1.
                 exploit REG_SOUND_FP. eauto. eauto. eauto. eauto. auto.
                 intros R2.
                 exploit flow_loans_projections_spec. eapply TYEQ2. eauto. 
                 eapply wt_projections_variance_imply; eauto.
                 instantiate (1 := le1).
                 intros (GE & R3).
                 (* We can only consider either va1 or va2 is
                 Invariant. The difficult case is va_src' = Covariant
                 then we cannot relate r_src and r_tgt; But we should
                 prove that if va_src' = Covariant then we can prove
                 that (phl22 ++ phl) does not contain deref of
                 reference. *)
                 admit.
              (* r_tgt is dead *)
              ** admit.
        -- destruct G2 as [G2 | (id2 & phl21 & phl22 & vs21 & A22 & A23 & A24)].
           (* Similar to above *)
           ++ admit.
           (** Hard Two reachable paths pass ph *)
           ++ admit.
      (* r2 is dead *)
      * admit.
    (* r1 is dead *)
    + admit.
Admitted.


(* Properties of Kildall solution *)
Lemma loans_flow_analyze_successor: forall entry cfg pc1 instr pc2 f live LoansEnv le2
    (AN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TR: transfer ce f cfg live (regset_fun f) pc1 (LoansEnv !! pc1) = le2),
    LoansEnv.ge (LoansEnv !! pc2) le2.
Proof.
  unfold loans_flow_analyze; intros. 
  destr_if_with_name AN LIVE.
  destr_if_with_name AN LOANS.
  inv AN.
  eapply LoansFlow.fixpoint_solution; try intro; simpl; eauto.
Qed.

Lemma LoansEnv_ge_inv: forall le1 st2,
    LoansEnv.ge le1 (LoansEnv.State st2) ->
    exists st1, le1 = LoansEnv.State st1 /\ LOrgEnv.ge st1 st2.
Proof.
  intros. destruct le1; simpl in H; try contradiction; eauto.
Qed.

Lemma region_liveness_analyze_successor: forall entry cfg pc1 instr pc2 f live LoansEnv live1
    (AN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TR: RegionLiveness.transfer f cfg (regset_fun f) pc2 (live !! pc2) = live1),
    RegionSetLat.ge (live !! pc1) live1.
Proof.
  unfold loans_flow_analyze; intros. 
  destr_if_with_name AN LIVE.
  destr_if_with_name AN LOANS.
  inv AN.
  eapply RegionLive.fixpoint_solution; try intro; simpl; eauto.
  intros. unfold RegionLiveness.transfer. rewrite H. reflexivity.
Qed.


Ltac simpl_getIM IM :=
  generalize IM as IM1; intros;
  inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst;
  try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *.

Lemma step_preservation: forall s1 t s2,
    sound_state s1 ->
    Step L s1 t s2 ->
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP. inv STEP.
  (* Sassign *)
  - inv SOUND. inv BORCK_STMT.
    (* unfold move check and borrow check result. TODO: write ltac for these unfold code *)
    (* simpl in TR. simpl_getIM IM. *)
    (* destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence. *)
    (* unfold move_check_expr in MOVE1. *)
    (* destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence. *)
    (* destruct p0 as (mayinit' & mayuninit'). *)
    (* destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence. *)
    (* inv TR. *)
    simpl in TR. rewrite LOANS_ST in TR. 
    unfold BorrowCheckPolonius.borrow_check_stmt, borrow_check_stmt_aux, check_assignment in TR.
    monadInv TR. monadInv EQ.
    rename EQ0 into BORCK_EXPR. rename EQ1 into BORCKP.
    (* end of unfold *)
    set (live_st := (RegionLiveness.transfer f cfg (regset_fun f) pc live !! pc)) in *.
    set (loans_env1 := (LOrgEnv.apply_liveness live_st loans_env)) in *.
    assert (LIVE_EQ: live_st = reg_expr_live e (reg_assign_place p (live!!pc))).
    { unfold live_st. unfold RegionLiveness.transfer. rewrite SEL.
      rewrite STMT. reflexivity. }
    (* soundness w.r.t. apply_liveness *)
    assert (BORROW_APPRO1: sound_loan_analysis ce live_st loans_env1 fpm1).
    { admit. }
    (* soundness of eval_expr *)
    unfold eval_assign in EVAL.
    monadInv EVAL. destruct x3 as (ph1 & vs). monadInv EQ2.
    destruct x; destruct x0.
    exploit eval_expr_preserves_borchk_approx; eauto.
    (* wt_expr *) admit.
    intros (BORROW_APPRO2 & BORROW_APPRO2_FP).
    (* soundness w.r.t. to invalidate_fp_ref *)
    set (fpm1' := (invalidate_conflict_ref_fpm p AWrite Ashallow x2)) in *.
    set (fp1' := (invalidate_conflict_ref p AWrite Ashallow x1)) in *.
    unfold check_shallow_write_place in BORCKP. destr_if_with_name BORCKP ILLP.    
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx in BORROW_APPRO2 as BORROW_APPRO3.
    2: eauto.
    eapply invalidate_conflict_ref_preserves_borchk_approx in BORROW_APPRO2_FP as BORROW_APPRO3_FP. 
    2: eauto.    
    (* soundness w.r.t. before_write_place *)
    set (le2:= (kill_loans (transfer_expr loans_env1 e) p)).
    exploit before_write_place_sound; eauto. intros (BORROW_APPRO4 & BORROW_APPRO4_FP).  
    (* soundness w.r.t. flow_loans *)
    set (le3:= flow_loans le2 (typeof e) (typeof_place p) Covariant).    
    (* type checking result *)
    assert (WTPH: exists va, wt_path_variance ce (fpm_to_tenv fpm2) p = OK (typeof_place p, va)) by admit.
    destruct WTPH as (va & WTPH).
    (* getting path from wt_fpm is well typed *)
    assert (WT_ASS_PH: exists ty, wt_path ce (fpm_to_tenv fpm2) ph = OK ty /\ type_eq_except_origins ty (typeof_place p) = true). admit.
    destruct WT_ASS_PH as (ph_ty & WT_ASS_PH & TYEQ1).
    (** Difficult  *)
    exploit flow_loans_sound. eauto. eauto.
    (** TODO: soundness of region relations  *)
    admit. admit.
    2: eauto.
    instantiate (1 := va). instantiate (1 := typeof_place p).
    admit.                      (* soundness of region relations derived from before_write_place *)
    admit.                      (* result of clear_footprint *)
    eapply WT_ASS_PH. auto.
    admit.                      (* type checking result *)
    admit.                      (* wt_fpm *)
    admit.                      (* wt_footprint *)
    instantiate (1 := Covariant). instantiate (1 := live !! pc).
    intros (BORROW_APPRO5 & BORROW_REL_APPRO5).
    
    (* Start to prove local sound-approximation of one step transition *)
    exploit loans_flow_analyze_successor; eauto. left. reflexivity.
    unfold transfer. rewrite SEL, LOANS_ST, STMT. intros GE1. 
    edestruct LoansEnv_ge_inv as (le4 & A1 & GE2); eauto.
    econstructor. eauto.
    econstructor. eauto. eauto. eauto.
    eapply sound_loan_analysis_liveness_monotonicity.
    2: { eapply region_liveness_analyze_successor; eauto. left. auto. }
    eapply sound_loan_analysis_monotonicity. eapply GE2. eauto.
          
  - admit.
  - admit.
    (* Sdrop *)
  - admit.
  (* storagelive *)
  - admit.
  (* storagedead *)
  - admit.
  (* Scall *)
  - unfold generate_call_parameters in REF_OUT.
    rename phl into cutpoints.
    monadInv REF_OUT.
    

Admitted.
    

End BORROW_CHECK.

End ADT_ENV.
