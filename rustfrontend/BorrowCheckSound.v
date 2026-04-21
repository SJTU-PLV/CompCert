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
Require Import RustIRspec.
Require Import RustOp RustIR RustIRcfg Rusttyping.
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



Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation fp_graph := (@fp_graph ame).
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

Let move_check_stmt (ae: INIT_AN) body cfg s ts := match_stmt get_init_info ae (move_check_stmt ce) (check_cond_expr ce) body cfg s ts.

(* Result of the loans-flow analysis and the result of the borrow
checking *)

Let LOANS_AN : Type := (PMap.t RegionSet.t * PMap.t LoansEnv.t).

Let borrow_check_stmt (ae: LOANS_AN) regs f cfg s ts := match_stmt (get_borck_result regs f cfg) ae (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg s ts.

(** Over-approximation of the borrow analysis. Note that this
definition is not specific to which borrow checking algorithms you
use, e.g., NLL or Polonius, because we just use their final result of
the compuation, i.e., both of them compute active loans at each point
of the program. *)

(* We also need to know that generic region this path locates
at....  *)
Definition extern_loc_region (fpm: fp_map) (ph: path) : option origin :=
  let (id, pj) := ph in
  match fpm ! id with
  | Some (_, _, r, _, _) =>
      r
  | _ => None
  end.

Definition loan_approx (fpm: fp_map) (ln: loan) (ph: path) : Prop :=
  match ln, extern_loc_region fpm ph with
  | Lintern _ p, None =>
      (* TODO: maybe we should use path uniformly *)
      let (id1, pj1) := path_of_place p in
      let (id2, pj2) := ph in
      id1 = id2 /\ projections_contain pj1 pj2 = true
  | Lextern org1, Some org2 =>
      org1 = org2 
  | _, _ => False
  end.

Definition sound_loan_analysis ce (le: LOrgEnv.t) (fpm: fp_map) : Prop :=
  forall ph owner_ph opt_ph vs1 vs2 mut b ofs r ty ls,
    (* If we make these two get_xxx as assumptions, how can we use
    this approximation property to prove progress, i.e., how to prove
    these two assumptions. For example, when we prove the progress in
    eval_pexpr on Eplace, the two get functions can be proved to make
    progress by using induciton, this approximation property and
    property about "all owners pointed by reference is init" *)
    get_owner_path_map ph fpm = OK (owner_ph, vs1) ->
    get_owner_footprint_map owner_ph fpm = OK (fp_ref mut b ofs opt_ph vs2) ->
    wt_path ce (fpm_to_tenv fpm) ph = OK (Treference r mut ty) ->
    (* We use loans map to tell if r is live or not instead of using
    the liveness set because we need the loans set of this region *)
    LOrgEnv.get r le = Live ls ->
    (* Safety: this reference is not invalidated *)
    (exists rph, opt_ph = Some rph)
    /\ (* Approximation: all (mutable) paths in the vs2 are
    approximated in the loans map *)
      (forall vph, In vph vs2 ->
              exists ln, LoanSet.In ln ls /\ loan_approx fpm ln vph).


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

Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s ts pc next cont brk nret k fpm mayinit mayuninit live LoansEnv loans_env ns sup
    (* The init and loans-flow analysis results *)
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The result of move checking and borrow checking *)
    (MCK_STMT: move_check_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s ts (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt (live, LoansEnv) (regset_fun f) f cfg s ts (mk_cfg_info pc next cont brk nret))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (* (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k (mk_cfg_kinfo next cont brk nret) bor_stk fpf) *)
    (*Over-approximation of the move checking. *)
    (INIT_APPRO: sound_init_analysis fpm mayinit mayuninit universe)
    (* Over-approximation of the borrow checking *)
    (BORROR_APPRO: sound_loan_analysis ce loans_env fpm),
    sound_state (State f s k ns fpm sup).


| sound_dropstate: forall id co fp b ofs st m membs k fpf bor_stk MP fpm ph
    (CO: ce ! id = Some co)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned)
    (* The location of the dropped place *)
    (GFP: get_owner_loc_footprint_map ph fpm = Some (b, Ptrofs.unsigned ofs, fp))
    (* drop_member_footprint says that fp matches (co, st, membs) *)
    (DROPMEMB: drop_member_footprint id co fp st membs)
    (CONT: sound_drop_cont k bor_stk (fpf_func fpm fpf))
    (** We cannot remove the element from fpl because it would make the
    location (b, ofs) not freeable anymore! *)
    (* fpl1 is the locations that have been dropped *)
    (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP)
    (MPRED: m |= MP),
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    sound_state (Dropstate id (Vptr b ofs) st membs k bor_stk m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k bor_stk VMP MP
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL_LIST: sem_wt_val_list ce fpl args VMP)
    (* Used in assign_loc_sound in function entry proof *)
    (ANORM: val_casted_list args tyargs)
    (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl)
    (COHERENT: coherent_fpf ce fpf MP)
    (MPRED: m |= VMP ** MP)
    (STK: sound_stacks k bor_stk fpf),
    (** TODO: borrow check invariant is missing at function call *)
    (* also disjointness of fpl and fpf *)
    sound_state (Callstate vf args k bor_stk m)
| sound_returnstate: forall sg fpf m k retty rfp v bor_stk VMP MP
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = retty)
    (WTVAL: sem_wt_val ce rfp v VMP)
    (CAST: val_casted v retty)
    (WTFP: wt_footprint ce retty rfp)
    (COHERENT: coherent_fpf ce fpf MP)
    (MPRED: m |= VMP ** MP)    
    (STK: sound_stacks k bor_stk fpf),
    (** TODO: borrow check invariant is missing at function return *)
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)), *)
    sound_state (Returnstate v k bor_stk m)
.
