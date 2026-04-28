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


Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation fp_graph := (@fp_graph ame).
Notation get_owner_path_map := (@get_owner_path_map ame).
Notation cont := (@cont ame).
Notation state := (@state ame).

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

(* We also need to know that generic region this path locates
at....  *)
Definition extern_loc_region (orgm: PTree.t (option origin)) (ph: path) : option origin :=
  let (id, pj) := ph in
  match orgm ! id with
  | Some r =>
      r
  | _ => None
  end.

Definition mutability_match (ref_mut loan_mut: mutkind) : Prop :=
  match ref_mut, loan_mut with
  | Mutable, Mutable => True
  (* If this reference is immutable reference, than we do not need to
  care the how we create this loan *)
  | Immutable, _ => True
  | _, _ => False
  end.

Definition loan_approx (orgm: PTree.t (option origin)) (ln: loan) (ref_mut: mutkind) (ph: path) : Prop :=
  match ln, extern_loc_region orgm ph with
  | Lintern loan_mut p, None =>
      (** Note: mut is the precise mutability of the reference we are focusing. *)
      (* TODO: maybe we should use path uniformly *)
      let (id1, pj1) := path_of_place p in
      let (id2, pj2) := ph in
      id1 = id2 /\ projections_contain pj1 pj2 = true /\ mutability_match ref_mut loan_mut
  | Lextern org1, Some org2 =>
      org1 = org2 
  | _, _ => False
  end.

Definition loans_approx_views (orgm: PTree.t (option origin)) (ls: LoanSet.t) (ref_mut: mutkind) (vs: views) : Prop :=
  forall vph, In vph vs ->
         exists ln, LoanSet.In ln ls /\ loan_approx orgm ln ref_mut vph.

Definition fpm_to_orgm (fpm: fp_map) : PTree.t (option origin) :=
  PTree.map1 (fun '(_,_,r,_,_) => r) fpm.


(* Why do we need region liveness here? *)
Definition sound_loan_analysis ce (live: RegionSet.t) (le: LOrgEnv.t) (fpm: fp_map) : Prop :=
  forall ph owner_ph opt_ph vs1 vs2 mut b ofs r ty
    (* If we make these two get_xxx as assumptions, how can we use
    this approximation property to prove progress, i.e., how to prove
    these two assumptions. For example, when we prove the progress in
    eval_pexpr on Eplace, the two get functions can be proved to make
    progress by using induciton, this approximation property and
    property about "all owners pointed by reference is init" *)
    (GET_PH: get_owner_path_map ph fpm = OK (owner_ph, vs1))
    (GET_FP: get_owner_footprint_map owner_ph fpm = OK (fp_ref mut b ofs opt_ph vs2))
    (WTPH: wt_path ce (fpm_to_tenv fpm) ph = OK (Treference r mut ty))
    (LIVE_REG: RegionSet.In r live),
    (* live region contains valid loans *)
    exists ls, LOrgEnv.get r le = Live ls
    (* Safety: this reference is not invalidated *)
    /\ (exists rph, opt_ph = Some rph)
    (* Approximation: all (mutable) paths in the vs2 are approximated
    in the loans map *)
    /\ loans_approx_views (fpm_to_orgm fpm) ls mut vs2.


(* For temporary values *)
Definition sound_loan_analysis_footprint ce (le: LOrgEnv.t) (fpm: fp_map) (fp: footprint) (ty: type) : Prop :=
  forall phl opt_ph vs mut b ofs r ty
    (GET_FP: get_reachable_footprint fpm phl fp = OK (fp_ref mut b ofs opt_ph vs))
    (WT_PROJS: wt_projections ce ty phl = OK (Treference r mut ty)),
    (* live region contains valid loans *)
    exists ls, LOrgEnv.get r le = Live ls
    (* Safety: this reference is not invalidated *)
    /\ (exists rph, opt_ph = Some rph)
    (* Approximation: all (mutable) paths in the vs are approximated
    in the loans map *)
    /\ loans_approx_views (fpm_to_orgm fpm) ls mut vs.

Definition sound_loan_analysis_footprint_list ce (le: LOrgEnv.t) (fpm: fp_map) (fpl: list footprint) (tyl: list type) : Prop :=
  Forall2 (sound_loan_analysis_footprint ce le fpm) fpl tyl.


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
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s pc next cont brk nret k fpm mayinit mayuninit live live_st LoansEnv loans_env ns sup
    (* The init and loans-flow analysis results *)
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The result of move checking and borrow checking *)
    (MCK_STMT: move_check_stmt_spec (maybeInit, maybeUninit, universe) f.(fn_body) cfg s s (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt_spec (live, LoansEnv) (regset_fun f) f cfg s s (mk_cfg_info pc next cont brk nret))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k (mk_cfg_kinfo next cont brk nret))
    (* Over-approximation of the move checking. *)
    (INIT_APPRO: sound_init_analysis fpm mayinit mayuninit universe)
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


Lemma get_owner_footprint_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ak am fp,
    get_owner_footprint_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK fp ->
    exists fp', get_owner_footprint_map ph1 fpm = OK fp'
           /\ invalidate_conflict_ref ph2 ak am fp' = fp.
Admitted.

Lemma get_owner_path_map_after_invalidate_ref: forall (fpm: fp_map) ph1 ph2 ph vs ak am,
    get_owner_path_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK (ph, vs) ->
    get_owner_path_map ph1 fpm = OK (ph, vs).    
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

Hint Resolve get_owner_footprint_map_after_invalidate_ref
             get_owner_path_map_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref: invalidate_fp_ref.

Hint Rewrite get_owner_footprint_map_after_invalidate_ref
             get_owner_path_map_after_invalidate_ref
             fpm_to_orgm_after_invalidate_ref
             fpm_to_tenv_after_invalidate_ref: invalidate_fp_ref.


(** invalidation of fp_ref preserves sound approximation invariant *)

Lemma illegal_access_false_implies: forall le p am ak r ls,
    illegal_access le p am ak = false ->
    LOrgEnv.get r le = Live ls ->
    conflict p ls am ak = false.
Proof.
  intros until ls. intros ILL.
  unfold illegal_access in ILL.
  erewrite PTree_Properties.exists_false in ILL. 
  unfold LOrgEnv.get.
  destruct (LOrgEnv.m le) ! (UnionFindDelete.UFD.repr (LOrgEnv.uf le) r) eqn: A; auto.  
  - intros. subst. 
    eapply ILL in A. unfold illegal_access_in_origin_state in A. 
    destruct conflict; try congruence.
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
  exploit get_owner_path_map_after_invalidate_ref; eauto. intros GET_PH1.
  (** The most important property we need to prove is that opt_ph in
  GET_FP may not be the same as the opt_ph in fpm because of the
  invalidation, but we need to prove that they are the same using the
  checking result of [illegal_access] *)  
  exploit (@get_owner_footprint_map_after_invalidate_ref); eauto.
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
Lemma sound_loan_analysis_liveness_refine: forall live1 live2 le fpm,
    sound_loan_analysis ce live2 le fpm ->
    RegionSet.Subset live1 live2 ->
    sound_loan_analysis ce live1 le fpm.
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

(** evaluation of expression preserves invariant *)

Lemma eval_pexpr_preserves_borchk_approx: forall pe fpm1 fpm2 live le vfp
  (BORROW_APPROX: sound_loan_analysis ce (reg_pexpr_live pe live) le fpm1)
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
    eapply sound_loan_analysis_liveness_refine; eauto. 
    admit.                          (* region liveness inclusion *)
  (* cktag *)
  - monadInv EVAL. 
    destruct x2; try congruence. inv EQ2.
    simpl in BORROW_APPROX; split; [eauto| try eapply sound_loan_analysis_footprint_trivial; eauto].
    simpl in BORROW_CHECK.
    destr_if_with_name BORROW_CHECK ILL_ACCESS.
    eapply invalidate_conflict_ref_fpm_preserves_borchk_approx; eauto.
    eapply sound_loan_analysis_liveness_refine; eauto.
    admit.                      (* liveness inclusion *)
  (** Eref *)
  - simpl in BORROW_CHECK. 
    destr_if_with_name BORROW_CHECK ILL.
    inv WT.
    monadInv EVAL. 
    destruct x1 as (b & ofs). inv EQ2.
    admit.
    
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
  (BORROW_APPROX: sound_loan_analysis ce (reg_expr_live e live) le fpm1)
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
    split; auto.
    eapply sound_loan_analysis_liveness_refine; eauto. admit.
  - eapply eval_pexpr_preserves_borchk_approx; eauto.
    inv WT. auto.
Admitted.

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
  - inv SOUND. inv MCK_STMT. inv BORCK_STMT.
    (* unfold move check and borrow check result. TODO: write ltac for these unfold code *)
    simpl in TR. simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    simpl in TR0. rewrite LOANS_ST in TR0. 
    unfold BorrowCheckPolonius.borrow_check_stmt, borrow_check_stmt_aux, check_assignment in TR0.
    monadInv TR0. monadInv EQ.
    rename EQ0 into BORCK_EXPR. rename EQ1 into BORCKP.
    (* end of unfold *)
    set (live_st := (RegionLiveness.transfer f cfg (regset_fun f) pc live !! pc)) in *.
    set (loans_env1 := (LOrgEnv.apply_liveness live_st loans_env)) in *.
    assert (LIVE_EQ: live_st = reg_expr_live e (reg_assign_place p (live!!pc))).
    { unfold live_st. unfold RegionLiveness.transfer. rewrite SEL.
      rewrite STMT. reflexivity. }
    (** how to show that the regions in [e] and [p] are live, so that
    we can use the borrow check invariant *)
    (* evaluate expr *)
    exploit eval_expr_match. eauto. eapply MPRED. 
    eapply BORCK_INV. all: eauto. admit.
    intros (tv & tfp & fpm2 & mp1 & mp2 & TEVAL & FPMEQ & WTVAL & MEQ1 & COH1 & A1 & A2).
    (* evaluate assignee place: before that, we need to prove moving a
    place in the evaluation of expression preserve the borrow check
    invariant for the sv_map and fp_map *)

Admitted.

