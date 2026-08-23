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
Require Import MapsMisc.
Require Import RustIRspec.

Import ListNotations.

Local Open Scope error_monad_scope.

(** A variant of [RustIRspec] in which evaluated values cross statement and
    function boundaries through fresh temporary entries in the local store. *)

(** ** Centralized local-store operations *)

(** Temporary entries have no concrete location. *)
Definition temporary_entry (ty: type) (fp: footprint)
    : block * Z * type * footprint :=
  (1%positive, 0%Z, ty, fp).

Definition save_temporary (fpm: fp_map) (ty: type) (fp: footprint)
    : res (ident * fp_map) :=
  let tmp := FreshMax.fresh fpm in
  OK (tmp, PTree.set tmp (temporary_entry ty fp) fpm).

Definition save_temporaries (fpm: fp_map) (tys: list type)
    (fps: list footprint) : res (list ident * fp_map) :=
  if Nat.eqb (length tys) (length fps) then
    let tmps := FreshMax.fresh_idents fpm (length fps) in
    let entries := map (fun '(ty, fp) => temporary_entry ty fp)
                       (combine tys fps) in
    OK (tmps, set_fresh_list fpm entries)
  else Error (msg "temporary type/value arity mismatch").

Definition eval_expr_save_plain (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (e: expr) : res (ident * fp_map) :=
  do (fp, fpm1) <- eval_expr fidx ce fpm e;
  save_temporary fpm1 (typeof e) fp.

Definition eval_expr_save_variant (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (e: expr) (orgs: list origin) (enum_id fid: ident)
    (tag fofs: Z) : res (ident * fp_map) :=
  do (fp, fpm1) <- eval_expr fidx ce fpm e;
  save_temporary fpm1 (Tvariant orgs enum_id)
    (fp_enum enum_id tag fid fofs fp).

Definition eval_expr_save_box (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (e: expr) (ty: type) (b: block)
    : res (ident * fp_map) :=
  do (fp, fpm1) <- eval_expr fidx ce fpm e;
  save_temporary fpm1 (Tbox ty) (fp_box b fp).

Definition eval_exprlist_save (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (el: list expr) : res (list ident * fp_map) :=
  do (fps, fpm1) <- eval_exprlist fidx ce fpm el;
  save_temporaries fpm1 (map typeof el) fps.

Definition take_temporary (fpm: fp_map) (tmp: ident)
    : res (footprint * fp_map) :=
  do fp <- get_owner_footprint_map (tmp, nil) fpm;
  OK (fp, PTree.remove tmp fpm).

Fixpoint take_temporaries (fpm: fp_map) (tmps: list ident)
    : res (list footprint * fp_map) :=
  match tmps with
  | nil => OK (nil, fpm)
  | tmp :: tmps1 =>
      do (fp, fpm1) <- take_temporary fpm tmp;
      do (fps, fpm2) <- take_temporaries fpm1 tmps1;
      OK (fp :: fps, fpm2)
  end.

Definition shallow_clear_place (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (p: place) : res (path * fp_map) :=
  let ps := enc_path fidx p in
  let fpm1 := invalidate_conflict_ref_fpm ps AWrite Ashallow fpm in
  do (ph, vs) <- get_owner_path_map ps fpm1;
  do dropped <- check_path_is_dropped fpm1 ph;
  if dropped then
    do fpm2 <- clear_footprint_map ce ph fpm1;
    OK (ph, kill_views_ref_fpm vs fpm2)
  else Error (msg "assignment target is not dropped").

Definition drop_place (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (p: place) : res fp_map :=
  let ps := enc_path fidx p in
  let fpm1 := invalidate_conflict_ref_fpm ps AWrite Adeep fpm in
  do droppable <- check_path_is_droppable fpm1 ps;
  if droppable then clear_footprint_map ce ps fpm1
  else Error (msg "drop target is not droppable").

Definition write_remove_temp (fpm: fp_map)
    (tmp: ident) (ph: path) : res fp_map :=
  do fp <- get_owner_footprint_map (tmp, nil) fpm;
  do fpm1 <- set_footprint_map ph fp fpm;
  OK (PTree.remove tmp fpm1).

Definition storage_dead (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (id: ident) : res fp_map :=
  do dropped <- check_path_is_dropped fpm (enc_path fidx (id, nil));
  if dropped then clear_footprint_map ce (enc_path fidx (id, nil)) fpm
  else Error (msg "dead local is not dropped").

(** ** Function-boundary operations *)

Definition function_entry_from_temporaries (ce: composite_env) (f: function)
    (tmps: list ident) (fpm: fp_map) (fidx: frame_idx) (sup: Mem.sup)
    : res (fp_map * Mem.sup) :=
  do (args, fpm1) <- take_temporaries fpm tmps;
  function_entry ce f args fpm1 fidx sup.

Definition function_exit_to_temporary (f: function) (tmp: ident)
    (fpm: fp_map) (fidx: frame_idx) : res fp_map :=
  do tmp_fp <- get_owner_footprint_map (tmp, nil) fpm;
  let paths := vars_to_paths fidx (f.(fn_vars) ++ f.(fn_params)) in
  let fpm1 := invalidate_conflict_ref_fpm_list paths AWrite Ashallow fpm in
  let fpm2 := kill_views_ref_fpm paths fpm1 in
  OK (pop_stack fpm2 fidx (f.(fn_vars) ++ f.(fn_params))).

(** ** Program states *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (fpm: fp_map)
    (fidx: frame_idx)
    (sup: Mem.sup) : state
| Callstate
    (fun_id: ident)
    (args: list ident)
    (fpm: fp_map)
    (fidx: frame_idx)
    (sup: Mem.sup)
    (k: cont) : state
| Returnstate
    (retv: ident)
    (fpm: fp_map)
    (fidx: frame_idx)
    (sup: Mem.sup)
    (k: cont) : state.

Section SMALLSTEP.

Variable ge: genv.

Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e (p: place) tmp fpm1 fpm2 fpm3 fpm4 ph k sup fidx
    (EVAL: eval_expr_save_plain ge fidx fpm1 e = OK (tmp, fpm2))
    (SHALLOW: shallow_clear_place ge fidx fpm2 p = OK (ph, fpm3))
    (WRITE: write_remove_temp fpm3 tmp ph = OK fpm4),
    step (State f (Sassign p e) k fpm1 fidx sup) E0
         (State f Sskip k fpm4 fidx sup)
| step_assign_variant: forall f e (p: place) k fpm1 fpm2 fpm3 fpm4 tmp ph
    co fid enum_id orgs fty fidx sup fofs tag
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK fty)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (EVAL: eval_expr_save_variant ge fidx fpm1 e orgs enum_id fid tag fofs =
           OK (tmp, fpm2))
    (SHALLOW: shallow_clear_place ge fidx fpm2 p = OK (ph, fpm3))
    (WRITE: write_remove_temp fpm3 tmp ph = OK fpm4),
    step (State f (Sassign_variant p enum_id fid e) k fpm1 fidx sup) E0
         (State f Sskip k fpm4 fidx sup)
| step_box: forall f e (p: place) k ty fpm1 fpm2 fpm3 fpm4 tmp ph fidx sup
    (TYP: typeof_place p = Tbox ty)
    (EVAL: eval_expr_save_box ge fidx fpm1 e ty (Mem.fresh_block sup) =
           OK (tmp, fpm2))
    (SHALLOW: shallow_clear_place ge fidx fpm2 p = OK (ph, fpm3))
    (WRITE: write_remove_temp fpm3 tmp ph = OK fpm4),
    step (State f (Sbox p e) k fpm1 fidx sup) E0
         (State f Sskip k fpm4 fidx (Mem.sup_incr sup))
| step_drop: forall fpm1 fpm2 k f (p: place) fidx sup
    (DROP: drop_place ge fidx fpm1 p = OK fpm2),
    step (State f (Sdrop p) k fpm1 fidx sup) E0
         (State f Sskip k fpm2 fidx sup)
| step_storagelive: forall f k fidx fpm id sup,
    step (State f (Sstoragelive id) k fpm fidx sup) E0
         (State f Sskip k fpm fidx sup)
| step_storagedead: forall f k fidx fpm1 fpm2 id sup
    (DEAD: storage_dead ge fidx fpm1 id = OK fpm2),
    step (State f (Sstoragedead id) k fpm1 fidx sup) E0
         (State f Sskip k fpm2 fidx sup)
| step_call: forall f ty al k tyargs fd cconv tyres p orgs org_rels
    fun_id fpm1 fpm2 args fidx sup
    (CASE: classify_fun ty = fun_case_f tyargs tyres cconv)
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (EVAL: eval_exprlist_save ge fidx fpm1 al = OK (args, fpm2))
    (NOT_DROP: function_not_drop_glue fd),
    step (State f (Scall p (Eglobal fun_id ty) al) k fpm1 fidx sup) E0
         (Callstate fun_id args fpm2 fidx sup (Kcall p f k))
| step_internal_function: forall fun_id vargs k fpm1 fpm2 f fidx sup1 sup2
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry_from_temporaries ge f vargs fpm1
              (fidx + 1)%positive sup1 = OK (fpm2, sup2)),
    step (Callstate fun_id vargs fpm1 fidx sup1 k) E0
         (State f f.(fn_body) k fpm2 (fidx + 1)%positive sup2)
| step_return_1: forall p tmp fpm1 fpm2 fpm3 f k ck fidx sup
    (CONT: call_cont k = Some ck)
    (EVAL: eval_expr_save_plain ge fidx fpm1
              (Emoveplace p (typeof_place p)) = OK (tmp, fpm2))
    (EXIT: function_exit_to_temporary f tmp fpm2 fidx = OK fpm3),
    step (State f (Sreturn p) k fpm1 fidx sup) E0
         (Returnstate tmp fpm3 (fidx - 1)%positive sup ck)
| step_returnstate: forall (p: place) tmp fpm1 fpm2 fpm3 ph f k fidx sup
    (SHALLOW: shallow_clear_place ge fidx fpm1 p = OK (ph, fpm2))
    (WRITE: write_remove_temp fpm2 tmp ph = OK fpm3),
    step (Returnstate tmp fpm1 fidx sup (Kcall p f k)) E0
         (State f Sskip k fpm3 fidx sup)
| step_seq: forall f s1 s2 k fpm fidx sup,
    step (State f (Ssequence s1 s2) k fpm fidx sup) E0
         (State f s1 (Kseq s2 k) fpm fidx sup)
| step_skip_seq: forall f s k fpm fidx sup,
    step (State f Sskip (Kseq s k) fpm fidx sup) E0
         (State f s k fpm fidx sup)
| step_continue_seq: forall f s k fpm fidx sup,
    step (State f Scontinue (Kseq s k) fpm fidx sup) E0
         (State f Scontinue k fpm fidx sup)
| step_break_seq: forall f s k fpm fidx sup,
    step (State f Sbreak (Kseq s k) fpm fidx sup) E0
         (State f Sbreak k fpm fidx sup)
| step_ifthenelse: forall f a s1 s2 k fpm1 fpm2 v b sup fidx
    (EVAL: eval_pexpr fidx fpm1 a = OK (fp_scalar Mint8unsigned v, fpm2))
    (BOOL: bool_val v (typeof a) = Some b),
    step (State f (Sifthenelse (Epure a) s1 s2) k fpm1 fidx sup) E0
         (State f (if b then s1 else s2) k fpm2 fidx sup)
| step_loop: forall f s k fpm fidx sup,
    step (State f (Sloop s) k fpm fidx sup) E0
         (State f s (Kloop s k) fpm fidx sup)
| step_skip_or_continue_loop: forall f s k fpm fidx x sup
    (SKIP_CONT: x = Sskip \/ x = Scontinue),
    step (State f x (Kloop s k) fpm fidx sup) E0
         (State f s (Kloop s k) fpm fidx sup)
| step_break_loop: forall f s k fpm fidx sup,
    step (State f Sbreak (Kloop s k) fpm fidx sup) E0
         (State f Sskip k fpm fidx sup)
.

(** The query/reply payloads remain exactly those of [RustIRspec]. *)
Definition li_rs_spec : language_interface := RustIRspec.li_rs_spec.

Inductive initial_state: (query li_rs_spec) -> state -> Prop :=
| initial_state_intro: forall f targs tres tcc vargs orgs org_rels fun_id
    fpm1 fpm2 fidx sup args
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (TYF: type_of_function f = Tfunction orgs org_rels targs tres tcc)
    (NOTDROP: f.(fn_drop_glue) = None)
    (SAVE: save_temporaries fpm1 (type_list_of_typelist targs) vargs =
           OK (args, fpm2)),
    initial_state
      (RustIRspec.rspec_q fun_id
        (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge)
        vargs fpm1 fidx sup)
      (Callstate fun_id args fpm2 fidx sup Kstop).

Inductive at_external: state -> (query li_rs_spec) -> Prop :=
| at_external_intro: forall fun_id name args vargs k targs tres cconv
    orgs org_rels fpm1 fpm2 fidx sup
    (FINDF: ge.(genv_defmap) ! fun_id =
      Some (Gfun (External orgs org_rels
        (EF_external name (signature_of_type targs tres cconv))
        targs tres cconv)))
    (TAKE: take_temporaries fpm1 args = OK (vargs, fpm2)),
    at_external (Callstate fun_id args fpm1 fidx sup k)
      (RustIRspec.rspec_q fun_id
        (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge)
        vargs fpm2 fidx sup).

Inductive after_external: state -> (reply li_rs_spec) -> state -> Prop :=
| after_external_intro: forall fun_id name args k targs tres cconv orgs org_rels
    fpm1 fpm2 fpm3 fidx1 fidx2 v tmp sup1 sup2
    (FINDF: ge.(genv_defmap) ! fun_id =
      Some (Gfun (External orgs org_rels
        (EF_external name (signature_of_type targs tres cconv))
        targs tres cconv)))
    (SAVE: save_temporary fpm2 tres v = OK (tmp, fpm3)),
    after_external
      (Callstate fun_id args fpm1 fidx1 sup1 k)
      (RustIRspec.rspec_r v fpm2 fidx2 sup2)
      (Returnstate tmp fpm3 fidx2 sup2 k).

Inductive final_state: state -> (reply li_rs_spec) -> Prop :=
| final_state_intro: forall tmp v fpm1 fpm2 fidx sup
    (TAKE: take_temporary fpm1 tmp = OK (v, fpm2)),
    final_state (Returnstate tmp fpm1 fidx sup Kstop)
      (RustIRspec.rspec_r v fpm2 fidx sup).

End SMALLSTEP.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external
    after_external (fun _ => final_state) globalenv p.
