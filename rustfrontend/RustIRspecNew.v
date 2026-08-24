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

(** ** Evaluation of expressions *)

(* Used in Emoveplace and Sdrop; we do not require that p must be a
move path *)
Definition move_out_place (ce: composite_env) (fidx: frame_idx)
    (fpm: fp_map) (p: place) : res (footprint * fp_map) :=
  let ps := enc_path fidx p in
  let fpm1 := invalidate_conflict_ref_fpm ps AWrite Adeep fpm in
  do (ph, _) <- get_owner_path_map ps fpm1;
  do fp <- get_owner_footprint_map ph fpm1;
  do fpm2 <- clear_footprint_map ce ph fpm1;
  OK (fp, fpm2).
  (* do droppable <- check_path_is_droppable fpm1 ps; *)
  (* if droppable then clear_footprint_map ce ps fpm1 *)
  (* else Error (msg "drop target is not droppable"). *)

Section EXPR.
  
Variable frame: positive.

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
      let p := (enc_path frame p) in
      (* We first do invalidation and then get the footprint because
      we do not want to do invalidate on the footprint we get. *)
      let fpm1 := invalidate_conflict_ref_fpm p ARead Adeep fpm in
      do (ph, _) <- get_owner_path_map p fpm1;
      do (_, fp) <- get_owner_loc_footprint_map ph fpm1;
      OK (fp, fpm1)
  | Ecktag p fid =>
      let p := (enc_path frame p) in
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
      let p := (enc_path frame p) in
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
      (* let p := (enc_path frame p) in *)
      (* let fpm1 := invalidate_conflict_ref_fpm p AWrite Adeep fpm in *)
      (* do (_, fp) <- get_owner_loc_footprint_map p fpm1; *)
      (* do fpm2 <- clear_footprint_map ce p fpm1; *)
      (* OK (fp, fpm2) *)
      move_out_place ce frame fpm p
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
  (* used to make sure we do not have reference that points to leak
  memory *)
  do dropped <- check_path_is_dropped fpm1 ph;
  if dropped then
    do fpm2 <- clear_footprint_map ce ph fpm1;
    OK (ph, kill_views_ref_fpm vs fpm2)
  else Error (msg "assignment target is not dropped").

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
| step_drop: forall fpm1 fpm2 k f (p: place) fidx sup fp
    (* fp is the footprint we want to drop *)
    (DROP: move_out_place ge fidx fpm1 p = OK (fp, fpm2)),
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
