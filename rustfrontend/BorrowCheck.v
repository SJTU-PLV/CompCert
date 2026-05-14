Require Import Coqlib.
Require Import lib.Integers.
Require Import Maps.
Require Import AST.
Require Import Values.
Require Import Rusttypes RustIR RustIRcfg.
Require Import Errors.
Require Import Rusttyping.
Require Import MoveChecking.
Require Import BorrowCheckPolonius.

Import ListNotations.
Open Scope error_monad_scope.

(** The borrow checking algorithm which mainly consists of the
following sequence of passes that check each function:

1. A move checking pass that checks each access of owner place (i.e.,
a place that is not nested within some reference) is initialized;

2. A simple "type checking" pass which checks:

   2.1. Every place and expression existed in the function is well
   typed, e.g., the type of [*p] where [p: &mut &i32] must be [&i32];

   2.2. There is no mutation for immutable places, e.g., for [p:
   &i32], we cannot do [*p = ...];

   2.3. There is no move operation for non-owner place, e.g., for [p:
   &mut Box<i32>] we cannot do [move *p];

3. The core of the borrow checking:

   3.1. The loans-flow analysis which computes active loans at each
   point;

   3.2. A checking phase which checks illegal access of place, i.e.,
   the access of this place is conflict with the active loans at this
   point.
*)

Definition check_region_uniqueness (f: function) : res unit :=
  OK tt.

Definition check_no_live_local_regions_at_entry (live: RegionLiveness.RegionSet.t) (f: function) : res unit :=
  let regs := concat (map origins_of_type (map snd (f.(fn_vars) ++ f.(fn_params)))) in
  if forallb (fun r => negb (RegionLiveness.RegionSet.mem r live)) regs then
    OK tt
  else
    Error (msg "There is some region of local variables/parameters that are live at the function entry (which means it is used without initialization)").

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (* Check the uniqueness of the region names which should be ensured
  by ReplaceOrigin pass *)
  do _ <- check_region_uniqueness f;
  (** * 1. Move checking *)
  (* 1.1 Init Analaysis *)
  do init_analysis_res <- InitAnalysis.analyze ce f cfg entry;
  (* 1.2. Run move checking ! *)
  do _ <- collect_move_check_result ce f cfg init_analysis_res;
  (** * 2. Type checking  *)
  (* Naive syntactic type checking. The reason we put syntactic type
  checking here instead of using a separated type check function (like
  Ctyping) is that sound_state and wt_state rely on each other due to
  well typedness property in wf_own_env. *)
  let te := (bind_vars (bind_vars (PTree.empty _) f.(fn_params)) f.(fn_vars)) in
  let (_, universe) := init_analysis_res in  
  (* We should check that all the places in the universe of the
  init-analysis is well-typed *)
  do _ <- check_universe_wf te ce universe;
  do _ <- check_cyclic_struct_res ce (var_types (f.(fn_params) ++ f.(fn_vars)));
  do _ <- check_valid_types (var_types (f.(fn_params) ++ f.(fn_vars)));
  (* syntactic type checking *)
  do _ <- type_check_stmt ce te (fn_body f);
  (** TODO: add the checking for mutability *)
  (** * 3. Borrow checking *)
  (* 3.1. Loans-flow analysis *)
  do (live, loansEnv) <- loans_flow_analyze ce f cfg entry;
  (* 3.2. check illegal access of active loans *)
  let generic_regions := RegionLiveness.live_generic_regions (fn_generic_origins f) in
  (* There should be no local regions that are live at the entry
  (which means that it is used without initialization) *)
  do _ <- check_no_live_local_regions_at_entry (live !! entry) f;
  collect_borrow_check_result generic_regions f cfg (live, loansEnv).

Definition borrow_check_fundef (ce : composite_env) (id : ident) (fd : fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match borrow_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error msg
      end
  | External orgs rels ef targs tres cconv =>
      (* We do not support builtin external functions for now *)
      match ef with
      | EF_external _ _
      | EF_malloc
      | EF_free =>
          OK (External orgs rels ef targs tres cconv)
      | _ => Error [MSG "unsupported builtin external function"]
      end
  end.

Definition transl_globvar := fun (_ : ident) (ty : type) => OK ty.

Definition borrow_check_program (p : program) :=
  (* check composite environment *)
  do _ <- check_composite_env (prog_comp_env p);
  (* borrow check each function *)
  do p1 <- (transform_partial_program2 (borrow_check_fundef (prog_comp_env p)) transl_globvar p);
   OK
     {|
     prog_defs := AST.prog_defs p1;
     prog_public := AST.prog_public p1;
     prog_main := AST.prog_main p1;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
