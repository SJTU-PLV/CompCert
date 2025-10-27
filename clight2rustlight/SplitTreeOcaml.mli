(* file: clight2rustlight/SplitTreeOcaml.mli *)

open! Camlcoq
open! Rustlight

type ident = AST.ident

(** The environment type is now an alias for the one defined in Coq. *)
type split_tree_env = TranslationEnv.TranslationEnv.t

(**
 * Creates an empty, initial split tree environment.
 *)
val initial_env : split_tree_env

(**
 * A stateful version of find_and_split that explicitly takes and returns the environment.
 * This is the function that will be linked to the Coq Parameter.
 * Returns: (statement, new_vars, new_env)
 * where new_vars is a list of (ident * coq_type) pairs for newly generated variables.
 *)
val find_and_split_stateful
  : ident -> ident -> Z.t -> Z.t -> split_tree_env -> (statement * (ident * Rusttypes.coq_type) list) * split_tree_env

(**
 * A stateful version of flush_assignments_for_vars.
 *)
val flush_assignments_for_vars : ident list -> split_tree_env -> (statement * split_tree_env)

(**
 * A stateful version of is_base_ptr_managed.
 *)
val is_base_ptr_managed : ident -> split_tree_env -> bool

(**
 * A stateful version of resolve_direct_access.
 *)
val resolve_direct_access : ident -> Z.t -> split_tree_env -> (ident * Z.t)