open! Camlcoq
open! Rustlight
open! Rusttypes
open! Maps
open! TranslationEnv (* 导入 Coq 环境模块 *)

type ident = AST.ident

(** The environment type is now an alias for the one defined in Coq. *)
type split_tree_env = TranslationEnv.t

let (>>=) = Result.bind
let ok x = Ok x
let error msg = Error msg

type leaf_info = {
  rust_var: ident;
  start_offset: int;
  end_offset: int;
}

and t =
  | Leaf of leaf_info
  | Internal of {
      split_offset: int;
      left: t;
      right: t;
    }

(* type tree = t *)

type base_ptr_state = {
  tree: t;
  pending_assignments: int PTree.t;
}

(*** MODIFICATION: This is now our INTERNAL state representation ***)
type internal_env = {
  forest: base_ptr_state PTree.t;
  pointer_to_base_map: ident PTree.t;
}

(*** MODIFICATION: Helper functions to pack/unpack our internal state ***)
(* This is a HACK. Coq's TranslationEnv has no field for pointer_to_base_map. *)
(* We will store it in the var_map using Obj.magic to cast types. *)
let unpack_env (coq_env: TranslationEnv.t) : internal_env =
  let current_st_scope =
    match coq_env.TranslationEnv.st_map with (* <- 修正 *)
    | scope :: _ -> scope
    | [] -> PTree.empty
  in
  let current_var_scope =
    match coq_env.TranslationEnv.var_map with (* <- 修正 *)
    | scope :: _ -> scope
    | [] -> PTree.empty
  in
  {
    forest = Obj.magic current_st_scope;
    pointer_to_base_map = Obj.magic current_var_scope;
  }

let pack_env (internal_env: internal_env) (coq_env: TranslationEnv.t) : TranslationEnv.t =
  let new_st_scope = Obj.magic internal_env.forest in
  let new_var_scope = Obj.magic internal_env.pointer_to_base_map in
  let new_st_map =
    match coq_env.TranslationEnv.st_map with (* <- 修正 *)
    | _ :: rest -> new_st_scope :: rest
    | [] -> [new_st_scope]
  in
  let new_var_map =
      match coq_env.TranslationEnv.var_map with (* <- 修正 *)
      | _ :: rest -> new_var_scope :: rest
      | [] -> [new_var_scope]
  in
  { TranslationEnv.st_map = new_st_map; TranslationEnv.var_map = new_var_map } (* <- 修正 *)

(* A clean, empty environment. *)
let initial_env : TranslationEnv.t =
  let empty_internal = { forest = PTree.empty; pointer_to_base_map = PTree.empty } in
  pack_env empty_internal TranslationEnv.empty

(* ... (find_and_split_rec and sequence_of_statements remain unchanged) ... *)
let rec find_and_split_rec (tree: t) (target_c_offset: int) : ((statement list * t * ident), string) result =
   match tree with
  | Leaf l ->
      if target_c_offset < l.start_offset || target_c_offset > l.end_offset then
        error (Printf.sprintf "Target offset %d is outside the leaf's range [%d, %d)"
                 target_c_offset l.start_offset l.end_offset)
      else
        let relative_offset = target_c_offset - l.start_offset in
        let left_tmp_id = fresh_atom () in
        let right_tmp_id = fresh_atom () in
        let slice_type = Tslice(Mutable, Tint(Ctypes.I32, Ctypes.Signed)) in
        let usize_type = Rusttypes.Tlong(Ctypes.Unsigned) in  (* Use u64 for usize on 64-bit systems *)
        let result_place = Ppair (Plocal (left_tmp_id, slice_type), Plocal (right_tmp_id, slice_type)) in
        let split_stmt =
          Smethod_call(
            result_place,
            (Epure (Eplace (Plocal (l.rust_var, slice_type), slice_type))),  (* receiver *)
            (intern_string "split_at_mut"),  (* method_name *)
            [
              Epure (Econst_long (Z.of_uint relative_offset, usize_type))
            ]
          )
        in
        let new_internal_node =
          (Internal {
            split_offset = target_c_offset;
            left = Leaf { rust_var = left_tmp_id; start_offset = l.start_offset; end_offset = target_c_offset };
            right = Leaf { rust_var = right_tmp_id; start_offset = target_c_offset; end_offset = l.end_offset };
          } : t)
        in
        ok ([split_stmt], new_internal_node, right_tmp_id)

  | Internal i ->
      if target_c_offset < i.split_offset then
        find_and_split_rec i.left target_c_offset
        >>= fun (stmts, updated_left_subtree, target_var) ->
        ok (stmts, (Internal { i with left = updated_left_subtree } : t), target_var)
      else
        find_and_split_rec i.right target_c_offset
        >>= fun (stmts, updated_right_subtree, target_var) ->
        ok (stmts, (Internal { i with right = updated_right_subtree } : t), target_var)

let sequence_of_statements (stmts: statement list) : statement =
  List.fold_right
    (fun s1 s2 -> if s1 = Sskip then s2 else if s2 = Sskip then s1 else Ssequence(s1, s2))
    stmts
    Sskip

(*** MODIFICATION: Update the main function signature and logic ***)
(* Helper function to extract variables from Ppair places *)
let rec extract_vars_from_place (p: place) : (ident * Rusttypes.coq_type) list =
  match p with
  | Plocal (id, ty) -> [(id, ty)]
  | Ppair (p1, p2) -> extract_vars_from_place p1 @ extract_vars_from_place p2
  | _ -> []

(* Helper function to extract new variables from split statements *)
let extract_new_vars_from_stmts (stmts: statement list) : (ident * Rusttypes.coq_type) list =
  List.fold_left (fun acc stmt ->
    match stmt with
    | Smethod_call (p, _, _, _) ->
        (* For split_at_mut, p is typically a Ppair *)
        let vars = extract_vars_from_place p in
        acc @ vars
    | _ -> acc
  ) [] stmts

let find_and_split_stateful (base_ptr_id: ident) (new_ptr_id: ident) (c_offset: Z.t) (array_size_z: Z.t) (coq_env: TranslationEnv.t) : (statement * (ident * Rusttypes.coq_type) list) * TranslationEnv.t =
  let env = unpack_env coq_env in (* Unpack to internal format *)
  let c_offset_int = Z.to_int c_offset in
  let array_size_int = Z.to_int array_size_z in

  (* If base_ptr_id is not in forest, check if it's a derived pointer *)
  let actual_base_id = 
    match PTree.get base_ptr_id env.forest with
    | Some _ -> base_ptr_id  (* It's already a base pointer *)
    | None ->
        (* Check if it's a derived pointer that maps to a real base *)
        match PTree.get base_ptr_id env.pointer_to_base_map with
        | Some real_base -> real_base
        | None -> base_ptr_id  (* Use itself as base *)
  in

  let state_opt =
    match PTree.get actual_base_id env.forest with
    | Some state -> Some state
    | None ->
        (* If array_size is 0, we can't create initial tree - skip split *)
        if array_size_int = 0 then
          None
        else
          let initial_tree = Leaf {
            rust_var = actual_base_id;
            start_offset = 0;
            end_offset = array_size_int;
          } in
          Some { tree = initial_tree; pending_assignments = PTree.empty }
  in
  
  match state_opt with
  | None ->
      (* Cannot proceed with split - return no-op and unchanged environment *)
      ((Sskip, []), coq_env)
  | Some state ->

  (* Adjust offset if base_ptr_id is a derived pointer *)
  let adjusted_offset =
    if base_ptr_id = actual_base_id then
      c_offset_int
    else
      (* Get the offset of base_ptr_id relative to actual_base_id *)
      match PTree.get base_ptr_id state.pending_assignments with
      | Some base_offset -> base_offset + c_offset_int
      | None -> c_offset_int  (* Assume 0 if not found *)
  in

  match find_and_split_rec state.tree adjusted_offset with
  | Ok (split_stmts, updated_tree, _target_rust_var) ->
      let new_pending = PTree.set new_ptr_id adjusted_offset state.pending_assignments in
      let new_state = { tree = updated_tree; pending_assignments = new_pending } in
      let new_forest = PTree.set actual_base_id new_state env.forest in
      let new_pointer_map = PTree.set new_ptr_id actual_base_id env.pointer_to_base_map in
      let new_internal_env = { forest = new_forest; pointer_to_base_map = new_pointer_map } in
      let new_vars = extract_new_vars_from_stmts split_stmts in
      ((sequence_of_statements split_stmts, new_vars), pack_env new_internal_env coq_env) (* Pack back *)
  | Error msg ->
      failwith ("SplitTree Error: " ^ msg)

(* ... (find_leaf_at_offset remains the same) ... *)
let rec find_leaf_at_offset (tree: t) (target_offset: int) : ident option =
  match tree with
  | Leaf l ->
      if l.start_offset = target_offset then Some l.rust_var else None
  | Internal i ->
      if target_offset < i.split_offset then
        find_leaf_at_offset i.left target_offset
      else
        find_leaf_at_offset i.right target_offset

(*** MODIFICATION: Update flush_assignments_for_vars signature and logic ***)
let flush_assignments_for_vars (vars: ident list) (coq_env: TranslationEnv.t) : (statement * TranslationEnv.t) =
  let env = unpack_env coq_env in
  (* ... (the rest of the function logic from your original file remains exactly the same, just use `env` instead of `coq_env`) ... *)
  let base_ptrs_to_flush : unit PTree.t =
    List.fold_left (fun acc var_id ->
      match PTree.get var_id env.pointer_to_base_map with
      | Some base_ptr_id -> PTree.set base_ptr_id () acc
      | None -> acc
    ) PTree.empty vars
  in
  let processing_function
      ((stmts_acc, forest_acc): statement list * base_ptr_state PTree.t)
      (base_ptr: ident)
      (_: unit)
      : (statement list * base_ptr_state PTree.t) =
    match PTree.get base_ptr forest_acc with
    | Some state ->
        if PTree.elements state.pending_assignments <> [] then
          let assignments_fold_func
              (inner_acc: statement list)
              (c_var: ident)
              (c_offset: int)
            : statement list =
            match find_leaf_at_offset state.tree c_offset with
            | Some rust_leaf_var ->
                (* Don't generate assignment statements - they cause borrow conflicts *)
                (* The resolve_direct_access will handle variable resolution *)
                inner_acc
            | None ->
                let error_msg = Printf.sprintf "SplitTree flush: could not find leaf for C var at offset %d" c_offset in
                failwith error_msg
          in
          let new_stmts_for_this_base_ptr = PTree.fold assignments_fold_func state.pending_assignments [] in
          let new_state = { state with pending_assignments = PTree.empty } in
          let updated_forest = PTree.set base_ptr new_state forest_acc in
          (new_stmts_for_this_base_ptr @ stmts_acc, updated_forest)
        else
          (stmts_acc, forest_acc)
    | None ->
        (stmts_acc, forest_acc)
  in
  let (assignment_stmts, new_forest) = PTree.fold processing_function base_ptrs_to_flush ([], env.forest) in
  let final_internal_env = { env with forest = new_forest } in
  (sequence_of_statements assignment_stmts, pack_env final_internal_env coq_env)

(*** MODIFICATION: Update is_base_ptr_managed signature and logic ***)
let is_base_ptr_managed (base_ptr_id: ident) (coq_env: TranslationEnv.t) : bool =
  let env = unpack_env coq_env in
  (* Check if it's directly in forest, OR if it's a derived pointer that maps to a base *)
  match PTree.get base_ptr_id env.forest with
  | Some _ -> true
  | None   -> 
      (* Not a direct base - check if it's a derived pointer *)
      (match PTree.get base_ptr_id env.pointer_to_base_map with
       | Some _ -> true  (* It's managed because it derives from a base *)
       | None -> false)

(* ... (find_leaf_for_abs_offset remains the same) ... *)
let rec find_leaf_for_abs_offset (tree: t) (target_offset: int) : (ident * int) option =
  match tree with
  | Leaf l ->
      if target_offset >= l.start_offset && target_offset < l.end_offset then
        Some (l.rust_var, target_offset - l.start_offset)
      else
        None
  | Internal i ->
      if target_offset < i.split_offset then
        find_leaf_for_abs_offset i.left target_offset
      else
        find_leaf_for_abs_offset i.right target_offset

(*** MODIFICATION: Update resolve_direct_access signature and logic ***)
let resolve_direct_access (base_ptr_id: ident) (abs_offset_z: Z.t) (coq_env: TranslationEnv.t) : (ident * Z.t) =
  let env = unpack_env coq_env in
  let abs_offset = Z.to_int abs_offset_z in
  match PTree.get base_ptr_id env.forest with
  | Some state ->
      (match find_leaf_for_abs_offset state.tree abs_offset with
       | Some (leaf_var, relative_offset) ->
           (leaf_var, Z.of_uint relative_offset)
       | None ->
           failwith (Printf.sprintf "SplitTree resolve error: offset %d is out of bounds for base pointer"
                      abs_offset)
      )
  | None ->
      (base_ptr_id, abs_offset_z)