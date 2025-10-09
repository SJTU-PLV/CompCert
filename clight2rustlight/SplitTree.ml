open! Camlcoq
open! Rustlight
open! Rusttypes

type ident = AST.ident

module IdentMap = Map.Make(struct
  type t = ident
  let compare = compare
end)

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

(* 核心修改1: pending_assignments 现在存储 C 变量到其目标偏移量的映射 *)
type base_ptr_state = {
  tree: t;
  pending_assignments: int IdentMap.t; (* <c_var, c_offset> *)
}

let forest : base_ptr_state IdentMap.t ref = ref IdentMap.empty
let pointer_to_base_map : ident IdentMap.t ref = ref IdentMap.empty

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
        let usize_type = Tint(Ctypes.I32, Ctypes.Unsigned) in
        let result_place = Ppair (Plocal (left_tmp_id, Tunit), Plocal (right_tmp_id, Tunit)) in
        let split_stmt =
          Scall(
            result_place,
            (Epure (Eplace (Rustlight.Plocal (intern_string "split_at_mut", Tunit), Tunit))),
            [
              Epure (Eplace (Plocal (l.rust_var, slice_type), slice_type));
              Epure (Econst_int (Z.of_uint relative_offset, usize_type))
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

let find_and_split (base_ptr_id: ident) (new_ptr_id: ident) (c_offset: Z.t) (array_size_z: Z.t) : statement =
  let c_offset_int = Z.to_int c_offset in
  let array_size_int = Z.to_int array_size_z in

  let state =
    match IdentMap.find_opt base_ptr_id !forest with
    | Some state -> state
    | None ->
        let initial_tree = Leaf {
          rust_var = base_ptr_id;
          start_offset = 0;
          end_offset = array_size_int;
        } in
        { tree = initial_tree; pending_assignments = IdentMap.empty }
  in

  match find_and_split_rec state.tree c_offset_int with
  | Ok (split_stmts, updated_tree, _target_rust_var) ->
      (* 核心修改2: 只记录 c_var -> c_offset 的映射，不再记录临时的 rust_var *)
      let new_pending = IdentMap.add new_ptr_id c_offset_int state.pending_assignments in
      let new_state = { tree = updated_tree; pending_assignments = new_pending } in
      forest := IdentMap.add base_ptr_id new_state !forest;
      pointer_to_base_map := IdentMap.add new_ptr_id base_ptr_id !pointer_to_base_map;
      sequence_of_statements split_stmts
  | Error msg ->
      failwith ("SplitTree Error: " ^ msg)

(* 核心修改3: 新增一个辅助函数，用于在最终的树中查找代表特定偏移量的叶子节点 *)
let rec find_leaf_at_offset (tree: t) (target_offset: int) : ident option =
  match tree with
  | Leaf l ->
      (* 一个叶子节点代表一个指针当且仅当它的起始位置完全匹配 *)
      if l.start_offset = target_offset then Some l.rust_var else None
  | Internal i ->
      if target_offset < i.split_offset then
        find_leaf_at_offset i.left target_offset
      else
        find_leaf_at_offset i.right target_offset

(* 重命名并修正逻辑 *)
let flush_assignments_for_vars (vars: ident list) : statement =
  let base_ptrs_to_flush =
    List.fold_left (fun acc var ->
      match IdentMap.find_opt var !pointer_to_base_map with
      | Some base_ptr -> IdentMap.add base_ptr () acc
      | None -> acc
    ) IdentMap.empty vars
  in

  let assignment_stmts = ref [] in

  IdentMap.iter (fun base_ptr () ->
    match IdentMap.find_opt base_ptr !forest with
    | Some state ->
        (* 只有当存在需要生成的待定赋值时才继续。
           begin/end 用于包裹多个语句。*)
        if not (IdentMap.is_empty state.pending_assignments) then begin
          (* 1. 遍历待定赋值，并使用 find_leaf_at_offset 查找正确的叶子 *)
          IdentMap.iter (fun c_var c_offset ->
            match find_leaf_at_offset state.tree c_offset with
            | Some rust_leaf_var ->
                let ty = Tslice(Mutable, Tint(Ctypes.I32, Ctypes.Signed)) in
                let assign_stmt =
                  Sassign(Plocal(c_var, ty), Epure(Eplace(Plocal(rust_leaf_var, ty), ty)))
                in
                assignment_stmts := assign_stmt :: !assignment_stmts
            | None ->
                failwith (Printf.sprintf "SplitTree flush logic error: could not find leaf for offset %d" c_offset)
          ) state.pending_assignments;

          (* 2. 核心修改：只清空待定赋值，但保留树 *)
          let new_state = { state with pending_assignments = IdentMap.empty } in
          forest := IdentMap.add base_ptr new_state !forest
        end
    | None -> ()
  ) base_ptrs_to_flush;

  sequence_of_statements (List.rev !assignment_stmts)

(* let flush_and_destroy_for_vars (vars: ident list) : statement =
  let base_ptrs_to_flush =
    List.fold_left (fun acc var ->
      match IdentMap.find_opt var !pointer_to_base_map with
      | Some base_ptr -> IdentMap.add base_ptr () acc
      | None -> acc
    ) IdentMap.empty vars
  in

  let assignment_stmts = ref [] in

  IdentMap.iter (fun base_ptr () ->
    match IdentMap.find_opt base_ptr !forest with
    | Some state ->
        (* 核心修改4: 遍历待定赋值，并使用 find_leaf_at_offset 查找正确的叶子 *)
        IdentMap.iter (fun c_var c_offset ->
          match find_leaf_at_offset state.tree c_offset with
          | Some rust_leaf_var ->
              let ty = Tslice(Mutable, type_int32s) in
              let assign_stmt =
                Sassign(Plocal(c_var, ty), Epure(Eplace(Plocal(rust_leaf_var, ty), ty)))
              in
              assignment_stmts := assign_stmt :: !assignment_stmts
          | None ->
              (* 这个错误表示我们的逻辑有问题，一个待定指针没有在最终的树中找到对应的叶子 *)
              failwith (Printf.sprintf "SplitTree flush logic error: could not find leaf for offset %d" c_offset)
        ) state.pending_assignments;

        (* 清理状态 *)
        IdentMap.iter (fun c_var _ ->
          pointer_to_base_map := IdentMap.remove c_var !pointer_to_base_map
        ) state.pending_assignments;
        forest := IdentMap.remove base_ptr !forest

    | None -> ()
  ) base_ptrs_to_flush;

  sequence_of_statements (List.rev !assignment_stmts) *)

  (* 新增辅助函数：在树中查找包含给定绝对偏移量的叶子 *)
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

(**
 * 实现 is_base_ptr_managed
 *)
let is_base_ptr_managed (base_ptr_id: ident) : bool =
  IdentMap.mem base_ptr_id !forest

(**
 * 实现 resolve_direct_access
 *)
let resolve_direct_access (base_ptr_id: ident) (abs_offset_z: Z.t) : (ident * Z.t) =
  let abs_offset = Z.to_int abs_offset_z in
  match IdentMap.find_opt base_ptr_id !forest with
  | Some state ->
      (match find_leaf_for_abs_offset state.tree abs_offset with
       | Some (leaf_var, relative_offset) ->
           (leaf_var, Z.of_uint relative_offset)
       | None ->
           (* 如果找不到，这是一个严重错误，说明偏移量越界了 *)
           failwith (Printf.sprintf "SplitTree resolve error: offset %d is out of bounds for base pointer"
                      abs_offset)
      )
  | None ->
      (* 如果基指针未被管理，理论上不应该调用此函数。
         作为安全备用，我们返回原始值。 *)
      (base_ptr_id, abs_offset_z)