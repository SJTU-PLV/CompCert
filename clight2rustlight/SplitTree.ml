open! Camlcoq
open! Rustlight        (* 引入 Rustlight，它定义了 statement, pexpr 等 *)
open! Rusttypes        (* 引入 Rusttypes 以便直接使用 Tunit *)

type ident = AST.ident (* FIX: 与 .mli 文件保持一致，明确定义 ident *)

(* 我们直接使用标准的 OCaml result 类型及其函数 *)
let (>>=) = Result.bind
let ok x = Ok x
let error msg = Error msg

(** Information about a leaf node in the tree, representing an available slice. *)
type leaf_info = {
  rust_var: ident; (* The Rust variable name for this slice. *)
  c_offset: int;   (* The starting offset of this slice relative to the original C pointer. *)
}

(** Information about an internal node, representing a point where a slice was split. *)
type internal_node_info = {
  split_c_offset: int; (* The absolute C offset where the split occurred. *)
  left: t;             (* The left sub-tree (slice before the split point). *)
  right: t;            (* The right sub-tree (slice at and after the split point). *)
}

(** The recursive definition of a split tree. *)
and t =
  | Leaf of leaf_info
  | Internal of internal_node_info

(** Creates an initial split tree for a new base pointer. *)
let init root_var =
  Leaf { rust_var = root_var; c_offset = 0 }

(** Module for our state map: from C variable ident to its split tree *)
module IdentMap = Map.Make(struct
  type t = ident
  let compare = compare
end)

(** The global state: a map from C base pointers to their split trees. *)
let split_tree_state : t IdentMap.t ref = ref IdentMap.empty

(**
 * A recursive helper to find the correct leaf, generate the split statement,
 * and return the updated tree structure.
 * 它返回一个标准的 ('ok, 'error) result 类型。
 *)
let rec find_and_split_rec (tree: t) (target_c_offset: int) =
  match tree with
  | Leaf l ->
      if target_c_offset < l.c_offset then
        error (Printf.sprintf "Logic error: target offset %d is smaller than leaf's start offset %d" target_c_offset l.c_offset)
      else
        let relative_offset = target_c_offset - l.c_offset in

        let left_tmp_id = fresh_atom () in
        let right_tmp_id = fresh_atom () in

        let result_place =
          Ppair (
            Plocal (left_tmp_id, Tunit),
            Plocal (right_tmp_id, Tunit)
          )
        in

        let split_stmt =
          Scall(
            result_place,
            (Epure (Eplace (Rustlight.Plocal (intern_string "split_at_mut", Tunit), Tunit))),
            [
              Epure (Eplace (Plocal (l.rust_var, Tunit), Tunit));
              Epure (Econst_int (Z.of_uint relative_offset, Tunit))
            ]
          )
        in

        let new_internal_node =
          (* FIX: 添加类型注解 (: t) 来消除 Internal 构造器的歧义 *)
          (Internal {
            split_c_offset = target_c_offset;
            left = Leaf { rust_var = left_tmp_id; c_offset = l.c_offset };
            right = Leaf { rust_var = right_tmp_id; c_offset = target_c_offset };
          } : t)
        in
        ok (split_stmt, (left_tmp_id, right_tmp_id), new_internal_node)

  | Internal i ->
      if target_c_offset < i.split_c_offset then
        find_and_split_rec i.left target_c_offset
        >>= fun (stmt, new_vars, updated_left_subtree) ->
        (* FIX: 添加类型注解 (: t) 来消除 Internal 构造器的歧义 *)
        ok (stmt, new_vars, (Internal { i with left = updated_left_subtree } : t))
      else
        find_and_split_rec i.right target_c_offset
        >>= fun (stmt, new_vars, updated_right_subtree) ->
        (* FIX: 添加类型注解 (: t) 来消除 Internal 构造器的歧义 *)
        ok (stmt, new_vars, (Internal { i with right = updated_right_subtree } : t))

(**
 * This is the function called from the Coq-generated code via extraction.
 * It matches the signature `ident -> ident -> Z.t -> statement`.
 *)
let find_and_split (base_ptr_id: ident) (new_ptr_id: ident) (c_offset: Z.t) : statement =
  let c_offset_int = Z.to_int c_offset in

  let current_tree =
    match IdentMap.find_opt base_ptr_id !split_tree_state with
    | Some tree -> tree
    | None -> init base_ptr_id
  in

  match find_and_split_rec current_tree c_offset_int with
  | Ok (split_stmt, (_left_var, right_var), updated_tree) ->
      split_tree_state := IdentMap.add base_ptr_id updated_tree !split_tree_state;

      let final_stmt =
        Ssequence(
          split_stmt,
          Sassign(Plocal(new_ptr_id, Tunit), Epure(Eplace(Plocal(right_var, Tunit), Tunit)))
        )
      in
      final_stmt

  | Error msg ->
      failwith ("SplitTree Error: " ^ msg)