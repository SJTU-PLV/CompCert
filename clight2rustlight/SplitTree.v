(**
 * This file provides the formal definition of Split Trees in Coq.
 * A split tree is a data structure used during the C-to-Rustlight translation
 * to track how C variables that are contiguous in memory are accessed via
 * pointer arithmetic. This allows translating unsafe C pointer operations
 * into safe Rust slice operations.
 *
 * The definitions here are designed to be compatible with the existing OCaml
 * interface (SplitTree.mli) and will be extracted to OCaml code.
 *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Ctypes.

Require Import List.
Import ListNotations.

Module SplitTree.

  (**
   * A [node] represents a single element in the memory layout being tracked.
   * It contains the identifier [id] and C type [ty] of the variable.
   *)
  Record node : Type := MkNode {
    id : ident;
    ty : type
  }.

  (**
   * The core [tree] structure. It is a recursive binary tree.
   * - [Leaf]: Represents a single C variable.
   * - [Node]: Represents the concatenation of two memory regions,
   * each represented by a subtree.
   *)
  Inductive tree : Type :=
  | Leaf: node -> tree
  | Node: tree -> tree -> tree.

  (**
   * Definition of the main split tree map [t].
   * It's a map from a root identifier (the pointer used for arithmetic)
   * to the [tree] that describes the memory layout accessible from that pointer.
   * This corresponds to `(ident, tree) PTree.t` in OCaml.
   *)
  Definition t : Type := PTree.t tree.

  (**
   * [empty] represents an empty collection of split trees.
   *)
  Definition empty : t :=
    PTree.empty tree.

  (**
   * [add_leaf root_id var_id var_ty st_map]
   *
   * Creates a new split tree for [root_id] containing a single leaf
   * for the variable [var_id] of type [var_ty].
   * If a tree for [root_id] already exists, it is overwritten.
   *)
  Definition add_leaf (root_id: ident) (var_id: ident) (var_ty: type) (st_map: t) : t :=
    let n := MkNode var_id var_ty in
    let l := Leaf n in
    PTree.set root_id l st_map.

  (**
   * [add_item root_id1 root_id2 st_map]
   *
   * Merges the split trees of [root_id1] and [root_id2] into a new tree
   * under the name [root_id1]. The new tree is a [Node] where the left
   * child is the tree of [root_id1] and the right child is the tree of [root_id2].
   * The tree for [root_id2] is removed from the map.
   * If either tree does not exist, the map is returned unchanged.
   *)
  Definition add_item (root_id1: ident) (root_id2: ident) (st_map: t) : t :=
    match (st_map ! root_id1), (st_map ! root_id2) with
    | Some t1, Some t2 =>
        let new_tree := Node t1 t2 in
        let st_map' := PTree.set root_id1 new_tree st_map in
        PTree.remove root_id2 st_map'
    | _, _ =>
        st_map
    end.

  (**
   * [find_opt root_id st_map]
   *
   * Finds the split tree associated with [root_id] in the map.
   * Returns [Some tree] if found, [None] otherwise.
   *)
  Definition find_opt (root_id: ident) (st_map: t) : option tree :=
    st_map ! root_id.

  (**
   * [get_variables_rec tr]
   *
   * A recursive helper function to traverse a [tree] and collect all
   * variables ([node]s) in a list.
   *)
  Fixpoint get_variables_rec (tr: tree) : list node :=
    match tr with
    | Leaf n => [n]
    | Node t1 t2 => (get_variables_rec t1) ++ (get_variables_rec t2)
    end.

  (**
   * [get_variables root_id st_map]
   *
   * Returns a list of all variables (identifier and type) contained
   * within the split tree of [root_id].
   * If no tree is found for [root_id], returns an empty list.
   *)
  Definition get_variables (root_id: ident) (st_map: t) : list node :=
    match st_map ! root_id with
    | Some tr => get_variables_rec tr
    | None => []
    end.

  (**
   * [print_tree tr]
   *
   * This function is for debugging purposes. Since Coq does not handle
   * I/O, we declare its type as a parameter. The actual implementation
   * will be provided in OCaml during extraction, where it will print
   * the tree structure to the console.
   *)
  Parameter print_tree : tree -> unit.

End SplitTree.