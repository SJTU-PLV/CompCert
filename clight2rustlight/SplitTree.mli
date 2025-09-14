open! Rustlight
open Camlcoq

(** A unique identifier, typically for a variable. *)
type ident = AST.ident (* FIX: 明确定义 ident 类型别名 *)

(** Abstract type for a split tree. *)
type t

(** Information about a leaf node in the tree. *)
type leaf_info = {
  rust_var: ident; (* The Rust variable name for this slice. *)
  c_offset: int;   (* The starting offset of this slice relative to the original C pointer. *)
}

(** Creates an initial split tree for a new base pointer.
    @param root_var The initial Rust variable representing the whole array/slice. *)
val init: ident -> t

(** The main public function to be called from the Coq-generated code. *)
val find_and_split : ident -> ident -> Z.t -> statement