(* file: clight2rustlight/TranslationEnv.v *)

Require Import Coqlib.
Require Import Maps.
Require Import compcert.clight2rustlight.SplitTree.
Require Import List.
Import ListNotations.

Require Import AST.

Module TranslationEnv.

  (* 定义作用域栈：一个从 ident 到 'a 的映射 (PTree) 的列表 *)
  Definition scoped_map (A: Type) := list (PTree.t A).

  (* 定义完整的翻译环境 *)
  Record t : Type := mk_env {
    st_map : scoped_map SplitTree.t;
    (* 你也可以把其他需要作用域管理的变量放在这里 *)
    var_map : scoped_map Ctypes.type; 
  }.

  (* 创建一个空的初始环境 *)
  Definition empty : t :=
    mk_env [] [].

  (* 进入一个新作用域：在每个栈的头部压入一个空Map *)
  Definition enter_scope (env: t) : t :=
  mk_env (@PTree.empty SplitTree.t :: env.(st_map))
         (@PTree.empty Ctypes.type :: env.(var_map)).

  (* 离开一个作用域：弹出每个栈的头部 *)
  Definition exit_scope (env: t) : t :=
    match env.(st_map), env.(var_map) with
    | _ :: st_rest, _ :: var_rest => mk_env st_rest var_rest
    | _, _ => env (* 已经是全局作用域 *)
    end.

  (* 在当前作用域添加一个分裂树 *)
  Definition add_split_tree (id: ident) (st: SplitTree.t) (env: t) : t :=
    match env.(st_map) with
    | current_scope :: rest =>
        let new_scope := PTree.set id st current_scope in
        mk_env (new_scope :: rest) env.(var_map)
    | [] => env (* 错误情况 *)
    end.

  Definition add_var (id: ident) (ty: Ctypes.type) (env: t) : t :=
    match env.(var_map) with
    | current_scope :: rest =>
        let new_scope := PTree.set id ty current_scope in
        mk_env env.(st_map) (new_scope :: rest)
    | [] => env (* 不应该在没有作用域的情况下发生 *)
    end.

  (* 查找一个分裂树（从内到外）*)
  Fixpoint find_split_tree (id: ident) (scopes: scoped_map SplitTree.t) : option SplitTree.t :=
    match scopes with
    | [] => None
    | current_scope :: rest =>
        match current_scope ! id with
        | Some st => Some st
        | None => find_split_tree id rest
        end
    end.
    
End TranslationEnv.