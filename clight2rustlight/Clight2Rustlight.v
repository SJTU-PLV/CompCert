(* ********************************************************************* *)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Yaodong Wen, SJTU-PLV                                      *)
(*                                                                     *)
(*  Copyright SJTU-PLV.  All rights reserved.  This file is            *)
(*  distributed under the terms of the GNU Lesser General Public        *)
(*  License as published by the Free Software Foundation, either        *)
(*  version 2.1 of the License, or (at your option) any later version.  *)
(*                                                                     *)
(* ********************************************************************* *)

(* Conversion from Clight AST to Rustlight AST *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Values.
Require Import Floats.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import Globalenvs.
Require Import Errors.

Require Import cfrontend.Clight.
Require Import rustfrontend.Rustlight.

Import ListNotations.
Require Import Lists.List.

(* Require Import compcert.clight2rustlight.TranslationEnv. *)
(* Require Import compcert.clight2rustlight.SplitTree. *)

(** State and error monad for generating fresh identifiers. *)

(* get a fresh atom and update the next atom *)
(* Local Open Scope error_monad_scope. *)

Parameter fresh_atom : unit -> ident.

Definition max_nat_limit := 1000000%positive.

Record var_info : Type := mkvar_info {
  vi_type : type;
  vi_origin : ptr_origin
}.

Definition var_env := PTree.t var_info.

Definition empty_var_env : var_env := PTree.empty var_info.

Record generator : Type := mkgenerator {
  gen_next : ident;
  gen_trail : list (ident * type);
  gen_env : var_env
}.

(* 查找第一个可用标识符的辅助函数 *)
Fixpoint find_fresh (candidate: positive) (locals: list ident) (max_limit: nat):=
  match max_limit with
  | S n =>
      if in_dec ident_eq candidate locals then
          find_fresh (Pos.succ candidate) locals n
      else
          candidate
  | 0%nat =>
      max_nat_limit
  end.

Inductive result (A: Type) (g: generator) : Type :=
| Err: Errors.errmsg -> result A g
| Res: A -> forall (g': generator), result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g.

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
    | Err msg => Err msg
    | Res a g' =>
        match f a g' with
        | Err msg => Err msg
        | Res b g'' => Res b g'' 
        end
    end.

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Declare Scope gensym_monad_scope.
Notation "'do' X <- A ; B" := (bind A (fun X => B))
                                (at level 200, X ident, A at level 100, B at level 200)
    : gensym_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
                                        (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition initial_generator : generator :=
  mkgenerator 10000%positive nil empty_var_env.

Definition gensym (locals: list ident) (ty: type) : mon ident :=
  fun (g: generator) =>
  if Pos.leb (Pos.succ (gen_next g)) max_nat_limit then
  let fresh_id := find_fresh (gen_next g) locals (Pos.to_nat max_nat_limit) in
  Res fresh_id
      (mkgenerator (Pos.succ fresh_id) ((fresh_id, ty) :: gen_trail g) g.(gen_env))
  else Err (msg "gensym: out of fresh id limit").

Definition get_gen : mon generator :=
  fun g => Res g g.

Definition put_gen (g': generator) : mon unit :=
  fun _ => Res tt g'.

Definition modify_gen (f: generator -> generator) : mon unit :=
  fun g => Res tt (f g).

Definition update_env (f: var_env -> var_env) : mon unit :=
  modify_gen (fun g => mkgenerator g.(gen_next) g.(gen_trail) (f g.(gen_env))).

Definition set_var_info (id: ident) (ty: type) (origin: ptr_origin) : mon unit :=
  update_env (fun env => PTree.set id (mkvar_info ty origin) env).

Definition set_var_info_raw (id: ident) (info: var_info) : mon unit :=
  update_env (fun env => PTree.set id info env).

Definition get_var_info (id: ident) : mon (option var_info) :=
  fun g => Res (PTree.get id g.(gen_env)) g.

Definition get_var_origin (id: ident) : mon ptr_origin :=
  fun g =>
    match PTree.get id g.(gen_env) with
    | Some info => Res info.(vi_origin) g
    | None => Res PtrUnknown g
    end.

Definition forget_var (id: ident) : mon unit :=
  update_env (fun env => PTree.remove id env).

Inductive var_scope :=
| ScopeParam
| ScopeLocal
| ScopeTemp.

(* Definition new_origin := 1%positive. *)

(** Convert Clight type to Rustlight type *)
Fixpoint to_rusttype (ty: Ctypes.type): Rusttypes.type :=
  match ty with
  | Ctypes.Tvoid => Rusttypes.Tvoid
  | Ctypes.Tint sz si _ => Rusttypes.Tint sz si
  | Ctypes.Tlong si _ => Rusttypes.Tlong si
  | Ctypes.Tfloat fz _ => Rusttypes.Tfloat fz
  | Ctypes.Tstruct id _ => Rusttypes.Tstruct nil id
  | Ctypes.Tunion id _ => Rusttypes.Tvariant nil id
  | Ctypes.Tpointer ty _ => Rusttypes.Tslice Mutable (to_rusttype ty) Rusttypes.PtrUnknown
  (*todo*)
  | Ctypes.Tarray ty' sz _ => Rusttypes.Tarray Mutable (to_rusttype ty') sz
  | Ctypes.Tfunction tyl ty' cc => 
      Rusttypes.Tfunction nil nil (to_rusttypelist tyl) (to_rusttype ty') cc
  end
    
with to_rusttypelist (tyl: Ctypes.typelist) : Rusttypes.typelist :=
       match tyl with
       | Ctypes.Tnil => Rusttypes.Tnil
       | Ctypes.Tcons ty tyl => 
           Rusttypes.Tcons (to_rusttype ty) (to_rusttypelist tyl)
       end.

Definition to_rusttype_global (ty: Ctypes.type): Rusttypes.type :=
  match ty with
  | Ctypes.Tpointer ty _ => Rusttypes.Tslice Immutable (to_rusttype ty) Rusttypes.PtrUnknown
  (*todo*)
  | Ctypes.Tarray ty' sz _ => Rusttypes.Tarray Immutable (to_rusttype ty') sz
  | _ => to_rusttype ty
  end.

Definition is_pointer_type (ty: Ctypes.type) : bool :=
  match ty with
  | Ctypes.Tpointer _ _ => true
  | _ => false
  end.

Definition rust_type_with_origin (ty: Ctypes.type) (origin: ptr_origin) : type :=
  match ty with
  | Ctypes.Tpointer ty' _ => Rusttypes.Tslice Rusttypes.Mutable (to_rusttype ty') origin
  | _ => to_rusttype ty
  end.

Definition origin_for_decl (default_origin: ptr_origin) (ty: Ctypes.type) : ptr_origin :=
  match ty with
  | Ctypes.Tpointer _ _ => default_origin
  | _ => PtrUnknown
  end.

Definition register_single_var (default_origin: ptr_origin) (decl: ident * Ctypes.type) : mon unit :=
  let '(id, ty) := decl in
  let origin := origin_for_decl default_origin ty in
  let rty := rust_type_with_origin ty origin in
  set_var_info id rty origin.

Fixpoint register_var_list (default_origin: ptr_origin) (decls: list (ident * Ctypes.type)) : mon unit :=
  match decls with
  | [] => ret tt
  | decl :: rest =>
      do _ <- register_single_var default_origin decl;
      register_var_list default_origin rest
  end.

Definition lookup_type_in_env (env: var_env) (id: ident) (fallback: type) : type :=
  match PTree.get id env with
  | Some info => info.(vi_type)
  | None => fallback
  end.

Definition map_decl_types (env: var_env) (decls: list (ident * Ctypes.type)) :
  list (ident * type) :=
  List.map (fun '(id, ty) => (id, lookup_type_in_env env id (to_rusttype ty))) decls.

Definition get_rusttype_for_id (id: ident) (cty: Ctypes.type) : mon type :=
  fun g => Res (lookup_type_in_env g.(gen_env) id (to_rusttype cty)) g.

Definition update_var_origin (id: ident) (ty: Ctypes.type) (origin: ptr_origin) : mon unit :=
  set_var_info id (rust_type_with_origin ty origin) origin.

Definition prefer_origin (primary fallback: ptr_origin) : ptr_origin :=
  match primary with
  | PtrUnknown => fallback
  | _ => primary
  end.

Fixpoint infer_origin_from_expr (e: Clight.expr) : mon ptr_origin :=
  match e with
  | Clight.Evar id ty =>
      match ty with
      | Ctypes.Tpointer _ _ => get_var_origin id
      | _ => ret PtrUnknown
      end
  | Clight.Etempvar id ty =>
      match ty with
      | Ctypes.Tpointer _ _ => get_var_origin id
      | _ => ret PtrUnknown
      end
  | Clight.Econst_int i ty =>
      match ty with
      | Ctypes.Tpointer _ _ =>
          if Int.eq i Int.zero then ret PtrNull else ret PtrUnknown
      | _ => ret PtrUnknown
      end
  | Clight.Econst_long l ty =>
      match ty with
      | Ctypes.Tpointer _ _ =>
          if Int64.eq l Int64.zero then ret PtrNull else ret PtrUnknown
      | _ => ret PtrUnknown
      end
  | Clight.Ecast e' ty =>
      match ty with
      | Ctypes.Tpointer _ _ => infer_origin_from_expr e'
      | _ => ret PtrUnknown
      end
  | Clight.Eunop _ e' ty =>
      match ty with
      | Ctypes.Tpointer _ _ => infer_origin_from_expr e'
      | _ => ret PtrUnknown
      end
  | Clight.Eaddrof _ ty =>
      match ty with
      | Ctypes.Tpointer _ _ => ret PtrBorrowed
      | _ => ret PtrUnknown
      end
  | Clight.Ebinop _ e1 e2 ty =>
      match ty with
      | Ctypes.Tpointer _ _ =>
          do o1 <- infer_origin_from_expr e1;
          do o2 <- infer_origin_from_expr e2;
          ret (prefer_origin o1 o2)
      | _ => ret PtrUnknown
      end
  | Clight.Ederef e' ty =>
      match ty with
      | Ctypes.Tpointer _ _ => ret PtrUnknown
      | _ => ret PtrUnknown
      end
  | Clight.Efield _ _ ty =>
      match ty with
      | Ctypes.Tpointer _ _ => ret PtrUnknown
      | _ => ret PtrUnknown
      end
  | _ => ret PtrUnknown
  end.

Definition update_var_origin_from_expr (id: ident) (ty: Ctypes.type) (rhs: Clight.expr) : mon unit :=
  match ty with
  | Ctypes.Tpointer _ _ =>
      do origin <- infer_origin_from_expr rhs;
      update_var_origin id ty origin
  | _ => ret tt
  end.

Definition update_place_origin (lhs rhs: Clight.expr) : mon unit :=
  match lhs with
  | Clight.Evar id ty => update_var_origin_from_expr id ty rhs
  | Clight.Etempvar id ty => update_var_origin_from_expr id ty rhs
  | _ => ret tt
  end.

Definition update_temp_origin (id: ident) (rhs_ty: Ctypes.type) (rhs: Clight.expr) : mon unit :=
  update_var_origin_from_expr id rhs_ty rhs.

Parameter (malloc_id free_id: ident).

Definition origin_from_call (call_e: Clight.expr) : ptr_origin :=
  match call_e with
  | Clight.Evar fid _ =>
      if ident_eq fid malloc_id then PtrHeap else PtrUnknown
  | _ => PtrUnknown
  end.

Definition update_call_result_origin (id: ident) (ret_ty: Ctypes.type) (call_e: Clight.expr) : mon unit :=
  match ret_ty with
  | Ctypes.Tpointer _ _ =>
      let origin := origin_from_call call_e in
      update_var_origin id ret_ty origin
  | _ => ret tt
  end.

Definition get_return_ctype fe : option Ctypes.type :=
  match fe with
  | Evar _ fty 
  | Etempvar _ fty=>
      match fty with
      | Tpointer (Ctypes.Tfunction _ ty' _) _
      | Ctypes.Tfunction _ ty' _=> Some ty'
      | _ => None
      end
  | _ => None
  end.

Definition get_return_type fe : option type :=
  match get_return_ctype fe with
  | Some ty => Some (to_rusttype ty)
  | None => None
  end.

Definition malloc_decl : (Ctypes.fundef Clight.function) :=
  (Ctypes.External EF_malloc (Ctypes.Tcons Ctyping.size_t Ctypes.Tnil) (Tpointer Ctypes.Tvoid noattr) cc_default).
Definition free_decl : (Ctypes.fundef Clight.function) :=
  (Ctypes.External EF_free (Ctypes.Tcons (Tpointer Ctypes.Tvoid noattr) Ctypes.Tnil) Ctypes.Tvoid cc_default).
(* Definition free_fun_expr : Clight.expr :=
  Evar free_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer Ctypes.Tvoid noattr) Ctypes.Tnil) Ctypes.Tvoid cc_default).
(* return [free(arg)], ty is the type arg points to, i.e. [arg: *ty] *)
Definition call_free (arg: Clight.expr) : Clight.statement :=
  Clight.Scall None free_fun_expr (arg :: nil). *)

Section TRANSL.

  (* Variable ce: composite_env.
    Variable tce: Rusttypes.composite_env. *)

  (* Local Open Scope string_scope. *)
  Local Open Scope gensym_monad_scope.

  Fixpoint expr_depth (e: Clight.expr) : nat :=
    match e with
    | Clight.Evar _ _ => 2
    | Clight.Ederef e' _ => 2 + 2 * expr_depth e'
    | Clight.Ebinop _ e1 e2 _ => 2 + 2 * ((expr_depth e1) + (expr_depth e2))
    | Clight.Eunop _ e' _ => 2 + 2 * expr_depth e'
    | Clight.Efield e' _ _ => 2 + 2 * expr_depth e'
    | Clight.Eaddrof e' _ => 2 + 2 * expr_depth e'
    | Clight.Ecast e' _ => 2 + 2 * expr_depth e'
    | Clight.Econst_int _ _ => 2
    | Clight.Econst_float _ _ => 2
    | Clight.Econst_single _ _ => 2
    | Clight.Econst_long _ _ => 2
    | Clight.Esizeof _ _ => 2
    | Clight.Ealignof _ _ => 2
    | Clight.Etempvar _ _ => 2
    end.


  (* This helper function is used to generate a place for sub-expr of deref expr in c *)
  Fixpoint sub_cexpr_to_place (locals: list ident) (depth: nat) (e: Clight.expr): mon Rustlight.place :=
    let sub_cexpr_to_place := sub_cexpr_to_place locals depth in
    match depth with
    | 0%nat => error (msg "Unsupported lvalue expression: depth is 0")
    | S d =>
      (* let cexpr_to_place := cexpr_to_place d in *)
      let cexpr_to_pexpr := cexpr_to_pexpr locals d in
      match e with
      | Clight.Evar id ty =>
          do rty <- get_rusttype_for_id id ty;
          ret (Rustlight.Plocal id rty)
      | Clight.Etempvar id ty =>
          do rty <- get_rusttype_for_id id ty;
          ret (Rustlight.Plocal id rty)
      | Clight.Ederef e' ty =>
          do p <- sub_cexpr_to_place e';
          ret (Rustlight.Pderef p (rust_type_with_origin ty PtrUnknown))
      | Clight.Efield e' id ty =>
          do p <- sub_cexpr_to_place e';
          ret (Rustlight.Pfield p id (rust_type_with_origin ty PtrUnknown))
      | Clight.Ebinop op e1 e2 ty => 
            match ty with
            | Ctypes.Tpointer _ _ =>
                do origin <- infer_origin_from_expr e;
                let rty := rust_type_with_origin ty origin in
                do i <- gensym locals rty;
                do _ <- update_var_origin i ty origin;
                do e1' <- cexpr_to_pexpr e1;
                do e2' <- cexpr_to_pexpr e2;
                let re := Rustlight.Ebinop op e1' e2' rty in
                ret (Rustlight.Pparenthesize i rty re)
            | _ =>
                error (msg "not pointer, Unsupported lvalue binary operation")
            end
      (* | Clight.Ecast e' ty => 
            match ty with
            | Ctypes.Tpointer _ _ => 
                do i <- gensym locals (to_rusttype ty);
                do e'' <- cexpr_to_pexpr e';
                let rty := to_rusttype ty in
                let re := Rustlight.Eas e'' rty in
                ret (Rustlight.Pparenthesize i (to_rusttype ty) re)
            | _ => error (msg "lvalue cast only support pointer")
            end *)
      | _ => error (msg "Unsupported lvalue expression in sub_cexpr_to_place")
      end
    end

  (** Convert Clight expression to Rustlight place *)
  with cexpr_to_place (locals: list ident) (depth: nat) (e: Clight.expr): mon Rustlight.place :=
    match depth with
    | 0%nat => error (msg "Unsupported lvalue expression: depth is 0")
    | S d =>
      let cexpr_to_place := cexpr_to_place locals d in
      let sub_cexpr_to_place := sub_cexpr_to_place locals d in
      (* let cexpr_to_pexpr := cexpr_to_pexpr d in *)
      match e with
      | Clight.Evar id ty =>
          do rty <- get_rusttype_for_id id ty;
          ret (Rustlight.Plocal id rty)
      | Clight.Etempvar id ty =>
          do rty <- get_rusttype_for_id id ty;
          ret (Rustlight.Plocal id rty)
      | Clight.Ederef e' ty =>
          do p <- sub_cexpr_to_place e';
          ret (Rustlight.Pderef p (rust_type_with_origin ty PtrUnknown))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Pfield p id (rust_type_with_origin ty PtrUnknown))
      | Clight.Ebinop _ _ _ _ => 
          error (msg "Unsupported lvalue expression: binary operation")
      | Clight.Econst_int _ _ => error (msg "Unsupported lvalue expression: constant integer")
      | Clight.Econst_float _ _ => error (msg "Unsupported lvalue expression: constant float")
      | Clight.Econst_single _ _ => error (msg "Unsupported lvalue expression: constant single")
      | Clight.Econst_long _ _ => error (msg "Unsupported lvalue expression: constant long")
      | Clight.Eunop _ _ _ => error (msg ("Unsupported lvalue expression: unary operation "))
      | Clight.Esizeof _ _ => error (msg "Unsupported lvalue expression: sizeof")
      | Clight.Ealignof _ _ => error (msg "Unsupported lvalue expression: alignof")
      | Clight.Ecast _ _ => 
          error (msg "Unsupported lvalue expression: cast")
      | _ => error (msg "Unsupported lvalue expression: unknown expression")
      end
    end
  (** Convert Clight expression to Rustlight pure expression *)
  with cexpr_to_pexpr (locals: list ident) (depth: nat) (e: Clight.expr): mon Rustlight.pexpr :=
    match depth with
    | 0%nat => error (msg "Unsupported rvalue expression: depth is 0")
    | S d =>
      let cexpr_to_place := cexpr_to_place locals d in
      let cexpr_to_pexpr := cexpr_to_pexpr locals d in
      match e with
      | Clight.Econst_int i ty =>
          let rty :=
            match ty with
            | Ctypes.Tpointer _ _ =>
                if Int.eq i Int.zero
                then rust_type_with_origin ty PtrNull
                else rust_type_with_origin ty PtrUnknown
            | _ => to_rusttype ty
            end in
          ret (Rustlight.Econst_int i rty)
      | Clight.Econst_float f ty => ret (Rustlight.Econst_float f (to_rusttype ty))
      | Clight.Econst_single f ty => ret (Rustlight.Econst_single f (to_rusttype ty))
      | Clight.Econst_long l ty =>
          let rty :=
            match ty with
            | Ctypes.Tpointer _ _ =>
                if Int64.eq l Int64.zero
                then rust_type_with_origin ty PtrNull
                else rust_type_with_origin ty PtrUnknown
            | _ => to_rusttype ty
            end in
          ret (Rustlight.Econst_long l rty)
      | Clight.Eunop op e' ty => 
          do pe <- cexpr_to_pexpr e';
          match ty with
          | Ctypes.Tpointer _ _ =>
              do origin <- infer_origin_from_expr (Clight.Eunop op e' ty);
              ret (Rustlight.Eunop op pe (rust_type_with_origin ty origin))
          | _ =>
              ret (Rustlight.Eunop op pe (to_rusttype ty))
          end
      | Clight.Ebinop op e1 e2 ty => 
          do pe1 <- cexpr_to_pexpr e1;
          do pe2 <- cexpr_to_pexpr e2;
          match ty with
          | Ctypes.Tpointer _ _ =>
              do origin <- infer_origin_from_expr (Clight.Ebinop op e1 e2 ty);
              ret (Rustlight.Ebinop op pe1 pe2 (rust_type_with_origin ty origin))
          | _ =>
              ret (Rustlight.Ebinop op pe1 pe2 (to_rusttype ty))
          end
      | Clight.Evar id ty => 
          do rty <- get_rusttype_for_id id ty;
          let p := Rustlight.Plocal id rty in
          ret (Eplace p rty)
      | Clight.Etempvar id ty =>
          do rty <- get_rusttype_for_id id ty;
          let p := Rustlight.Plocal id rty in
          ret (Eplace p rty)
      | Clight.Eaddrof e' ty => 
          let rty := rust_type_with_origin ty PtrBorrowed in
          do i <- gensym locals rty;
          do p <- cexpr_to_place e';
          ret (Eref i Mutable p rty)
      | Clight.Ederef e' ty => 
          do e'' <- cexpr_to_pexpr e';
          ret (Rustlight.Ederef e'' (rust_type_with_origin ty PtrUnknown))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          let rty := rust_type_with_origin ty PtrUnknown in
          ret (Rustlight.Eplace (Rustlight.Pfield p id rty) rty)
      | Clight.Esizeof ty ty' => ret (Rustlight.Esizeof (to_rusttype ty) (to_rusttype ty'))
      | Clight.Ecast e' ty => 
          do pe <- cexpr_to_pexpr e';
          match ty with
          | Ctypes.Tpointer _ _ =>
              do origin <- infer_origin_from_expr (Clight.Ecast e' ty);
              ret (Rustlight.Eas pe (rust_type_with_origin ty origin))
          | _ =>
              ret (Rustlight.Eas pe (to_rusttype ty))
          end
      (* | Clight.Ealignof ty ty' => ret (Rustlight.Ealignof (to_rusttype ty) (to_rusttype ty')) *)
      | _ => error (msg "Unsupported rvalue expression")
      end
    end.

  
  Fixpoint transl_expr_list (locals: list ident) (el: list Clight.expr) : mon (list Rustlight.pexpr) :=
  match el with
  | nil => ret nil
  | e :: rest =>
      do pe <- cexpr_to_pexpr locals (expr_depth e) e;
      do rest' <- transl_expr_list locals rest;
      ret (pe :: rest')
  end.

  Definition pexpr_to_expr (pe: Rustlight.pexpr): Rustlight.expr :=
  Rustlight.Epure pe.

  Definition empty_place (locals: list ident): mon Rustlight.place := 
    do i <- gensym locals Rusttypes.Tunit;
    ret (Rustlight.Plocal i Rusttypes.Tunit). 
  
  Definition tbool := Ctypes.Tint IBool Unsigned noattr.

  Fixpoint collect_case_conds (ls: Clight.labeled_statements) : list Z :=
    match ls with
    | Clight.LSnil => []
    | Clight.LScons (Some n) _ rest => n :: collect_case_conds rest
    | Clight.LScons None _ rest => collect_case_conds rest
    end.
  
  Fixpoint ends_with_break (s: Clight.statement) : bool :=
    match s with
    | Clight.Sbreak => true
    | Clight.Ssequence _ s2 => ends_with_break s2
    | _ => false
    end.

  Fixpoint remove_break (s: Clight.statement) : Clight.statement :=
    match s with
    | Clight.Sbreak => Clight.Sskip
    | Clight.Ssequence s1 s2 =>
        Clight.Ssequence s1 (remove_break s2)
    | s => s
    end.  

  Fixpoint ends_with_break_rs (s: Rustlight.statement) : bool :=
    match s with
    | Rustlight.Sbreak => true
    | Rustlight.Ssequence _ s2 => ends_with_break_rs s2
    | _ => false
    end.
  
  Fixpoint remove_break_rs (s: Rustlight.statement) : Rustlight.statement :=
    match s with
    | Rustlight.Sbreak => Rustlight.Sskip
    | Rustlight.Ssequence s1 s2 =>
        Rustlight.Ssequence s1 (remove_break_rs s2)
    | s => s
    end.

  (* Fixpoint collect_until_break_and_rest
    (ls: Clight.labeled_statements)
    : mon (Clight.statement * Clight.labeled_statements) :=
    match ls with
    | Clight.LSnil => ret (Clight.Sskip, Clight.LSnil)
    | Clight.LScons o st rest =>
        (* do rs <- transl_stmt st; *)
        let rs' := remove_break st in
        if ends_with_break st then
          ret (rs', rest)
        else
          do (rest_stmts, rest_ls) <- collect_until_break_and_rest rest;
          ret (Clight.Ssequence rs' rest_stmts, rest_ls)
    end. *)

  Fixpoint split_cases
  (ls: Clight.labeled_statements)
  : list (option Z * Clight.statement) :=
  match ls with
  | Clight.LSnil => []
  | Clight.LScons o st rest =>
      let st' := remove_break st in
      if ends_with_break st || (match rest with Clight.LSnil => true | _ => false end) then
        ((o, st') :: split_cases rest)
      else
        let '(rest_cases) := split_cases rest in
        match rest_cases with
        | [] => [(o, st')]
        | (o', st'') :: xs => (o, Clight.Ssequence st' st'') :: rest_cases
        end
  end.

  (* Fixpoint split_cases
    (ls: Clight.labeled_statements)
    (acc: list (option Z * Clight.statement))
    : list (option Z * Clight.statement) :=
    match ls with
    | Clight.LSnil => List.rev acc
    | Clight.LScons o st rest =>
        let st' := remove_break st in
        if ends_with_break st || (match rest with Clight.LSnil => true | _ => false end) then
          split_cases rest ((o, st') :: acc)
        else
          let '(rest_cases) := split_cases rest acc in
          match rest_cases with
          | [] => [(o, st')]
          | (o', st'') :: xs => (o, Clight.Ssequence st' st'') :: rest_cases
          end
    end. *)

  Definition default_cond (e: Clight.expr) (case_conds: list Z) : Clight.expr :=
  fold_right (fun n acc =>
    Clight.Ebinop Oand
        (Clight.Ebinop One
          e
          (Clight.Econst_int (Int.repr n) (Clight.typeof e))
          tbool)
          acc
          tbool
  ) (Clight.Econst_int (Int.repr 1) tbool) case_conds.

  Fixpoint build_ifelse
    (e: Clight.expr)
    (case_conds: list Z)
    (lst: list (option Z * Clight.statement))
    : Clight.statement :=
    match lst with
    | [] => Clight.Sskip
    | (Some n, st) :: xs =>
        let cond := Clight.Ebinop Oeq e
                      (Clight.Econst_int (Int.repr n) (Clight.typeof e))
                      tbool in
        Clight.Sifthenelse cond st (build_ifelse e case_conds xs)
    | (None, st) :: xs =>
        let cond := default_cond e case_conds in
        Clight.Sifthenelse cond st (build_ifelse e case_conds xs)
    end.

  Definition switch_to_ifelse (e: Clight.expr) (cases: Clight.labeled_statements) : Clight.statement :=
    let case_conds := collect_case_conds cases in
    let cases_list := split_cases cases in
    build_ifelse e case_conds cases_list.

  Fixpoint elim_switch (s: Clight.statement) : Clight.statement :=
    match s with
    | Clight.Sskip => Clight.Sskip
    | Clight.Ssequence s1 s2 =>
        Clight.Ssequence (elim_switch s1) (elim_switch s2)
    | Clight.Sifthenelse e s1 s2 =>
        Clight.Sifthenelse e (elim_switch s1) (elim_switch s2)
    | Clight.Sloop s1 s2 =>
        Clight.Sloop (elim_switch s1) (elim_switch s2)
    | Clight.Sbreak => Clight.Sbreak
    | Clight.Scontinue => Clight.Scontinue
    | Clight.Sassign e1 e2 => Clight.Sassign e1 e2
    | Clight.Sset id e => Clight.Sset id e
    | Clight.Scall optid e args => Clight.Scall optid e args
    | Clight.Sreturn None => Clight.Sreturn None
    | Clight.Sreturn (Some e) => Clight.Sreturn (Some e)
    | Clight.Sswitch e cases =>
        switch_to_ifelse e cases
    | Clight.Slabel lbl s1 =>
        Clight.Slabel lbl (elim_switch s1)
    | Clight.Sgoto lbl => Clight.Sgoto lbl
    | Clight.Sbuiltin optid ef tyargs args =>
        Clight.Sbuiltin optid ef tyargs args
    end.

  Fixpoint transl_stmt (locals: list ident) (ret_ty: Ctypes.type) (s: Clight.statement): mon Rustlight.statement :=
  let cexpr_to_place := cexpr_to_place locals in
  let cexpr_to_pexpr := cexpr_to_pexpr locals in
  
  match s with
  | Clight.Sskip => ret Rustlight.Sskip
  | Clight.Sbreak => ret Rustlight.Sbreak
  | Clight.Scontinue => ret Rustlight.Scontinue

  | Clight.Sassign e1 e2 =>
      do _ <- update_place_origin e1 e2;
      do p <- cexpr_to_place (expr_depth e1) e1;
      do pe <- cexpr_to_pexpr (expr_depth e2) e2;
      ret (Rustlight.Sassign p (Rustlight.Epure pe))

  | Clight.Sset id e =>
      let ty := Clight.typeof e in
      do _ <- update_temp_origin id ty e;
      do pe <- cexpr_to_pexpr (expr_depth e) e;
      do rty <- get_rusttype_for_id id ty;
      let assign_stmt := Rustlight.Sassign (Rustlight.Plocal id rty) (Rustlight.Epure pe) in
      ret assign_stmt

  | Clight.Sifthenelse e s1 s2 =>
      do pe <- cexpr_to_pexpr (expr_depth e) e;
      do rs1 <- transl_stmt locals ret_ty s1;
      do rs2 <- transl_stmt locals ret_ty s2;
      ret (Rustlight.Sifthenelse (Rustlight.Epure pe) rs1 rs2)

  | Clight.Scall optid e args =>
      do pe <- cexpr_to_pexpr (expr_depth e) e;
      do pargs <- transl_expr_list locals args;
      match optid with
      | None => 
          do dummy_place <- empty_place locals;
          ret (Rustlight.Scall dummy_place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
      | Some id => 
          match get_return_ctype e with
          | Some cty =>
              do _ <- update_call_result_origin id cty e;
              do rty <- get_rusttype_for_id id cty;
              let place := Rustlight.Plocal id rty in
              ret (Rustlight.Scall place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
          | None => 
              error (msg "Cannot get return type of function in Scall: Clight2Rustlight")
          end
      end

  | Clight.Sreturn (Some e) => 
      let expected_cty := ret_ty in
      do origin_expr <- infer_origin_from_expr e;
      let origin :=
        match expected_cty, e with
        | Ctypes.Tpointer _ _, Clight.Econst_int i _ =>
            if Int.eq i Int.zero then PtrNull else origin_expr
        | Ctypes.Tpointer _ _, Clight.Econst_long l _ =>
            if Int64.eq l Int64.zero then PtrNull else origin_expr
        | _, _ => origin_expr
        end in
      let rty := rust_type_with_origin expected_cty origin in
      do pe <- cexpr_to_pexpr (expr_depth e) e;
      do i <- gensym locals rty;
      do _ <- set_var_info i rty origin;
      let ret_place := Rustlight.Plocal i rty in
      let translated_return := Rustlight.Ssequence
          (Rustlight.Sassign ret_place (Rustlight.Epure pe))
          (Rustlight.Sreturn ret_place)
      in
      ret translated_return
      
  | Clight.Sreturn None => 
      do dummy_place <- empty_place locals;
      ret (Rustlight.Sreturn dummy_place)

  | Clight.Ssequence s1 s2 => 
      do rs1 <- transl_stmt locals ret_ty s1;
      do rs2 <- transl_stmt locals ret_ty s2;
      ret (Rustlight.Ssequence rs1 rs2)

  | Clight.Sloop s1 s2 =>
      do rs1 <- transl_stmt locals ret_ty s1;
      do rs2 <- transl_stmt locals ret_ty s2;
      ret (Rustlight.Sloop (Rustlight.Ssequence rs1 rs2))

  | _ => error (msg "Unsupported statement type in transl_stmt")
  end.



  (* with transl_stmt_list (locals: list ident) (ls: list Clight.statement): mon (list Rustlight.statement) :=
    let transl_stmt := transl_stmt locals in
    let transl_stmt_list := transl_stmt_list locals in
    match ls with
    | nil => ret nil
    | s :: res =>
      do rs <- transl_stmt s;
      do rres <- transl_stmt_list res;
      ret (rs :: rres)
    end. *)

    (* get most largest id in id list *)
  (* Fixpoint max_pos (l: list positive) : positive :=
    match l with
    | nil => 1%positive (* 默认最小值 *)
    | hd :: tl => Pos.max hd (max_pos tl)
    end. *)
  
  (* get all id from expr in clight *)
  (* Fixpoint get_ids_expr (e: Clight.expr) : list positive :=
    match e with
    | Clight.Evar id _ => [id]
    | Clight.Etempvar id _ => [id]
    | Clight.Ederef e1 _ => get_ids_expr e1
    | Clight.Eaddrof e1 _ => get_ids_expr e1
    | Clight.Eunop _ e1 _ => get_ids_expr e1
    | Clight.Ebinop _ e1 e2 _ => get_ids_expr e1 ++ get_ids_expr e2
    | Clight.Ecast e1 _ => get_ids_expr e1
    | Clight.Efield e1 _ _ => get_ids_expr e1
    | _ => []
    end. *)

  (* get all id from statement in clight *)
  (* Fixpoint get_ids_stmt (s: Clight.statement) : list positive :=
    match s with
    | Clight.Sskip => []
    | Clight.Sassign e1 e2 => get_ids_expr e1 ++ get_ids_expr e2
    | Clight.Ssequence s1 s2 => get_ids_stmt s1 ++ get_ids_stmt s2
    | Clight.Sset id e => id :: get_ids_expr e
    | Clight.Scall optid e args =>
        match optid with
        | None => get_ids_expr e ++ List.flat_map get_ids_expr args
        | Some id => id :: (get_ids_expr e ++ List.flat_map get_ids_expr args)
        end
    | Clight.Sbuiltin optid _ _ le =>
        match optid with
        | None => List.flat_map get_ids_expr le
        | Some id => id :: (List.flat_map get_ids_expr le)
        end
    | Clight.Sifthenelse e s1 s2 => get_ids_expr e ++ get_ids_stmt s1 ++ get_ids_stmt s2
    | Clight.Sloop s1 s2 => get_ids_stmt s1 ++ get_ids_stmt s2
    (* | Clight.Swhile e s1 s2 => get_ids_expr e ++ get_ids_stmt s1 ++ get_ids_stmt s2 *)
    | Clight.Sbreak => []
    | Clight.Scontinue => []
    | Clight.Sreturn None => []
    | Clight.Sreturn (Some e) => get_ids_expr e
    | Clight.Sswitch e ls => get_ids_expr e ++ get_ids_labeled_statements ls
    | Clight.Slabel _ s => get_ids_stmt s
    | Clight.Sgoto _ => []
    end
  with get_ids_labeled_statements (ls: Clight.labeled_statements) : list positive :=
    match ls with
    | Clight.LSnil => []
    | Clight.LScons _ st ls => 
        get_ids_stmt st ++ get_ids_labeled_statements ls
    end. *)

  (* get all id from function in clight *)
  (* Definition get_max_id_function (f: Clight.function) : positive :=
  max_pos (get_ids_stmt f.(Clight.fn_body)). *)

  (** Remove the pattern "return 0" from the end of a statement *)
  Fixpoint remove_return_zero_pattern (s: Clight.statement): Clight.statement :=
    match s with
    | Clight.Ssequence s1 s2 =>
        (* Check if s2 is exactly "return 0" *)
        match s2 with
        | Clight.Sreturn (Some return_expr) =>
            match return_expr with
            | Clight.Econst_int n _ =>
                if Int.eq n Int.zero then
                    (* Found "return 0" - remove it *)
                    s1
                else
                    (* Not returning 0, keep both statements *)
                    Clight.Ssequence s1 (remove_return_zero_pattern s2)
            | _ =>
                (* Not returning constant, keep both statements *)
                Clight.Ssequence s1 (remove_return_zero_pattern s2)
            end
        | _ =>
            (* Not a return statement, recursively process both parts *)
            Clight.Ssequence s1 (remove_return_zero_pattern s2)
        end
    | _ => s
    end.

Require Import SimplLocals.
  (** Convert Clight function to Rustlight function *)
  Definition transl_function (main_id: ident) (id: ident) (f: Clight.function): res Rustlight.function :=
    let cenv_ids := VSet.elements (cenv_for f) in
    let locals_clight := List.map (@fst ident _) (Clight.fn_params f ++ Clight.fn_vars f ++ Clight.fn_temps f) in
    let locals := cenv_ids ++ locals_clight in
    let no_swtich_stmts := elim_switch (Clight.fn_body f) in

    let init_gen :=
      let after_params := register_var_list PtrBorrowed (Clight.fn_params f) in
      match after_params initial_generator with
      | Err msg => Error msg
      | Res _ g_params =>
          let after_locals := register_var_list PtrUnknown (Clight.fn_vars f) in
          match after_locals g_params with
          | Err msg => Error msg
          | Res _ g_locals =>
              let after_temps := register_var_list PtrUnknown (Clight.fn_temps f) in
              match after_temps g_locals with
              | Err msg => Error msg
              | Res _ g_final => OK g_final
              end
          end
      end
    in
    match init_gen with
    | Error msg => Error msg
    | OK initial_gen_with_scope =>
    (* let max_id := Pos.succ (max_pos locals) in *)
    (* main function in rust is different in c 
     c:    int main() { ...; return 0; }
     rust: fn main() {}  *)
    if ident_eq main_id id then
      match no_swtich_stmts with
      | Clight.Ssequence inner_stmt _ =>  (* delete Ssequence (return 0) *)
        let inner_stmt := remove_return_zero_pattern inner_stmt in  
              match transl_stmt locals (Clight.fn_return f) inner_stmt initial_gen_with_scope with
              | Err msg => Error msg
              | Res body g =>
                  (* check that temporaries are not repeated *)
                  if list_norepet_dec ident_eq (var_names g.(gen_trail)) then
                    if list_disjoint_dec ident_eq locals (var_names g.(gen_trail)) then
                    let param_types := map_decl_types g.(gen_env) (Clight.fn_params f) in
                    let local_types := map_decl_types g.(gen_env)
                                        (Clight.fn_vars f ++ Clight.fn_temps f) in
                    OK {| Rustlight.fn_generic_origins := [];
                         Rustlight.fn_origins_relation := [];
                         Rustlight.fn_drop_glue := None;
                         Rustlight.fn_return := Tunit;  
                         (* In rust, return value of main is Tunit *)
                         Rustlight.fn_callconv := (Clight.fn_callconv f);
                         (* Rustlight.fn_vars := locals ++ g.(gen_trail); *)
                         Rustlight.fn_vars := local_types ++ g.(gen_trail);
                         Rustlight.fn_params := param_types;
                         Rustlight.fn_body := body
                       |}
                    else
                      let vars := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_vars f) in
                      let temps := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_temps f) in
                      let params := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_params f) in
                      let g_trail := flat_map (fun '(id, ty) => [POS id; MSG " "]) g.(gen_trail) in
                      let msg := 
                        MSG "temporary variables in Clight2rustlight are not disjoint with locals" ::
                        MSG "      vars: " :: vars ++
                        MSG "           temps: " :: temps ++
                        MSG "           params: " :: params ++
                        MSG "           g_trail: " :: g_trail ++
                        nil in
                      Error msg
                  else
                    Error (msg "repeated temporary variables in Clight2rustlight")
              end
      | _ => Error (msg "Main function has unexpected structure")
      end
    else
      (* other function *)
      match transl_stmt locals (Clight.fn_return f) no_swtich_stmts initial_gen_with_scope with
      | Err msg => Error msg
      | Res body g =>
          (* check that temporaries are not repeated *)
          if list_norepet_dec ident_eq (var_names g.(gen_trail)) then
            if list_disjoint_dec ident_eq locals (var_names g.(gen_trail)) then
            let param_types := map_decl_types g.(gen_env) (Clight.fn_params f) in
            let local_types := map_decl_types g.(gen_env)
                                    (Clight.fn_vars f ++ Clight.fn_temps f) in
            OK {| Rustlight.fn_generic_origins := [];
                 Rustlight.fn_origins_relation := [];
                 Rustlight.fn_drop_glue := None;
                 Rustlight.fn_return := to_rusttype (Clight.fn_return f);
                 Rustlight.fn_callconv := (Clight.fn_callconv f);
                 Rustlight.fn_vars := local_types ++ g.(gen_trail);
                 Rustlight.fn_params := param_types;
                 Rustlight.fn_body := body
               |}
            else
              let vars := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_vars f) in
              let temps := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_temps f) in
              let params := flat_map (fun '(id, ty) => [POS id; MSG " "]) (Clight.fn_params f) in
              let g_trail := flat_map (fun '(id, ty) => [POS id; MSG " "]) g.(gen_trail) in
              let msg := 
                MSG "temporary variables in Clight2rustlight are not disjoint with locals" ::
                MSG "      vars: " :: vars ++
                MSG "           temps: " :: temps ++
                MSG "           params: " :: params ++
                MSG "           g_trail: " :: g_trail ++
                nil in
              Error msg
          else
            Error (msg "repeated temporary variables in Clight2rustlight")
      end
    end.

(* Definition tint := Ctypes.Tint I32 Signed noattr.
Parameter _b : ident.
Parameter _t'1 : ident.
Parameter _f : ident.

Definition test_main : Clight.function := {|
  Clight.fn_return := tint;
  Clight.fn_callconv := cc_default;
  Clight.fn_params := nil;
  Clight.fn_vars := nil;
  Clight.fn_temps := ((_b, tint) :: (_t'1, tint) :: nil);
  Clight.fn_body :=
(Clight.Ssequence
  (Clight.Ssequence
    (Clight.Scall (Some _t'1)
      (Clight.Evar _f (Ctypes.Tfunction (Ctypes.Tcons tint Ctypes.Tnil) tint cc_default))
      ((Clight.Econst_int (Int.repr 3) tint) :: nil))
    (Clight.Sset _b (Clight.Etempvar _t'1 tint)))
  (Clight.Sreturn (Some (Clight.Econst_int (Int.repr 0) tint))))
|}. *)
  
(* Compute transl_function 1%positive 1%positive test_main. *)

  (* Local Open Scope string_scope. *)
  

  Local Open Scope error_monad_scope.

  Definition transl_fundef (main_id: ident) (id: ident) (f: Clight.fundef): res Rustlight.fundef :=
    match f with
    | Ctypes.Internal func =>
        do tf <- transl_function main_id id func;
        OK (Internal tf)
    | Ctypes.External extfun typelist ty cconv =>
        OK (External [] [] extfun (to_rusttypelist typelist) (to_rusttype ty) cconv)
    end.

  (* Convert a global definition keeping Rustlight.fundef but changing Ctypes.type to Rusttypes.type *)
  Definition convert_globdef_type (gdef: globdef Rustlight.fundef Ctypes.type): globdef Rustlight.fundef Rusttypes.type :=
    match gdef with
    | Gfun f =>
        match f with
        | Internal fd =>
            Gfun (Internal fd)
        | External origins org_rels ef args mon cc =>
            Gfun (External origins org_rels ef args mon cc) 
        end
    | Gvar v =>
        Gvar {|
            gvar_info := to_rusttype v.(gvar_info);
            gvar_init := v.(gvar_init);
            gvar_readonly := v.(gvar_readonly);
            gvar_volatile := v.(gvar_volatile)
          |}
    end.

  Local Open Scope gensym_monad_scope.

  (* get id from Ctype member *)
  Definition get_member_id (m: Ctypes.member) : ident :=
    match m with
    | Ctypes.Member_plain id _ => id
    | Ctypes.Member_bitfield id _ _ _ _ _ => id
    end.

  (* get id from Ctype members *)
  Definition get_members_id (ms: Ctypes.members) : list ident :=
    List.map get_member_id ms.

  (* get id from Ctype composite_definition *)
  Definition get_composite_definition_id (cd: Ctypes.composite_definition) : list ident :=
    match cd with
    | Ctypes.Composite id _ ms _ => id :: get_members_id ms
    end.
  
  (* get id from Ctype composite_definition list *)
  Fixpoint get_composite_definition_ids (cd: list Ctypes.composite_definition) : list ident :=
    match cd with
    | nil => nil
    | h::t => get_composite_definition_id h ++ get_composite_definition_ids t
    end.

  (* get max id from Ctype composite_definition list *)
  (* Definition get_max_composite_definition_id (cd: list Ctypes.composite_definition) : ident :=
    max_pos (get_composite_definition_ids cd). *)
    
  (* convert Ctype member to Rusttype member *)
  Fixpoint convert_members (ms:Ctypes.members) : mon Rusttypes.members :=
    match ms with
    | nil => ret (nil)
    | h::t => match h with
              | (Ctypes.Member_plain id ty) =>
                  do cm <- convert_members t;
                  ret ((Rusttypes.Member_plain id (to_rusttype ty)) :: cm)
              | (Ctypes.Member_bitfield id _ _ _ _ _) =>
                  error (msg "not support member bitfield")
              end
    end.

  Fixpoint convert_composite_definition (cd:list Ctypes.composite_definition) : mon (list Rusttypes.composite_definition) :=
    match cd with
    | nil => ret (nil)
    | (Ctypes.Composite id su m a)::t =>
        let new_su := match su with
                      | Ctypes.Struct => Rusttypes.Struct
                      | Ctypes.Union => Rusttypes.TaggedUnion 
                      end in
        do new_m <- convert_members m;
        do rcd <- convert_composite_definition t;
        ret ((Rusttypes.Composite id new_su new_m [] []) :: rcd)
    end.

  Local Open Scope error_monad_scope.

  Definition transf_var (id: ident) (ty: Ctypes.type) := OK (to_rusttype ty).
  
  Definition transf_globvar (i: ident) (g: globvar Ctypes.type) : res (globvar type) :=
    do info' <- transf_var i g.(gvar_info);
    OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)). 

  Definition transl_program (p: Clight.program): res program :=
    (* let max_composite_definition_id := get_max_composite_definition_id (Ctypes.prog_types p) in *)
    (* create initial generator with max id *)
    let initial_gen := initial_generator (*(Pos.succ max_composite_definition_id)*) in
    match convert_composite_definition (Ctypes.prog_types p) initial_gen with
    | Res co_defs g =>
        let tce := Rusttypes.build_composite_env co_defs in
        (match tce with
         | OK tce =>
             fun Hyp =>
               (* auxiliary function, just to pass main_ident *)
               let transl_def (main_id: ident) (def: ident * globdef Clight.fundef Ctypes.type) :=
                 match def with
                 | (id, Gfun f) =>
                     do tf <- transl_fundef main_id id f;  (* pass ident *)
                     OK (id, Gfun tf)
                 | (id, Gvar v) =>
                     do tv <- transf_globvar id v;
                     OK (id, Gvar tv)
                 end in
               (* transfer all def *)
               let transl_def := fun def => transl_def (Ctypes.prog_main p) def in
               do defs <- mmap transl_def (Ctypes.prog_defs p);
               (* add malloc and free, to pass check_malloc_free_existence in Clightgen.v *)
               let defs := if in_dec ident_eq malloc_id (List.map (fun '(id, ty) => id) defs)
                 then defs else (malloc_id, Gfun (Rusttypes.External [] [] AST.EF_malloc 
                  Rusttypes.Tnil Rusttypes.Tunit AST.cc_default)) :: defs in
               let defs := if in_dec ident_eq free_id (List.map (fun '(id, ty) => id) defs)
                then defs else (free_id, Gfun (Rusttypes.External [] [] AST.EF_free 
                  Rusttypes.Tnil Rusttypes.Tunit AST.cc_default)):: defs in
               OK {| Rusttypes.prog_defs := defs;
                    Rusttypes.prog_public := AST.prog_public p;
                    Rusttypes.prog_main := AST.prog_main p;
                    Rusttypes.prog_types := co_defs;
                    Rusttypes.prog_comp_env := tce;
                    Rusttypes.prog_comp_env_eq := Hyp |}
         | Error msg => fun _ => Error msg
         end) (eq_refl tce)
    | Err msg => Error msg
    end.

End TRANSL.
