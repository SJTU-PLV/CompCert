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

(** State and error monad for generating fresh identifiers. *)

(* get a fresh atom and update the next atom *)
(* Local Open Scope error_monad_scope. *)

Parameter fresh_atom : unit -> ident.

Definition max_nat_limit := 1000000%positive.

Parameter external_find_and_split : ident -> ident -> Z -> Rustlight.statement.
(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
                               gen_next: ident;
                               gen_trail: list (ident * type)
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

Definition initial_generator : generator :=
  mkgenerator 10000%positive nil.

(* Lemma find_fresh_incr0 :
  forall start locals n,
  Ple (find_fresh start locals n) (find_fresh (Pos.succ start) locals n).
Proof.
  intros. induction start; simpl.
Admitted.
Lemma find_fresh_incr : 
  forall start locals n,
  Ple start max_nat_limit ->
  Ple start (find_fresh start locals n).
Proof.
  intros. induction n; simpl.
  - apply H.
  - destruct (in_dec ident_eq start locals) eqn:E. 
    + eapply Ple_trans. 2: { apply find_fresh_incr0.  }
      apply IHn.
    + apply Ple_refl.
Qed.

Lemma find_fresh_property g locals :
  Ple (gen_next g) max_nat_limit ->
  Ple (gen_next g) (find_fresh (gen_next g) locals (Pos.to_nat max_nat_limit)).
Proof.
  apply find_fresh_incr.
Qed. *)

Definition gensym (locals: list ident) (ty: type) : mon ident :=
  fun (g: generator) =>
  if Pos.leb (Pos.succ (gen_next g)) max_nat_limit then
  let fresh_id := find_fresh (gen_next g) locals (Pos.to_nat max_nat_limit) in
  Res fresh_id
      (mkgenerator (Pos.succ fresh_id) ((fresh_id, ty) :: gen_trail g))
  else Err (msg "gensym: out of fresh id limit").

Definition new_origin := 1%positive.

(** Convert Clight type to Rustlight type *)
Fixpoint to_rusttype (ty: Ctypes.type): Rusttypes.type :=
  match ty with
  | Ctypes.Tvoid => Rusttypes.Tvoid
  | Ctypes.Tint sz si _ => Rusttypes.Tint sz si
  | Ctypes.Tlong si _ => Rusttypes.Tlong si
  | Ctypes.Tfloat fz _ => Rusttypes.Tfloat fz
  | Ctypes.Tstruct id _ => Rusttypes.Tstruct nil id
  | Ctypes.Tunion id _ => Rusttypes.Tvariant nil id
  | Ctypes.Tpointer ty _ => Rusttypes.Tslice Mutable (to_rusttype ty)
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
  | Ctypes.Tpointer ty _ => Rusttypes.Tslice Immutable (to_rusttype ty)
  (*todo*)
  | Ctypes.Tarray ty' sz _ => Rusttypes.Tarray Immutable (to_rusttype ty') sz
  | _ => to_rusttype ty
  end.

Definition get_return_type fe : option type :=
  match fe with
  | Evar _ fty 
  | Etempvar _ fty=>
      match fty with
      | Tpointer (Ctypes.Tfunction _ ty' _) _
      | Ctypes.Tfunction _ ty' _=> Some (to_rusttype ty')
      | _ => None
      end
  | _ => None
  end.

Parameter (malloc_id free_id: ident).

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

  Fixpoint sub_cexpr_to_place (locals: list ident) (depth: nat) (e: Clight.expr): mon Rustlight.place :=
    let sub_cexpr_to_place := sub_cexpr_to_place locals depth in
    match depth with
    | 0%nat => error (msg "Unsupported lvalue expression: depth is 0")
    | S d =>
      (* let cexpr_to_place := cexpr_to_place d in *)
      let cexpr_to_pexpr := cexpr_to_pexpr locals d in
      match e with
      | Clight.Evar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Etempvar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Ederef e' ty =>
          do p <- sub_cexpr_to_place e';
          ret (Rustlight.Pderef p (to_rusttype ty))
      | Clight.Efield e' id ty =>
          do p <- sub_cexpr_to_place e';
          ret (Rustlight.Pfield p id (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
            match ty with
            | Ctypes.Tpointer _ _ =>
                do i <- gensym locals (to_rusttype ty);
                do e1' <- cexpr_to_pexpr e1;
                do e2' <- cexpr_to_pexpr e2;
                let rty := to_rusttype ty in
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
      | Clight.Evar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Etempvar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Ederef e' ty=>
          match e' with
          | Clight.Ebinop op e1 e2 ty1 =>
              match op with
              | Oadd => 
                  do p <- sub_cexpr_to_place e';
                  ret (Rustlight.Pderef p (to_rusttype ty))
              | _ =>
                  error (msg "Unsupported lvalue expression: binary operation in dereference")
              end
          | _ =>
              do p <- sub_cexpr_to_place e';
              ret (Rustlight.Pderef p (to_rusttype ty))
          end
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Pfield p id (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
          error (msg "Unsupported lvalue expression: binary operation")
      (* FIXME: support Pdowncast *)
      | Clight.Econst_int _ _ => error (msg "Unsupported lvalue expression: constant integer")
      | Clight.Econst_float _ _ => error (msg "Unsupported lvalue expression: constant float")
      | Clight.Econst_single _ _ => error (msg "Unsupported lvalue expression: constant single")
      | Clight.Econst_long _ _ => error (msg "Unsupported lvalue expression: constant long")
      | Clight.Eunop op e' ty => error (msg ("Unsupported lvalue expression: unary operation "))
      | Clight.Esizeof ty' ty => error (msg "Unsupported lvalue expression: sizeof")
      | Clight.Ealignof ty' ty => error (msg "Unsupported lvalue expression: alignof")
      | Clight.Ecast e' ty => 
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
      | Clight.Econst_int i ty => ret (Rustlight.Econst_int i (to_rusttype ty))
      | Clight.Econst_float f ty => ret (Rustlight.Econst_float f (to_rusttype ty))
      | Clight.Econst_single f ty => ret (Rustlight.Econst_single f (to_rusttype ty))
      | Clight.Econst_long l ty => ret (Rustlight.Econst_long l (to_rusttype ty))
      | Clight.Eunop op e' ty => 
          do pe <- cexpr_to_pexpr e';
          ret (Rustlight.Eunop op pe (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
          do pe1 <- cexpr_to_pexpr e1;
          do pe2 <- cexpr_to_pexpr e2;
          ret (Rustlight.Ebinop op pe1 pe2 (to_rusttype ty))
      | Clight.Evar id ty => 
          let p := Rustlight.Plocal id (to_rusttype ty) in
          (* ret (Eplace p (to_rusttype ty)) *)
          ret (Eplace p (to_rusttype ty))
      | Clight.Etempvar id ty =>
          let p := Rustlight.Plocal id (to_rusttype ty) in
          (* ret (Eplace p (to_rusttype ty)) *)
          ret (Eplace p (to_rusttype ty))
      | Clight.Eaddrof e' ty => 
          do i <- gensym locals (to_rusttype ty);
          do p <- cexpr_to_place e';
          ret (Eref i Mutable p (to_rusttype ty))
      | Clight.Ederef e' ty => 
          do e'' <- cexpr_to_pexpr e';
          ret (Rustlight.Ederef e'' (to_rusttype ty))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Eplace (Rustlight.Pfield p id (to_rusttype ty)) (to_rusttype ty))
      | Clight.Esizeof ty ty' => ret (Rustlight.Esizeof (to_rusttype ty) (to_rusttype ty'))
      | Clight.Ecast e' ty => 
          do pe <- cexpr_to_pexpr e';
          ret (Rustlight.Eas pe (to_rusttype ty))
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

  (* Helper to identify malloc calls *)
  
  Definition get_temp_id (e: Clight.expr) : mon ident :=
  match e with
  | Clight.Evar id _ 
  | Clight.Etempvar id _
  | Clight.Ecast (Clight.Etempvar id _) _
  | Clight.Ecast (Clight.Evar id _) _ => ret id
  | _ =>
      error (msg "Cannot get return value id of function: Clight2Rustlight")
  end.

  Fixpoint transl_stmt (locals: list ident) (s: Clight.statement): mon Rustlight.statement :=
    let transl_stmt := transl_stmt locals in
    let cexpr_to_place := cexpr_to_place locals in
    let cexpr_to_pexpr := cexpr_to_pexpr locals in
    (* let transl_stmt_list := transl_stmt_list locals in *)
    match s with
            (* if andb (ident_eq tmp1 tmp2) (is_malloc f) then *)
                (* do rid <- get_temp_id e; *)
                (* do pf <- cexpr_to_pexpr (expr_depth f) f;
                do pargs <- transl_expr_list locals args;
                let target_place := Rustlight.Plocal var (to_rusttype (Clight.typeof e)) in
                ret (Rustlight.Scall target_place (Rustlight.Epure pf) (map pexpr_to_expr pargs)) *)
            (* else
              (* normal sequence *)
              do rs1 <- transl_stmt (Clight.Scall (Some tmp1) f args);
              do rs2 <- transl_stmt (Clight.Sset var (Clight.Ecast (Clight.Etempvar tmp2 tyt) ty));
              ret (Rustlight.Ssequence rs1 rs2) *)
    | Clight.Sskip => ret Rustlight.Sskip
    | Clight.Ssequence s1 s2 => 
        match s2 with
        | Clight.Scall _ _ _ =>
            error (msg "Not implemented yet: Scall")
        | Clight.Sset _ _ =>
            error (msg "Not implemented yet: Sset")
        | Clight.Sbuiltin _ _ _ _ =>
            error (msg "Not implemented yet: Sbuiltin")
        (* | Clight.Sskip => 
            do rs1 <- transl_stmt s1;
            do rs2 <- transl_stmt s2;
            ret (Rustlight.Ssequence rs1 rs2) *)
        | Clight.Slabel _ _ => error (msg "Not implemented yet: Slabel in sequence")
        | Clight.Sgoto _ => error (msg "Not implemented yet: Sgoto in sequence")
        | Clight.Sreturn _ => error (msg "Not implemented yet: Sreturn in sequence")
        | Clight.Sswitch _ _ => error (msg "Not implemented yet: Sswitch in sequence")
        | Clight.Sloop _ _ => error (msg "Not implemented yet: Sloop in sequence")
        | Clight.Sbreak => error (msg "Not implemented yet: Sbreak in sequence")
        | Clight.Scontinue => error (msg "Not implemented yet: Scontinue in sequence")
        | Clight.Sassign _ _ => 
            error (msg "Not implemented yet: Sassign in sequence")
        | Clight.Sifthenelse _ _ _ =>
            error (msg "Not implemented yet: Sifthenelse in sequence")
        (* | Clight.Ssequence _ _ =>
            error (msg "Not implemented yet: nested sequence in sequence") *)
        | _ =>
            do rs1 <- transl_stmt s1;
            do rs2 <- transl_stmt s2;
            ret (Rustlight.Ssequence rs1 rs2)
        end
        (* match (s1,s2) with
        | ( (Clight.Scall (Some tmp1) f args), (Clight.Sset var e) ) =>
            error (msg "Not implemented yet: sequence of call and set")
        | ( (Clight.Scall _ _ _), (Clight.Sset _ _) ) =>
            error (msg "Not implemented yet: sequence of call and set")
        | _ =>
            do rs1 <- transl_stmt s1;
            do rs2 <- transl_stmt s2;
            ret (Rustlight.Ssequence rs1 rs2)
        end *)
    | Clight.Sifthenelse e s1 s2 => 
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        do rs1 <- transl_stmt s1;
        do rs2 <- transl_stmt s2;
        ret (Rustlight.Sifthenelse (Rustlight.Epure pe) rs1 rs2)
    | Clight.Sloop s1 s2 => 
        do rs1 <- transl_stmt s1;
        do set2 <- transl_stmt s2;
        let rs2 := (Rustlight.Ssequence rs1 set2) in
        ret (Rustlight.Sloop rs2)
    | Clight.Sbreak => ret Rustlight.Sbreak
    | Clight.Scontinue => ret Rustlight.Scontinue
    | Clight.Sassign e1 e2 => 
        match e2 with
        | Clight.Ebinop Oadd (Clight.Evar base_ptr_id _) (Clight.Econst_int offset _) _ =>
            (* 检测到模式： new_ptr = base_ptr + constant *)
            match e1 with
            | Clight.Evar new_ptr_id _ =>
                (* 这是我们要处理的指针运算！*)
                let c_offset := Int.unsigned offset in
                (* 我们调用在 Coq 中定义的外部函数 *)
                let split_stmt := external_find_and_split base_ptr_id new_ptr_id c_offset in
                (* 使用 'ret' 将纯粹的 statement 提升到 monad 中，这修复了原始的类型错误 *)
                ret split_stmt
            | _ => (* 左边不是简单变量，按原逻辑处理 *)
                do p <- cexpr_to_place (expr_depth e1) e1;
                do pe <- cexpr_to_pexpr (expr_depth e2) e2;
                ret (Rustlight.Sassign p (Rustlight.Epure pe))
            end
        | _ =>
            (* 不是指针加法，按原逻辑处理 *)
            do p <- cexpr_to_place (expr_depth e1) e1;
            do pe <- cexpr_to_pexpr (expr_depth e2) e2;
            ret (Rustlight.Sassign p (Rustlight.Epure pe))
        end
    | Clight.Sset id e => 
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        ret (Rustlight.Sassign (Rustlight.Plocal id (to_rusttype (Clight.typeof e))) 
               (Rustlight.Epure pe))
    | Clight.Scall optid e args =>
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        do pargs <- transl_expr_list locals args;
        match optid with
        | None => 
            (* without return value *)
            do dummy_place <- empty_place locals;
            ret (Rustlight.Scall dummy_place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
        | Some id => 
            (* with return value *)
            (* let func_ty := to_rusttype (Clight.typeof e) in *)
            match get_return_type e with
            | Some ty' =>
                let place := Rustlight.Plocal id ty' in
                ret (Rustlight.Scall place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
            | None => 
                error (msg "Cannot get return type of function in transl_stmt: Clight2Rustlight")
            end
        end
    | Clight.Sreturn None => 
        (* no return value*)
        do dummy_place <- empty_place locals;
        ret (Rustlight.Sreturn dummy_place)
    | Clight.Sreturn (Some e) => 
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        (* create a temp variable to store return value *)
        do i <- gensym locals (to_rusttype (Clight.typeof e));
        let ret_place := Rustlight.Plocal i (to_rusttype (Clight.typeof e)) in
        (* assign the return value to the temp variable and return *)
        ret (Rustlight.Ssequence
               (Rustlight.Sassign ret_place (Rustlight.Epure pe))
               (Rustlight.Sreturn ret_place))
    (* | Clight.Sswitch e cases =>
        let stmt := switch_to_ifelse e cases in
        do rstmt <- transl_stmt stmt;
        ret rstmt        *)
    (* | Clight.Sswitch e cases =>
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        let case_conds := collect_case_conds cases in
        let fix convert_cases (ls: Clight.labeled_statements) : mon Rustlight.statement :=
          match ls with
          | Clight.LSnil => ret Rustlight.Sskip
          | Clight.LScons (Some n) st rest =>
              let cond := Rustlight.Ebinop Oeq pe
                            (Rustlight.Econst_int (Int.repr n) (to_rusttype (Clight.typeof e)))
                            (Rusttypes.Tint IBool Unsigned) in
              do (stmts, rest_ls) <- collect_until_break_and_rest ls;
              do rstmts <- transl_stmt stmts;
              do rest_stmt <- convert_cases rest_ls;
              ret (Rustlight.Sifthenelse cond rstmts rest_stmt)
          | Clight.LScons None st rest =>
              let default_cond :=
              fold_right (fun n acc =>
                Rustlight.Ebinop Oand
                    (Rustlight.Ebinop Oeq pe
                      (Rustlight.Econst_int (Int.repr n) (to_rusttype (Clight.typeof e)))
                      (Rusttypes.Tint IBool Unsigned)) acc
                    (Rusttypes.Tint IBool Unsigned))
            (Rustlight.Econst_int Int.one (Rusttypes.Tint IBool Unsigned))
            case_conds in
              do (stmts, rest_ls) <- collect_until_break_and_rest ls;
              do rstmts <- transl_stmt stmts;
              do rest_stmt <- convert_cases rest_ls;
              ret (Rustlight.Sifthenelse default_cond rstmts rest_stmt)
          end
        in convert_cases cases *)
    (* | Clight.Sswitch e cases =>
        do pe <- cexpr_to_pexpr (expr_depth e) e;
        let case_conds := collect_case_conds cases in
        let rec_convert_cases :=
          fix convert_cases (ls: Clight.labeled_statements) (fallthrough: Rustlight.statement) : mon Rustlight.statement :=
            match ls with
            | Clight.LSnil => ret fallthrough
            | Clight.LScons (Some n) st rest =>
                do rs <- transl_stmt st;
                let cond := Rustlight.Ebinop Oeq pe
                             (Rustlight.Econst_int (Int.repr n) (to_rusttype (Clight.typeof e)))
                             (Rusttypes.Tint IBool Unsigned) in
                do rest_stmt <- convert_cases rest fallthrough;
                if ends_with_break rs then
                  ret (Rustlight.Sifthenelse cond rs rest_stmt)
                else
                  (* do rest_stmt <- convert_cases rest fallthrough; *)
                  ret (Rustlight.Sifthenelse cond (Rustlight.Ssequence rs rest_stmt) rest_stmt)
            | Clight.LScons None st rest =>
                do rs <- transl_stmt st;
                let default_cond :=
                  fold_right (fun n acc =>
                    Rustlight.Ebinop Oand
                        (Rustlight.Ebinop Oeq pe
                          (Rustlight.Econst_int (Int.repr n) (to_rusttype (Clight.typeof e)))
                          (Rusttypes.Tint IBool Unsigned)) acc
                        (Rusttypes.Tint IBool Unsigned))
                    (Rustlight.Econst_int Int.one (Rusttypes.Tint IBool Unsigned))
                    case_conds in
                do rest_stmt <- convert_cases rest fallthrough;
                if ends_with_break rs then
                  ret (Rustlight.Sifthenelse default_cond rs rest_stmt)
                else
                  (* do rest_stmt <- convert_cases rest fallthrough; *)
                  ret (Rustlight.Sifthenelse default_cond (Rustlight.Ssequence rs rest_stmt) rest_stmt)
            end
        in
        rec_convert_cases cases Rustlight.Sskip *)
    | _ => error (msg "Unsupported statement type")
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
    (* let max_id := Pos.succ (max_pos locals) in *)
    (* main function in rust is different in c 
     c:    int main() { ...; return 0; }
     rust: fn main() {}  *)
    if ident_eq main_id id then
      match no_swtich_stmts with
      | Clight.Ssequence inner_stmt _ =>  (* delete Ssequence (return 0) *)
        let inner_stmt := remove_return_zero_pattern inner_stmt in  
              match transl_stmt locals inner_stmt initial_generator with
              | Err msg => Error msg
              | Res body g =>
                  (* check that temporaries are not repeated *)
                  if list_norepet_dec ident_eq (var_names g.(gen_trail)) then
                    if list_disjoint_dec ident_eq locals (var_names g.(gen_trail)) then
                    OK {| Rustlight.fn_generic_origins := [];
                         Rustlight.fn_origins_relation := [];
                         Rustlight.fn_drop_glue := None;
                         Rustlight.fn_return := Tunit;  
                         (* In rust, return value of main is Tunit *)
                         Rustlight.fn_callconv := (Clight.fn_callconv f);
                         (* Rustlight.fn_vars := locals ++ g.(gen_trail); *)
                         Rustlight.fn_vars := (List.map (fun '(id, ty) => (id, to_rusttype ty)) 
                                                 (Clight.fn_vars f ++ Clight.fn_temps f)) ++ g.(gen_trail);
                         Rustlight.fn_params := List.map (fun '(id, ty) => (id, to_rusttype ty)) 
                                                  (Clight.fn_params f);
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
      match transl_stmt locals no_swtich_stmts initial_generator with
      | Err msg => Error msg
      | Res body g =>
          (* check that temporaries are not repeated *)
          if list_norepet_dec ident_eq (var_names g.(gen_trail)) then
            if list_disjoint_dec ident_eq locals (var_names g.(gen_trail)) then
            OK {| Rustlight.fn_generic_origins := [];
                 Rustlight.fn_origins_relation := [];
                 Rustlight.fn_drop_glue := None;
                 Rustlight.fn_return := to_rusttype (Clight.fn_return f);
                 Rustlight.fn_callconv := (Clight.fn_callconv f);
                 Rustlight.fn_vars := (List.map (fun '(id, ty) => (id, to_rusttype ty)) 
                                         (Clight.fn_vars f ++ Clight.fn_temps f)) ++ g.(gen_trail);
                 Rustlight.fn_params := List.map (fun '(id, ty) => (id, to_rusttype ty)) 
                                          (Clight.fn_params f);
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
