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
Require Import Errors.

Require Import cfrontend.Clight.
Require Import rustfrontend.Rustlight.

Import ListNotations.

(* Local Open Scope error_monad_scope. *)

Parameter dummy_origin : unit -> origin.

(** State and error monad for generating fresh identifiers. *)

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.

Arguments Err [A g].
Arguments Res [A g].

Definition mon (A: Type) := forall (g: generator), result A g.

Definition ret {A: Type} (x: A) : mon A :=
  fun g => Res x g (Ple_refl (gen_next g)).

Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
  fun g => Err msg.

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  fun g =>
    match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
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

Parameter first_unused_ident: unit -> ident.

Definition initial_generator (x: unit) : generator :=
  mkgenerator (first_unused_ident x) nil.

Definition gensym (ty: type): mon ident :=
  fun (g: generator) =>
    Res (gen_next g)
        (mkgenerator (Pos.succ (gen_next g)) ((gen_next g, ty) :: gen_trail g))
        (Ple_succ (gen_next g)).

(** Convert Clight type to Rustlight type *)
Fixpoint to_rusttype (ty: Ctypes.type): Rusttypes.type :=
  match ty with
  | Ctypes.Tvoid => Rusttypes.Tunit
  | Ctypes.Tint sz si _ => Rusttypes.Tint sz si
  | Ctypes.Tlong si _ => Rusttypes.Tlong si
  | Ctypes.Tfloat fz _ => Rusttypes.Tfloat fz
  | Ctypes.Tstruct id _ => Rusttypes.Tstruct nil id
  | Ctypes.Tunion id _ => Rusttypes.Tvariant nil id
  | Ctypes.Tpointer ty _ => Rusttypes.Traw_pointer mutable (to_rusttype ty)
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


Section MEMORY.

  Parameter (malloc_id free_id: ident).

  Definition malloc_decl : (Ctypes.fundef Clight.function) :=
    (Ctypes.External EF_malloc (Ctypes.Tcons Ctyping.size_t Ctypes.Tnil) (Tpointer Ctypes.Tvoid noattr) cc_default).

  Definition free_decl : (Ctypes.fundef Clight.function) :=
    (Ctypes.External EF_free (Ctypes.Tcons (Tpointer Ctypes.Tvoid noattr) Ctypes.Tnil) Tvoid cc_default).

  Definition free_fun_expr : Clight.expr :=
    Evar free_id (Ctypes.Tfunction (Ctypes.Tcons (Tpointer Tvoid noattr) Ctypes.Tnil) Ctypes.Tvoid cc_default).

  (* return [free(arg)], ty is the type arg points to, i.e. [arg: *ty] *)
  Definition call_free (arg: Clight.expr) : Clight.statement :=
    Clight.Scall None free_fun_expr (arg :: nil).

End MEMORY.

  Section TRANSL.

    (* Variable ce: composite_env.
    Variable tce: Rusttypes.composite_env. *)

    (* Local Open Scope string_scope. *)
    Local Open Scope gensym_monad_scope.

    Fixpoint binary_to_place (e: Clight.expr) : mon ((list int) * (list (ident * type))) :=
        match e with
        | Clight.Econst_int offset _ => 
            ret ([offset], nil)
        | Clight.Econst_long offset64 _ => 
            ret ([Int.repr (Int64.unsigned offset64)],nil)
        | Clight.Evar id ty2 =>
                ret (nil,[(id,(to_rusttype ty2))])
        | Clight.Etempvar id ty2 =>
            (* match ty2 with
            | Ctypes.Tint _ _ _ 
            | Ctypes.Tlong _ _ => *)
                ret (nil,[(id,(to_rusttype ty2))])
            (* | _ => error (msg "In binary_to_place(tempvar) : index of pointer add can only be int or long")
            end *)
        | Clight.Econst_float _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: float constant")
        | Clight.Econst_single _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: single-precision float constant")
        | Clight.Ederef _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: dereference")
        | Clight.Eaddrof _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: address-of")
        | Clight.Eunop op _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: unary operation")
        | Clight.Ecast _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: cast operation")
        | Clight.Efield _ _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: field operation")
        | Clight.Esizeof _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: sizeof operation")
        | Clight.Ealignof _ _ =>
            error (msg "In binary_to_place : Unsupported index expression in pointer addition: alignof operation")
        | Clight.Ebinop op e1' e2' ty' =>
            match op with
            | Oadd =>
                do r1 <- binary_to_place e1';
                do r2 <- binary_to_place e2';
                let (LIntL, LL) := r1 in
                let (LIntR, LR) := r2 in
                ret (LIntL ++ LIntR, LL ++ LR)
            | _ => error (msg "In binary_to_place: pointer only support add op")
            end
        end.

    (** Convert Clight expression to Rustlight place *)
    Fixpoint cexpr_to_place (e: Clight.expr): mon Rustlight.place :=
      match e with
      | Clight.Evar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Etempvar id ty => ret (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Ederef e' ty=>
          do p <- cexpr_to_place e';
          ret (Rustlight.Pderef p (to_rusttype ty))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Pfield p id (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
          match ty with
          | Ctypes.Tpointer _ _ =>
              match op with
              | Oadd =>
                  do r1 <- binary_to_place e1;
                  do r2 <- binary_to_place e2;
                  let (LI1,LP1) := r1 in
                  let (LI2,LP2) := r2 in
                  let LI := LI1 ++ LI2 in
                  let LP := LP1 ++ LP2 in
                  (* drop out the name of array, for example: int a[2]; we not need offset(a)*)
                    match LP with
                    | (i, _) :: t => ret (Rustlight.Pparenthesize i (to_rusttype ty) LI t)
                    | nil => error (msg "array pointer cannot be null")  
                    end                
              | _ => error (msg "pointer only support add op")
              end
          | _ =>
              error (msg "not pointer, Unsupported lvalue expression")
          end
      (* FIXME: support Pdowncast *)
      | Clight.Econst_int _ _ => error (msg "Unsupported lvalue expression: constant integer")
      | Clight.Econst_float _ _ => error (msg "Unsupported lvalue expression: constant float")
      | Clight.Eunop op e ty => error (msg ("Unsupported lvalue expression: unary operation "))
      | Clight.Esizeof ty' ty => error (msg "Unsupported lvalue expression: sizeof")
      | Clight.Ealignof ty' ty => error (msg "Unsupported lvalue expression: alignof")
      | Clight.Ecast e ty => 
          match ty with
          | Ctypes.Tpointer _ _ => 
              do i <- gensym (to_rusttype ty);
              ret (Rustlight.Plocal i (to_rusttype ty))
          | _ => error (msg "lvalue cast only support pointer")
          end
      | _ => error (msg "Unsupported lvalue expression: unknown expression")
      end.

    (** Convert Clight expression to Rustlight pure expression *)
    Fixpoint cexpr_to_pexpr (locals: list ident) (e: Clight.expr): mon Rustlight.pexpr :=
      match e with
      | Clight.Econst_int i ty => ret (Rustlight.Econst_int i (to_rusttype ty))
      | Clight.Econst_float f ty => ret (Rustlight.Econst_float f (to_rusttype ty))
      | Clight.Econst_single f ty => ret (Rustlight.Econst_single f (to_rusttype ty))
      | Clight.Econst_long l ty => ret (Rustlight.Econst_long l (to_rusttype ty))
      | Clight.Eunop op e' ty => 
          do pe <- cexpr_to_pexpr locals e';
          ret (Rustlight.Eunop op pe (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
          do pe1 <- cexpr_to_pexpr locals e1;
          do pe2 <- cexpr_to_pexpr locals e2;
          ret (Rustlight.Ebinop op pe1 pe2 (to_rusttype ty))
      | Clight.Evar id ty => 
          if in_dec ident_eq id locals then
            do p <- cexpr_to_place (Clight.Evar id ty);
            ret (Eplace p (to_rusttype ty))
          else
            ret (Eglobal id (to_rusttype ty))
      | Clight.Etempvar id ty =>
        (* if in_dec ident_eq id locals then
          do p <- cexpr_to_place (Clight.Evar id ty);
          ret (Eplace p (to_rusttype ty))
        else *)
          do p <- cexpr_to_place (Clight.Evar id ty);
          ret (Eplace p (to_rusttype ty))
      | Clight.Eaddrof e' ty => 
          do i <- gensym (to_rusttype ty);
          do p <- cexpr_to_place e';
          ret (Eref i Mutable p (to_rusttype ty))
      | Clight.Ederef e' ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Eplace (Rustlight.Pderef p (to_rusttype ty)) (to_rusttype ty))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          ret (Rustlight.Eplace (Rustlight.Pfield p id (to_rusttype ty)) (to_rusttype ty))
      | Clight.Esizeof ty ty' => ret (Rustlight.Esizeof (to_rusttype ty) (to_rusttype ty'))
      | Clight.Ecast e' ty => 
          do pe <- cexpr_to_pexpr locals e';
          ret (Rustlight.Eas pe (to_rusttype ty))
      (* | Clight.Ealignof ty ty' => ret (Rustlight.Ealignof (to_rusttype ty) (to_rusttype ty')) *)
      | _ => error (msg "Unsupported rvalue expression")
      end.

    Fixpoint transl_expr_list (locals: list ident) (el: list Clight.expr) : mon (list Rustlight.pexpr) :=
      match el with
      | nil => ret nil
      | e :: rest =>
          do pe <- cexpr_to_pexpr locals e;
          do rest' <- transl_expr_list locals rest;
          ret (pe :: rest')
      end.

    Definition pexpr_to_expr (pe: Rustlight.pexpr): Rustlight.expr :=
      Rustlight.Epure pe.

    Definition empty_place : Rustlight.place := 
      Rustlight.Plocal 1%positive Rusttypes.Tunit. 
    

    Fixpoint transl_stmt (locals: list ident) (s: Clight.statement): mon Rustlight.statement :=
      let transl_stmt := transl_stmt locals in
      match s with
      | Clight.Sskip => ret Rustlight.Sskip
      | Clight.Ssequence s1 s2 => 
          do rs1 <- transl_stmt s1;
          do rs2 <- transl_stmt s2;
          ret (Rustlight.Ssequence rs1 rs2)
      | Clight.Sifthenelse e s1 s2 => 
          do pe <- cexpr_to_pexpr locals e;
          do rs1 <- transl_stmt s1;
          do rs2 <- transl_stmt s2;
          ret (Rustlight.Sifthenelse (Rustlight.Epure pe) rs1 rs2)
      | Clight.Sloop s1 s2 => 
          do rs1 <- transl_stmt s1;
          ret (Rustlight.Sloop rs1)
      | Clight.Sbreak => ret Rustlight.Sbreak
      | Clight.Scontinue => ret Rustlight.Scontinue
      | Clight.Sassign e1 e2 => 
          do p <- cexpr_to_place e1;
          do pe <- cexpr_to_pexpr locals e2;
          ret (Rustlight.Sassign p (Rustlight.Epure pe))
      | Clight.Sset id e => 
          do pe <- cexpr_to_pexpr locals e;
          ret (Rustlight.Sassign (Rustlight.Plocal id (to_rusttype (Clight.typeof e))) 
                (Rustlight.Epure pe))
      | Clight.Scall optid e args =>
          do pe <- cexpr_to_pexpr locals e;
          do pargs <- transl_expr_list locals args;
          match optid with
          | None => 
              (* without return value *)
              let dummy_place := empty_place in
              ret (Rustlight.Scall dummy_place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
          | Some id => 
              (* with return value *)
              let ret_ty := to_rusttype (Clight.typeof e) in
              let place := Rustlight.Plocal id ret_ty in
              ret (Rustlight.Scall place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
          end
      | Clight.Sreturn None => 
          (* no return value*)
          ret (Rustlight.Sreturn empty_place)
      | Clight.Sreturn (Some e) => 
          do pe <- cexpr_to_pexpr locals e;
          (* create a temp variable to store return value *)
          let ret_place := Rustlight.Plocal 2%positive (to_rusttype (Clight.typeof e)) in
          (* assign the return value to the temp variable and return *)
          ret (Rustlight.Ssequence
                (Rustlight.Sassign ret_place (Rustlight.Epure pe))
                (Rustlight.Sreturn ret_place))
      (* | Clight.Sswitch e cases =>
        do pe <- cexpr_to_pexpr locals e;
        let fix convert_cases (cases: Clight.labeled_statements) : mon Rustlight.statement :=
            match cases with
            | nil => ret Rustlight.Sskip
            | Clight.LScase n s rest =>
                do rs <- transl_stmt s;
                do rest_stmt <- convert_cases rest;
                let cond := Rustlight.Ebinop Ceq (Rustlight.Epure pe) 
                                             (Rustlight.Econst_int n (to_rusttype (Clight.typeof e))) 
                                             Rusttypes.Tbool in
                ret (Rustlight.Sifthenelse cond rs rest_stmt)
            | Clight.LSdefault s rest =>
                transl_stmt s
            end
        in
        convert_cases cases *)
      | _ => error (msg "Unsupported statement type")
      end.

    (** Convert Clight function to Rustlight function *)
    Definition transl_function (f: Clight.function): res Rustlight.function :=
      let locals := List.map (@fst ident _) (Clight.fn_params f ++ Clight.fn_vars f) in
      match transl_stmt locals (Clight.fn_body f) (initial_generator tt) with
      | Err msg =>
          Error msg
      | Res body g i =>
      OK {| Rustlight.fn_generic_origins := [];
           Rustlight.fn_origins_relation := [];
           Rustlight.fn_drop_glue := None;
           Rustlight.fn_return := to_rusttype (Clight.fn_return f);
           Rustlight.fn_callconv := (Clight.fn_callconv f);
           (* save temp variable in clight in stack(fn_vars) *)
           (* FIXME *)
           Rustlight.fn_vars := (List.map (fun '(id, ty) => (id, to_rusttype ty)) (Clight.fn_vars f ++ Clight.fn_temps f)) ++ g.(gen_trail);
           Rustlight.fn_params := List.map (fun '(id, ty) => (id, to_rusttype ty)) (Clight.fn_params f);
           Rustlight.fn_body := body
         |}
        end.

         Local Open Scope error_monad_scope.

    Definition transl_fundef (id: ident) (f: Clight.fundef): res Rustlight.fundef :=
      match f with
      | Ctypes.Internal func =>
          do tf <- transl_function func;
          OK (Internal tf)
      | Ctypes.External extfun typelist ty cconv =>
          OK (External [] [] extfun (to_rusttypelist typelist) (to_rusttype ty) cconv)
      end.

    Definition transl_globvar (id: ident) (ty: Ctypes.type) := OK (to_rusttype ty).
    (** This translates a Clight program into a Rustlight program.
        It maps each function definition using transl_fundef and preserves program structure. *)
    
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

    Definition transl_program (p: Clight.program): res program :=
      let initial_gen := initial_generator tt in
      match convert_composite_definition (Ctypes.prog_types p) initial_gen with
      | Res co_defs g i =>
          let tce := Rusttypes.build_composite_env co_defs in
          (match tce with
          | OK tce =>
          fun Hyp =>
              let ce := Ctypes.prog_comp_env p in
              do p1 <- transform_partial_program2 transl_fundef transl_globvar p;
              OK {| Rusttypes.prog_defs := AST.prog_defs p1;
                    Rusttypes.prog_public := AST.prog_public p1;
                    Rusttypes.prog_main := AST.prog_main p1;
                    Rusttypes.prog_types := co_defs;
                    Rusttypes.prog_comp_env := tce;
                    Rusttypes.prog_comp_env_eq := Hyp |}
                    | Error msg => fun _ => Error msg
                    end) (eq_refl tce)
      | Err msg => Error msg
      end.
  
    End TRANSL.
