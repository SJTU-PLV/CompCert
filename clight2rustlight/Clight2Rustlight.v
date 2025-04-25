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
Require Import Floats.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import Errors.

Require Import cfrontend.Clight.
Require Import rustfrontend.Rustlight.

Import ListNotations.

Local Open Scope error_monad_scope.

(** Convert Clight type to Rustlight type *)
Fixpoint to_rusttype (ty: Ctypes.type): Rusttypes.type :=
  match ty with
  | Ctypes.Tvoid => Rusttypes.Tunit
  | Ctypes.Tint sz si _ => Rusttypes.Tint sz si
  | Ctypes.Tlong si _ => Rusttypes.Tlong si
  | Ctypes.Tfloat fz _ => Rusttypes.Tfloat fz
  | Ctypes.Tstruct id _ => Rusttypes.Tstruct nil id
  | Ctypes.Tunion id _ => Rusttypes.Tvariant nil id
  (* FIXME: 1%positive *)
  | Ctypes.Tpointer ty _ => Rusttypes.Treference 1%positive Mutable (to_rusttype ty)
  (*todo*)
  | Ctypes.Tarray ty' sz _ => Rusttypes.Tarray (to_rusttype ty') sz
  | Ctypes.Tfunction tyl ty' cc => 
      Rusttypes.Tfunction nil nil (to_rustlight tyl) (to_rusttype ty') cc
  end
    
with to_rustlight (tyl: Ctypes.typelist) : Rusttypes.typelist :=
       match tyl with
       | Ctypes.Tnil => Rusttypes.Tnil
       | Ctypes.Tcons ty tyl => 
           Rusttypes.Tcons (to_rusttype ty) (to_rustlight tyl)
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

    Variable ce: composite_env.
    Variable tce: Rusttypes.composite_env.

    Local Open Scope string_scope.

    Local Open Scope error_monad_scope.
    

    (** Convert Clight expression to Rustlight place *)
    Fixpoint cexpr_to_place (e: Clight.expr): res Rustlight.place :=
      match e with
      | Clight.Evar id ty =>OK (Rustlight.Plocal id (to_rusttype ty))
      | Clight.Ederef e' ty=>
          do p <- cexpr_to_place e';
          OK (Rustlight.Pderef p (to_rusttype ty))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          OK (Rustlight.Pfield p id (to_rusttype ty))
      (* FIXME: support Pdowncast *)
      | _ => Error (msg "Unsupported lvalue expression")
      end.

    (** Convert Clight expression to Rustlight pure expression *)
    Fixpoint cexpr_to_pexpr (locals: list ident) (e: Clight.expr): res Rustlight.pexpr :=
      match e with
      | Clight.Econst_int i ty => OK (Rustlight.Econst_int i (to_rusttype ty))
      | Clight.Econst_float f ty => OK (Rustlight.Econst_float f (to_rusttype ty))
      | Clight.Econst_single f ty => OK (Rustlight.Econst_single f (to_rusttype ty))
      | Clight.Econst_long l ty => OK (Rustlight.Econst_long l (to_rusttype ty))
      | Clight.Eunop op e' ty => 
          do pe <- cexpr_to_pexpr locals e';
          OK (Rustlight.Eunop op pe (to_rusttype ty))
      | Clight.Ebinop op e1 e2 ty => 
          do pe1 <- cexpr_to_pexpr locals e1;
          do pe2 <- cexpr_to_pexpr locals e2;
          OK (Rustlight.Ebinop op pe1 pe2 (to_rusttype ty))
      | Clight.Evar id ty => 
          if in_dec ident_eq id locals then
            do p <- cexpr_to_place (Clight.Evar id ty);
            OK (Eplace p (to_rusttype ty))
          else
            OK (Eglobal id (to_rusttype ty))
      | Clight.Eaddrof e ty => 
          do p <- cexpr_to_place e;
          OK (Eref 2%positive Mutable p (to_rusttype ty))
      | Clight.Ederef e ty => 
          do p <- cexpr_to_place e;
          OK (Rustlight.Eplace (Rustlight.Pderef p (to_rusttype ty)) (to_rusttype ty))
      | Clight.Efield e' id ty => 
          do p <- cexpr_to_place e';
          OK (Rustlight.Eplace (Rustlight.Pfield p id (to_rusttype ty)) (to_rusttype ty))
      (* | Clight.Ecast e' ty => cexpr_to_pexpr locals e'
      | Clight.Esizeof ty ty' => OK (Rustlight.Esizeof (to_rusttype ty) (to_rusttype ty')) *)
      (* | Clight.Ealignof ty ty' => OK (Rustlight.Ealignof (to_rusttype ty) (to_rusttype ty')) *)
      (*FIXME ???*)
      (*  *)
      | _ => Error (msg "Unsupported rvalue expression")
      end.

    Fixpoint transl_expr_list (locals: list ident) (el: list Clight.expr) : res (list Rustlight.pexpr) :=
      match el with
      | nil => OK nil
      | e :: rest =>
          do pe <- cexpr_to_pexpr locals e;
          do rest' <- transl_expr_list locals rest;
          OK (pe :: rest')
      end.

    Definition pexpr_to_expr (pe: Rustlight.pexpr): Rustlight.expr :=
      Rustlight.Epure pe.

    Definition empty_place : Rustlight.place := 
      Rustlight.Plocal 1%positive Rusttypes.Tunit. 
    

    Fixpoint transl_stmt (locals: list ident) (s: Clight.statement): res Rustlight.statement :=
      let transl_stmt := transl_stmt locals in
      match s with
      | Clight.Sskip => OK Rustlight.Sskip
      | Clight.Ssequence s1 s2 => 
          do rs1 <- transl_stmt s1;
          do rs2 <- transl_stmt s2;
          OK (Rustlight.Ssequence rs1 rs2)
      | Clight.Sifthenelse e s1 s2 => 
          do pe <- cexpr_to_pexpr locals e;
          do rs1 <- transl_stmt s1;
          do rs2 <- transl_stmt s2;
          OK (Rustlight.Sifthenelse (Rustlight.Epure pe) rs1 rs2)
      | Clight.Sloop s1 s2 => 
          do rs1 <- transl_stmt s1;
          OK (Rustlight.Sloop rs1)
      | Clight.Sbreak => OK Rustlight.Sbreak
      | Clight.Scontinue => OK Rustlight.Scontinue
      | Clight.Sassign e1 e2 => 
          do p <- cexpr_to_place e1;
          do pe <- cexpr_to_pexpr locals e2;
          OK (Rustlight.Sassign p (Rustlight.Epure pe))
      (* | Clight.Sset id e => 
          do pe <- cexpr_to_pexpr locals e;
          OK (Rustlight.Sassign (Rustlight.Plocal id (to_rusttype (Clight.typeof e))) 
                (Rustlight.Epure pe)) *)
      | Clight.Scall optid e args =>
          do pe <- cexpr_to_pexpr locals e;
          do pargs <- transl_expr_list locals args;
          match optid with
          | None => 
              (* without return value *)
              let dummy_place := empty_place in
              OK (Rustlight.Scall dummy_place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
          | Some id => 
              (* with return value *)
              let ret_ty := to_rusttype (Clight.typeof e) in
              let place := Rustlight.Plocal id ret_ty in
              OK (Rustlight.Scall place (Rustlight.Epure pe) (map pexpr_to_expr pargs))
          end
      | Clight.Sreturn None => 
          (* no return value*)
          OK (Rustlight.Sreturn empty_place)
      | Clight.Sreturn (Some e) => 
          do pe <- cexpr_to_pexpr locals e;
          (* create a temp variable to store return value *)
          let ret_place := Rustlight.Plocal 2%positive (to_rusttype (Clight.typeof e)) in
          (* assign the return value to the temp variable and return *)
          OK (Rustlight.Ssequence
                (Rustlight.Sassign ret_place (Rustlight.Epure pe))
                (Rustlight.Sreturn ret_place))
      (* | Clight.Sswitch e cases =>
        do pe <- cexpr_to_pexpr locals e;
        let fix convert_cases (cases: Clight.labeled_statements) : res Rustlight.statement :=
            match cases with
            | nil => OK Rustlight.Sskip
            | Clight.LScase n s rest =>
                do rs <- transl_stmt s;
                do rest_stmt <- convert_cases rest;
                let cond := Rustlight.Ebinop Ceq (Rustlight.Epure pe) 
                                             (Rustlight.Econst_int n (to_rusttype (Clight.typeof e))) 
                                             Rusttypes.Tbool in
                OK (Rustlight.Sifthenelse cond rs rest_stmt)
            | Clight.LSdefault s rest =>
                transl_stmt s
            end
        in
        convert_cases cases *)
      | _ => Error (msg "Unsupported statement type")
      end.

    (** Convert Clight function to Rustlight function *)
    Definition transl_function (f: Clight.function): res Rustlight.function :=
      let locals := List.map (@fst ident _) (Clight.fn_params f ++ Clight.fn_vars f) in
      do body <- transl_stmt locals (Clight.fn_body f);
      OK {| Rustlight.fn_generic_origins := [];
           Rustlight.fn_origins_relation := [];
           Rustlight.fn_drop_glue := None;
           Rustlight.fn_return := to_rusttype (Clight.fn_return f);
           Rustlight.fn_callconv := (Clight.fn_callconv f);
           (* save temp variable in clight in stack(fn_vars) *)
           Rustlight.fn_vars := List.map (fun '(id, ty) => (id, to_rusttype ty)) (Clight.fn_vars f ++ Clight.fn_temps f);
           Rustlight.fn_params := List.map (fun '(id, ty) => (id, to_rusttype ty)) (Clight.fn_params f);
           Rustlight.fn_body := body
         |}.

    Definition transl_fundef (id: ident) (f: Clight.fundef): res Rustlight.fundef :=
      match f with
      | Ctypes.Internal func =>
          do tf <- transl_function func;
          OK (Internal tf)
      | Ctypes.External extfun typelist ty cconv =>
          OK (External [] [] extfun (to_rustlight typelist) (to_rusttype ty) cconv)
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
          | External origins org_rels ef args res cc =>
              Gfun (External origins org_rels ef args res cc) 
          end
      | Gvar v =>
          Gvar {|
              gvar_info := to_rusttype v.(gvar_info);
              gvar_init := v.(gvar_init);
              gvar_readonly := v.(gvar_readonly);
              gvar_volatile := v.(gvar_volatile)
            |}
      end.

    Fixpoint convert_members (ms:Ctypes.members) : res Rusttypes.members :=
      match ms with
      | nil => OK (nil)
      | h::t => match h with
                | (Ctypes.Member_plain id ty) =>
                    do cm <- convert_members t;
                    OK ((Rusttypes.Member_plain id (to_rusttype ty)) :: cm)
                | (Ctypes.Member_bitfield id _ _ _ _ _) =>
                    Error (msg "not support member bitfield")
                end
      end.

    Fixpoint convert_composite_definition (cd:list Ctypes.composite_definition) : res (list Rusttypes.composite_definition) :=
      match cd with
      | nil => OK (nil)
      | (Ctypes.Composite id su m a)::t =>
          let new_su := match su with
                        | Ctypes.Struct => Rusttypes.Struct
                        | Ctypes.Union => Rusttypes.TaggedUnion 
                        end in
          do new_m <- convert_members m;
          do rcd <- convert_composite_definition t;
          OK ((Rusttypes.Composite id new_su new_m [] []) :: rcd)
      end.

    Definition transl_program (p: Clight.program): res program :=
      match convert_composite_definition (Ctypes.prog_types p) with
      | OK co_defs =>
          let tce := Rusttypes.build_composite_env co_defs in
          (match tce as m return (tce = m) -> res program with
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
      | _ =>Error (msg "error in transl_composites (clight2rustlight)")
      end.
  
    End TRANSL.
