Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Rustlight RustIR.

Import ListNotations.

Local Open Scope error_monad_scope.

(** Translation from Rustlight to RustIR. The main step is to generate
the drop operations and explicit scope annotations in the end of a
variable. We also need to insert drops for those out-of-scope variable
in [break], [continue] and [return] *)

Fixpoint makeseq (l: list statement) : statement :=
  match l with
  | nil => Sskip
  | s :: l' => Ssequence s (makeseq l')
  end.


Section COMPOSITE_ENV.

Variable ce: composite_env.

(* Insert storagedead before drop for local variables *)
(* Definition gen_drops (local: bool) (l: list (ident * type)) : statement := *)
(*   let drops := fold_right *)
(*                  (fun elt acc => *)
(*                     if own_type ce (snd elt) then *)
(*                       if local then *)
(*                         (Sdrop (Plocal (fst elt) (snd elt))) :: acc *)
(*                       else (Ssequence (Sdrop (Plocal (fst elt) (snd elt))) (Sstoragedead (fst elt))) :: acc *)
(*                     else *)
(*                       if local then *)
(*                         (Sstoragedead (fst elt)) :: acc *)
(*                       else acc) nil l in *)
(*   makeseq drops. *)


(* It is different from gen_drops_for_vars because we also need to
generate storagedead for those variables which are about to out of
scope. *)
Definition gen_drops_for_escape_vars (vars: list (ident * type)) : statement :=
  makeseq (concat (map (fun '(id, ty) =>
                          if own_type ce ty then
                            (* adhoc: to ensure that the storagedead
                            is connected to the the next statement to
                            make match_drop_insert_kind works *)
                            [(Sdrop (Plocal id ty)); (Sstoragedead id)]
                              (* The skip is used to avoid stuttering *)
                          else [RustIR.Sskip; (Sstoragedead id)]) vars)).

Definition gen_drop (p: place) : statement :=
  (* Sskip is used to prevent stuttering *)
  makeseq (if own_type ce (typeof_place p) then [Sdrop p] else [RustIR.Sskip]).

(* Generate sequence of drop statements for the list of variables with
own_type *)
Definition gen_drops_for_vars (params: list (ident * type)) : statement :=
  makeseq (map (fun '(id, ty) =>
                  if own_type ce ty then
                    (Sdrop (Plocal id ty))
                  else RustIR.Sskip) params).


(* [vars] is a stack of variable list. Eack stack frame corresponds to
a loop where these variables are declared. [params_drops] are the
statement for dropping the parameters *)
Fixpoint transl_stmt (params: list (ident * type)) (* (retv: place) *) (stmt: Rustlight.statement) (vars: list (list (ident * type))) : statement :=
  let transl_stmt := transl_stmt params (* retv *) in
  match stmt with
  | Rustlight.Sskip => Sskip
  | Slet id ty stmt' =>
      let s := transl_stmt stmt' (list_list_cons (id,ty) vars) in
      (* drop would contain storagedead *)
      let drop := gen_drops_for_escape_vars [(id,ty)] in
      (* The additional skip is used to simulate the Dendlet in
      Rustlightown *)
      Ssequence (Sstoragelive id) (Ssequence (Ssequence s drop) Sskip)
  | Rustlight.Sassign p e =>
      let drop := gen_drop p in
      Ssequence drop (Sassign p e)
  | Rustlight.Sassign_variant p enum_id fid e =>
      let drop := gen_drop p in
      Ssequence drop (Sassign_variant p enum_id fid e)      
  | Rustlight.Sbox p e =>
      let drop := gen_drop p in
      Ssequence drop (Sbox p e)
  | Rustlight.Scall p e el =>
      let drop := gen_drop p in
      Ssequence drop (Scall p e el)
  | Rustlight.Smethod_call p receiver method_name el =>
      let drop := gen_drop p in
      Ssequence drop (Smethod_call p receiver method_name el)
  | Rustlight.Ssequence s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Ssequence s1' s2'
  | Rustlight.Sifthenelse e s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Sifthenelse e s1' s2'
  | Rustlight.Sloop s =>
      let s := transl_stmt s (nil :: vars) in
      Sloop s
  | Rustlight.Sbreak =>
      let drops := gen_drops_for_escape_vars (hd nil vars) in
      Ssequence drops Sbreak
  | Rustlight.Scontinue =>
      let drops := gen_drops_for_escape_vars (hd nil vars) in
      Ssequence drops Scontinue
  | Rustlight.Sreturn p =>
      let drops := gen_drops_for_escape_vars (concat vars) in
      (** Unused comment: The fresh return variable is used to store
      the return value before the drops otherwise the moved place in
      return expression may be dropped (because its ownership is moved
      after the drop) and the return value depends on this moved
      place. May be we can use some temporary variables to do this so
      that we do not need to protect this variable *)
      (* let s := Sassign retv e in *)
      (* let ty := typeof_place retv in *)
      (* let rete := if own_type ce ty then Emoveplace retv ty else (Epure (Eplace retv ty)) in *)
      (* also insert drop statements for parameters after dropping
          variables *)
      Ssequence drops (Ssequence (gen_drops_for_vars params) (Sreturn p))
      (* |  _ => *)
      (*     makeseq (drops :: (gen_drops_for_params params) :: (Sreturn None) :: nil) *)
      (* end *)
  end.

(* Add return to the end of the program *)
(* Fixpoint elaborate_return (stmt: Rustlight.statement) : Rustlight.statement := *)
(*   match stmt with *)
(*   | Rustlight.Ssequence _ s => *)
(*       elaborate_return s *)
(*   | Rustlight.Sreturn _ => stmt *)
(*   | _ => Rustlight.Ssequence stmt (Rustlight.Sreturn None) *)
(*   end. *)

(** We want to optimize the return value. For example, when we return
a unit value, it can be optimized to return none. But it is unused for
simplicity. *)
Definition ret_var (ty: type) (v: ident) : option place :=
  if type_eq ty Tunit then None else Some (Plocal v ty).


(* Parameter fresh_atom : unit -> ident. *)

(* The main job is to extract the variables and translate the statement *)

Definition transl_function (f: Rustlight.function) : function :=
  (* generate the return variable *)
  (* let retv := fresh_atom tt in *)
  (* no need to insert return *)
  (* let body := elaborate_return f.(Rustlight.fn_body) in *)
  let stmt' := transl_stmt f.(Rustlight.fn_params) f.(Rustlight.fn_body) nil in
  (* add the return variable to variable list *)
  (mkfunction f.(Rustlight.fn_generic_origins)
            f.(Rustlight.fn_origins_relation)
            f.(Rustlight.fn_drop_glue)
            f.(Rustlight.fn_return)
            f.(Rustlight.fn_callconv)
            (f.(Rustlight.fn_vars))
            f.(Rustlight.fn_params)
            stmt').

Definition transl_fundef (fd: Rustlight.fundef) : fundef :=
  match fd with
  | Internal f => (Internal (transl_function f))
  | External orgs org_rels ef targs tres cconv => (External orgs org_rels ef targs tres cconv)
  end.

End COMPOSITE_ENV.

Definition transl_program (p: Rustlight.program) : program :=
  let p1 := transform_program (transl_fundef p.(prog_comp_env)) p in
   {| prog_defs := AST.prog_defs p1;
    prog_public := AST.prog_public p1;
    prog_main := AST.prog_main p1;
    prog_types := prog_types p;
    prog_comp_env := prog_comp_env p;
    prog_comp_env_eq := prog_comp_env_eq p |}.
