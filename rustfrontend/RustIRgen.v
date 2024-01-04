Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import RustlightBase Selector.


(** Translation from Rustlight to RustIR. The main step is to generate
the drop operations and lifetime annotations in the end of a
variable. We also need to insert drops for those out-of-scope variable
in [break] and [continue] *)


Definition list_list_cons {A: Type} (e: A) (l: list (list A)) :=
  match l with
  | nil => (e::nil)::nil
  | l' :: l => (e::l') :: l
  end.

Fixpoint makeseq_rec (s: statement) (l: list statement) : statement :=
  match l with
  | nil => s
  | s' :: l' => makeseq_rec (Ssequence s s') l'
  end.

Definition makeseq (l: list statement) : statement :=
  makeseq_rec Sskip l.

Definition gen_drops (l: list (ident * type)) : statement :=
  let drops := map (fun elt => (Sdrop (Plocal (fst elt) (snd elt)))) l in
  makeseq drops.

(* [vars] is a stack of variable list. Eack stack frame corresponds to
a loop where these variables are declared *)
Fixpoint transl_stmt (stmt: RustlightBase.statement) (vars: list (list (ident * type))) : statement :=
  match stmt with
  | RustlightBase.Sskip => Sskip
  | Slet id ty stmt' =>
      let s := transl_stmt stmt' (list_list_cons (id,ty) vars) in
      let drop := Sdrop (Plocal id ty) in
      Ssequence (Sstoragelive id) (Ssequence s (Ssequence drop (Sstoragedead id)))
  | RustlightBase.Sassign p be =>
      Sassign p be
  | RustlightBase.Scall p e el =>
      Scall p e el
  | RustlightBase.Ssequence s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Ssequence s1' s2'
  | RustlightBase.Sifthenelse e s1 s2 =>
      let s1' := transl_stmt s1 vars in
      let s2' := transl_stmt s2 vars in
      Sifthenelse e s1' s2'
  | RustlightBase.Sloop s =>
      let s := transl_stmt s (nil :: vars) in
      Sloop s        
  | RustlightBase.Sbreak =>
      let drops := gen_drops (hd nil vars) in
      Ssequence drops Sbreak
  | RustlightBase.Scontinue =>
      let drops := gen_drops (hd nil vars) in
      Ssequence drops Scontinue
  | RustlightBase.Sreturn e =>
      Sreturn e
  end.



Fixpoint extract_vars (stmt: RustlightBase.statement) : list (ident * type) :=
  match stmt with
  | Slet id ty s =>
      (id,ty) :: extract_vars s
  | RustlightBase.Ssequence s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | RustlightBase.Sifthenelse _ s1 s2 =>
      extract_vars s1 ++ extract_vars s2
  | RustlightBase.Sloop s =>
      extract_vars s
  | _ => nil
  end.


(* The main job is to extract the variables and translate the statement *)
Definition transl_function (f: RustlightBase.function) : function :=
  let vars := extract_vars f.(RustlightBase.fn_body) in
  mkfunction f.(RustlightBase.fn_return)
             f.(RustlightBase.fn_callconv)
             f.(RustlightBase.fn_params)
             vars
             (transl_stmt f.(RustlightBase.fn_body) nil).

Definition transl_fundef (fd: RustlightBase.fundef) : fundef :=
  match fd with
  | Internal f => (Internal (transl_function f))
  | External _ ef targs tres cconv => External function ef targs tres cconv
  end.

Definition transl_program (p: RustlightBase.program) : program :=
  let p1 := transform_program transl_fundef p in
  {| prog_defs := AST.prog_defs p1;
    prog_public := AST.prog_public p1;
    prog_main := AST.prog_main p1;
    prog_types := prog_types p;
    prog_comp_env := prog_comp_env p;
    prog_comp_env_eq := prog_comp_env_eq p |}.
