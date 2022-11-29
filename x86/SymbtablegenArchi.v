Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProg RelocProgram.
Require Import CheckDef.
Require Import LocalLib.
Require Globalenvs.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Definition instr_invalid (i: instruction) := 
  match i with
  | Pjmp_l _ 
  | Pjcc _ _ 
  | Pjcc2 _ _ _ 
  (*Remove this instr after symbol table gen*)
  | Pjmptbl _ _
  | Pjmptbl_rel _ _
  | Pallocframe _ _ _
  | Pfreeframe _ _ _ => True
  (* | Pload_parent_pointer _ _ _ => True *)
  | _ => False
  end.

Definition instr_valid i := ~instr_invalid i.

Lemma instr_invalid_dec: forall i, {instr_invalid i} + {~instr_invalid i}.
Proof.
  destruct i; cbn; auto.
Qed.

Lemma instr_valid_dec: forall i, {instr_valid i} + {~instr_valid i}.
Proof.
  unfold instr_valid.
  destruct i; cbn; auto.
Qed.

Definition def_instrs_valid (def: (globdef fundef unit)) :=
  match def with
  | (Gvar v) => True
  | (Gfun f) =>
    match f with
    | External _ => True
    | Internal f =>  Forall instr_valid (fn_code f)
    end
  end.

Lemma def_instrs_valid_dec: 
  forall def, {def_instrs_valid def} + {~def_instrs_valid def}.
Proof.
  destruct def.
  - destruct f. 
    + simpl. apply Forall_dec. apply instr_valid_dec.
    + simpl. auto.
  - simpl. auto.
Qed.