Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.
Require Import Asm Asmrel.

Require Import Integers Intv.

(** *Implementation of Server in Asm *)

(* C-level spec : in C code:
L1:
int key;
void encrypt (int input, void ( *complete)(int* __ ))){
  int output = input ^ key;
  complete(&output);
}

L2:
const int key = 42;
void encrypt (int input, void ( *complete)(int* __ )){
  int output = input ^ key;
  complete(&output)
}
                         *)
                              
Definition main_id := (42%positive).
Definition encrypt_id := (1%positive).
Definition key_id := (2%positive).
Definition complete_id := (3%positive).

Definition intptr__void_sg : signature := mksignature (AST.Tlong :: nil) Tvoid cc_default.
Definition int_fptr__void_sg : signature := mksignature (AST.Tint :: AST.Tlong :: nil) Tint cc_default.

(** registers responding to above signatures*)

Require Import Conventions1.
(* Compute (is_callee_save Machregs.DI). *)
(* Compute (loc_arguments int__void_sg). *)
(* = if Archi.win64 then One (Locations.R Machregs.CX) :: nil else One (Locations.R Machregs.DI) :: nil *)
(* Compute (loc_arguments int_fptr__void_sg). *)
(*= if Archi.win64
       then One (Locations.R Machregs.CX) :: One (Locations.R Machregs.DX) :: nil
       else One (Locations.R Machregs.DI) :: One (Locations.R Machregs.SI) :: nil
 *)
(* Compute is_callee_save (Machregs.AX). *)
(* = false *)
(** * Implementation of b1.asm, corresponding to L1 *)

Definition key_def := {|
  gvar_info := tt;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

(*
L1: 
Pallocframe 24 16 0

Pmov key RAX //read key from memory to RAX as argument
Pxor RAX RDI //xor op
Pmov RDI 8(RSP) // store the output on stack
Plea 8(RSP) RDI // transfer the address of output as argument
Pcall_r RSI //call function pointer

Pfreeframe 24 16 0
Pret

*)
Definition code_b1: list instruction :=
   Pallocframe 24 (Ptrofs.repr 16) Ptrofs.zero ::
     Pmovl_rm RAX (Addrmode None None (inr (key_id, Ptrofs.zero))) ::
     Pxorl_rr RDI RAX ::
     Pmov_mr_a (Addrmode (Some RSP) None (inl 8)) RDI ::
     Pleaq RDI (Addrmode (Some RSP) None (inl 8)) ::
     Pcall_r RSI (intptr__void_sg) ::
     Pfreeframe 24 (Ptrofs.repr 16) Ptrofs.zero ::
     Pret ::
     nil.

Definition func_encrypt_b1: Asm.function :=
  Asm.mkfunction (int_fptr__void_sg) code_b1.

Definition global_definitions_b1 : list (ident * globdef fundef unit) :=
  (key_id, Gvar key_def) ::
    (encrypt_id, Gfun(Internal func_encrypt_b1)) ::
    (complete_id, Gfun(External (EF_external "complete" intptr__void_sg))) ::
  nil.

Definition public_idents : list ident :=
(key_id :: encrypt_id :: complete_id :: nil).

Definition b1: program := mkprogram global_definitions_b1 public_idents main_id.

(** * Implementation of b2.asm, corresponding to L2 *)

Definition key_def_const := {|
  gvar_info := tt;
  gvar_init := Init_int32 (Int.repr 42) :: nil;
  gvar_readonly := true;
  gvar_volatile := false
|}.

(*
L2: 
Pallocframe 24 16 0

Pxor 42 RDI //xor op
Pmov RDI 8(RSP) // store the output on stack
Plea 8(RSP) RDI // transfer the address of output as argument
Pcall_r RSI //call function pointer

Pfreeframe 24 16 0
Pret

Pallocframe 16 8 0

Pxori 42 RDI //read key from memory to RDI as argument
Pcall_r RSI

Pfreeframe 16 8 0
Pret

*)
Definition code_b2: list instruction :=
   Pallocframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     Pxorl_ri RDI (Int.repr 42) ::
     Pmov_mr_a (Addrmode (Some RSP) None (inl 8)) RDI ::
     Pleaq RDI (Addrmode (Some RSP) None (inl 8)) ::
     Pcall_r RSI (intptr__void_sg) ::
     Pfreeframe 16 (Ptrofs.repr 8) Ptrofs.zero ::
     Pret ::
     nil.

Definition func_encrypt_b2: Asm.function :=
  Asm.mkfunction (int_fptr__void_sg) code_b2.

Definition global_definitions_b2 : list (ident * globdef fundef unit) :=
  (key_id, Gvar key_def_const) ::
  (encrypt_id, Gfun(Internal func_encrypt_b2)) ::
  (complete_id, Gfun(External (EF_external "complete" intptr__void_sg))) ::
  nil.

Definition b2: program := mkprogram global_definitions_b2 public_idents main_id.
