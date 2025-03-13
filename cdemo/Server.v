Require Import Coqlib Errors.
Require Import AST Linking Smallstep.

Require Import LanguageInterface.

Require Import Ctypes Cop Clight Clightrel.
Require Import Clightdefs.

Require Import Integers Intv.
Require Import MultiLibs.
Require Import Encrypt Client.


(*
2 void encrypt ( int i , int * r ) ;
3 void * server ( void * a ) {
4 int * i = (( Arg * ) a ) -> input ;
5 int * r = (( Arg * ) a ) -> result ;
6 int size = (( Arg * ) a ) -> size ;
7
8 for ( int j = 0; j < size ; j ++) {
9 encrypt ( input [ j ] , result + j ) ;
10 yield () ; }
11 return NULL ;
12 }
*)


(** Ids *)

Definition i_id := 8%positive.
Definition r_id := 9%positive.
Definition size_id := 10%positive.
Definition j_id := 11%positive.
Definition a_id := 12%positive.

(** Defs *)

Definition i_def :=
  {|
    gvar_info := tptr tint;
    gvar_init := nil; 
    gvar_readonly := false;
    gvar_volatile := false
  |}.

Definition r_def := i_def.

Definition size_def :=
  {|
    gvar_info := tint;
    gvar_init := nil; 
    gvar_readonly := false;
    gvar_volatile := false
  |}.

Definition j_def := size_def.


(** Declaration of external function [encrypt] *)
Definition func_encrypt_external : fundef :=
  (External (EF_external "encrypt" int_ptr__void_sg)
          (Tcons tint (Tcons (tptr tint)  Tnil))
          Tvoid
          cc_default).

(** Definition of function [server] *)

(**  void * server ( void * a ) {
     int * i = (( Arg * ) a ) -> input ;
     int * r = (( Arg * ) a ) -> result ;
     int size = (( Arg * ) a ) -> size ;
     
     for ( int j = 0; j < size ; j ++) {
     encrypt ( i[j] , r + j ) ;
     yield () ; }
     return NULL ;
     }           *)

Definition arg_expr : expr := (Evar (a_id) (Tpointer Arg_type noattr)).

Definition set_i_code : statement :=
  Sassign (Evar i_id (tptr tint)) (Efield (Ederef arg_expr Arg_type) input_mem_id (tptr tint)).

Definition set_r_code : statement :=
  Sassign (Evar r_id (tptr tint)) (Efield (Ederef arg_expr Arg_type) result_mem_id (tptr tint)).

Definition set_size_code : statement :=
  Sassign (Evar size_id tint) (Efield (Ederef arg_expr Arg_type) size_mem_id tint).


Definition input_index_j :=
  Ebinop Oadd (Evar i_id (tptr tint))
            (Evar j_id tint)
            (tptr tint).

Definition result_index_j :=
  Ebinop Oadd (Evar i_id (tptr tint))
            (Evar j_id tint)
            (tptr tint).

(** for ( int j = 0; j < size ; j ++) {
     encrypt ( i[ j ] , r + j ) ;
     yield () ; } *)


Definition code_call_encrypt :=
  Scall (Some encrypt_id)
    (Evar encrypt_id (Tfunction (Tcons tint (Tcons (tptr tint) Tnil)) (tint) cc_default))
    (Ederef input_index_j tint :: result_index_j :: nil).

Definition code_forloop :=
  Sfor (Sassign (Evar j_id tint) (Econst_int Int.zero tint)) (** j = 0 *)
    (Ebinop Olt (Evar j_id tint) (Econst_int (Int.repr 5) tint) tint) (** j < N*)
    ( Ssequence
        code_call_encrypt
        (Scall (Some yield_id) (Evar yield_id (Tfunction Tnil Tvoid cc_default)) nil)
    ) (** encrypt (i[j], r+j); yield () ;*)
    (Sassign (Evar j_id tint) (Ebinop Oadd (Evar j_id tint) (Econst_int Int.one tint) tint)). (** j++*)

Definition func_server_code : statement :=
  Ssequence set_i_code (** Set i*)
    (Ssequence set_r_code (** Set r*)
       (Ssequence set_size_code (** Set size *)
          (Ssequence code_forloop (** For loop *)
             (Sreturn (Some (Econst_long Int64.zero (tptr (tptr Tvoid))))) (** Return NULL*)
    ))).

Definition func_server :=
  {|
    fn_return := Tvoid;
    fn_callconv := cc_default;
    fn_params := (a_id, tptr Tvoid) :: nil;
    fn_vars := (i_id, tptr tint) :: (r_id, tptr tint) :: (size_id, tint) :: (j_id, tint) :: nil;
    fn_temps := nil;
    fn_body := func_server_code
  |}.

Definition global_defs_server : list (ident * globdef fundef type) :=
  (server_id, Gfun (Internal func_server)) ::
  nil.

(** we need ids of primitives here? *)
Definition public_defs_server : list ident :=
  server_id :: nil.

Program Definition server : Clight.program :=
  mkprogram composites global_defs_server public_defs_client main_id _.
Next Obligation.
  reflexivity.
Qed.
