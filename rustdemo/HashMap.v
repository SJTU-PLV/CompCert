Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop.
Require Import Rusttypes Ctypes Clight.
Require Import Clightdefs.
Require Import LinkedList.

Local Open Scope error_monad_scope.
Import ListNotations.

(** Identifiers  *)

Definition init_hmap : ident := 155%positive.
Definition hmap : ident := 146%positive.
Definition find_bucket : ident := 45%positive.
Definition index : ident := 145%positive.
Definition buk : ident := 90%positive.
Definition main : ident := 23%positive.
Definition delete_hmap : ident := 190%positive.
Definition hmap_operate_on : ident := 33%positive.


(** Type definitions  *)

Definition hmap_ty : type := Tpointer (to_ctype List_box) noattr.

(* The type of pointers pointing to a cell storing List_box *)
Definition List_box_ptr : type := Tpointer (to_ctype List_box) noattr.
Definition List_ptr : type := Tpointer (to_ctype List_ty) noattr.

(* find_bucket function *)

Definition find_bucket_func : function := {|
  fn_return := List_box_ptr;
  fn_callconv := cc_default;
  fn_params := ((hmap, hmap_ty) ::
                (key, tint) :: nil);
  fn_vars := nil;
  fn_temps := (index, tint) :: nil;
  fn_body :=
(Ssequence  
   (Scall (Some index)
      (Evar hash (Tfunction (Tcons tint (Tcons tuint Tnil)) tuint cc_default))
      ((Evar key tint) :: (Econst_int (Int.repr 10) tuint) :: nil))
   (Sreturn (Some (Ebinop Oadd
                   (Evar hmap List_box_ptr)
                   (Evar index tint)
                   List_box_ptr))))
|}.


(* hmap_operate_on function *)
  
Definition hmap_operate_on_func := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((hmap, hmap_ty) ::
                (key, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((buk, List_box_ptr) ::
               (tmp, List_ptr) :: nil);
  fn_body :=
(Ssequence  
 (Scall (Some buk)
    (Evar find_bucket (Tfunction
                         (Tcons hmap_ty (Tcons tint Tnil))
                         List_box_ptr cc_default))
    ((Evar hmap hmap_ty) :: (Evar key tint) :: nil))   
  (Sifthenelse (Ebinop Oeq
                 (Ederef (Evar buk List_box_ptr)
                   List_ptr)
                 (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint)
    (Sreturn None)
    (Ssequence
      (Scall (Some tmp)
        (Evar find (Tfunction
                      (Tcons List_ptr (Tcons tint Tnil))
                      List_ptr cc_default))
        ((Ederef (Evar buk List_box_ptr) List_ptr) :: (Evar key tint) :: nil))
      (Sassign (Ederef (Evar buk List_box_ptr) List_ptr) (Evar tmp List_ptr)))))
|}.


(* process function *)

Definition process_func := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((val, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := (Sreturn (Some (Evar val tint)))
|}.

(* Definition of hash_map program *)

Definition composites : list composite_definition := nil.

Definition global_definitions : list (ident * globdef fundef type) :=
  (find_bucket, Gfun(Internal find_bucket_func)) ::
  (process, Gfun(Internal process_func)) ::
  (hmap_operate_on, Gfun(Internal hmap_operate_on_func)) ::
  (hash,
   Gfun(External (EF_external "hash"
                   (AST.mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tuint Tnil)) tint
     cc_default)) :: nil.

Definition public_idents : list ident :=
  (hmap_operate_on :: process :: find_bucket :: nil).

Definition hash_map_prog : Clight.program :=
  mkprogram composites global_definitions public_idents main Logic.I.


