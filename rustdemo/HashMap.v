Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Cop.
Require Import Rusttypes Ctypes Clight.
Require Import Clightdefs Clightgen.
Require Import LinkedList.

Local Open Scope error_monad_scope.
Import ListNotations.

(** Identifiers  *)

Definition init_hmap : ident := 155%positive.
Definition hmap : ident := 146%positive.
Definition find_bucket : ident := 45%positive.
Definition index : ident := 145%positive.
Definition buk : ident := 90%positive.
Definition delete_hmap : ident := 190%positive.
Definition hmap_process : ident := 33%positive.
Definition hmap_set : ident := 44%positive.

(** Type definitions  *)

Definition hmap_ty : type := Tpointer (to_ctype List_box) noattr.

(* The type of pointers pointing to a cell storing List_box *)
Definition List_box_ptr : type := Tpointer (to_ctype List_box) noattr.
Definition List_ptr : type := Tpointer (to_ctype List_ty) noattr.

Definition buk_size : Z := 10.

(* find_bucket function *)

Definition find_bucket_func : function := {|
  fn_return := List_box_ptr;
  fn_callconv := cc_default;
  fn_params := ((hmap, hmap_ty) ::
                (key, tint) :: nil);
  fn_vars := nil;
  fn_temps := (index, tuint) :: nil;
  fn_body :=
(Ssequence  
   (Scall (Some index)
      (Evar hash (Tfunction (Tcons tint (Tcons tuint Tnil)) tuint cc_default))
      ((Evar key tint) :: (Econst_int (Int.repr buk_size) tuint) :: nil))
   (Sreturn (Some (Ebinop Oadd
                   (Evar hmap List_box_ptr)
                   (Etempvar index tuint)
                   List_box_ptr))))
|}.


(* hmap_process function *)

Definition hmap_operate_on_ty := Tfunction (Tcons hmap_ty (Tcons tint Tnil)) Tvoid cc_default.

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
                 (Ederef (Etempvar buk List_box_ptr)
                   List_ptr)
                 (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint)
    (Sreturn None)
    (Ssequence
      (Scall (Some tmp)
        (Evar find (Tfunction
                      (Tcons List_ptr (Tcons tint Tnil))
                      List_ptr cc_default))
        ((Ederef (Etempvar buk List_box_ptr) List_ptr) :: (Evar key tint) :: nil))
      (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr)))))
|}.


(* process function *)

Definition process_func := {|
  fn_return := tptr tint;
  fn_callconv := cc_default;
  fn_params := ((val, tptr tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body := Ssequence
               (Sassign (Ederef (Evar val (tptr tint)) tint)
                  (Ebinop Oxor (Ederef (Evar val (tptr tint)) tint) (Econst_int (Int.repr 42) tint) tint))
               (Sreturn (Some (Evar val (tptr tint))));
|}.

(* Initialzation function for the hash map *)

Definition malloc_ty := Tfunction (Ctypes.Tcons Ctyping.size_t Ctypes.Tnil) (Tpointer Ctypes.Tvoid noattr)  cc_default.

Definition init_hmap_loop_cond := 
  (Sifthenelse
     (Ebinop Olt (Etempvar tmp tuint) (Econst_int (Int.repr buk_size) tuint) tint) (* loop cond: tmp < buk_size *)
     Sskip Sbreak).

Definition init_hmap_loop_body :=
  (Sassign      (* loop body: hmap[tmp] = NULL *)
     (Ederef (Ebinop Oadd (Etempvar hmap hmap_ty) (Etempvar tmp tuint) hmap_ty) List_box_ptr)
     (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid))).

Definition init_hmap_after_loop :=
  (* tmp++ *)
  (Sset tmp (Ebinop Oadd (Etempvar tmp tuint) (Econst_int Int.one tuint) tuint)).

Definition init_hmap_loop :=
  (Sloop (Ssequence init_hmap_loop_cond init_hmap_loop_body) init_hmap_after_loop).


(* HashMap init_hmap(){
    HashMap hmap = malloc(sizeof(List_ptr) * buk_size);
    for(int i = 0; i < buk_size; ++i){
        hmap[i] = NULL;
    }
    return hmap; }
 *)
Definition init_hmap_func := {|
  fn_return := hmap_ty;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := (hmap, hmap_ty) :: (tmp, tuint) :: nil; 
  fn_body := Ssequence
               (* call malloc *)
               (Scall (Some hmap) (Evar malloc malloc_ty) [Ebinop Omul (Esizeof List_ptr Ctyping.size_t) (Econst_int (Int.repr buk_size) tuint) Ctyping.size_t])
               (* for loop used to initialize the hash map *)
               (Ssequence
                  (* If we use Sfor we need to unfold Sfor to define
                  the safety invariant, so we just directly use Sloop *)
                  (Ssequence
                     (Sset tmp (Econst_int Int.zero tuint)) (* loop init: tmp = 0 *)
                     init_hmap_loop)
                  (* return hmap *)
                  (Sreturn (Some (Etempvar hmap hmap_ty))));
|}.


Definition init_hmap_ty := Tfunction Tnil hmap_ty cc_default.

(* set function *)

Definition find_bucket_ty := (Tfunction (Tcons hmap_ty (Tcons tint Tnil)) List_box_ptr cc_default).

Definition val_ty := tptr tint.

Definition insert_ty := (Tfunction (Tcons List_ptr (Tcons tint (Tcons val_ty Tnil))) List_ptr cc_default).

Definition empty_list_ty := Tfunction Tnil List_ptr cc_default.

(* void hmap_set(HashMap hmap, int key, int* val){
    List_ptr* buk = find_bucket(hmap, key);
    List_ptr tmp;
    if ( *buk == NULL){
        tmp = empty_list();
    }
    else{
        tmp = *buk;
    }
    * buk = insert(tmp, key, val);
} *)

Definition hmap_set_cond :=
  (Sifthenelse (Ebinop Oeq
                  (Ederef (Etempvar buk List_box_ptr)
                     List_ptr)
                  (Ecast (Econst_long (Int64.repr 0) tlong) (tptr tvoid)) tint)
     (* tmp = empty_list() *)
     (Scall (Some tmp)
        (Evar empty_list empty_list_ty) nil)
     (* tmp = *buk *)
     (Sset tmp (Ederef (Etempvar buk List_box_ptr) List_ptr))).
  

Definition hmap_set_after_cond := (Ssequence
    (Scall (Some tmp) (Evar insert insert_ty)
        (Etempvar tmp List_ptr :: (Evar key tint) :: (Evar val val_ty) :: nil))
    (Sassign (Ederef (Etempvar buk List_box_ptr) List_ptr) (Etempvar tmp List_ptr))).

Definition hmap_set_func := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((hmap, hmap_ty) ::
                (key, tint) ::
                (val, val_ty) :: nil);
  fn_vars := nil;
  fn_temps := ((buk, List_box_ptr) ::
               (tmp, List_ptr) :: nil); (* tmp is used to store the
               empty and the list after insertion *)
  fn_body :=
(Ssequence  
 (Scall (Some buk)
    (Evar find_bucket find_bucket_ty)
    ((Evar hmap hmap_ty) :: (Evar key tint) :: nil))
 (Ssequence
    hmap_set_cond
    (* *buk = insert(tmp, key, val) *)
    hmap_set_after_cond))
|}.

Definition hmap_set_ty := (Tfunction (Tcons hmap_ty (Tcons tint (Tcons val_ty Tnil))) hmap_ty cc_default).

(* main function *)

(* int main(){ *)
(*     HashMap hmap = init_hmap(); *)
(*     hmap_process(hmap, 1); *)
(*     return 0; *)
(* } *)

Definition main_assign_value := (Sassign (Ederef (Evar val val_ty) tint) (Econst_int (Int.repr 23) tint)).

Definition main_call_hmap_set := (Scall (Some hmap) (Evar hmap_set hmap_set_ty) [Evar hmap hmap_ty; Econst_int (Int.repr 42) tint; Evar val val_ty]).

Definition main_insert_key_value :=
  Ssequence
    (* use malloc to allocate the heap memory for the value *)
    (Scall (Some val) (Evar malloc malloc_ty) [Esizeof tint tlong])
    (Ssequence
       (* initialize this value *)
       main_assign_value
       main_call_hmap_set).

Definition main_after_insertion := (Ssequence
        (Scall None (Evar hmap_process hmap_operate_on_ty)
           [Etempvar hmap hmap_ty; Econst_int Int.one tint])
        (Sreturn (Some (Econst_int Int.zero tint)))).

Definition main_after_init_hmap :=
  Ssequence
    (* insert (42,23) into the hash map *)
    main_insert_key_value
    (* call hmap_operate_on *)
    main_after_insertion.
   
Definition main_func := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := (hmap, hmap_ty) :: (val, val_ty) :: nil;
  fn_body := Ssequence
               (Scall (Some hmap) (Evar init_hmap init_hmap_ty) nil)
               main_after_init_hmap;
|}.


(* Definition of hash_map program *)

Definition composites : list composite_definition := nil.

Definition hash_ext : fundef := (External (EF_external "hash"
                                    (AST.mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                                       cc_default)) (Tcons tint (Tcons tuint Tnil)) tuint
                          cc_default).

Definition find_ext: fundef := (External (EF_external "find"
                                    (AST.mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                                       cc_default)) (Tcons List_ptr (Tcons tint Tnil)) List_ptr
                          cc_default).

Definition empty_list_ext: fundef := (External
                                        (EF_external "empty_list"
                                           (AST.mksignature nil AST.Tlong cc_default))
                                        Tnil List_ptr cc_default).

Definition global_definitions : list (ident * globdef fundef type) :=
  (find_bucket, Gfun(Internal find_bucket_func)) ::
  (process, Gfun(Internal process_func)) ::
  (hmap_process, Gfun(Internal hmap_operate_on_func)) ::
  (hmap_set, (Gfun (Internal hmap_set_func))) ::
  (init_hmap, Gfun (Internal init_hmap_func)) ::
  (main, Gfun (Internal main_func)) ::
  (malloc, Gfun malloc_decl) ::       (* Declaration of malloc *)
  (hash, Gfun hash_ext) ::
  (find, Gfun find_ext) ::
  (empty_list, Gfun empty_list_ext) :: nil.


Definition public_idents : list ident :=
  (hmap_process :: process :: find_bucket :: hash :: find :: init_hmap :: main :: malloc :: empty_list :: nil).

Definition hash_map_prog : Clight.program :=
  mkprogram composites global_definitions public_idents main Logic.I.


