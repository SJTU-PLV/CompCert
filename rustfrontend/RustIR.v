Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop RustOp.
Require Import LanguageInterface.
Require Import Clight Rustlight Rustlightown.
Require Import InitDomain.

Import ListNotations.

(** * Rust Intermediate Rrepresentation  *)

(** To compile Rustlight to RustIR, we replace the scopes (let stmt)
with StorageLive (StorageDead) statements, use AST to represent the
program, analyze the AST by first transforming it to CFG (using
selector technique) and insert explicit drop operations (so that the
RustIR has no ownership semantics) *)


(* The definitions of expression and place are the same as Rustlight *)

(** Statement: we add [Storagelive] and [Storagedead] to indicate the
lifetime of a local variable, because all the variables are declared
in the entry of function which is different from Rustlight. For now,
this two statements have no semantics. They are used for borrow
checking. We use [drop(p)] statement to indicate that we may need to
drop the content of [p] depending on the ownership environment. The
[Sreturn] returns the a predefined return variable instead of an
expression because we need to insert drop between the evaluation of
the returned expression and the return statement *)

Inductive statement : Type :=
| Sskip: statement                   (**r do nothing *)
| Sassign: place -> expr -> statement (**r assignment [place = rvalue] *)
| Sassign_variant : place -> ident -> ident -> expr -> statement (**r [place] = [ident(expr)] *)
| Sbox: place -> expr -> statement       (**r [place = Box::new(expr)]  *)
| Sstoragelive: ident -> statement       (**r id becomes avalible *)
| Sstoragedead: ident -> statement       (**r id becomes un-avalible *)
| Sdrop: place -> statement             (**r conditionally drop the place [p]. [p] must be an ownership pointer. *)
| Scall: place -> expr -> list expr -> statement (**r function call, p = f(...). It is a abbr. of let p = f() in *)
| Ssequence: statement -> statement -> statement  (**r sequence *)
| Sifthenelse: expr  -> statement -> statement -> statement (**r conditional *)
| Sloop: statement -> statement (**r infinite loop *)
| Sbreak: statement                      (**r [break] statement *)
| Scontinue: statement                   (**r [continue] statement *)
| Sreturn: option expr -> statement.      (**r [return] statement *)


Record function : Type := mkfunction {
  fn_generic_origins : list origin;
  fn_origins_relation: list (origin * origin);
  fn_drop_glue: option ident;
  fn_return: type;
  fn_callconv: calling_convention;
  fn_vars: list (ident * type);
  fn_params: list (ident * type);
  fn_body: statement
}.

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.

Definition type_of_function (f: function) : type :=
  Tfunction (fn_generic_origins f) (fn_origins_relation f) (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  | External orgs org_rels ef typs typ cc =>
      Tfunction orgs org_rels typs typ cc
  end.

(* some helper function *)

Fixpoint makeseq (l: list statement) : statement :=
  match l with
  (* To ensure that target program must move at least one step *)
  | nil => (Ssequence Sskip Sskip)
  | s :: l' => Ssequence s (makeseq l')
  end.

Local Open Scope error_monad_scope.

(** Genenrate drop map which maps composite id to its drop glue id *)


(* Extract composite id to drop glue id list *)
Definition extract_drop_id (g: ident * globdef fundef type) : ident * ident :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => (comp_id, glue_id)
      | None => (1%positive, glue_id)
      end
  | _ => (1%positive, glue_id)
  end.

Definition check_drop_glue (g: ident * globdef fundef type) : bool :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => true
      | None => false
      end
  | _ => false
  end.

Definition generate_dropm (p: program) :=
  let drop_glue_ids := map extract_drop_id (filter check_drop_glue p.(prog_defs)) in
  PTree_Properties.of_list drop_glue_ids.


(** General semantics definitions *)

Section SEMANTICS.

(** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.
      
(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** Allocate memory blocks for function parameters/variables and build
the local environment *)
Inductive alloc_variables (ce: composite_env) : env -> mem ->
                                                list (ident * type) ->
                                                env -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables ce e m nil e m
| alloc_variables_cons:
  forall e m id ty vars m1 b1 m2 e2,
    Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
    alloc_variables ce (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
    alloc_variables ce e m ((id, ty) :: vars) e2 m2.

(** Assign the values to the memory blocks of the function parameters  *)
Inductive bind_parameters (ce: composite_env) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ce e m nil nil m
  | bind_paranmeters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ce ty m b Ptrofs.zero v1 m1 ->
      bind_parameters ce e m1 params vl m2 ->
      bind_parameters ce e m ((id, ty) :: params) (v1 :: vl) m2.

End SEMANTICS.

(* Used in RustIRown and InitAnalysis *)

Section COMP_ENV.

Variable ce : composite_env.

Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign_variant p _ _ e
  | Sassign p e
  | Sbox p e =>
      collect_place ce p (collect_expr ce e m)
  | Scall p _ al =>
      collect_place ce p (collect_exprlist ce al m)
  | Sreturn (Some e) =>
      collect_expr ce e m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_stmt s1 (collect_stmt s2 (collect_expr ce e m))
  | Sloop s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  if list_norepet_dec ident_eq (map fst vars) then
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    (** TODO: add all the parameters and variables to l (may be useless?) *)
    let init_map := fold_right (collect_place ce) (PTree.empty LPaths.t) l in
    Errors.OK (collect_stmt f.(fn_body) init_map)
  else
    Errors.Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil).

End COMP_ENV.


(* Repeated definitions from Rustlightown because the genvs are
different *)
Section DROPMEMBER.

Variable ge: genv.

(** Some definitions for dropstate and dropplace *)

(* It corresponds to drop_glue_for_member in Clightgen *)
Definition type_to_drop_member_state (fid: ident) (fty: type) : option drop_member_state :=
  if own_type ge fty then
    let tys := drop_glue_children_types fty in
    match tys with
    | nil => None
    | ty :: tys' =>
        match ty with       
        | Tvariant _ id
        | Tstruct _ id =>
            (* provide evidence for the simulation *)
            match ge.(genv_dropm) ! id with
            | Some _ =>
                Some (drop_member_comp fid fty ty tys')
            | None => None
            end
        | _ => Some (drop_member_box fid fty tys)
        end
    end
  else None.


(* big step to recursively drop boxes [Tbox (Tbox (Tbox
...))]. (b,ofs) is the address of the starting block *)
Inductive drop_box_rec (b: block) (ofs: ptrofs) : mem -> list type -> mem -> Prop :=
| drop_box_rec_nil: forall m,
    drop_box_rec b ofs m nil m
| drop_box_rec_cons: forall m m1 m2 b1 ofs1 ty tys,
    (* (b1, ofs1) is the address of [ty] *)
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m (ty :: tys) m2
.

Inductive extcall_free_sem_mem_error: val -> mem -> Prop :=
| free_error1: forall (b : block) (lo : ptrofs) (m : mem),
    ~ Mem.valid_access m Mptr b (Ptrofs.unsigned lo - size_chunk Mptr) Readable ->
    extcall_free_sem_mem_error (Vptr b lo) m
| free_error2: forall (b : block) (lo sz : ptrofs) (m m' : mem),
    Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
    Ptrofs.unsigned sz > 0 ->
    ~ Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable ->
    extcall_free_sem_mem_error (Vptr b lo) m.


Inductive drop_box_rec_mem_error (b: block) (ofs: ptrofs) : mem -> list type -> Prop :=
| drop_box_rec_error1: forall m ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error2: forall m ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem_mem_error (Vptr b1 ofs1) m -> 
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error3: forall m m1 ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    extcall_free_sem ge [Vptr b1 ofs1] m E0 Vundef m1 ->
    drop_box_rec_mem_error b ofs m1 tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
.

End DROPMEMBER.
