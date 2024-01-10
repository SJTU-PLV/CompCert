Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import LanguageInterface.

(** The rust surface syntax *)

Inductive expr : Type :=
| Eval (v: val) (ty: type)                                  (**r constant *)
| Evar (x: ident) (ty: type)                                (**r variable *)
| Ebox (r: expr) (ty: type)                                 (**r allocate a heap block *)
| Efield (l: expr) (f: ident) (ty: type) (**r access to a member of a struct *)
| Ederef (r: expr) (ty: type)        (**r pointer dereference (unary [*]) *)
| Eunop (op: unary_operation) (r: expr) (ty: type)
(**r unary arithmetic operation *)
| Ebinop (op: binary_operation) (r1 r2: expr) (ty: type)
                                           (**r binary arithmetic operation *)
| Eassign (l: expr) (r: expr) (ty: type)          (**r assignment [l = r] *)
| Ecall (r1: expr) (rargs: exprlist) (ty: type)

with exprlist : Type :=
  | Enil
  | Econs (r1: expr) (rl: exprlist).

Definition typeof (e: expr) : type :=
  match e with
  | Eval _ ty
  | Evar _ ty
  | Ebox _ ty
  | Efield _ _ ty
  | Ederef _ ty
  | Eunop _ _ ty
  | Ebinop _ _ _ ty                  
  | Eassign _ _ ty
  | Ecall _ _ ty => ty
end.

Inductive statement : Type :=
| Sskip : statement                   (**r do nothing *)
| Sdo : expr -> statement            (**r evaluate expression for side effects *)
| Slet: ident -> type -> statement -> statement  (**r [Slet id ty] opens a new scope with one variable of type ty *)
| Ssequence : statement -> statement -> statement  (**r sequence *)
| Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
| Swhile : expr -> statement -> statement   (**r [while] loop *)
| Sloop: statement -> statement                               (**r infinite loop *)
| Sbreak : statement                      (**r [break] statement *)
| Scontinue : statement                   (**r [continue] statement *)
| Sreturn : option expr -> statement     (**r [return] statement *)
| Smatch : expr -> arm_statements -> statement  (**r pattern match statements *)

with arm_statements : Type :=            (**r cases of a [match] *)
  | ASnil: arm_statements
  | AScons: option (ident * ident) -> statement -> arm_statements -> arm_statements.
                      (**r [None] is [default], [Some (fid, id)] is [case fid (id)] *)


Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type); 
  fn_body: statement
}.  

Definition fundef := Rusttypes.fundef function.

Definition program := Rusttypes.program function.


(** Notations for Rustsyntax programs *)


Definition A : ident := 1%positive.
Definition B : ident := 2%positive.
Definition C : ident := 3%positive.
Definition D : ident := 4%positive.
Definition E : ident := 5%positive.

Declare Custom Entry rustsyntax.
Declare Scope rustsyntax_scope.
Declare Custom Entry rustsyntax_aux.

Notation "<{ s }>" := s (s custom rustsyntax_aux) : rustsyntax_scope.
Notation "s" := s (in custom rustsyntax_aux at level 0, s custom rustsyntax) : rustsyntax_scope.

(* uncomment it would disable the pretty-print *)
(* Notation " x " := x (in custom rustsyntax at level 0, x global). (* It indicate that the custom entry should parse global *) *)

(* Notations for statement *)
Notation "'if' e 'then' s1 'else' s2 'end'" := (Sifthenelse e s1 s2) (in custom rustsyntax at level 80, s1 at level 99, s2 at level 99) : rustsyntax_scope.
Notation "s1 ; s2" := (Ssequence s1 s2) (in custom rustsyntax at level 99, right associativity) : rustsyntax_scope.
Notation "'do' e" := (Sdo e) (in custom rustsyntax at level 80, e at level 20) : rustsyntax_scope.
Notation "'skip'" := Sskip (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'break'" := Sbreak (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'continue'" := Scontinue (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'return0'" := (Sreturn None) (in custom rustsyntax at level 0) : rustsyntax_scope.
Notation "'return' e" := (Sreturn (@Some expr e)) (in custom rustsyntax at level 80, e at level 20) : rustsyntax_scope.
Notation "'let' x : t 'in' s 'end' " := (Slet x t s) (in custom rustsyntax at level 80, s at level 99, x global, t global) : rustsyntax_scope.
Notation "'loop' s 'end'" := (Sloop s) (in custom rustsyntax at level 80, s at level 99) : rustsyntax_scope.
Notation "'while' e 'do' s 'end'" := (Swhile e s) (in custom rustsyntax at level 80, e at level 20, s at level 99) : rustsyntax_scope.
(** TODO: define the notations for match statement *)

(* Notations for expression *)

(* expression is at level 20 *)
Notation " ( x ) " := x (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " x # t " := (Evar x t) (in custom rustsyntax at level 0, x global, t global)  : rustsyntax_scope.
Notation "'Box' ( e )" := (Ebox e (Tbox (typeof e) noattr)) (in custom rustsyntax at level 10, e at level 20)  : rustsyntax_scope.
Notation " ! e " := (Ederef e (deref_type (typeof e))) (in custom rustsyntax at level 10, e at level 20) : rustsyntax_scope.
Notation " e . x < t > " := (Efield e x t) (in custom rustsyntax at level 10, t global) : rustsyntax_scope.
Notation " l := r " := (Eassign l r Tunit) (in custom rustsyntax at level 17, r at level 20) : rustsyntax_scope.
Notation " { x , .. , y } " := (Econs x .. (Econs y Enil) .. ) (in custom rustsyntax at level 20) : rustsyntax_scope.
Notation " f @ l " := (Ecall f l) (in custom rustsyntax at level 10, l at level 10) : rustsyntax_scope.
Notation " e1 < e2 " := (Ebinop Ole e1 e2 type_bool) (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " $ k " := (Eval (Vint (Int.repr k)) type_int32s) (in custom rustsyntax at level 10, k constr) : rustsyntax_scope.
Notation " e1 * e2 " := (Ebinop Omul e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.
Notation " e1 - e2 " := (Ebinop Osub e1 e2 (typeof e1))  (in custom rustsyntax at level 15, e2 at level 20, left associativity) : rustsyntax_scope.


(* Print Grammar constr. *)
(* Print Custom Grammar rustsyntax. *)

Open Scope rustsyntax_scope.

Definition var_a : expr := <{ A # type_int32s }>.
Definition box_a : expr := <{ Box(A # type_int32s) }>.
(* Definition deref_box_a_global : expr := <{ ! box_a }>. *)
Definition deref_box_a : expr := <{ ! Box(A # type_int32s) }>.


(* Example 1 *)

Definition box_int := Tbox type_int32s noattr.

Definition ex1 (a b: ident) :=
  <{ do (a#type_int32s) := !(b#box_int);
     let C : box_int in
     if ((a#type_int32s) < !(b#box_int)) then
       do (C#box_int) := (b#box_int)
     else
       do (b#box_int) := Box($3)
     end
     end
    }>.


(* Example 2 *)


(* Print Custom Grammar rustsyntax. *)

Definition N : ident := 30%positive.

Definition fact (n: Z) :=
  <{ let N : type_int32s in
     do (N#type_int32s) := $n;
     let A : type_int32s in
     do (A#type_int32s) := $1;
     let B : box_int in
     do (B#box_int) := Box(!A#type_int32s);
     while (($0) < (N#type_int32s)) do
       let C : box_int in
       do (C#box_int) := Box(!B#box_int); (* comment it to check the init analysis *)
       do (!C#box_int) := Box(!B#box_int) * (N#type_int32s);
       do (N#type_int32s) := (N#type_int32s) - $1;
       do (B#box_int) := (C#box_int)
       end                       
     end
     end end end
    }>.
