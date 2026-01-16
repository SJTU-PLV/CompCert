Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST Errors.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepSafe.
Require Import Listmisc.
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import RustIR.
Require Import LanguageInterface.

Import ListNotations.

Local Open Scope error_monad_scope.

(* Definition of Adt *)

Record Adt : Type := {
    repr: Type;
    repr_inv: repr -> Prop;         (* representation invariant. It may
    not useful in RustIRspec *)
    exposed_borrow: repr -> list ident; (* The exposed borrow indexes *)
  }.

Definition adt_env : Type := ident -> Adt.

Section SPEC.

(* I think this environment is a premise for the whole borrow checking
proof and the RustIRspec. When we want to use the borow checking
proof, we must provide its instance. *)
Variable ae: adt_env.

(** RustIR functional specification. *)

(* Function environment *)

(* Structured values. The structure is similar to the type of this
value. *)
Inductive sval : Type :=
| sv_bot
| sv_scalar (v: val)            (* scalar value: v cannot be Vptr *)
| sv_box (sv: sval) 
| sv_struct (id: ident) (svl: list (ident * sval))
| sv_enum (id: ident) (fid: ident) (sv: sval)
| sv_ref (ph: path) (* (cached: option sval) (getter: sval -> sval) (setter: sval -> sval -> sval) *) (* reference to an owner at [phs] *)
| sv_object (id: ident) (obj: repr (ae id)) (exposed: list (ident * sval))
.

Definition sv_map := PTree.t sval.

(* Operations for sval *)

Definition sem_cast (sv : sval) (t1 t2 : type) : res sval :=
  match sv with
  | sv_scalar v =>
      match sem_cast v t1 t2 with
      | Some v1 => OK (sv_scalar v1)
      | None => Error nil
      end
  (* We do not support casting for other kinds of value for now *)
  | _ => OK sv
  end.

Definition sval_casted (sv: sval) (ty: type) : Prop :=
  match sv with
  | sv_scalar v =>
      val_casted v ty
  | _ => True
  end.


Inductive sval_casted_list : list sval -> typelist -> Prop :=
  | vcl_nil : sval_casted_list nil Tnil
  | vcl_cons : forall (v1 : sval) (vl : list sval) (ty1 : type) (tyl : typelist),
               sval_casted v1 ty1 ->
               sval_casted_list vl tyl -> sval_casted_list (v1 :: vl) (Tcons ty1 tyl).

(* Operations for the environment *)

Fixpoint get_owner_sval (phl: list projection) (sv: sval) : res sval :=
  match phl with
  | nil => OK sv
  | ph :: l =>
      match ph, sv with
      | proj_deref, sv_box sv1 =>
          get_owner_sval l sv1
      | proj_field fid, sv_struct _ fpl =>
          match find_field fid fpl with
          | Some sv1 =>
              get_owner_sval l sv1
          | None => Error nil
          end
      (* Get the object's exposed borrowable value *)
      | proj_field fid, sv_object _ _ vl =>
          match find_field fid vl with
          | Some sv1 =>
              get_owner_sval l sv1
          | None => Error nil
          end
      | proj_downcast fid1, sv_enum _ fid2 sv1 =>
          if ident_eq fid1 fid2 then
            get_owner_sval l sv1
          else
            Error nil
      | _, _  => Error nil
      end
  end.

Definition get_owner_sval_map (ph: path) (e: sv_map) : res sval :=
  let (id, pj) := ph in
  match e ! id with
  | Some sv =>
      get_owner_sval pj sv
  | None =>
      Error nil
  end.

(* To get the location of arbitary path, we divide it into two steps:
first we use [get_owner_path] to obtain the path of these projections
in the tree and second we use [get_owner_sval] to obtain its sval. *)
Fixpoint get_owner_path (e: sv_map) (ph: path) (phl: list projection) (sv: sval)  : res path :=
  match phl with
  | nil => OK ph
  | pj :: l =>
      let ph1 := (fst ph, snd ph ++ [pj]) in
      match pj, sv with
      | proj_deref, sv_box sv1 =>
          get_owner_path e ph1 l sv1
      | proj_field fid, sv_struct _ fpl =>
          match find_field fid fpl with
          | Some sv1 =>
              get_owner_path e ph1 l sv1
          | None => Error nil
          end
      | proj_field fid, sv_object _ _ fpl =>
          match find_field fid fpl with
          | Some sv1 =>
              get_owner_path e ph1 l sv1
          | None => Error nil
          end
      | proj_downcast _, sv_enum _ _ sv1 =>
          (* Should we add tag checking here? *)
          get_owner_path e ph1 l sv1
      | proj_deref, sv_ref ph2 =>
          do fp2 <- get_owner_sval_map ph2 e;
          get_owner_path e ph2 l fp2
      | _, _  => Error nil
      end
  end.

(* This actually can be used to define "reachability" *)
Definition get_owner_path_sv_map (ps: path) (e: sv_map) : res path :=
  let (id, phl) := ps in
  match e!id with
  | Some sv =>
      get_owner_path e (id, nil) phl sv
  | _ => Error nil
  end.


Definition set_field_sv (fid: ident) (v: sval) (svl: list (ident * sval)) : list (ident * sval) :=
  set_field fid (fun _ => v) svl.

Fixpoint set_sval (phl: list projection) (v: sval) (root: sval) : res sval :=
  match phl with
  | nil => OK v
  | ph :: l =>
      match ph, root with
      | proj_deref, sv_box sv1 =>
          do sv2 <- set_sval l v sv1;
          OK (sv_box sv2)
      | proj_field fid, sv_struct id svl =>
          match find_field fid svl with
          | Some fsv =>
              do fsv1 <- set_sval l v fsv;
              OK (sv_struct id (set_field_sv fid fsv1 svl)) 
          | None => Error nil
          end
      | proj_field fid, sv_object id obj svl =>
          match find_field fid svl with
          | Some fsv =>
              do fsv1 <- set_sval l v fsv;
              OK (sv_object id obj (set_field_sv fid fsv1 svl)) 
          | None => Error nil
          end
      | proj_downcast fid, sv_enum id fid1 sv1 =>
          if ident_eq fid fid1 then
            do sv2 <- set_sval l v sv1;
            OK (sv_enum id fid1 sv2)
          else Error nil
      | _, _ => Error nil
      end
  end.

Definition set_sval_map (ph: path) (v: sval) (e: sv_map) : res sv_map :=
  let (id, phl) := ph in
  match e!id with
  | Some sv =>
      do sv1 <- set_sval phl v sv;
      OK (PTree.set id sv1 e)
  | None => Error nil
  end.


(* Different from the footprint in the simulation, we set sv_bot to
the location of the original value that is to be cleared *)
Definition clear_sval_map (ph: path) (e: sv_map) : res sv_map :=
  do sv <- get_owner_sval_map ph e;
  set_sval_map ph sv_bot e.

(* Operations for the function call and return *)

(** Some generic operations for adding and collecting paths from fpm or sv_map *)

Definition add_ref_path (ph: path) (l: list path) : list path :=
  if existsb (fun ph1 => is_prefix_path ph1 ph) l then
    l
  else
    (* We keep the non-prefix paths *)
    let l1 := filter (fun ph1 => negb (is_prefix_path ph ph1)) l in
    ph :: l.

Fixpoint add_ref_paths (l acc: list path) : list path :=
  match l with
  | nil => acc
  | ph :: l' =>
      add_ref_paths l' (add_ref_path ph acc)
  end.

Definition lex_ord_lt := lex_ord lt lt.

Lemma remove_first_length_lt {A B: Type} eqA : forall (l1: list A) (l2 l2': list B) x 
    (InH: In x l1),
    lex_ord_lt (length (remove eqA x l1), length l2)  (length l1, length l2').
Proof.
  intros. eapply lex_ord_left.
  eapply remove_length_lt. auto.
Qed.

Lemma lex_lt_cons_snd {A B: Type} : forall (l1: list A) (l2 l2': list B) x
    (EQ: l2' = x :: l2),
    lex_ord_lt (length l1, length l2)  (length l1, length l2').
Proof.
  intros. rewrite EQ.
  eapply lex_ord_right. simpl. 
  econstructor.
Qed.

(* Recursively collect ref paths. The actual definition of get_paths
depends on the definition of structured memory *)
Fixpoint collect_ref_paths_generic (get_paths: path -> res (list path)) (collected: list path) (to_visit: list path) (not_visited: list path) (ACC: Acc lex_ord_lt (length not_visited, length to_visit)) {struct ACC} : res (list path) :=
  (match to_visit as to_visit0 return (to_visit = to_visit0) -> res (list path) with
  | nil => fun _ => OK collected
  | ph :: to_visit1 =>
      fun eqH =>
        match in_dec path_eq ph not_visited with
        | left InH =>
            let not_visited1 := (remove path_eq ph not_visited) in
            let collected1 := add_ref_path ph collected in
            do new_paths <- get_paths ph;
            let ACC1 := Acc_inv ACC (remove_first_length_lt path_eq not_visited (new_paths ++ to_visit1) to_visit ph InH) in
            collect_ref_paths_generic get_paths collected1 (new_paths ++ to_visit1) not_visited1 ACC1
        (* This ph has been visited so we skip it *)
        | right _ =>
            let ACC1 := Acc_inv ACC (lex_lt_cons_snd not_visited to_visit1 to_visit ph eqH) in
            collect_ref_paths_generic get_paths collected to_visit1 not_visited ACC1
        end
  end) eq_refl.

Lemma lex_ord_lt_acc_intro {A B: Type} : forall (l1: list A) (l2: list B),
    Acc lex_ord_lt (length l1, length l2).
Proof. 
  intros.
  eapply wf_lex_ord. all: eapply Nat.lt_wf_0.
Qed.

Definition suffix_projections (phl1 phl2: list projection) : list projection :=
  skipn (length phl1) phl2.

(* We do not return (option path) to simplify the semantics. Note that
our final goal is to prove no UB in this semantics, so we need to
ensure that None case is impossible *)
Definition generate_new_suffix_path (l: list path) (ph: path) : res path :=
  match list_find (fun ph1 => is_prefix_path ph1 ph) l with
  | Some (idx, ph1) =>
      (* We cannot convert zero *)
      let new_id := Pos.of_nat (S idx) in
      let pj := suffix_projections (snd ph1) (snd ph) in
      OK (new_id, pj)
  | None => Error nil
  end.

(* The reverse operaiton of generate_new_suffix_path *)
(* ph= (id, pj) is the returned path where id can be seen as the index
of the l *)
Definition recover_ref_path (l: list path) (ph: path) : res path :=
  let (id, pj) := ph in
  match nth_error l (pred (Pos.to_nat id)) with
  | Some ph1 =>
      (* ph1 is the path in the caller's svm, the actual path of ph
      should be defined as appending the projecitons of ph into the
      projetions of ph1 *)
      OK ((fst ph1, snd ph1 ++ pj))
  | None =>
      Error nil
  end.


(** Implementation dependent operations *)

(* collect the owner paths stored in the leaf nodes that are sv_ref *)
Fixpoint collect_sval_ref_paths (sv: sval) : list path :=
  match sv with
  | sv_struct _ svl =>
      flat_map  (fun '(_, fsv) => collect_sval_ref_paths fsv) svl
  | sv_enum _ _ fsv =>
      collect_sval_ref_paths fsv
  | sv_box sv1 =>
      collect_sval_ref_paths sv1
  | sv_ref ph =>
      ph :: nil
  (* We assume that object cannot have referenece to the current environment *)
  (* | sv_object *)
  | _ => nil
  end.

Definition collect_svm_ref_paths (svm: sv_map) : list path :=
  let svl := map (fun '(_, sv) => sv) (PTree.elements svm) in
  flat_map collect_sval_ref_paths svl.

Definition get_owner_sval_map_ref_paths (svm: sv_map) (ph: path) : res (list path) :=
  do sv <- get_owner_sval_map ph svm;
  OK (collect_sval_ref_paths sv).

(* We need to ensure that all the returned paths are disjoint, its
located note contain deep_init sval, and form a closure *)
Definition collect_svm_args_ref_paths (svm: sv_map) (args: list sval) : res (list path) :=
  let not_visited := collect_svm_ref_paths svm in
  let to_visit := flat_map collect_sval_ref_paths args in
  collect_ref_paths_generic (get_owner_sval_map_ref_paths svm) nil to_visit not_visited (lex_ord_lt_acc_intro _ _).


Fixpoint generate_new_suffix_path_sval (l: list path) (sv: sval) : res sval :=
  match sv with
  | sv_ref ph =>
      do ph1 <- generate_new_suffix_path l ph;
      OK (sv_ref ph1)
  | sv_box sv1 =>
      do sv1' <- generate_new_suffix_path_sval l sv1;
      OK (sv_box sv1')
  | sv_struct id svl =>
      do svl1 <- (mmap (fun '(fid, fsv) => 
                            do fsv1 <- generate_new_suffix_path_sval l fsv;
                            OK (fid, fsv1)) svl);
      OK (sv_struct id svl1)
  | sv_enum id fid fsv =>
      do fsv1 <- generate_new_suffix_path_sval l fsv;
      OK (sv_enum id fid fsv1)
  | _ => OK sv
  end.

(* Collect the svals that are passed via reference to the environment *)
Definition collect_svm_passed_ref_sval (svm: sv_map) (l: list path) : res (list sval) :=
  mmap (fun ph => do sv <- get_owner_sval_map ph svm;
               generate_new_suffix_path_sval l sv) l.

(* set sv_bot to the location that passed via reference *)
Fixpoint clear_svm_passed_ref_sval (svm: sv_map) (l: list path) : res sv_map :=
  match l with
  | nil => OK svm
  | ph :: phl =>
      do svm1 <- set_sval_map ph sv_bot svm;
      clear_svm_passed_ref_sval svm1 phl
  end.

(* The output parameters contain two parts: one for the normal
arguments and the others are the memory locations passed via
reference *)
Definition generate_call_parameters (svm: sv_map) (args: list sval) : res (list sval * list sval * list path) :=
  do extern_paths <- collect_svm_args_ref_paths svm args;
  do args1 <- mmap (generate_new_suffix_path_sval extern_paths) args;
  do extern_svs <- collect_svm_passed_ref_sval svm extern_paths;
  OK (args1, extern_svs, extern_paths).

(* For funciton return, we need to reset the path name of the external
reference location to its normalized forms (i.e., the ordinal in the
list passed by caller). We can reuse the generate_new_suffix_path_sval
to do this work. *)
Definition generate_return_parameters (svm: sv_map) (retv: sval) (ns: list ident) : res (sval * list sval) :=
  let phs := map (fun id => (id, nil)) ns in
  do retv1 <- generate_new_suffix_path_sval phs retv;
  do out_params <- collect_svm_passed_ref_sval svm phs;
  OK (retv1, out_params).


(* When receive return value/input arguments from environment, the
current function should recover the normalized names that are passed
to environment (or generate new names to avoid name conflict with the
current variable names at function entry). These two kinds of
operations can be done using recover_sval_ref_paths. *)
Fixpoint recover_sval_ref_paths (l: list path) (sv: sval)  : res sval :=
  match sv with
  | sv_ref ph =>
      do ph1 <- recover_ref_path l ph;
      OK (sv_ref ph1)
  | sv_box sv1 =>
      do sv1' <- recover_sval_ref_paths l sv1;
      OK (sv_box sv1')
  | sv_struct id svl =>
      do svl1 <- mmap (fun '(fid, fsv) => 
                        do fsv1 <- recover_sval_ref_paths l fsv;
                        OK (fid, fsv1)) svl;
      OK (sv_struct id svl1)
  | sv_enum id fid fsv =>
      do fsv1 <- recover_sval_ref_paths l fsv;
      OK (sv_enum id fid fsv1)
  | _ =>
      OK sv
  end.


(* When the caller receives the returned sval and the
reference-passed sval list, it updates their reference paths and
then putback to the svm. The caller should guarantee that the external
svals are normalized into the form same as those passed by the
caller *)
Definition receive_return_sval (svm: sv_map) (l: list path) (retv: sval) (externs: list sval) : res (sval * sv_map) :=
  do retv1 <- recover_sval_ref_paths l retv;
  do externs1 <- mmap (recover_sval_ref_paths l) externs;
  let phs_externs := combine l externs1 in
  do svm1 <- mfold_left (fun acc '(ph, sv) => set_sval_map ph sv acc) phs_externs svm;
  OK (retv1, svm1).

Definition receive_incoming_params (fresh_paths: list path) (args: list sval) (in_params: list sval) : res (list sval * list sval) :=
  do args1 <- mmap (recover_sval_ref_paths fresh_paths) args;
  do in_params1 <- mmap (recover_sval_ref_paths fresh_paths) in_params;
  OK (args1, in_params1).
  

Section SEMANTICS.

(** ** Global environment  *)

Definition rustir_defmap := PTree.t (globdef fundef type).

Record genv := { genv_genv:> Genv.t fundef type; genv_defmap :> rustir_defmap ; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv:= Genv.globalenv se p; genv_defmap := prog_defmap p ; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.

(** ** Evaluation of expressions *)

Section EXPR.
  
Fixpoint eval_pexpr (e: sv_map) (pe: pexpr) : res sval :=
  match pe with
  | Eunit => OK (sv_scalar (Vint Int.zero))
  | Econst_int i ty => OK (sv_scalar (Vint i))
  | Econst_float f ty => OK (sv_scalar (Vfloat f))
  | Econst_single f ty => OK (sv_scalar (Vsingle f))
  | Econst_long i ty => OK (sv_scalar (Vlong i))
  | Eunop op a t =>
      do v1 <- eval_pexpr e a;
      match v1 with
      | sv_scalar v2 =>
          match sem_unary_operation op v2 t with
          | Some v3 =>
              OK (sv_scalar v3)
          | None =>
              Error nil
          end
      | _ => Error nil
      end
  | Ebinop op a1 a2 t =>
      do v1 <- eval_pexpr e a1;
      do v2 <- eval_pexpr e a2;
      match v1, v2 with
      | sv_scalar v1', sv_scalar v2' =>
          match sem_binary_operation_rust op v1' (typeof_pexpr a1) v2' (typeof_pexpr a2) with
          | Some v =>
              OK (sv_scalar v)
          | None =>
              Error nil
          end
      | _, _ => Error nil
      end
  | Eplace p ty =>
      do ph <- get_owner_path_sv_map p e;
      get_owner_sval_map ph e
  | Ecktag p fid =>
      do ph <- get_owner_path_sv_map p e;
      do v <- get_owner_sval_map ph e;
      match v with
      | sv_enum _ fid1 _ =>
          OK (sv_scalar (Val.of_bool (ident_eq fid fid1)))
      | _ => Error nil
      end
  | Eref _ _ p _ =>
      OK (sv_ref p)
  | _ => Error nil
  end.
      
Definition eval_expr (e: sv_map) (a: expr) : res (sval * sv_map) :=
  match a with
  | Emoveplace p _ =>
      do v <- get_owner_sval_map p e;
      do e1 <- clear_sval_map p e;
      OK (v, e1)
  | Epure pe =>
      do v <- eval_pexpr e pe;
      OK (v, e)
  end.

Fixpoint eval_exprlist (m: sv_map) (al: list expr) (tyl: typelist) : res (list sval * sv_map) :=
  match al, tyl with
  | nil, Tnil => OK (nil, m)
  | a :: al1, Tcons ty tyl1 =>
      do (v1, m1) <- eval_expr m a;
      do v1' <- sem_cast v1 (typeof a) ty;
      do (vl, m2) <- eval_exprlist m1 al1 tyl1;
      OK (v1' :: vl, m2)
  | _, _ => Error nil
  end.

End EXPR.

(** ** Program states *)

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: place -> function -> list path -> list ident -> sv_map -> cont -> cont
.


(* Return from dropstate, dropplace and dropinsert is UB *)
Fixpoint call_cont (k: cont) : option cont :=
  match k with
  | Kseq _ k => call_cont k
  | Kloop _ k => call_cont k
  | _ => Some k
  end.


Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ _ => True
  | _ => False
  end.

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (inout: list ident)         (* used to record the new idents for the in-out parameters *)
    (e: sv_map): state
| Callstate
    (fun_id: ident)
    (args: list sval)
    (inout: list sval)
    (k: cont): state
| Returnstate
    (res: sval)
    (inout: list sval)
    (k: cont): state.


(* Initialize of function *)

(* Copy from memory *)

Fixpoint find_max_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => Pos.max hd (find_max_pos tl)
  end.

Fixpoint npos (n: nat) (p: positive) : list positive :=
  match n with
  | O => nil
  | S n' =>
      p :: (npos n' (Pos.succ p))
  end.

Fixpoint bind_params (m: sv_map) (l: list ident) (vl: list sval) : res sv_map :=
  match l, vl with
  | nil, nil => OK m
  | id :: l1, v :: vl1 =>
      do m1 <- set_sval_map (id, nil) v m;
      bind_params m1 l1 vl1
  | _, _ => Error nil
  end.
      

Definition function_entry (f: function) (args: list sval) (in_params: list sval) : res (list ident * sv_map) :=
  let names := field_idents (fn_params f ++ fn_vars f) in
  let fresh_var := Pos.succ (find_max_pos names) in
  let fresh_vars := npos (length in_params) fresh_var in
  (* Substitute the old name in args and in_params with the fresh names *)
  let fresh_paths : list path := map (fun id => (id, nil)) fresh_vars in
  do (args1, in_params1) <- receive_incoming_params fresh_paths args in_params;
  (* set the value to the map *)
  do m1 <- bind_params (PTree.empty sval) (field_idents (fn_params f)) args1;
  do m2 <- bind_params m1 fresh_vars in_params1;
  do m3 <- bind_params m2 (field_idents (fn_vars f)) (repeat sv_bot (length (fn_vars f)));
  OK (fresh_vars, m3).

Section SMALLSTEP.

Variable ge: genv.

Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e (p: place) m1 m2 m3 ph v v1 ns k
    (EVALP: get_owner_path_sv_map p m1 = OK ph)
    (EVALE: eval_expr m1 e = OK (v, m2))
    (CAST: sem_cast v (typeof e) (typeof_place p) = OK v1)
    (ASS: set_sval_map ph v1 m2 = OK m3),
    step (State f (Sassign p e) k ns m1) E0 (State f Sskip k ns m3)
| step_assign_variant: forall f e (p: place) k m1 m2 m3 v v1 co fid enum_id orgs ph fty ns
    (EVALP: get_owner_path_sv_map p m1 = OK ph)
    (EVALE: eval_expr m1 e = OK (v, m2))
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK fty)
    (CAST: sem_cast v (typeof e) fty = OK v1)
    (ASS: set_sval_map ph (sv_enum enum_id fid v1) m2 = OK m3),
    step (State f (Sassign_variant p enum_id fid e) k ns m1) E0 (State f Sskip k ns m3)
| step_box: forall f e (p: place) k ty m1 m2 m3 v v1 ph ns
    (EVALP: get_owner_path_sv_map p m1 = OK ph)
    (EVALE: eval_expr m1 e = OK (v, m2))
    (TYP: typeof_place p = Tbox ty)
    (CAST: sem_cast v (typeof e) ty = OK v1)
    (ASS: set_sval_map ph (sv_box v1) m2 = OK m3),
    step (State f (Sbox p e) k ns m1) E0 (State f Sskip k ns m3)
(** bigl-step drop semantics: just like a move operation *)
| step_drop: forall m1 m2 k f (p: place) ph ns
    (EVALP: get_owner_path_sv_map p m1 = OK ph)
    (DROP: clear_sval_map ph m1 = OK m2),
    step (State f (Sdrop p) k ns m1) E0 (State f Sskip k ns m2)
| step_storagelive: forall f k ns m id,
    step (State f (Sstoragelive id) k ns m) E0 (State f Sskip k ns m)
| step_storagedead: forall f k ns m id,
    step (State f (Sstoragedead id) k ns m) E0 (State f Sskip k ns m)
| step_call: forall f ty al k tyargs fd cconv tyres p orgs org_rels fun_id m1 m2 args args1 out_params ns phl
    (CASE: classify_fun ty = fun_case_f tyargs tyres cconv)
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (EVAL: eval_exprlist m1 al tyargs = OK (args, m2))
    (NOT_DROP: function_not_drop_glue fd)
    (* Collect the footprint that is passed via reference *)
    (REF_OUT: generate_call_parameters m2 args = OK (args1, out_params, phl)),
    step (State f (Scall p (Eglobal fun_id ty) al) k ns m1) E0 (Callstate fun_id args1 out_params (Kcall p f phl ns m2 k))
| step_internal_function: forall fun_id vargs in_params k m f ns
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry f vargs in_params = OK (ns, m)),
    step (Callstate fun_id vargs in_params k) E0 (State f f.(fn_body) k ns m)

(** We do not support axiomatic external call *)
(* | step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels *)
(*     (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc)) *)
(*     (NORMAL: ef <> EF_malloc /\ ef <> EF_free), *)
(*     external_call ef ge vargs m t v m' -> *)
(*     step (Callstate vf vargs k m) t (Returnstate v k m') *)
   
(** Return cases *)
(* | step_return_0: forall e lb m1 m2 f k, *)
(*     (forall id b t, e ! id = Some (b, t) -> complete_type ge t = true) -> *)
(*     blocks_of_env ge e = lb -> *)
(*     (* drop the stack blocks *) *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     (* return unit or Vundef? *) *)
(*     step (State f (Sreturn None) k e m1) E0 (Returnstate Vundef (call_cont k) m2) *)
| step_return_1: forall p v v1 v2 m1 f k ck ns out_params
    (CONT: call_cont k = Some ck)
    (EVAL: eval_pexpr m1 (Eplace p (typeof_place p)) = OK v)
    (CAST: sem_cast v (typeof_place p) f.(fn_return) = OK v1)
    (** Rename the external footprint to match the use of the names passed
    in this function *)
    (NORMALIZE: generate_return_parameters m1 v1 ns = OK (v2, out_params)),
    step (State f (Sreturn p) k ns m1) E0 (Returnstate v2 out_params ck)
(* no return statement but reach the end of the function *)
(* | step_skip_call: forall e lb m1 m2 f k, *)
(*     is_call_cont k -> *)
(*     (forall id b t, e ! id = Some (b, t) -> complete_type ge t = true) -> *)
(*     blocks_of_env ge e = lb -> *)
(*     Mem.free_list m1 lb = Some m2 -> *)
(*     step (State f Sskip k e m1) E0 (Returnstate Vundef (call_cont k) m2) *)
         
| step_returnstate: forall (p: place) v v1 m1 m2 m3 f k out_params phl ph ns
    (* We need to first putback the ref-passed location and the do the
    assignment because p may locate in those ref-passed locations *)
    (PUTBACK: receive_return_sval m1 phl v out_params = OK (v1, m2))
    (EVALP: get_owner_path_sv_map p m1 = OK ph)
    (CASTED: sval_casted v1 (typeof_place p))
    (ASS: set_sval_map ph v1 m2 = OK m3),
    step (Returnstate v out_params (Kcall p f phl ns m1 k)) E0 (State f Sskip k ns m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m,
    step (State f (Ssequence s1 s2) k e m)
      E0 (State f s1 (Kseq s2 k) e m)
| step_skip_seq: forall f s k e m,
    step (State f Sskip (Kseq s k) e m)
      E0 (State f s k e m)
| step_continue_seq: forall f s k e m,
    step (State f Scontinue (Kseq s k) e m)
      E0 (State f Scontinue k e m)
| step_break_seq: forall f s k e m,
    step (State f Sbreak (Kseq s k) e m)
      E0 (State f Sbreak k e m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b
    (* there is no receiver for the moved place, so it must be None *)
    (EVAL: eval_pexpr m a = OK (sv_scalar v1)),
    bool_val v1 (typeof a) = Some b ->
    step (State f (Sifthenelse (Epure a) s1 s2) k e m)
      E0 (State f (if b then s1 else s2) k e m)
| step_loop: forall f s k e m,
    step (State f (Sloop s) k e m)
      E0 (State f s (Kloop s k) e m)
| step_skip_or_continue_loop:  forall f s k e m x,
    x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e m)
      E0 (State f s (Kloop s k) e m)
| step_break_loop:  forall f s k e m,
    step (State f Sbreak (Kloop s k) e m)
      E0 (State f Sskip k e m)
.

(** Language interfaces for the RustIR specification *)

Record rust_spec_query :=
  rspec_q {
    rspec_fid: ident;
    rspec_sg: rust_signature;
    rspec_args: list sval;
    rspec_in_params: list sval;
  }.

Record rust_spec_reply :=
  rspec_r {
    rspec_retval: sval;
    rspec_out_params: list sval;
  }.

Definition li_rs_spec : language_interface :=
  {|
    query := rust_spec_query;
    reply := rust_spec_reply;
    entry _ := Vundef;
  |}.


(** Open semantics *)

Inductive initial_state: (query li_rs_spec) -> state -> Prop :=
| initial_state_intro: forall f targs tres tcc vargs orgs org_rels fun_id in_params
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (TYF: type_of_function f = Tfunction orgs org_rels targs tres tcc)
    (* This function must not be drop glue *)
    (NOTDROP: f.(fn_drop_glue) = None)
    (* how to use it? *)
    (CAST: sval_casted_list vargs targs),
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rspec_q fun_id (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs in_params)
      (Callstate fun_id vargs in_params Kstop).


Inductive at_external: state -> (query li_rs_spec) -> Prop :=
| at_external_intro: forall fun_id name args k targs tres cconv orgs org_rels in_params
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv))),
    at_external (Callstate fun_id args in_params k) (rspec_q fun_id (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args in_params).

Inductive after_external: state -> (reply li_rs_spec) -> state -> Prop:=
| after_external_intro: forall fun_id args k in_params out_params v,
    after_external
      (Callstate fun_id args in_params k)
      (rspec_r v out_params)
      (Returnstate v out_params k).

Inductive final_state: state -> (reply li_rs_spec) -> Prop:=
| final_state_intro: forall v out_params,
    final_state (Returnstate v out_params Kstop) (rspec_r v out_params).

End SMALLSTEP.

End SEMANTICS.

Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

End SPEC.
