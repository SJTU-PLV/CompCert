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
Require Import Ctypes Rusttypes Rusttyping Rustlight.
Require Import RustIR.
Require Import LanguageInterface.
Require Import InitDomain StkBorPermission.

Import ListNotations.

Local Open Scope error_monad_scope.

Section WT_PATH.

Variable ce: composite_env.

Fixpoint wt_projections (ty: type) (phl: list projection) : res type :=
  match phl with
  | nil => OK ty
  | ph :: phl1 =>
      do ty1 <- 
           match ph with
           | proj_deref => type_deref ty
           | proj_field fid => type_field ce ty fid
           | proj_downcast fid => type_downcast ce ty fid
           end;
      wt_projections ty1 phl1
  end.

Definition wt_path (te: typenv) (phs: path) : res type :=
  let (id, phl) := phs in
  match te ! id with
  | Some ty =>
      wt_projections ty phl
  | None =>
      Error (msg "no local type")
  end.

End WT_PATH.

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
Context {ae: adt_env}.

(** RustIR functional specification. *)

(* Function environment *)

Definition views := list path.

Lemma path_views_eq: forall (x: path * views) (y: path * views),
    {x = y} + {x <> y}.
Proof.
  intros. destruct x, y.
  generalize path_eq (list_eq_dec path_eq). intros.
  decide equality.
Qed.

(* Structured values. The structure is similar to the type of this
value. *)
Inductive sval : Type :=
| sv_bot
| sv_scalar (v: val)            (* scalar value: v cannot be Vptr *)
| sv_box (sv: sval) 
| sv_struct (id: ident) (svl: list (ident * sval))
| sv_enum (id: ident) (fid: ident) (sv: sval)
| sv_ref (mut: mutkind) (ph: path) (vs: views) (* reference to an
  owner at [phs]. We use [vs] to record other owner path that directly
  mutably reference to [ph] (precisely shallow children of [ph]). *)
| sv_object (id: ident) (obj: repr (ae id)) (exposed: list (ident * (type * sval)))
.

Definition sv_map := PTree.t (option origin * type * sval).

Coercion svm_to_tenv (svm: sv_map) : typenv := PTree.map1 (fun '(_, ty, _) => ty) svm.


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
          | Some (_, sv1) =>
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
  | Some (_, _, sv) =>
      get_owner_sval pj sv
  | None =>
      Error nil
  end.

Definition append_proj (pj: projection) (ph: path) :=
  (fst ph, snd ph ++ [pj]).

(* To get the location of arbitary path, we divide it into two steps:
first we use [get_owner_path] to obtain the path of these projections
in the tree and second we use [get_owner_sval] to obtain its sval. We
also collect all aliased paths (which directly points to the owner
path) of this owner path to do dynamic alias analysis. *)
Fixpoint get_owner_path (e: sv_map) (ph: path) (phl: list projection) (sv: sval) (alias: list path) : res (path * views) :=
  match phl with
  | nil => OK (ph, alias)
  | pj :: l =>
      let ph1 := append_proj pj ph in
      let alias1 := map (append_proj pj) alias in
      match pj, sv with
      | proj_deref, sv_box sv1 =>
          (* Since we get the reference of ph1 via its dominator, we
          do not need to record other paths that point to ph1 *)
          get_owner_path e ph1 l sv1 nil
      | proj_field fid, sv_struct _ fpl =>
          match find_field fid fpl with
          | Some sv1 =>
              get_owner_path e ph1 l sv1 alias1
          | None => Error nil
          end
      | proj_field fid, sv_object _ _ fpl =>
          match find_field fid fpl with
          | Some (_, sv1) =>
              (* Since object is the dominator of its exposed fields
              and note that all the paths alias set are the paths that
              point to the object itself, but there may be other paths
              that point to this object which are created by
              reborrowing, which cannot be tracted by alias set, so we
              require that all the paths reachable to this object must
              be included in the loans of the created reference. *)
              get_owner_path e ph1 l sv1 nil
          | None => Error nil
          end
      | proj_downcast _, sv_enum _ _ sv1 =>
          (* Should we add tag checking here? *)
          get_owner_path e ph1 l sv1 alias1
      | proj_deref, sv_ref mut ph2 vs =>
          do sv2 <- get_owner_sval_map ph2 e;
          (* It this reference is mutable reference, we add the deref
          path of this reference and its views as the alias path of
          [ph2]. It it is immutable, we should add [vs] only because
          all the path in [vs] can mutate the value in [ph2]. *)
          let alias2 := match mut with | Mutable => ph1 :: vs | Immutable => vs end in
          get_owner_path e ph2 l sv2 alias2
      | _, _  => Error nil
      end
  end.

(* This actually can be used to define "reachability" *)
Definition get_owner_path_sv_map (ps: path) (e: sv_map) : res (path * views) :=
  let (id, phl) := ps in
  match e!id with
  | Some (_, _, sv) =>
      get_owner_path e (id, nil) phl sv nil
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
          | Some (fty, fsv) =>
              do fsv1 <- set_sval l v fsv;
              OK (sv_object id obj (set_field fid (fun _ => (fty, fsv1)) svl)) 
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
  | Some (ty, r, sv) =>
      do sv1 <- set_sval phl v sv;
      OK (PTree.set id (ty, r, sv1) e)
  | None => Error nil
  end.


(* Different from the footprint in the simulation, we set sv_bot to
the location of the original value that is to be cleared *)
Definition clear_sval_map (ph: path) (e: sv_map) : res sv_map :=
  do sv <- get_owner_sval_map ph e;
  set_sval_map ph sv_bot e.

(* Operations for the function call and return *)

(** Some generic operations for adding and collecting paths from fpm or sv_map *)

Definition add_ref_path_views (ph: path) (vs: views) (r: origin) (ty: type) (l: list (path * (views * origin * type))) : list (path * (views * origin * type)):=
  if existsb (fun ph1 => is_prefix_path ph1 ph) (map fst l) then
    l
  else
    (* We keep the non-prefix paths *)
    let l1 := filter (fun '(ph1, (_, _, _)) => negb (is_prefix_path ph ph1)) l in
    (ph, (vs, r, ty)) :: l.

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
depends on the definition of structured memory. The returned list of
paths are the view of the reference which points to the owner path. We
need to remember it so that we can abstract it, pass it to callee and
then recover from the returned abstract view and recover to the
concrete views. [get_paths] gets the paths that a reference points to
along with the views of this reference. It may be not useful to
parametrize the get_paths as we can just use the result from the
RustIRspec to construct the footprint that are passed to the callee
instead of using footprint's specific get_paths function. *)
Fixpoint collect_ref_paths_generic (get_paths: path -> type -> res (list (path * (views * origin * type)))) (collected: list (path * (views * origin * type))) (to_visit: list (path * (views * origin * type))) (not_visited: list path) (ACC: Acc lex_ord_lt (length not_visited, length to_visit)) {struct ACC} : res (list (path * (views * origin * type))) :=
  (match to_visit as to_visit0 return (to_visit = to_visit0) -> res (list (path * (views * origin * type))) with
  | nil => fun _ => OK collected
  | (ph, (vs, r, ty)) :: to_visit1 =>
      fun eqH =>
        (** TODO: it may be better to use filter instead of remove  *)
        match in_dec path_eq ph not_visited with
        | left InH =>
            let not_visited1 := (remove path_eq ph not_visited) in
            let collected1 := add_ref_path_views ph vs r ty collected in
            do new_paths <- get_paths ph ty;
            let ACC1 := Acc_inv ACC (remove_first_length_lt path_eq not_visited (new_paths ++ to_visit1) to_visit ph InH) in
            collect_ref_paths_generic get_paths collected1 (new_paths ++ to_visit1) not_visited1 ACC1
        (* This ph has been visited so we skip it *)
        | right _ =>
            let ACC1 := Acc_inv ACC (lex_lt_cons_snd not_visited to_visit1 to_visit (ph, (vs, r, ty)) eqH) in
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

(* collect the owner paths stored in the leaf nodes that are
sv_ref. *)
Fixpoint collect_sval_ref_paths (sv: sval) : list path :=
  match sv with
  | sv_struct _ svl =>
      flat_map  (fun '(fid, fsv) => collect_sval_ref_paths fsv) svl
  | sv_enum _ fid fsv =>
      collect_sval_ref_paths fsv 
  | sv_box sv1 =>
      collect_sval_ref_paths sv1
  | sv_ref _ ph vs =>
      ph :: nil
  (* We assume that object cannot have referenece to the current environment *)
  (* | sv_object *)
  | _ => nil
  end.

(* Similar to collect_sval_ref_paths, we also return the projections
of the reference path. It is only used in collect_sval_ref_paths_types *)
Fixpoint collect_sval_ref_paths_projections (pj: list projection) (sv: sval) : list (path * views * list projection) :=
  match sv with
  | sv_struct _ svl =>
      flat_map  (fun '(fid, fsv) => collect_sval_ref_paths_projections (pj ++ [proj_field fid]) fsv) svl
  | sv_enum _ fid fsv =>
      collect_sval_ref_paths_projections (pj ++ [proj_downcast fid]) fsv 
  | sv_box sv1 =>
      collect_sval_ref_paths_projections (pj ++ [proj_deref]) sv1
  | sv_ref _ ph vs =>
      (ph, vs, pj) :: nil
  (* We assume that object cannot have referenece to the current environment *)
  (* | sv_object *)
  | _ => nil
  end.

Definition collect_ref_type_region ce (ty: type) (pj: list projection) : res (origin * type) :=
    do ty1 <- wt_projections ce ty pj;
    match ty1 with
    | Treference r _ ty2 =>
        OK (r, ty2)
    | _ => Error nil
    end.

Definition collect_sval_ref_paths_types ce (ty_sv: type * sval) : res (list (path * (views * origin * type))) :=
  let (ty, sv) := ty_sv in
  let l := collect_sval_ref_paths_projections nil sv in
  mmap (fun '(ph, vs, pj) => do (r, ty1) <- collect_ref_type_region ce ty pj;
                          OK (ph, (vs, r, ty1))) l.

(* collect all the unvisited owner path *)
Definition collect_svm_ref_paths (svm: sv_map) : list path :=
  let svl := map (fun '(_, (_, _, sv)) => sv) (PTree.elements svm) in
  flat_map (collect_sval_ref_paths) svl.

(* [ty] should be computed from the function arguments types *)
Definition get_owner_sval_map_ref_paths ce (svm: sv_map) (ph: path) (ty: type) : res (list (path * (views * origin * type))) :=
  do sv <- get_owner_sval_map ph svm;
  (collect_sval_ref_paths_types ce (ty, sv)).

(* We need to ensure that all the returned paths are disjoint, its
located note contain deep_init sval, and form a closure. The types of
the argument come from function signature, meaning that they contain
generic regions. *)
Definition collect_svm_args_ref_paths ce (svm: sv_map) (args: list (type * sval)) : res (list (path * (views * origin * type))) :=
  let not_visited := collect_svm_ref_paths svm in
  do l <- mmap (collect_sval_ref_paths_types ce) args;  
  let to_visit := concat l in
  collect_ref_paths_generic (get_owner_sval_map_ref_paths ce svm) nil to_visit not_visited (lex_ord_lt_acc_intro _ _).


Fixpoint generate_new_suffix_path_sval (process_views: path -> views -> views) (l: list path) (sv: sval) : res sval :=
  match sv with
  | sv_ref mut ph vs =>
      do ph1 <- generate_new_suffix_path l ph;
      (* We can directly use ph1 as the abstract view for callee? *)
      OK (sv_ref mut ph1 (process_views ph1 vs))
  | sv_box sv1 =>
      do sv1' <- generate_new_suffix_path_sval process_views l sv1;
      OK (sv_box sv1')
  | sv_struct id svl =>
      do svl1 <- (mmap (fun '(fid, fsv) => 
                            do fsv1 <- generate_new_suffix_path_sval process_views l fsv;
                            OK (fid, fsv1)) svl);
      OK (sv_struct id svl1)
  | sv_enum id fid fsv =>
      do fsv1 <- generate_new_suffix_path_sval process_views l fsv;
      OK (sv_enum id fid fsv1)
  | sv_object id obj svl =>
      do svl1 <- (mmap (fun '(fid, (fty, fsv)) => 
                            do fsv1 <- generate_new_suffix_path_sval process_views l fsv;
                            OK (fid, (fty, fsv1))) svl);
      OK (sv_object id obj svl1)
  | _ => OK sv
  end.


(* Collect the svals that are passed via reference to the environment *)
Definition collect_svm_passed_ref_sval (process_views: path -> views -> views) (svm: sv_map) (l: list path) : res (list sval) :=
  mmap (fun ph => do sv <- get_owner_sval_map ph svm;
               generate_new_suffix_path_sval process_views l sv) l.

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
Definition generate_call_parameters ce (svm: sv_map) (args: list (type * sval)) : res (list sval * list (origin * type * sval) * list (path * (views * origin * type))) :=
  do extern_paths <- collect_svm_args_ref_paths ce svm args;  
  do args1 <- mmap (generate_new_suffix_path_sval (fun ph _ => ph :: nil) (map fst extern_paths)) (map snd args);
  do inout_svals <- collect_svm_passed_ref_sval (fun ph _ => ph :: nil) svm (map fst extern_paths);
  (* collect (origin, type) for the inout arguments *)
  let inout_params := combine (map (fun '(_, (_, r, ty)) => (r, ty)) extern_paths) inout_svals in
  OK (args1, inout_params, extern_paths).

Definition normalize_returned_views (phs: list path) (_: path) (vs: views) : views :=
  (* If we cannot find the path in phs, it means that it is a local
  path of the callee and we can just ignore it. *)
  flat_map (fun ph => match generate_new_suffix_path phs ph with
                   | OK ph1 => ph1 :: nil
                   | _ => nil
                   end) vs.

(* For funciton return, we need to reset the path name of the external
reference location to its normalized forms (i.e., the ordinal in the
list passed by caller). We can reuse the generate_new_suffix_path_sval
to do this work. *)
Definition generate_return_parameters (svm: sv_map) (retv: sval) (ns: list ident) : res (sval * list sval) :=
  let phs := map (fun id => (id, nil)) ns in
  do retv1 <- generate_new_suffix_path_sval (normalize_returned_views phs) phs retv;
  do out_params <- collect_svm_passed_ref_sval (normalize_returned_views phs) svm phs;
  OK (retv1, out_params).


(* When receive return value/input arguments from environment, the
current function should recover the normalized names that are passed
to environment (or generate new names to avoid name conflict with the
current variable names at function entry). These two kinds of
operations can be done using recover_sval_ref_paths. *)
Fixpoint recover_sval_ref_paths (process_views: views -> views) (l: list path) (sv: sval)  : res sval :=
  match sv with
  | sv_ref ph vs =>
      (* There may be view from the callee local paths (e.g., by
      returning a reborrowed path), which should be ignored when
      recovering the concrete views. *)
      do ph1 <- recover_ref_path l ph; 
      OK (sv_ref ph1 (process_views vs))
  | sv_box sv1 =>
      do sv1' <- recover_sval_ref_paths process_views l sv1;
      OK (sv_box sv1')
  | sv_struct id svl =>
      do svl1 <- mmap (fun '(fid, fsv) => 
                        do fsv1 <- recover_sval_ref_paths process_views l fsv;
                        OK (fid, fsv1)) svl;
      OK (sv_struct id svl1)
  | sv_enum id fid fsv =>
      do fsv1 <- recover_sval_ref_paths process_views l fsv;
      OK (sv_enum id fid fsv1)
  | sv_object id obj svl =>
      do svl1 <- mmap (fun '(fid, fsv) => 
                        do fsv1 <- recover_sval_ref_paths process_views l fsv;
                        OK (fid, fsv1)) svl;
      OK (sv_object id obj svl1)
  | _ =>
      OK sv
  end.

(* The id in ph is the index of the views *)
Definition recover_views_from_abstract_path (l: list views) (ph: path) : views :=
  let (id, pj) := ph in
  match nth_error l (Init.Nat.pred (Pos.to_nat id)) with
  | Some vs => (map (fun ph1 => (fst ph1, snd ph1 ++ pj)) vs)
  | None => nil
  end.
  
Definition recover_views (l: list views) (vs: views) : views :=
  flat_map (recover_views_from_abstract_path l) vs.

(* When the caller receives the returned sval and the
reference-passed sval list, it updates their reference paths and
then putback to the svm. The caller should guarantee that the external
svals are normalized into the form same as those passed by the
caller *)
Definition receive_return_sval (svm: sv_map) (l: list (path * views)) (retv: sval) (externs: list sval) : res (sval * sv_map) :=
  let phl := map fst l in
  let vsl := map snd l in
  do retv1 <- recover_sval_ref_paths (recover_views vsl) phl retv;
  do externs1 <- mmap (recover_sval_ref_paths (recover_views vsl) phl) externs;
  let phs_externs := combine phl externs1 in
  do svm1 <- mfold_left (fun acc '(ph, sv) => set_sval_map ph sv acc) phs_externs svm;
  OK (retv1, svm1).

Definition rename_views (l: list path) (phl: list path) : views :=
  flat_map (fun ph1 => match recover_ref_path l ph1 with
                    | OK ph2 => ph2 :: nil
                    | _ => nil
                    end) phl.

Definition receive_incoming_params (fresh_paths: list path) (args: list sval) (inout_params: list (origin * type * sval)) : res (list sval * list (origin * type * sval)) :=
  do args1 <- mmap (recover_sval_ref_paths (rename_views fresh_paths) fresh_paths) args;
  do inout_params1 <- mmap (fun '(r, ty, sv) => 
                          do sv1 <- recover_sval_ref_paths (rename_views fresh_paths) fresh_paths sv;
                          OK (r, ty, sv1)) inout_params;
  OK (args1, inout_params1).
  

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
      do (ph, _) <- get_owner_path_sv_map p e;
      get_owner_sval_map ph e
  | Ecktag p fid =>
      do (ph, _) <- get_owner_path_sv_map p e;
      do v <- get_owner_sval_map ph e;
      match v with
      | sv_enum _ fid1 _ =>
          OK (sv_scalar (Val.of_bool (ident_eq fid fid1)))
      | _ => Error nil
      end
  | Eref _ _ p _ =>
      do (ph, vs) <- get_owner_path_sv_map p e;
      OK (sv_ref ph vs)
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
| Kcall: place -> function -> list (path * (views * origin * type)) -> list ident -> sv_map -> cont -> cont
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
    (inout: list (origin * type * sval))
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

Fixpoint bind_params (m: sv_map) (l: list (ident * type)) (vl: list (option origin * sval)) : res sv_map :=
  match l, vl with
  | nil, nil => OK m
  | (id, ty) :: l1, (r, v) :: vl1 =>
      let m1 := PTree.set id (r, ty, v) m in
      bind_params m1 l1 vl1
  | _, _ => Error nil
  end.

Fixpoint bind_inout_params (m: sv_map) (l: list ident) (vl: list (origin * type * sval)) : res sv_map :=
  match l, vl with
  | nil, nil => OK m
  | id :: l1, (r, ty, v) :: vl1 =>
      let m1 := PTree.set id (Some r, ty, v) m in
      bind_inout_params m1 l1 vl1
  | _, _ => Error nil
  end.


(* We should assume that the types in inout_params contain generic
regions instead of the local regions from the caller. *)
Definition function_entry (f: function) (args: list sval) (inout_params: list (origin * type * sval)) : res (list ident * sv_map) :=
  let names := field_idents (fn_params f ++ fn_vars f) in
  let fresh_var := Pos.succ (find_max_pos names) in
  let fresh_vars := npos (length inout_params) fresh_var in
  (* Substitute the old name in args and in_params with the fresh names *)
  let fresh_paths : list path := map (fun id => (id, nil)) fresh_vars in
  do (args1, inout_params1) <- receive_incoming_params fresh_paths args inout_params;
  (* set the value to the map *)
  do m1 <- bind_params (PTree.empty (option origin * type * sval)) (fn_params f) (map (fun v => (None, v)) args1);
  do m2 <- bind_inout_params m1 fresh_vars inout_params1;
  do m3 <- bind_params m2 (fn_vars f) (repeat (None, sv_bot) (length (fn_vars f)));
  OK (fresh_vars, m3).

Section SMALLSTEP.

Variable ge: genv.

Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e (p: place) m1 m2 m3 ph v v1 ns k vs
    (EVALP: get_owner_path_sv_map p m1 = OK (ph, vs))
    (EVALE: eval_expr m1 e = OK (v, m2))
    (CAST: sem_cast v (typeof e) (typeof_place p) = OK v1)
    (ASS: set_sval_map ph v1 m2 = OK m3),
    step (State f (Sassign p e) k ns m1) E0 (State f Sskip k ns m3)
| step_assign_variant: forall f e (p: place) k m1 m2 m3 v v1 co fid enum_id orgs ph fty ns vs
    (EVALP: get_owner_path_sv_map p m1 = OK (ph, vs))
    (EVALE: eval_expr m1 e = OK (v, m2))
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK fty)
    (CAST: sem_cast v (typeof e) fty = OK v1)
    (ASS: set_sval_map ph (sv_enum enum_id fid v1) m2 = OK m3),
    step (State f (Sassign_variant p enum_id fid e) k ns m1) E0 (State f Sskip k ns m3)
| step_box: forall f e (p: place) k ty m1 m2 m3 v v1 ph ns vs
    (EVALP: get_owner_path_sv_map p m1 = OK (ph, vs))
    (EVALE: eval_expr m1 e = OK (v, m2))
    (TYP: typeof_place p = Tbox ty)
    (CAST: sem_cast v (typeof e) ty = OK v1)
    (ASS: set_sval_map ph (sv_box v1) m2 = OK m3),
    step (State f (Sbox p e) k ns m1) E0 (State f Sskip k ns m3)
(** bigl-step drop semantics: just like a move operation *)
| step_drop: forall m1 m2 k f (p: place) ph ns vs
    (EVALP: get_owner_path_sv_map p m1 = OK (ph, vs))
    (DROP: clear_sval_map ph m1 = OK m2),
    step (State f (Sdrop p) k ns m1) E0 (State f Sskip k ns m2)
| step_storagelive: forall f k ns m id,
    step (State f (Sstoragelive id) k ns m) E0 (State f Sskip k ns m)
| step_storagedead: forall f k ns m id,
    step (State f (Sstoragedead id) k ns m) E0 (State f Sskip k ns m)
| step_call: forall f ty al k tyargs fd cconv tyres p orgs org_rels fun_id m1 m2 args args1 inout_params ns phl
    (CASE: classify_fun ty = fun_case_f tyargs tyres cconv)
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun fd))
    (TYF: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (EVAL: eval_exprlist m1 al tyargs = OK (args, m2))
    (NOT_DROP: function_not_drop_glue fd)
    (* Collect the footprint that is passed via reference *)
    (REF_OUT: generate_call_parameters ge m2 (combine (type_list_of_typelist tyargs) args) = OK (args1, inout_params, phl)),
    step (State f (Scall p (Eglobal fun_id ty) al) k ns m1) E0 (Callstate fun_id args1 inout_params (Kcall p f phl ns m2 k))
| step_internal_function: forall fun_id vargs inout_params k m f ns
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry f vargs inout_params = OK (ns, m)),
    step (Callstate fun_id vargs inout_params k) E0 (State f f.(fn_body) k ns m)

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
         
| step_returnstate: forall (p: place) v v1 m1 m2 m3 f k out_params phl ph ns vs
    (* We need to first putback the ref-passed location and the do the
    assignment because p may locate in those ref-passed locations *)
    (PUTBACK: receive_return_sval m1 (map (fun '(ph, (vs, _, _)) => (ph, vs)) phl) v out_params = OK (v1, m2))
    (EVALP: get_owner_path_sv_map p m1 = OK (ph, vs))
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
    rspec_inout_params: list (origin * type * sval);
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
| initial_state_intro: forall f targs tres tcc vargs orgs org_rels fun_id inout_params
    (FINDF: ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)))
    (TYF: type_of_function f = Tfunction orgs org_rels targs tres tcc)
    (* This function must not be drop glue *)
    (NOTDROP: f.(fn_drop_glue) = None)
    (* how to use it? *)
    (CAST: sval_casted_list vargs targs),
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rspec_q fun_id (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs inout_params)
      (Callstate fun_id vargs inout_params Kstop).


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
