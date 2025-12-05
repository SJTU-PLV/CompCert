Require Import Coqlib.
Require Import Integers.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight Rustlightown RustIR.
Require Import Errors.
Require Import InitDomain InitAnalysis RustIRcfg.
Require Import Rusttyping.
Require Import Wfsimpl.

Import ListNotations.
Local Open Scope error_monad_scope.

(* A strong must_movable definition to simplify the proof *)

Definition removeR {V: Type} (m1 m2: PTree.t V) :=
  exists id v, m2 ! id = Some v
          /\ m1 = PTree.remove id m2.

Lemma well_founded_removeR {V: Type} : well_founded (@removeR V).
Proof.
  eapply well_founded_lt_compat with (f := fun m => PTree_Properties.cardinal m).
  unfold removeR. intros x y (id & v & GET & RM). subst.
  eapply PTree_Properties.cardinal_remove. eauto.
Qed.  

Lemma PTree_removeR {V: Type} : forall id v (m: PTree.t V),
    m ! id = Some v ->
    removeR (PTree.remove id m) m.
Proof.
  intros. red. exists id, v.
  auto.
Qed.

Section REC.

  Variable ce: composite_env.
  Variable rec: forall (ce': composite_env), (removeR ce' ce) -> PathsMap.t -> PathsMap.t -> PathsMap.t -> place -> type -> bool.

  Fixpoint must_movable' (init uninit universe: PathsMap.t) (p: place) (ty: type) : bool :=
    match ty with
    | Tbox ty1 =>
        if must_init init uninit universe p then
          (** we need to consider that p may be is_full so that
          we do not need to check deref p *)
          if is_full universe p then
            true
          else
            must_movable' init uninit universe (Pderef p ty1) ty1
        else false
    | Tstruct orgs id =>
        match get_composite ce id with
        | co_some i co P _ =>
            if must_init init uninit universe p then
              (* This place must be full so that it is sem_wt *)
              if is_full universe p then
                true
              else false
            else
              (** we must check that this struct is a ZST or not. If
              it is ZST, it must be init and full *)
              match co_members co with
              | nil => false
              | _ =>
                  (* The whole struct is not in the universe, so we
              must check its sub-fields. One point is that we should
              also replace the generic regions in fty with the
              function-internal regions. TODO: find some way to make
              it more easy to reason about. *)
                  let fields_types := map (fun '(Member_plain fid fty) => 
                                             let rels := combine co.(co_generic_origins) orgs in
                                             let fty1 := replace_origin_in_type fty rels in
                                             (Pfield p fid fty1, fty1)) co.(co_members) in
                  (** All sub-fields must be movable *)
                  forallb (fun '(fp, ft) => rec (PTree.remove i ce) (PTree_removeR _ _ _ P) init uninit universe fp ft) fields_types
              end
        | co_none =>
            (* type error *) false
        end
    | Tvariant _ id =>
        (* may be not required *)
        match ce ! id with
        | Some _ =>
            must_init init uninit universe p && is_full universe p
        | None => false
        end
    (* scalar type is movable if it is init *)
    | Tunit
    | Tint _ _
    | Tlong _
    | Tfloat _ 
    | Treference _ _ _ => must_init init uninit universe p
    (* other types are unsupported to move *)
    | _ => false
    end.

End REC.
  
(* well_founded_lt_compat *)
(*   NoDup_incl_length *)
(*     get_composite *)
(*     list_norepet implies NoDup *)

(*     PTree.elements_remove *)

Definition must_movable_fix ce := Fix (@well_founded_removeR composite) must_movable' ce.

Definition must_movable ce init uninit universe p := must_movable_fix ce init uninit universe p (typeof_place p).

Section INIT.

Variable ce: composite_env.
Variable init uninit universe: PathsMap.t.
  
Fixpoint move_check_pexpr (pe : pexpr) : bool :=
  match pe with
  | Eplace p _
      (* replace all the p with (owner_place p) which can also
      minimize the changes of the move checking proof *)
      (* let op := owner_place p in *)
      (* if scalar_type ty then *)
        (* dominators are init means that the location if p is valid;
           the children of p is init means that the value of p is
           semantically wel-typed. Note that p may be downcast so we
           just require that the valid owner of p is init *)
      (* dominators_must_init init uninit universe op && must_init init uninit universe (valid_owner op) *)
        (* dominators_must_init init uninit universe p && must_init init uninit universe p *)
      (* else *)
        (* For now only support copy a scalar type value *)
        (* false *)
  | Ecktag p _
  | Eref _ _ p _ => 
      let op := owner_place p in
      dominators_must_init init uninit universe op && must_init init uninit universe (valid_owner op)
  | Eunop _ pe0 _ => move_check_pexpr pe0
  | Ebinop _ pe1 pe2 _ => move_check_pexpr pe1 && move_check_pexpr pe2
  (** Eglobal are unsupported *)        
  | Eglobal _ _ => false
  | _ => true
  end.

Definition move_check_expr' (e : expr) : bool :=
  match e with
  | Emoveplace p _ =>
      (* The type check phase must ensure that p = owner_place p as we
      cannot move from p if p has type [&mut Box<..>] *)
      if place_eq p (valid_owner p) then
        (* p is not downcast ... *)
        dominators_must_init init uninit universe p && must_movable ce init uninit universe p
      else
        (* p is downcast, we just check its valid_owner is init *)
        dominators_must_init init uninit universe p &&
        must_init init uninit universe (valid_owner p) && is_full universe (valid_owner p)
  | Epure pe => move_check_pexpr pe
  end.

(* This function returns the (init, uninit) pair after moving the
place in the expression, which is used to check the lhs of the
statement *)
Definition move_check_expr (e: expr) : option (PathsMap.t * PathsMap.t) :=
  if move_check_expr' e then
    (* Type checking should ensure p = owner_place p *)
    let p := moved_place e in
    match p with
    | Some p =>
        Some (remove_place p init, add_place universe p uninit)
    | None => Some (init, uninit)
    end
  else None.
         
Definition move_check_assign (p : place) :=
  dominators_must_init init uninit universe (owner_place p).

End INIT.

Fixpoint move_check_exprlist ce init uninit universe (l : list expr) : option (PathsMap.t * PathsMap.t) :=
  match l with
  | nil => Some (init, uninit)
  | e :: l' =>
      match move_check_expr ce init uninit universe e with
      | Some (init', uninit') =>
          move_check_exprlist ce init' uninit' universe l'
      | None =>
          None
      end
  end.


Definition move_check_stmt ce (an : IM.t * IM.t * PathsMap.t) (stmt : statement) : Errors.res statement :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>      
      match stmt with
      | Sassign p0 e
      | Sassign_variant p0 _ _ e
      | Sbox p0 e =>
          match move_check_expr ce mayinit mayuninit universe e with
          | Some (mayinit', mayuninit') =>
              (** We should check p0 after moving the place in e instead
                  of the analysis before moving the place of e ! *)
              if move_check_assign mayinit' mayuninit' universe p0
              then OK stmt
              else Error (msg "move_check_assign error")
          | None => Error (msg "move_check_expr error")
          end
      | Scall p0 _ el =>
          match move_check_exprlist ce mayinit mayuninit universe el with
          | Some (mayinit', mayuninit') =>
              if move_check_assign mayinit' mayuninit' universe p0
              then OK stmt
              else Error (msg "move_check_assign error in Scall")
          | None => Error (msg "move_check_exprlist error in Scall")
          end
      | Sreturn p =>
          (* Is it ok to assume that return p is moving p? *)
          let e := Emoveplace p (typeof_place p) in
          if move_check_expr' ce mayinit mayuninit universe e then
            OK stmt
          else
            Error (msg "move_check_expr error in Sreturn")
      | _ => OK stmt
      end
  (* impossible *)
  | _, _ => OK stmt
  end.

Definition check_cond_expr (an : IM.t * IM.t * PathsMap.t) (e: expr) : Errors.res unit :=
  let '(mayInit, mayUninit, universe) := an in
  match mayInit, mayUninit with
  | IM.State mayinit, IM.State mayuninit =>
      match e with
      | Emoveplace _ _ =>
          Error (msg "cannot move place in conditional expression")
      | Epure pe =>
          if move_check_pexpr mayinit mayuninit universe pe then
            OK tt
          else
            Error (msg "move_check_pexpr error in conditional expression")
      end
  | _, _ => OK tt
  end.

(** Translation validation of wf_own_env *)

Definition check_universe_shallow (universe: Paths.t) : bool :=
  Paths.for_all (fun p1 => Paths.for_all (fun p2 => negb (is_shallow_prefix p1 p2))
                          (Paths.filter (fun p2 => is_prefix_strict p1 p2) universe))
                universe.

Definition check_universe_no_downcast (universe: Paths.t) : bool :=
  Paths.for_all (fun p => forallb (fun ph => match ph with
                                        | ph_downcast _ _ => false
                                        | _ => true
                                        end) (snd (path_of_place p))) universe. 

Definition check_universe_own_type (universe: Paths.t) : bool :=
  Paths.for_all (fun p => match typeof_place p with
                       | Tbox _ => true
                       | _ => false
                       end) (Paths.filter (fun p => negb (is_full_internal universe p)) universe).

Definition check_universe_wt_place ce te (universe: Paths.t) : bool :=
  Paths.for_all (fun p => match type_check_place ce te p with
                       | OK _ => true
                       | _ => false
                       end) universe.

Definition check_universe_dominator_complete (universe: Paths.t) : bool :=
  Paths.for_all (fun p => forallb (fun p1 => Paths.mem p1 universe) (place_dominators p)) universe.


Definition check_universe_wf' ce te (universe: PathsMap.t) : bool :=
  (** Hard to debug! We can just comment one of the checking to see if
  it fails *)
  PTree_Properties.for_all universe (fun _ w => check_universe_dominator_complete w
                                             && check_universe_shallow w
                                             && check_universe_no_downcast w
                                             && check_universe_own_type w
                                             && check_universe_wt_place ce te w).

Definition check_universe_wf (te: typenv) (ce: composite_env) (universe: PathsMap.t) : Errors.res unit :=
  if check_universe_wf' ce te universe then
    OK tt
  else
    Error (msg "check_universe_wf fail")
.


(** Checking of non-cyclic reference in Tstruct *)

Lemma struct_or_variant_eq: forall (s1 s2: struct_or_variant),
    {s1 = s2} + {s1 <> s2}.
Proof. intros. decide equality. Defined.

Section REC.

  Variable ce: composite_env.
  Variable rec: forall (ce': composite_env), (removeR ce' ce) -> type -> bool.

  Definition check_cyclic_struct' (ty: type) : bool :=
    match ty with
    | Tstruct _ i =>
        match get_composite ce i with
        | co_some i co P _ =>
            forallb (fun '(Member_plain _ fty) => rec (PTree.remove i ce) (PTree_removeR _ _ _ P)fty) (co_members co) && (struct_or_variant_eq (co_sv co) Struct)
        | co_none => false
        end
    | _ => true
    end.

End REC.

Definition check_cyclic_struct ce (ty: type) : bool :=
  Fix (@well_founded_removeR composite) check_cyclic_struct' ce ty.

Definition check_cyclic_struct_res ce (tyl: list type) : Errors.res unit :=
  if forallb (check_cyclic_struct ce) tyl then
    OK tt
  else Error (msg "There is a cyclic reference of struct in the type of paramerters or variables").


(* Check that the types of locals are valid type (i.e., not reference,
array and function) *)
Definition check_valid_types (tyl: list type) : Errors.res unit :=
  if forallb valid_type tyl then
    OK tt
  else Error (msg "There is non-valid type in paramerters or variables").


Definition var_types (l: list (ident * type)) :=
  map snd l.

Definition collect_move_check_result ce f cfg analysis_res :=
  do _ <- transl_on_cfg get_init_info analysis_res (move_check_stmt ce) check_cond_expr f.(fn_body) cfg;
  OK tt.


(** Check the consistency of composite environment *)

Definition name_members (membs: members) : list ident :=
  map name_member membs.

Definition check_composite (id: ident) (co: composite) : bool :=
  Z.leb (co_sizeof co) Integers.Ptrofs.max_unsigned
  && Z.leb (list_length_z (co_members co)) Int.max_unsigned
  && list_norepet_dec ident_eq (name_members (co_members co)).

Definition check_composite_env (ce: composite_env) : Errors.res unit :=
  if PTree_Properties.for_all ce check_composite then
    OK tt
  else
    Error (msg "fail in checking composite environment").


(** The following code is used for printing the result of move
checking and type checking, which is not used in the top-level
soundness proof. *)

Definition move_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** 1. Init Analaysis *)
  do analysis_res <- analyze ce f cfg entry;
  (** 2. Naive syntactic type checking. The reason we put syntactic type *)
(*   checking here instead of using a separated type check function (like *)
(*   Ctyping) is that sound_state and wt_state rely on each other due to *)
(*   well typedness property in wf_own_env. *)
  let te := (bind_vars (bind_vars (PTree.empty _) f.(fn_params)) f.(fn_vars)) in
  let (_, universe) := analysis_res in
  do _ <- check_universe_wf te ce universe;
  do _ <- check_cyclic_struct_res ce (var_types (f.(fn_params) ++ f.(fn_vars)));
  do _ <- check_valid_types (var_types (f.(fn_params) ++ f.(fn_vars)));
  (* type checking *)
  do _ <- type_check_stmt ce te (fn_body f);
  (** 3. Run move checking ! *)
  do _ <- transl_on_cfg get_init_info analysis_res (move_check_stmt ce) check_cond_expr f.(fn_body) cfg;
  OK tt.

Definition move_check_fundef (ce : composite_env) (id : ident) (fd : fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match move_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error ([MSG "In function "; CTX id; MSG " , in pc "] ++ msg)
      end
  | External orgs rels ef targs tres cconv =>
      (* We do not support builtin external functions for now *)
      match ef with
      | EF_external _ _
      | EF_malloc
      | EF_free =>
          OK (External orgs rels ef targs tres cconv)
      | _ => Error ([MSG "In function "; CTX id; MSG " , unsupported builtin external function"])
      end
  end.

Definition transl_globvar := fun (_ : ident) (ty : type) => OK ty.

Definition move_check_program (p : program) :=
  (* 1. check composite environment *)
  do _ <- check_composite_env (prog_comp_env p);
  (* 2. move checking *)
  do p1 <- (transform_partial_program2 (move_check_fundef (prog_comp_env p)) transl_globvar p);
   OK
     {|
     prog_defs := AST.prog_defs p1;
     prog_public := AST.prog_public p1;
     prog_main := AST.prog_main p1;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.
 
