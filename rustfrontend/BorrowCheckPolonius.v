Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR RustIRcfg.
Require Import Errors.
Require Import ReplaceOrigins.
Require Import RegionLiveness BorrowCheckDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on Polonius (dataflow analysis) *)

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at pc "; POS pc; MSG " : "].

Section COMP_ENV.

Variable (ce: composite_env).

(** Transition *)

(* Support prefixes and support origins *)

Definition support_origins (p: place) : list origin :=
  let support_prefixes := p :: support_parent_places p in
  fold_right (fun elt acc => match elt with
                          | (Pderef p' ty) =>
                              match typeof_place p' with
                              | Treference org _ _ => org :: acc
                              | _ => acc
                              end
                          | _ => acc
                          end) nil support_prefixes.

Definition aggregate_origin_states (e: LOrgEnv.t) (orgs: list origin) : LOrgSt.t :=
  fold_left (fun acc elt => LOrgSt.lub acc (LOrgEnv.get elt e)) orgs LOrgSt.bot.

Definition borrowed_place_error (action site: string) (p: place) : errmsg :=
  [MSG action; MSG " place "]
  ++ errmsg_of_place p
  ++ [MSG " because it is borrowed; this error occurs in ";
      MSG site].

Definition map_loan_set (f: loan -> loan) (ls: LoanSet.t) : LoanSet.t :=
  LoanSet.fold (fun ln acc => LoanSet.add (f ln) acc) ls LoanSet.empty.

Definition loan_env_add (le: LOrgEnv.t) (r: origin) (ls: LOrgSt.t) : LOrgEnv.t :=
  LOrgEnv.set r (LOrgSt.lub ls (LOrgEnv.get r le)) le.

(* Transition of pure expression *)

Fixpoint transfer_pure_expr (e: LOrgEnv.t) (pe: pexpr) : LOrgEnv.t :=
  match pe with
  | Eref org mut p ty =>
      (* handle reborrow: add all the loans in the support *)
      (* prefix to org *)
      let support_orgs := support_origins p in
      (* aggregate the loans in the support origins *)
      let org_st := aggregate_origin_states e support_orgs in
      let s' := LOrgSt.lub org_st (Live (LoanSet.singleton (Lintern mut p))) in
      (** Simplification: we choose not to overwrite the e[org] to
      simplfy the proof because we do not need to prove that org does
      not appear in e. This simplification is OK because (1) it does
      not affect the soundness proof and (2) we can ensure that org
      must not appear in e using the ReplaceOrigins.v pass. *)
      loan_env_add e org s'
  | Eunop _ pe _ =>
      transfer_pure_expr e pe
  | Ebinop _ pe1 pe2 _ =>
      let e' := transfer_pure_expr e pe1 in
      transfer_pure_expr e' pe2
  (* Other constants *)
  | _ => e
  end.

Fixpoint check_pure_expr (e: LOrgEnv.t) (pe: pexpr) : res unit :=
  match pe with
 | Eplace p ty =>
      if illegal_access e p Adeep ARead then
        Error (borrowed_place_error "cannot access" "Eplace of transfer_pure_expr" p)
      else
        OK tt
  | Eref org mut p ty =>
      let ak := mut_to_access_kind mut in
      if illegal_access e p Adeep ak then
        Error (borrowed_place_error "cannot access" "Eref of transfer_pure_expr" p)
      else
        OK tt
  | Ecktag p id =>
      if illegal_access e p Ashallow ARead then
        Error (borrowed_place_error "cannot access" "Ecktag of transfer_pure_expr" p)
      else
        OK tt
  | Eunop _ pe _ =>
      check_pure_expr e pe
  | Ebinop _ pe1 pe2 _ =>
      do _ <- check_pure_expr e pe1;
      let e' := transfer_pure_expr e pe1 in
      check_pure_expr e' pe2
  (* Other constants *)
  | _ => OK tt 
  end.

(* transfer expression *)

Definition transfer_expr (oe: LOrgEnv.t) (e: expr) : LOrgEnv.t :=
  match e with
  | Emoveplace p ty =>
      oe
  | Epure pe =>
      transfer_pure_expr oe pe
  end.

Definition check_expr (oe: LOrgEnv.t) (e: expr) : res unit :=
  match e with
  | Emoveplace p ty =>
      if illegal_access oe p Adeep AWrite then
        Error (borrowed_place_error "cannot access" "Emoveplace of transfer_expr" p)
      else 
        OK tt
  | Epure pe =>
      check_pure_expr oe pe
  end.


Fixpoint transfer_exprlist (oe: LOrgEnv.t) (l: list expr) : LOrgEnv.t :=
  match l with
  | [] => oe
  | e :: l' =>
      let oe' := transfer_expr oe e in
      transfer_exprlist oe' l'
  end.

Fixpoint check_exprlist (oe: LOrgEnv.t) (l: list expr) : res unit :=
  match l with
  | [] => OK tt
  | e :: l' =>
      do _ <- check_expr oe e;
      let oe' := transfer_expr oe e in
      check_exprlist oe' l'
  end.


(* Flowing loans from source type to destination type *)

Definition flow_loans_by_regions (e: LOrgEnv.t) (org_src org_tgt: origin) (fk: flow_kind) : LOrgEnv.t :=
  match fk with
  | ByVal =>
      let st := LOrgSt.lub (LOrgEnv.get org_src e) (LOrgEnv.get org_tgt e) in
      LOrgEnv.set org_tgt st e
  | ByRef =>
      LOrgEnv.union org_src org_tgt e
  end.

(* Subtyping rules of rust borrow checker *)
Fixpoint flow_loans (e: LOrgEnv.t) (s d: type) (fk: flow_kind) : LOrgEnv.t :=
  match s,d with
  | Treference org1 mut1 ty1, Treference org2 mut2 ty2 =>
      let e1 := flow_loans_by_regions e org1 org2 fk in
      (* Rust does not support "types differ in mutability", so we can
         assume that the type checking has check that mut1 = mut2 *)
      let fk' := match mut1 with
                | Mutable => ByRef
                | Immutable => ByVal
                 end in
      flow_loans e1 ty1 ty2 (meet_flow_kinds fk fk')
  | Tbox ty1, Tbox ty2 =>
      (* Box is covariant over ty1/ty2*)
      flow_loans e ty1 ty2 (meet_flow_kinds fk ByVal)
  | Tstruct orgs1 id1, Tstruct orgs2 id2 
  | Tvariant orgs1 id1 , Tvariant orgs2 id2 =>
      (* type checking must ensure that id1 == id2 and len(orgs1) ==
      len(orgs2). We use id1 below *)
      (** TODO: for now we simplify the subtyping by assuming that the
      user defined type is **invariant** over each of the origin. To
      deal with this restriction, we need to write a function to query
      that what subtyping rule should be applied for a give origin *)
      let orgs := combine orgs1 orgs2 in
      fold_left (fun acc '(o1, o2) => LOrgEnv.union o1 o2 acc) orgs e
  (* scalar type *)
  | _, _ => e
  end.
          
Fixpoint flow_loans_list (e: LOrgEnv.t) (ls ld: list type) (k: flow_kind) : LOrgEnv.t :=
  match ls, ld with
  | s :: ls', d :: ld' =>
      flow_loans_list (flow_loans e s d k) ls' ld' k
  | _, _ =>
      e
  end.

(* Shallow write a place *)

Definition check_shallow_write_place (e: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access e p Ashallow AWrite then
    Error (borrowed_place_error "cannot write to" "shallow_write_place" p)
  else
    OK tt.

(* Auxilary functions for transition of statements *)

Definition kill_place_related_loans (p: place) (st: LOrgSt.t) : LOrgSt.t :=
  match st with
  | Live ls =>
      Live (LoanSet.filter (fun elt => match elt with
                              (* Note that we also clear p, so
                              clear_dead_loans should be perfomed
                              after check_shallow_write_place *)
                              | Lintern _ p' => negb (is_prefix p p')
                              | _ => true
                              end) ls)
  | Dead => Dead
  end.

(* When some loan [p] is overwritten, it should be cleared *)
Definition kill_loans (e: LOrgEnv.t) (p: place) : LOrgEnv.t :=
  LOrgEnv.map1 (kill_place_related_loans p) e.

(* Borrow check an assign statement *)

(* Definition transfer_assign_base (oe: LOrgEnv.t) (e: expr) : LOrgEnv.t := *)
(*   transfer_expr oe e. *)

Definition transfer_assignment (oe: LOrgEnv.t) (p: place) (e: expr) : LOrgEnv.t :=
  (* simple type checking *)
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  let oe1 := transfer_expr oe e in
  (* After checking the evaluation of e *)
  let oe2 := kill_loans oe1 p in
  flow_loans oe2 ty_src ty_dest ByVal.

(* The checking function is used for all kinds of assignment *)
Definition check_assignment (oe: LOrgEnv.t) (p: place) (e: expr) : res unit :=
  do _ <- check_expr oe e;
  let oe1 := transfer_expr oe e in
  check_shallow_write_place oe1 p.


Definition transfer_assign_variant (oe: LOrgEnv.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : LOrgEnv.t :=
  match typeof_place p with
  | Tvariant orgs_dest vid =>
      (* enum_id must be equal to vid, and we use vid below *)
      match ce!vid with
      | Some co =>
          match field_type fid (co_members co) with
          | OK ty_i =>
              let ty_src := typeof e in
              let orgs_src := co.(co_generic_origins) in
              let ty_dest := replace_origin_in_type ty_i (combine orgs_src orgs_dest) in
              let oe1 := transfer_expr oe e in
              (* After checking the evaluation of e *)
              let oe2 := kill_loans oe1 p in
              flow_loans oe2 ty_src ty_dest ByVal
          (* It would cause error before borrow checking *)
          | _ => oe
          end
      (* It would cause error before borrow checking *)            
      | _ => oe
      end
  (* It would cause error before borrow checking *)
  | _ => oe
  end.

Definition transfer_Sbox (oe: LOrgEnv.t) (p: place) (e: expr) : LOrgEnv.t :=
  (* [typeof_place p] must be Tbox, which should be checked at type
  checking phase *)
  let ty_dest := typeof_place p in
  let ty_src := Tbox (typeof e) in
  let oe1 := transfer_expr oe e in
  (* After checking the evaluation of e *)
  let oe2 := kill_loans oe1 p in
  flow_loans oe2 ty_src ty_dest ByVal.

  
(* bind the origins in two type *)
Fixpoint bind_type_origins (ty1 ty2: type) (fk: flow_kind) : list (origin * origin * flow_kind) :=
  match ty1, ty2 with
  | Treference org1 _ ty1, Treference org2 _ ty2 =>
      (org1, org2, fk) :: bind_type_origins ty1 ty2 ByRef
  | Tbox ty1, Tbox ty2 =>
      bind_type_origins ty1 ty2 ByRef
  | Tstruct orgs1 id1, Tstruct orgs2 id2
  | Tvariant orgs1 id1, Tvariant orgs2 id2 =>
      (* TODO: support covariant *)
      let len := length orgs1 in
      (combine (combine orgs1 orgs2) (repeat ByRef len))
  | _, _ => []
  end.

Fixpoint bind_type_origins_list (tyl: list (type * type)) :=
  match tyl with
  | nil => nil
  | (ty1, ty2) :: tyl =>
      bind_type_origins ty1 ty2 ByVal ++ (bind_type_origins_list tyl)
  end.

Definition flow_loans_origin_to_origin (se te: LOrgEnv.t) (src tgt: origin) : LOrgEnv.t :=
  LOrgEnv.set tgt (LOrgSt.lub (LOrgEnv.get src se) (LOrgEnv.get tgt te)) te.


Fixpoint flow_loans_bind (se: LOrgEnv.t) (te: LOrgEnv.t) (rels: list origin_rel) (l: list (origin * origin * flow_kind)) : LOrgEnv.t * list origin_rel :=
  match l with
  | nil => (te, rels)
  | (src, tgt, fk) :: l' =>
      let te' := flow_loans_origin_to_origin se te src tgt in
      let rels' := 
        match fk with
        | ByRef =>
            (src, tgt) :: rels
        | ByVal =>
            rels
        end in
      flow_loans_bind se te' rels' l'
  end.

(* flow the loans from parameter to callee arguments and return the
pair of origins for which we should generate invariant constrain *)
Definition bind_param_origins (e: LOrgEnv.t) (fe: LOrgEnv.t) (ptyl ftyl: list type) : (LOrgEnv.t * list origin_rel) :=
  let bind_pairs := bind_type_origins_list (combine ptyl ftyl) in
  flow_loans_bind e fe nil bind_pairs.
  (* else *)
  (*   Error (error_msg pc ++ [MSG "mismatch between the lengths of types (bind_param_origins)"]). *)

(** The parser sorts the signature relations by SCC-topological order on the
left-hand origin of each relation. *)
Fixpoint origin_reaches_fuel (fuel: nat) (rels: list origin_rel) (src tgt: origin) : bool :=
  if Pos.eqb src tgt then
    true
  else
    match fuel with
    | O => false
    | S fuel' =>
        existsb
          (fun '(org1, org2) =>
             if Pos.eqb src org1 then
               origin_reaches_fuel fuel' rels org2 tgt
             else
               false)
          rels
    end.

Definition origin_reaches (rels: list origin_rel) (src tgt: origin) : bool :=
  origin_reaches_fuel (length rels) rels src tgt.

Definition origin_strictly_precedes (rels: list origin_rel) (src tgt: origin) : bool :=
  origin_reaches rels src tgt && negb (origin_reaches rels tgt src).

Fixpoint check_topologically_sorted_origin_relations_aux
    (rels seen pending: list origin_rel) : bool :=
  match pending with
  | nil => true
  | (src, tgt) :: pending' =>
      forallb
        (fun '(prev_src, _) =>
           negb (origin_strictly_precedes rels src prev_src))
        seen
      && check_topologically_sorted_origin_relations_aux rels ((src, tgt) :: seen) pending'
  end.

Definition check_topologically_sorted_origin_relations (rels: list origin_rel) : bool :=
  check_topologically_sorted_origin_relations_aux rels nil rels.

(** Assumption: the relations of origin given by the function
signature has been sorted topologically, to ensure that we just need
to flow the origins in one round instead of flowing it until reaching
a fixed point. [check_topologically_sorted_origin_relations] checks this
ordering convention, but it is not used for now. *)
Definition after_call (fe: LOrgEnv.t) (rels: list origin_rel) : LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               (* it may be less efficient *)
               flow_loans_origin_to_origin acc acc src tgt) rels fe.


Definition flow_loans_origin_to_origin_with_alias (fe e: LOrgEnv.t) (forg org: origin) : LOrgEnv.t :=
  LOrgEnv.set org (LOrgSt.lub (LOrgEnv.get forg fe) (LOrgEnv.get org e)) e.

(* Flow back the loans based on the invariant relation established by
the bind_params_origins *)
Fixpoint flow_alias_after_call (rels: list origin_rel) (fe e: LOrgEnv.t) : LOrgEnv.t :=
  match rels with
  | nil => e
  | (org, forg) :: rels' =>
      flow_alias_after_call rels' fe (flow_loans_origin_to_origin_with_alias fe e forg org)
  end.

Definition flow_return_after_call (fe e: LOrgEnv.t) (frety tgt_ty: type) : LOrgEnv.t :=
  let l := bind_type_origins frety tgt_ty ByVal in
  fst (flow_loans_bind fe e nil l).
  (* (* we do not care the alias relation *) *)
  (* do (te', _) <- fold_left (flow_loans_bind_acc pc se) l (OK (te, nil)); *)
  (* OK te'. *)

(** TODO: to make it simpler  *)
Definition transfer_function_call (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : LOrgEnv.t :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      (* transfer the arguments *)
      let oe2 := transfer_exprlist oe1 args in      
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          oe2
      | None =>
          (* flow the loans from arguments to the parameter types of the function *)
          let oe3 := flow_loans_list oe2 args_tyl sig_tyl ByVal in
          (* apply the effect of the function call *)
          let oe4 := after_call oe3 org_rels in
          (* assign the return value to p *)
          flow_loans oe4 rty tgt_rety ByVal
          (** The following code is the old-version implementation of
          function call *)
      end
  | _ => oe1
(* Error (error_msg pc ++ [MSG "it is not a function type in check_function_call"])       *)
  end.

Definition check_function_call (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : res unit :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      do _ <- check_exprlist oe1 args;
      (* transfer the arguments *)
      let oe2 := transfer_exprlist oe1 args in      
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          OK tt
      | None =>
          (* flow the loans from arguments to the parameter types of the function *)
          let oe3 := flow_loans_list oe2 args_tyl sig_tyl ByVal in
          (* apply the effect of the function call *)
          let oe4 := after_call oe3 org_rels in
          (* check the assignment of assigning the return value to p *)
          check_shallow_write_place oe4 p
      end
  | _ => OK tt
  end.

End COMP_ENV.

Definition transfer_storagedead (f: function) (oe1: LOrgEnv.t) (id: ident) : LOrgEnv.t :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      (* After check_shallow_write_place *)
      (kill_loans oe1 (Plocal id ty))
  | None =>
      (* report errors in the type checking *)
      oe1
  end.

Definition check_storagedead (f: function) (oe1: LOrgEnv.t) (id: ident) : res unit :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      check_shallow_write_place oe1 (Plocal id ty)
  | _ =>
      OK tt
  end.

(** TODO: we need to consider p is initialized or not *)
Definition check_drop (oe1: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access oe1 p Adeep AWrite then
    Error (borrowed_place_error "cannot drop" "check_drop" p)
  else OK tt.

(** All the relations between the generic origins after the function
call must be declared in the function sigature *)

Definition live_origin (st: origin_state) : bool :=
  match st with
  | Live _ => true
  | Dead => false
  end.

Definition absence_of_internal_loans (st: LOrgSt.t) : bool :=
  match st with
  | Live ls =>
      LoanSet.for_all (fun ln => match ln with
                              | Lintern _ _ => false
                              | Lextern _ => true
                              end) ls
  (* Impossible *)
  | _ => true
  end.

(* Check if there is a generic region containing some internal loans
at the function return *)
Definition check_dangling (f: function) (e: LOrgEnv.t) : bool :=
  forallb (fun org => absence_of_internal_loans (LOrgEnv.get org e)) f.(fn_generic_origins).

Definition check_generic_origins_relations (f: function) (e: LOrgEnv.t) : bool :=
  (* This property can be guaranteed by the liveness analysis: All the
  generic origin must not be dead otherwise we are returing a dangling
  pointer *)
  (* forallb (fun org => live_origin (LOrgEnv.get org e)) f.(fn_generic_origins) && *)
  forallb (fun org1 =>
             forallb (fun org2 =>
                        if Pos.eqb org1 org2 then true
                        else match LOrgEnv.get org1 e, LOrgEnv.get org2 e with
                             | Live ls1, Live ls2 =>
                                 if LoanSet.subset ls1 ls2 then
                                   in_dec origin_rel_eq_dec (org1, org2) f.(fn_origins_relation)
                                 else if LoanSet.subset ls2 ls1 then
                                        in_dec origin_rel_eq_dec (org2, org1) f.(fn_origins_relation)
                                      else true
                             (* generic origins must be live which
                             should be already checked *)
                             | _, _ => false
                             end) f.(fn_generic_origins)) f.(fn_generic_origins).
  

(* We use it to ensure that we cannot return the address of stack blocks of the parameters *)
Fixpoint check_storagedead_list (l: list (ident * type)) (e: LOrgEnv.t) : res unit :=
  match l with
  | nil => OK tt
  | (id, ty) :: l' =>
      do _ <- check_shallow_write_place e (Plocal id ty);
      check_storagedead_list l' e
  end.
 
(* We use it to clear the reborrow of parameters at the function return *)
Fixpoint kill_loans_list (e: LOrgEnv.t) (l: list (ident * type)) : LOrgEnv.t :=
  match l with
  | nil => e
  | (id, ty) :: l' =>
      kill_loans_list (kill_loans e (Plocal id ty)) l'
  end.

(* We need to transfer the loans from the return variable to the
return type of this function *)
Definition transfer_return (f: function) (oe1: LOrgEnv.t) (p: place) : LOrgEnv.t :=
  (** The following code is copied from check_return *)
  let oe2 := flow_loans oe1 (typeof_place p) f.(fn_return) ByVal in
  (* To accept more programs, we clear all the regions except the
    generic ones before checking dangling references. *)
  let generic_regions := regset_fun f in
  let oe3 := LOrgEnv.apply_liveness generic_regions oe2 in
  (* kill the loans related to parameter *)
  let oe4 := kill_loans_list oe3 f.(fn_params) in
  oe4.
 

Definition check_return (f: function) (oe1: LOrgEnv.t) (p: place) : res unit :=
  if illegal_access oe1 p  Adeep ARead then
    (* Question: this error should be impossible (or the error has
    been found before this return statement)? Because there is no live
    regions (except generic regions) after the return statement. *)
    Error (borrowed_place_error "cannot return" "transfer_return" p)
  else
    let oe2 := flow_loans oe1 (typeof_place p) f.(fn_return) ByVal in
    (* To accept more programs, we clear all the regions except the
    generic ones before checking dangling references. *)
    let generic_regions := regset_fun f in
    let oe3 := LOrgEnv.apply_liveness generic_regions oe2 in
    (* check if there is reference to variables/parameters that are
    stored in the generic regions. Since we cannot ensure that we
    generate stroragedead for all the variables before function return
    (e.g., we may return inside a scope of a local variables), we
    should also check variables. *)
    do _ <- check_storagedead_list (f.(fn_vars) ++ f.(fn_params)) oe3;
    (* kill the loans related to variables/parameter *)
    let oe4 := kill_loans_list oe3 (f.(fn_vars) ++ f.(fn_params)) in
    if check_dangling f oe4 then
      if check_generic_origins_relations f oe4 then
        OK tt
      else
        Error [MSG "some relations in function return are not declared in the function signature"]
    else
      Error [MSG "Dangling pointer! There should not be internal loans in the generic regions at the function return"].

(* Transition of statements *)
        
Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (live: PMap.t RegionSet.t) (generic_regions: RegionSet.t) (pc: node) (before: LoansEnv.t) : LoansEnv.t :=
  match before with
  | LoansEnv.Bot => before
  | LoansEnv.State oe =>
      (* apply liveness result before transfer *)
      let live_after := PMap.get pc live in
      let live_before := RegionLiveness.transfer f cfg generic_regions pc live_after in
      let oe := LOrgEnv.apply_liveness live_before oe in
      let finish_transfer oe := (LoansEnv.State (LOrgEnv.apply_liveness live_after oe)) in
      match cfg ! pc with
      | None => LoansEnv.Bot
      | Some (Inop _) => before
      | Some (Icond e _ _) => LoansEnv.State (transfer_expr oe e)
      | Some Iend => before
      | Some (Isel sel next) =>
          match select_stmt f.(fn_body) sel with
          | None => LoansEnv.Bot
          | Some s =>
              match s with
              | Sassign p e => 
                  finish_transfer (transfer_assignment oe p e)
              | Sassign_variant p enum_id fid e =>
                  finish_transfer (transfer_assign_variant ce oe p enum_id fid e)
              | Sbox p e =>
                  finish_transfer (transfer_Sbox oe p e)
              | Scall p e l =>
                  finish_transfer (transfer_function_call oe p e l)
              | Sstoragedead id =>
                  finish_transfer (transfer_storagedead f oe id)
              (** Because our drop cannot access the region (i.e., the
              reference), so there is no need to make the region live
              until this drop statement. We do not need the technique
              of drop check for now. *)
              | Sreturn p =>
                  (* This transfer may be useless as we do not look up
                  the abstract state after the return, but we want to
                  use it to see what is the result of transfer at the
                  function return *)
                  LoansEnv.State (transfer_return f oe p)
              | _ => before
              end 
          end
      end
  end.

Module LoansFlow := Dataflow_Solver(LoansEnv)(NodeSetForward).


(** Initialization *)

(* The rule I-Fun. Maybe we should just initialize the generic origins
that appear in the arguments? *)
Definition init_function (f: function) : LOrgEnv.t :=
  (* initialize the loans of generic regions *)
  let oe1 := fold_left (fun acc elt =>
                          let os := Live (LoanSet.singleton (Lextern elt)) in
                          LOrgEnv.set elt os acc) f.(fn_generic_origins) LOrgEnv.bot in
  (* flow the loans from the function arguments to the parameters *)
  flow_loans_list oe1 f.(fn_param_types) (map snd f.(fn_params)) ByVal.
  
(** Run Liveness analysis and Loans-flow analysis *)

Definition loans_flow_analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t RegionSet.t * (PMap.t LoansEnv.t)) :=
  (* Liveness analysis for regions *)
  let generic_regions := regset_fun f in
  match RegionLiveness.analyze f cfg with
  | Some live =>
      let init_oe := init_function f in
      match LoansFlow.fixpoint cfg successors_instr (transfer ce f cfg live generic_regions) entry (LoansEnv.State init_oe) with
      (* For now we return liveness result for debug purpose *)
      | Some m => OK (live, m)
      | None =>
          Error [MSG "The loans-flow analysis fails with unknown reason"]
      end
  | None => 
      Error [MSG "The loans-flow analysis fails due to the failure of liveness analysis"]
  end.

(** Checking functions that are used in the transl_on_cfg *)

Definition borrow_check_stmt_aux (f: function) (le: LoansEnv.t) (stmt: statement) : res unit :=
  match le with
  | LoansEnv.State oe =>
      match stmt with
      | Sassign p e
      | Sassign_variant p _ _ e
      | Sbox p e =>
          check_assignment oe p e
      | Scall p e l =>
          check_function_call oe p e l
      | Sstoragedead id =>
          check_storagedead f oe id
      | Sdrop p =>
          check_drop oe p
      | Sreturn p =>
          check_return f oe p
      | _ =>
          OK tt
      end
  (* Impossible execution, but we should not report error *)
  | _ =>
      (* Error [MSG "Impossible: it is unreachable point"] *)
      OK tt
  end.
  
Definition borrow_check_stmt (f: function) (le: LoansEnv.t) (stmt: statement) : res statement :=
  do _ <- borrow_check_stmt_aux f le stmt;
  OK stmt.

Definition borrow_check_cond_expr (le: LoansEnv.t) (e: expr) : res unit :=
  match le with
  | LoansEnv.State oe =>
      check_expr oe e
  (* Impossible *)
  | _ =>
      (* Error [MSG "Impossible: it is unreachable point"] *)
      OK tt
  end.

(** FIXME: Get the loans environments before the evaluation of pc. We
should apply the liveness again here because Kildall only keep the
most approximated (consider lub operation) result in the loans
environments. *)
Definition get_borck_result generic_regions f cfg (live_loan_env: (PMap.t RegionSet.t * (PMap.t LoansEnv.t))) (pc: node) : LoansEnv.t :=
  let (live, loan_env) := live_loan_env in
  match loan_env !! pc with
  | LoansEnv.Bot => LoansEnv.Bot
  | LoansEnv.State oe =>
      (* apply liveness result before transfer *)
      let live_after := PMap.get pc live in
      let live_before := RegionLiveness.transfer f cfg generic_regions pc live_after in
      LoansEnv.State (LOrgEnv.apply_liveness live_before oe)
  end.

(* After calling borrow_check, we should find if there is any borrow
check error *)
Definition collect_borrow_check_result generic_region (f: function) (cfg: rustcfg) (loans_flow_res: (PMap.t RegionSet.t * (PMap.t LoansEnv.t))) : res unit :=
  do _ <- transl_on_cfg (get_borck_result generic_region f cfg) (loans_flow_res) (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg;
  OK tt.


(** The following code is used for printing the result of borrow
checking, which is not used in the top-level soundness proof. *)

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let generic_regions := regset_fun f in
  (** 1. Loans-flow analysis *)
  do loans_flow_res <- loans_flow_analyze ce f cfg entry;
  (** 2. Collect result of the borrow checking ! *)
  collect_borrow_check_result generic_regions f cfg loans_flow_res.

Definition transf_fundef (ce: composite_env) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match borrow_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error msg
      end
  | External orgs rels ef targs tres cconv => Errors.OK (External orgs rels ef targs tres cconv)
  end.

Definition transl_globvar (id: ident) (ty: type) := OK ty.

(* borrow check the whole module *)

Definition borrow_check_program (p: program) : res unit :=
  do _ <- transform_partial_program2 (transf_fundef p.(prog_comp_env)) transl_globvar p;
  OK tt.
