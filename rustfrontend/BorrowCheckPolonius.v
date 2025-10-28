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

 
(* Initialize the variable origins (InitInternOrigins in rule
BORROW-CHECL), which may be unnecessary because all the origins of
variables map to Live(∅) *)

(* Definition init_variables (oe: LOrgEnv.t) (vars: list (ident * type)) : LOrgEnv.t := *)
(*   match ae with *)
(*   | AE.Err _ _ => Error (msg "Unknown error occurs before initialize variables' origin environment") *)
(*   | AE.Bot => *)
(*       let tys := map snd f.(fn_vars) in *)
(*       (* For all origins in the variable type, set its state to Live(∅) *) *)
(*       let orgs := concat (map origins_of_type tys) in *)
(*       let oe := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs (PTree.empty LOrgSt.t) in *)
(*       OK (AE.State LoanSet.empty oe LAliasGraph.bot) *)
(*   | AE.State ls oe a => *)
(*       let tys := map snd f.(fn_vars) in *)
(*       (* For all origins in the variable type, set its state to Live(∅) *) *)
(*       let orgs := concat (map origins_of_type tys) in *)
(*       let oe' := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs oe in *)
(*       OK (AE.State ls oe' a) *)
(*   end. *)

(** Transition *)

(* Support prefixes and support origins *)

Definition support_origins (p: place) : list origin :=
  let support_prefixes := p :: support_parent_paths p in
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
               
(* Transition of pure expression *)

Fixpoint mutable_place (p: place) :=
  match p with
  | Plocal _ _ => true
  | Pfield p' _ _ => mutable_place p'
  | Pderef p' _ =>
      match typeof_place p' with
      | Treference _ Mutable _ => mutable_place p'
      | Tbox _ => true
      | _ => false
      end
  | Pdowncast p' _ _ => mutable_place p'
  end.

Fixpoint transfer_pure_expr (pc: node) (e: LOrgEnv.t) (pe: pexpr) : res LOrgEnv.t :=
  match pe with
  | Eplace p ty =>
      if illegal_access e p Adeep Aread then
        Error (error_msg pc ++ [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Eplace"])
      else
        OK e
  | Eref org mut p ty =>
      let ak := match mut with | Mutable => Awrite | Immutable => Aread end in
      if illegal_access e p Adeep ak then
        Error (error_msg pc ++ [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Eref"])
      else
        let l := Lintern mut p in
        (* handle reborrow: add all the loans in the support
         prefix to org *)
        let support_orgs := support_origins p in
        (* aggregate the loans in the support origins *)
        let org_st := aggregate_origin_states e support_orgs in
        (* FIXME: is it correct to just combine two state? *)
        let s' := LOrgSt.lub org_st (Live (LoanSet.singleton (Lintern mut p))) in
        let e' := LOrgEnv.set org s' e in
        OK e'
  | Ecktag p id =>
      if illegal_access e p Ashallow Aread then
        Error (error_msg pc ++ [MSG "access a place (transfer_pure_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Ecktag"])
      else
        OK e
  | Eunop _ pe _ =>
      transfer_pure_expr pc e pe
  | Ebinop _ pe1 pe2 _ =>
      do e' <- transfer_pure_expr pc e pe1;
      transfer_pure_expr pc e' pe2
  (* Other constants *)
  | _ => OK e
  end.

(* transfer expression *)

Definition transfer_expr (pc: node) (oe: LOrgEnv.t) (e: expr) : res LOrgEnv.t :=
  match e with
  | Emoveplace p ty =>
      if illegal_access oe p Adeep Awrite then
        Error (error_msg pc ++ [MSG "access a place (transfer_expr) which is borrowed; id is "; CTX (local_of_place p); MSG " in Emoveplace"])
      else 
        OK oe
  | Epure pe =>
      transfer_pure_expr pc oe pe
  end.

Fixpoint transfer_exprlist (pc: node) (oe: LOrgEnv.t) (l: list expr) : res LOrgEnv.t :=
  match l with
  | [] => OK oe
  | e :: l' =>
      do oe' <- transfer_expr pc oe e;
      transfer_exprlist pc oe' l'
  end.


(* Flowing loans from source type to destination type *)

Inductive flow_kind : Type := ByVal | ByRef.

(* Subtyping rules of rust borrow checker *)
Fixpoint flow_loans (e: LOrgEnv.t) (s d: type) (k: flow_kind) : LOrgEnv.t :=
  match s,d with
  | Treference org1 _ ty1, Treference org2 _ ty2 =>
      let e' := flow_loans e ty1 ty2 ByRef in
      match k with
      | ByVal =>
          let st := LOrgSt.lub (LOrgEnv.get org1 e') (LOrgEnv.get org2 e') in
          LOrgEnv.set org2 st e'
      | ByRef =>
          (* TODO: improve it to follow the subtyping rules instead of
          just using invariance *)
          LOrgEnv.union org1 org2 e'
      end
  | Tbox ty1, Tbox ty2 =>
      (* TODO: Box is covariant over ty1/ty2, so there is no need to
      pass ByRef *)
      flow_loans e ty1 ty2 ByRef
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

Definition shallow_write_place (pc: node) (f: function) (e: LOrgEnv.t) (p: place) : res LOrgEnv.t :=
  if illegal_access e p Ashallow Awrite then
    Error (error_msg pc ++ [MSG "access a place (shallow_write_place) which is borrowed; id is "; CTX (local_of_place p)])    
  else
    OK e.

  (*   match p with *)
  (*   | (Plocal id ty) => *)
  (*     if in_dec ident_eq id (var_names f.(fn_vars)) then *)
  (*       (* This place is a local variable, we can kill its loans *)
  (*       (i.e., its stored loans become inactive) *) *)
  (*       let orgs := origins_of_type ty in *)
  (*       let e'' := fold_left (fun acc elt => LOrgEnv.delete elt acc) orgs e' in *)
  (*       OK e'' *)
  (*     else *)
  (*       (* TODO: is it necessary to kill the loans mapped from the generic origins? *) *)
  (*       OK e' *)
  (* | _ =>  *)
  (*     if valid_access e p then *)
  (*       OK e' *)
  (*     else *)
  (*       Error (error_msg pc ++ [MSG "access an invalidated place (shallow_write_place); id is "; CTX (local_of_place p)]) *)
  (* end. *)

(* Auxilary functions for transition of statements *)

Definition clear_loans (p: place) (st: LOrgSt.t) : LOrgSt.t :=
  match st with
  | Live ls =>
      Live (LoanSet.filter (fun elt => match elt with
                              | Lintern _ p' => negb (is_prefix p p')
                              | _ => true
                              end) ls)
  | Dead => Dead
  end.

(* When some loan [p] is overwritten, it should be cleared *)
Definition clear_dead_loans (e: LOrgEnv.t) (p: place) : LOrgEnv.t :=
  LOrgEnv.map1 (clear_loans p) e.

(* Borrow check an assign statement *)

Definition transfer_assignment (pc: node) (f: function) (oe: LOrgEnv.t) (p: place) (e: expr) : res LOrgEnv.t :=
  (* simple type checking *)
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  (* assigning p would clear all the loans that are children of p in
  the origin state. For example, if we assign something to a, than
  loan **a is not live anymore, as we cannot access the original
  location of **a. *)
  do oe1 <- transfer_expr pc oe e;
  do oe2 <- shallow_write_place pc f oe1 p;
  let oe3 := clear_dead_loans oe2 p in
  OK (flow_loans oe3 ty_src ty_dest ByVal).


Definition transfer_assign_variant (pc: node) (f: function) (ce: composite_env) (oe: LOrgEnv.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : res LOrgEnv.t :=
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
              do oe1 <- transfer_expr pc oe e;
              do oe2 <- shallow_write_place pc f oe1 p;
              let oe3 := clear_dead_loans oe2 p in
              OK (flow_loans oe3 ty_src ty_dest ByVal)
          (* It would cause error before borrow checking *)
          | _ => OK oe
          end
      (* It would cause error before borrow checking *)            
      | _ => OK oe
      end
  (* It would cause error before borrow checking *)
  | _ => OK oe
  end.

  (*                   Error (error_msg pc ++ [MSG "place is not mutable in check_assign_variant"]) *)
  (*               else *)
  (*                 Error (error_msg pc ++ [MSG "type checking error in check_assign_variant"]) *)
  (*           | _ => *)
  (*               Error (error_msg pc ++ [MSG "cannot find the field of this variant (check_assign_variant)"]) *)
  (*           end *)
  (*       | _ => *)
  (*           Error (error_msg pc ++ [MSG "cannot find the variant (check_assign_variant)"]) *)
  (*       end *)
  (*     else Error (error_msg pc ++ [MSG "enum id mismatch between LHS and RHS (check_assign_variant)"]) *)
  (* | _ => *)
  (*     Error (error_msg pc ++ [MSG "target is not a variant (check_assign_variant)"]) *)

Definition transfer_Sbox (pc: node) (f: function) (oe: LOrgEnv.t) (p: place) (e: expr) : res LOrgEnv.t :=
  (* [typeof_place p] must be Tbox, which should be checked at type
  checking phase *)
  let ty_dest := typeof_place p in
  let ty_src := Tbox (typeof e) in
  (* assigning p would clear all the loans that are children of p in
  the origin state. For example, if we assign something to a, than
  loan **a is not live anymore, as we cannot access the original
  location of **a. *)
  do oe1 <- transfer_expr pc oe e;
  do oe2 <- shallow_write_place pc f oe1 p;
  let oe3 := clear_dead_loans oe2 p in
  OK (flow_loans oe3 ty_src ty_dest ByVal).

  
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
      (* else *)
      (*   Error (error_msg pc ++ [MSG "mismatch between the length of origins in type"; CTX id1; MSG "(bind_type_origins)"]) *)
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
  (* match LOrgEnv.get src se, LOrgEnv.get tgt te with *)
  (* | Live ls1, Live ls2 => *)
  (*     let te' := LOrgEnv.set tgt (Live (LoanSet.union ls1 ls2)) te in *)
  (*     OK te' *)
  (* | _, _ => *)
  (*     Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin"]) *)
  (* end. *)


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

(** Assumption: the relations of origin given by the function
signature has been sorted topologically, to ensure that we just need
to flow the origins in one round instead of flowing it until reaching
a fixed point *)
Definition after_call (fe: LOrgEnv.t) (rels: list origin_rel) : LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               (* it may be less efficient *)
               flow_loans_origin_to_origin acc acc src tgt) rels fe.


Definition flow_loans_origin_to_origin_with_alias (fe e: LOrgEnv.t) (forg org: origin) : LOrgEnv.t :=
  LOrgEnv.set org (LOrgSt.lub (LOrgEnv.get forg fe) (LOrgEnv.get org e)) e.

  (* match LOrgEnv.get src se, LOrgEnv.get tgt te with *)
  (* | Live ls1, Live ls2 => *)
  (*     let te' := set_loans_with_alias tgt (LoanSet.union ls1 ls2) te ag in *)
  (*     OK te' *)
  (* | _, _ => *)
  (*     Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin_with_alias"]) *)
  (* end. *)

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


Definition transfer_function_call (pc: node) (f: function) (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : res LOrgEnv.t :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      (* transfer the arguments *)
      do oe2 <- transfer_exprlist pc oe1 args;
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          OK oe2
      | None =>
          (* Move it to rusttyping. if forallb (fun '(ty1, ty2) => type_eq_except_origins ty1 ty2) (combine arg_tyl sig_tyl) && type_eq_except_origins tgt_rety rty then *)
          (* construct empty origin environments for function origins *)
          let foe1 := LOrgEnv.bot in
          let (foe2, rels) := bind_param_origins oe2 foe1 args_tyl sig_tyl in
          (* use the origin relation to simulate the flow of loans
             in the caller. foe2 is the initial env in the callee,
             foe3 is the final env *)
          let foe3 := after_call foe2 org_rels in
          (* update the invariant relation established by the
          evaluation of function parameters *)
          let oe3 := flow_alias_after_call rels foe3 oe2 in
          (* shallow write to p *)
          do oe4 <- shallow_write_place pc f oe3 p;
          let oe5 := clear_dead_loans oe4 p in
          OK (flow_return_after_call foe3 oe5 rty tgt_rety)
          (* (* kill relevant loans *) *)
          (*   let live3 := kill_loans live2 p in *)
          (*   (* flow loans to the return type and update alias *) *)
          (*   do oe4 <- flow_alias_after_call pc ag2 rels foe3 oe3; *)
          (*   do oe5 <- flow_return_after_call pc ag2 foe3 oe4 rty tgt_rety; *)
          (*   OK (live3, oe5, ag2) *)
          (* else *)
          (*   Error (error_msg pc ++ [MSG "type checking fails in check_function_call"]) *)
      end
  | _ => OK oe1
(* Error (error_msg pc ++ [MSG "it is not a function type in check_function_call"])       *)
  end.

Definition transfer_storagedead (pc: node) (f: function) (oe1: LOrgEnv.t) (id: ident) : res LOrgEnv.t :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      do oe2 <- shallow_write_place pc f oe1 (Plocal id ty);
      OK (clear_dead_loans oe2 (Plocal id ty))
  | None =>
      (* report errors in the type checking *)
      OK oe1
  end.

(** TODO: we need to consider p is initialized or not *)
Definition transfer_drop (pc: node) (oe1: LOrgEnv.t) (p: place) : res LOrgEnv.t :=
  if illegal_access oe1 p Adeep Awrite then
    Error (error_msg pc ++ [MSG "access a place which is borrowed: "; CTX (local_of_place p); MSG "in (check_drop)"])
  else OK oe1.

  (* (* if valid_access oe1 p then *) *)
  (*   let ls := relevant_loans live1 p Adeep in *)
  (*   let oe2 := invalidate_origins ls Awrite oe1 in *)
  (*   OK (live1, oe2, ag1) *)
  (* else Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG "in (check_drop)"]). *)


(** Unused: All the generic origins cannot contain any internal loans
(wrong!)  when returning from a function. Otherwise there may be a
dangling pointer. The functionality of checking dangling pointer is in
check return. We assume that all storagedeads are placed before return
statement *)

Definition check_dangle (f: function) (e: LOrgEnv.t) : bool :=
  forallb (fun org => match LOrgEnv.get org e with
                   | Live ls =>
                       negb (LoanSet.exists_ (fun l => match l with
                                                    | Lintern _ _ => true
                                                    | _ => false
                                                    end) ls)
                   (* impossible *)
                   | _ => false
                   end) f.(fn_generic_origins).
                              

(** All the relations between the generic origins after the function
call must be declared in the function sigature *)

Definition live_origin (st: origin_state) : bool :=
  match st with
  | Live _ => true
  | Dead => false
  end.

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
  

(* Definition check_return_expr (live1: LoanSet.t) (oe1: LOrgEnv.t) (ag1: LAliasGraph.t) (e: expr) (rety: type) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) := *)
(*   let ty_src := typeof e in *)
(*   if type_eq_except_origins ty_src rety then *)
(*     do (live2, oe2) <- transfer_expr pc live1 oe1 e; *)
(*     do (oe3, ag2) <- flow_loans pc oe2 ag1 ty_src rety ByVal; *)
(*     OK (live2, oe3, ag2) *)
(*   else *)
(*     Error (error_msg pc ++ [MSG "type error in function return"]). *)


Definition transfer_return (pc: node) (oe1: LOrgEnv.t) (p: place) (rety: type) : res LOrgEnv.t :=
  if illegal_access oe1 p  Adeep Aread then
    (* Question: this error should be impossible (or the error has
    been found before this return statement)? Because there is no live
    regions (except generic regions) after the return statement. *)
    Error (error_msg pc ++ [MSG "access a place which is borrowed"; CTX (local_of_place p); MSG "in (transfer_return)"])
  else
    OK oe1.

Definition finish_check_without_liveness (pc: node) (r: res LOrgEnv.t) : BORCK.t :=
  match r with
  | OK oe => BORCK.State oe
  | Error msg =>
      BORCK.Err pc msg
  end.

Definition finish_check (pc: node) (r: res LOrgEnv.t) (live: RegionSet.t) : BORCK.t :=
  match r with
  | OK oe => 
      (* We need to apply liveness result after transfer to prevent
      applying liveness after the join between two branches, which may
      cause some unprecision. This is because apply_liveness (e1 ⊔ e2)
      <> apply_liveness e1 ⊔ apply_liveness e2. *)
      let oe1 := LOrgEnv.apply_liveness live oe in
      BORCK.State oe1
  | Error msg =>
      BORCK.Err pc msg
  end.


(* Transition of statements *)
        
Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (live: PMap.t RegionSet.t) (generic_regions: RegionSet.t) (pc: node) (before: BORCK.t) : BORCK.t :=
  match before with
  | BORCK.Bot => before
  | BORCK.Err _ _ =>
      (* Error propagation *)
      before
  | BORCK.State oe =>
      (* apply liveness result before transfer *)
      let live_after := PMap.get pc live in
      let live_before := RegionLiveness.transfer f cfg generic_regions pc live_after in
      let oe := LOrgEnv.apply_liveness live_before oe in
      match cfg ! pc with
      | None => BORCK.Bot
      | Some (Inop _) => before
      | Some (Icond e _ _) => finish_check_without_liveness pc (transfer_expr pc oe e)
      | Some Iend => before
      | Some (Isel sel next) =>
          match select_stmt f.(fn_body) sel with
          | None => BORCK.Bot
          | Some s =>
              match s with
              | Sassign p e => 
                  finish_check pc (transfer_assignment pc f oe p e) live_after
              | Sassign_variant p enum_id fid e =>
                  finish_check pc (transfer_assign_variant pc f ce oe p enum_id fid e) live_after
              | Sbox p e =>
                  finish_check pc (transfer_Sbox pc f oe p e) live_after
              | Scall p e l =>
                  finish_check pc (transfer_function_call pc f oe p e l) live_after
              | Sstoragedead id =>
                  finish_check pc (transfer_storagedead pc f oe id) live_after
              | Sdrop p =>
                  finish_check pc (transfer_drop pc oe p) live_after
              | Sreturn p =>
                  let check_result := transfer_return pc oe p f.(fn_return) in
                  match check_result with
                  | OK oe1 =>
                      (** TODO: we still do not know how to check generic origins
                          at the end of the function using the Rustcfg
                          framework.... *)
                      if check_generic_origins_relations f oe1 then
                        BORCK.State oe1
                      else
                        BORCK.Err pc [MSG "some relations in function return are not declared in the function signature"]
                  | Error msg =>
                      BORCK.Err pc msg
                  end
              | _ => before
              end 
          end
      end
  end.

Module BorrowCheck := Dataflow_Solver(BORCK)(NodeSetForward).

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
  

(** Run Borrow Checking! *)

Definition borrow_check (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t RegionSet.t * (PMap.t BORCK.t)) :=
  (* Liveness analysis for regions *)
  let generic_regions := live_generic_regions (fn_generic_origins f) in
  match RegionLiveness.analyze f cfg with
  | Some live =>
      let init_oe := init_function f in
      match BorrowCheck.fixpoint cfg successors_instr (transfer ce f cfg live generic_regions) entry (BORCK.State init_oe) with
      (* For now we return liveness result for debug purpose *)
      | Some m => OK (live, m)
      | None =>
          Error [MSG "The borrow checking fails with unknown reason"]
      end
  | None => 
      Error [MSG "The borrow checking fails due to the failure of liveness analysis"]
  end.

(** Checking functions that are used in the transl_on_cfg *)

Definition collect_borck_result_stmt (borck_res: BORCK.t) (stmt: statement) : res statement :=
  match borck_res with
  | BORCK.Err pc msg =>
      (* usually pc has been already existed in msg *)
      Error msg
  | _ => OK stmt
  end.

Definition collect_borck_result_expr (borck_res: BORCK.t) (e: expr) : res unit :=
  match borck_res with
  | BORCK.Err pc msg =>
      Error msg
  | _ => OK tt
  end.

Definition get_borck_result (borck_res: (PMap.t BORCK.t)) (pc: node) : BORCK.t :=
  borck_res !! pc.

(* After calling borrow_check, we should find if there is any borrow
check error *)
Definition collect_borrow_check_result (ce: composite_env) (f: function) (cfg: rustcfg) (borck_res: (PMap.t RegionSet.t * (PMap.t BORCK.t))) : res unit :=
  do _ <- transl_on_cfg get_borck_result (snd borck_res) collect_borck_result_stmt collect_borck_result_expr f.(fn_body) cfg;
  OK tt.

(** TODO: we should combine it with move_check_function *)

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** 1. Borrow checking *)
  do borrow_check_res <- borrow_check ce f cfg entry;
  (** 2. Collect result of the borrow checking ! *)
  collect_borrow_check_result ce f cfg borrow_check_res.

Definition transf_fundef (ce: composite_env) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match borrow_check_function ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error ([MSG "In function "; CTX id; MSG " : "] ++ msg)
      end
  | External orgs rels ef targs tres cconv => Errors.OK (External orgs rels ef targs tres cconv)
  end.

Definition transl_globvar (id: ident) (ty: type) := OK ty.

(** TODO  *)
Definition check_origins_well_formedness (p: program) : bool :=
  true.

(* borrow check the whole module *)

Definition borrow_check_program (p: program) : res unit :=
  (* ensure that replaceOrigins has been executed before borrow checking *)
  if check_origins_well_formedness p then
    do _ <- transform_partial_program2 (transf_fundef p.(prog_comp_env)) transl_globvar p;
    OK tt
  else
    Error (msg "Origins in the program are not well formed").
