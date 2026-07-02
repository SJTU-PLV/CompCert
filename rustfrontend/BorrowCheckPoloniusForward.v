Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR RustIRcfg.
Require Import Rusttyping.
Require Import Errors.
Require Import ReplaceOrigins.
Require Import UnionFindDelete.
Require Import RegionLiveness BorrowCheckDomain.
Require Import BorrowCheckPolonius.

Import ListNotations.
Open Scope error_monad_scope.

(** A logging monad for computations that keep going while accumulating
    diagnostics.  There is intentionally no success/error branch here:
    the value is always produced, and any errors observed along the way
    are appended to the [errmsg] log. *)
Module Log.

Definition mon (A: Type) : Type := A * errmsg.

Definition ret {A: Type} (x: A) : mon A :=
  (x, nil).

Definition tell (msg: errmsg) : mon unit :=
  (tt, msg).

Definition with_log {A: Type} (x: A) (msg: errmsg) : mon A :=
  (x, msg).

Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
  let (a, log1) := x in
  let (b, log2) := f a in
  (b, log1 ++ log2).

Definition bind2 {A B C: Type} (x: mon (A * B)) (f: A -> B -> mon C) : mon C :=
  bind x (fun p => f (fst p) (snd p)).

Definition map {A B: Type} (f: A -> B) (x: mon A) : mon B :=
  bind x (fun a => ret (f a)).

Definition run {A: Type} (x: mon A) : A * errmsg := x.

Definition value {A: Type} (x: mon A) : A := fst x.

Definition log {A: Type} (x: mon A) : errmsg := snd x.

Definition append_log {A: Type} (x: mon A) (msg: errmsg) : mon A :=
  let (a, log1) := x in
  (a, log1 ++ msg).

Definition from_res {A: Type} (default: A) (x: res A) : mon A :=
  match x with
  | Errors.OK a => ret a
  | Errors.Error msg => with_log default msg
  end.

Definition guard (b: bool) (msg: errmsg) : mon bool :=
  if b then ret true else with_log false msg.

End Log.

Declare Scope log_monad_scope.

Notation "'logdo' X <- A ; B" := (Log.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : log_monad_scope.

Notation "'logdo' ( X , Y ) <- A ; B" := (Log.bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : log_monad_scope.

Open Scope log_monad_scope.

(** ** Abstract Interpreter of Borrow checking based on Polonius (dataflow analysis) *)

Definition borrow_error (action site: string) (p: place) : errmsg :=
  [MSG action; MSG " place "]
  ++ errmsg_of_place p
  ++ [MSG " because it contains some invalidated region; this error occurs in ";
      MSG site].

Section COMP_ENV.

Variable (ce: composite_env).
(* Check if we access an invalidate region *)

Definition invalidated_region_access (e: LOrgOptEnv.t) (r: origin) :=
 match LOrgOptEnv.get r e with
 | None => true  (* access an invalidated region *)
 | _ => false
 end.

Definition invalidated_access (e: LOrgOptEnv.t) (p: place) : bool :=
  existsb (invalidated_region_access e) (origins_of_type (root_type_of_place p)).


(* Region invalidation *)

Definition invalidate_region_state (p: place) (am: access_mode_bor) (ak: access_kind) (r: origin) (st: LOrgLnOptSt.t) : LOrgLnOptSt.t :=
  match st with
  | Some os =>
      match os with
      | LOrgLnSt.Live ls =>
          if conflict p ls am ak then None (* None denotes invalidated state *)
          else Some os
      | LOrgLnSt.Dead => Some os
      end
  | None => None
  end.

(* Invalidate the region that contains conflicting loan with p under
am and ak. TODO: It is unclear if we need to check every time that the generic regions cannot be invalidated *)
(* Definition invalidate_regions (e: LOrgOptEnv.t) (p : place) (am : access_mode_bor) (ak : access_kind) : Log.mon LOrgOptEnv.t := *)
(*   let m := (LOrgOptEnv.m e) in *)
(*   let e1 := LOrgOptEnv.mk (PTree.map (invalidate_region_state p am ak) m) (LOrgOptEnv.uf e) in *)
(*   (* check if we have invalidated some generic regions *) *)
(*   let msg :=  *)
(*     if existsb (invalidated_region_access e1) f.(fn_generic_origins) then *)
(*       [MSG " access place "] ++ errmsg_of_place p ++ [MSG " would invalidate some generic region"] *)
(*     else nil in *)
(*   Log.with_log e1 msg. *)

Definition invalidate_regions (e: LOrgOptEnv.t) (p : place) (am : access_mode_bor) (ak : access_kind) : LOrgOptEnv.t :=
  let m := (LOrgOptEnv.m e) in
  LOrgOptEnv.mk (PTree.map (invalidate_region_state p am ak) m) (LOrgOptEnv.uf e).

(* Transition of pure expression *)

Fixpoint transfer_pure_expr (e1: LOrgOptEnv.t) (pe: pexpr) : Log.mon LOrgOptEnv.t :=
  match pe with
  | Eplace p ty =>
      let msg := 
        if invalidated_access e1 p then
          (borrow_error "cannot access" "Eplace of transfer_pure_expr" p)
        else
          nil in
      Log.with_log (invalidate_regions e1 p Adeep ARead) msg
  | Eref org mut p ty =>
      let ak := mut_to_access_kind mut in
      let e2 := invalidate_regions e1 p Adeep ak in
      let msg := 
        if invalidated_access e2 p then
          (borrow_error "cannot access" "Eref of transfer_pure_expr" p)
        else
          nil in
      (* handle reborrow: add all the loans in the support *)
      (* prefix to org *)
      let support_orgs := support_origins p in
      (* aggregate the loans in the support origins *)
      let org_st := LOrgOptEnv.aggregate_origin_states e2 support_orgs in
      let s' := LOrgLnOptSt.lub org_st (Some (LOrgLnSt.Live (LoanSet.singleton (Lintern mut p)))) in
      (* We must overwrite org otherwise if we have a loop and org is
      invalidated, then we just return invalidated contents! *)
      Log.with_log (LOrgOptEnv.set org s' e2) msg
  | Ecktag p fid =>
      let msg := 
        if invalidated_access e1 p then
          (borrow_error "cannot access" "Ecktag of transfer_pure_expr" p)
        else
          nil in
      Log.with_log (invalidate_regions e1 p Ashallow ARead) msg
  | Eunop _ pe _ =>
      transfer_pure_expr e1 pe
  | Ebinop _ pe1 pe2 _ =>
      logdo e2 <- transfer_pure_expr e1 pe1;
      transfer_pure_expr e2 pe2
  (* Other constants *)
  | _ => Log.ret e1
  end.

(* transfer expression *)

Definition transfer_expr (oe: LOrgOptEnv.t) (e: expr) : Log.mon LOrgOptEnv.t :=
  match e with
  | Emoveplace p ty =>
      let msg := 
        if invalidated_access oe p then
          (borrow_error "cannot access" "Emoveplace of transfer_expr" p)
        else
          nil in
      Log.with_log (invalidate_regions oe p Adeep AWrite) msg
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


Fixpoint transfer_exprlist (oe: LOrgOptEnv.t) (l: list expr) : Log.mon LOrgOptEnv.t :=
  match l with
  | [] => Log.ret oe
  | e :: l' =>
      logdo oe' <- transfer_expr oe e;
      transfer_exprlist oe' l'
  end.


(* Shallow write a place *)

Fixpoint check_shallow_write_place (e: LOrgOptEnv.t) (p: place) : errmsg :=
  (* This checking ensures the safety of evaluation of p, we want to
  ensure that all regions encounter during the evaluation of p must be
  valid *)
  match p with
  | Plocal _ _ => nil
  | Pfield p1 _ _ 
  | Pdowncast p1 _ _ =>
      check_shallow_write_place e p1
  | Pderef p1 _ =>
      match typeof_place p1 with
      | Treference r _ _ =>
          let msg := match LOrgOptEnv.get r e with
                     | Some _ => nil
                     | None => (borrow_error "place evaluation may be invalid" "shallow_write_place" p)
                     end in
          msg ++ check_shallow_write_place e p1
      | _ => check_shallow_write_place e p1
      end
  end.

(* Auxilary functions for transition of statements *)

Definition kill_place_related_loans (p: place) (st: LOrgLnOptSt.t) : LOrgLnOptSt.t :=
  match st with
  | Some st =>
      match st with
      | LOrgLnSt.Live ls =>
          Some (LOrgLnSt.Live (LoanSet.filter (fun elt => match elt with
                              (* Note that we also clear p, so
                              clear_dead_loans should be perfomed
                              after check_shallow_write_place *)
                              | Lintern _ p' => negb (is_prefix p p')
                              | _ => true
                              end) ls))
      | LOrgLnSt.Dead => Some LOrgLnSt.Dead
      end
  | _ => None
  end.

(* When some loan [p] is overwritten, it should be cleared *)
Definition kill_loans (e: LOrgOptEnv.t) (p: place) : LOrgOptEnv.t :=
  LOrgOptEnv.map1 (kill_place_related_loans p) e.

Fixpoint clear_dead_regions (e: LOrgOptEnv.t) (l: list origin) : LOrgOptEnv.t :=
  match l with
  | nil => e
  | r :: l' =>
      clear_dead_regions (LOrgOptEnv.delete r e) l'
  end.

Definition clear_dead_regions_place (e: LOrgOptEnv.t) (p: place) : LOrgOptEnv.t :=
  match p with
  (* What if p is a paramter and contains generic regions? *)
  | Plocal id ty =>
      clear_dead_regions e (origins_of_type ty)
  | _ => e
  end.

(* Borrow check an assign statement *)

Definition before_assign (oe2: LOrgOptEnv.t) (p: place) : Log.mon LOrgOptEnv.t :=
  (* We cannot kill_loans here because there may be some active loans
  related to p and if we kill them, there may be soundness problem *)
  let oe3 := invalidate_regions oe2 p Ashallow AWrite in
  let msg := check_shallow_write_place oe3 p in
  logdo oe3 <- Log.with_log oe3 msg;
  (* After checking the evaluation of e *)
  let oe4 := kill_loans oe3 p in
  (* clear must-overwritten regions. Is this order correct? *)
  let oe5 := clear_dead_regions_place oe4 p in
  Log.ret oe5.

Fixpoint before_assign_list (oe: LOrgOptEnv.t) (l: list place) : Log.mon LOrgOptEnv.t :=
  match l with
  | nil => Log.ret oe
  | p :: l' =>
      logdo oe1 <- before_assign oe p;
      before_assign_list oe1 l'
end.
                                      
Definition transfer_assignment (oe1: LOrgOptEnv.t) (p: place) (e: expr) : Log.mon LOrgOptEnv.t :=
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  logdo oe2 <- transfer_expr oe1 e;
  logdo oe5 <- before_assign oe2 p; 
  Log.ret (LOrgOptEnv.flow_loans oe5 ty_src ty_dest Covariant).


Definition transfer_assign_variant (oe1: LOrgOptEnv.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : Log.mon LOrgOptEnv.t :=
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
              logdo oe2 <- transfer_expr oe1 e;
              logdo oe5 <- before_assign oe2 p;
              Log.ret (LOrgOptEnv.flow_loans oe5 ty_src ty_dest Covariant)
          (* It would cause error before borrow checking *)
          | _ => Log.ret oe1
          end
      (* It would cause error before borrow checking *)            
      | _ => Log.ret oe1
      end
  (* It would cause error before borrow checking *)
  | _ => Log.ret oe1
  end.

Definition transfer_Sbox (oe1: LOrgOptEnv.t) (p: place) (e: expr) : Log.mon LOrgOptEnv.t :=
  (* [typeof_place p] must be Tbox, which should be checked at type
  checking phase *)
  let ty_dest := typeof_place p in
  let ty_src := Tbox (typeof e) in
  logdo oe2 <- transfer_expr oe1 e;
  logdo oe5 <- before_assign oe2 p; 
  Log.ret (LOrgOptEnv.flow_loans oe5 ty_src ty_dest Covariant).
  (* (* After checking the evaluation of e *) *)
  (* let oe2 := kill_loans oe1 p in *)
  (* LOrgEnv.flow_loans oe2 ty_src ty_dest Covariant. *)


Definition flow_loans_origin_to_origin (se te: LOrgOptEnv.t) (src tgt: origin) : LOrgOptEnv.t :=
  LOrgOptEnv.set tgt (LOrgLnOptSt.lub (LOrgOptEnv.get src se) (LOrgOptEnv.get tgt te)) te.


Definition after_call (fe: LOrgOptEnv.t) (rels: list origin_rel) : LOrgOptEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               (* it may be less efficient *)
               flow_loans_origin_to_origin fe acc src tgt) rels fe.


(** TODO: to make it simpler  *)
Definition transfer_function_call (oe1: LOrgOptEnv.t) (p: place) (ef: expr) (args: list expr) : Log.mon LOrgOptEnv.t :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      (* transfer the arguments *)
      logdo oe2 <- transfer_exprlist oe1 args;
      (* flow the loans from arguments to the parameter types of the function *)
      let oe3 := LOrgOptEnv.flow_loans_list oe2 args_tyl sig_tyl Covariant in
      (** We check that each generic region is a singleton set, i.e.,
      we do not generate invariant relation for any two regions (which
      cannot be expressed in the function signature for now) *)
      let msg := 
        if no_sameclass (LOrgOptEnv.uf oe3) orgs then        
          nil
        else
          [MSG "There is some generic region that may not be a singleton when calling a function"] in
      logdo oe3 <- Log.with_log oe3 msg;
      (* apply the effect of the function call *)
      let oe4 := after_call oe3 org_rels in
      (* (* kill loans *) *)
      (* let oe5 := kill_loans oe4 p in *)
      logdo oe5 <- before_assign oe4 p; 
      (* assign the return value to p *)
      Log.ret (LOrgOptEnv.flow_loans oe5 rty tgt_rety Covariant)
  | _ => Log.ret oe1
(* Error (error_msg pc ++ [MSG "it is not a function type in check_function_call"])       *)
  end.

End COMP_ENV.

Definition transfer_storagedead (f: function) (oe1: LOrgOptEnv.t) (id: ident) : Log.mon LOrgOptEnv.t :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      (* After check_shallow_write_place *)
      (* (kill_loans oe1 (Plocal id ty)) *)
      (* We can use this function to simulate the effect of storagedead *)
      before_assign oe1 (Plocal id ty)
  | None =>
      (* report errors in the type checking *)
      Log.ret oe1
  end.


(** TODO: we need to consider p is initialized or not *)
Definition transfer_drop (oe1: LOrgOptEnv.t) (p: place) : Log.mon LOrgOptEnv.t :=
  Log.ret (invalidate_regions oe1 p Adeep AWrite).

(* Check if there is a generic region containing some internal loans *)
(* at the function return *)
Definition check_dangling (f: function) (e: LOrgOptEnv.t) : bool :=
  forallb (fun org => match (LOrgOptEnv.get org e) with
                   | Some st => absence_of_internal_loans st
                   | _ => true
                   end) f.(fn_generic_origins).

Definition check_generic_origins_relations (f: function) (e: LOrgOptEnv.t) : bool :=
  (* This property can be guaranteed by the liveness analysis: All the
  generic origin must not be dead otherwise we are returing a dangling
  pointer *)
  (* forallb (fun org => live_origin (LOrgEnv.get org e)) f.(fn_generic_origins) && *)
  forallb (fun org1 => 
             forallb 
               (fun org2 =>
                  if Pos.eqb org1 org2 then true
                  else match LOrgOptEnv.get org1 e with
                       | Some (LOrgLnSt.Live ls1) =>
                           if LoanSet.mem (Lextern org2) ls1 then
                             in_dec origin_rel_eq_dec (org2, org1) f.(fn_origins_relation)
                           (* else if LoanSet.subset ls2 ls1 then *)
                           (*        in_dec origin_rel_eq_dec (org2, org1) f.(fn_origins_relation) *)
                           else true
                       (* generic origins must be live which *)
                       (*                 should be already checked *)
                       | _ => true
                       end) f.(fn_generic_origins)) f.(fn_generic_origins).
  

(* We use it to ensure that we cannot return the address of stack blocks of the parameters *)
(* Fixpoint check_storagedead_list (l: list (ident * type)) (e: LOrgEnv.t) : res unit := *)
(*   match l with *)
(*   | nil => OK tt *)
(*   | (id, ty) :: l' => *)
(*       do _ <- check_shallow_write_place e (Plocal id ty); *)
(*       check_storagedead_list l' e *)
(*   end. *)
 
(* (* We use it to clear the reborrow of parameters at the function return *) *)
(* Fixpoint kill_loans_list (e: LOrgEnv.t) (l: list (ident * type)) : LOrgEnv.t := *)
(*   match l with *)
(*   | nil => e *)
(*   | (id, ty) :: l' => *)
(*       kill_loans_list (kill_loans e (Plocal id ty)) l' *)
(*   end. *)

Definition check_return (f: function) (oe: LOrgOptEnv.t) : errmsg :=
  let msg1 := 
    (* If there is invalidated region in the generic regions *)
    if existsb (invalidated_region_access oe) (fn_generic_origins f) then
      [MSG " there is some invalidated generate regions in the function return "]
    else nil in
  let msg2 :=
    if check_dangling f oe then
      nil
    else [MSG "Dangling pointer! There should not be internal loans in the generic regions at the function return"] in
  let msg3 := 
    (* check if there is reference to variables/parameters that are
    stored in the generic regions. Since we cannot ensure that we
    generate stroragedead for all the variables before function return
    (e.g., we may return inside a scope of a local variables), we
    should also check variables. *)
    if check_generic_origins_relations f oe then
      nil
    else
      [MSG "some relations in function return are not declared in the function signature"] in
  msg1 ++ msg2 ++ msg3.

(* We need to transfer the loans from the return variable to the
return type of this function *)
Definition transfer_return (f: function) (oe1: LOrgOptEnv.t) (p: place) : Log.mon LOrgOptEnv.t :=
  let oe2 := invalidate_regions oe1 p Adeep AWrite in
  (* kill loans should be perfomed on oe3 after flowing loans *)
  let oe3 := LOrgOptEnv.flow_loans oe2 (typeof_place p) f.(fn_return) Covariant in
  (* simulate the free operations *)
  logdo oe4 <- before_assign_list oe3 (map (fun '(id, ty) => Plocal id ty) (f.(fn_vars) ++ f.(fn_params)));
  let msg := check_return f oe4 in
  Log.with_log oe4 msg.
 

(* Transition of statements *)

Definition transfer_stmt ce f oe s : LOrgOptEnv.t * errmsg :=
  let finish_transfer (st: Log.mon LOrgOptEnv.t) := ((Log.value st), (Log.log st)) in
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
  | Sdrop p =>
      finish_transfer (transfer_drop oe p)
  | Sreturn p =>
      finish_transfer (transfer_return f oe p)
  | _ => (oe, nil)
  end.

Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (pc: node) (before: LoansOptEnv.t) : LoansOptEnv.t :=
  match before with
  | LoansOptEnv.Bot => before
  | LoansOptEnv.State oe _ =>
      let finish_transfer (st: Log.mon LOrgOptEnv.t) := LoansOptEnv.State (Log.value st) (Log.log st) in
      match cfg ! pc with
      | None => LoansOptEnv.Bot
      | Some (Inop _) => before
      | Some (Icond e _ _) => finish_transfer (transfer_expr oe e)
      | Some Iend => before
      | Some (Isel sel next) =>
          match select_stmt f.(fn_body) sel with
          | None => LoansOptEnv.Bot
          | Some s =>
              let (oe, msg) := transfer_stmt ce f oe s in
              LoansOptEnv.State oe msg
              (* match s with *)
              (* | Sassign p e =>  *)
              (*     finish_transfer (transfer_assignment oe p e) *)
              (* | Sassign_variant p enum_id fid e => *)
              (*     finish_transfer (transfer_assign_variant ce oe p enum_id fid e) *)
              (* | Sbox p e => *)
              (*     finish_transfer (transfer_Sbox oe p e) *)
              (* | Scall p e l => *)
              (*     finish_transfer (transfer_function_call oe p e l) *)
              (* | Sstoragedead id => *)
              (*     finish_transfer (transfer_storagedead f oe id) *)
              (* | Sdrop p => *)
              (*     finish_transfer (transfer_drop oe p) *)
              (* | Sreturn p => *)
              (*     finish_transfer (transfer_return f oe p) *)
              (* | _ => LoansOptEnv.State oe nil *)
              (* end  *)
          end
      end
  end.

Module BorrowCheckAbs := Dataflow_Solver(LoansOptEnv)(NodeSetForward).


(** Initialization *)

(* The rule I-Fun. Maybe we should just initialize the generic origins
that appear in the arguments? *)
Definition init_function (f: function) : LOrgOptEnv.t :=
  (* initialize the loans of generic regions *)
  let oe1 := fold_left (fun acc elt =>
                          let os := Some (LOrgLnSt.Live (LoanSet.singleton (Lextern elt))) in
                          LOrgOptEnv.set elt os acc) f.(fn_generic_origins) LOrgOptEnv.bot in
  (* flow the loans from the function arguments to the parameters *)
  LOrgOptEnv.flow_loans_list oe1 f.(fn_param_types) (map snd f.(fn_params)) Covariant.
  
(** Run Liveness analysis and Loans-flow analysis *)

Definition borrow_check_interpret (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t LoansOptEnv.t) :=
  let init_oe := init_function f in
  match BorrowCheckAbs.fixpoint cfg successors_instr (transfer ce f cfg) entry (LoansOptEnv.State init_oe nil) with
  (* For now we return liveness result for debug purpose *)
  | Some m => OK m
  | None =>
      Error [MSG "The borrow-checking abstract interpreter fails with unknown reason"]
  end.

(** Checking functions that are used in the transl_on_cfg *)

Definition borrow_check_stmt_aux ce (f: function) (le: LoansOptEnv.t) (stmt: statement) : res unit :=
  match le with
  | LoansOptEnv.State oe _ =>
      let (_, msg) := transfer_stmt ce f oe stmt in
      match msg with
      | nil => OK tt
      | _ => Error msg
      end
  (* Error [MSG "Impossible: it is unreachable point"] *)
  | _ => OK tt
  end.
  
Definition borrow_check_stmt ce (f: function) (le: LoansOptEnv.t) (stmt: statement) : res statement :=
  do _ <- borrow_check_stmt_aux ce f le stmt;
  OK stmt.

Definition borrow_check_cond_expr (le: LoansOptEnv.t) (e: expr) : res unit :=
  match le with
  | LoansOptEnv.State oe _ =>
      let st := transfer_expr oe e in
      match (Log.log st) with
      | nil => OK tt
      | _ => Error (Log.log st)
      end
  (* Impossible *)
  | _ =>
      (* Error [MSG "Impossible: it is unreachable point"] *)
      OK tt
  end.

Definition get_borck_result (abs_env: (PMap.t LoansOptEnv.t)) (pc: node) : LoansOptEnv.t :=
  abs_env !! pc.

(* After calling borrow_check, we should find if there is any borrow
check error *)
Definition collect_borrow_check_result ce (f: function) (cfg: rustcfg) (abs_env: (PMap.t LoansOptEnv.t)) : res unit :=
  do _ <- transl_on_cfg get_borck_result abs_env (borrow_check_stmt ce f) borrow_check_cond_expr f.(fn_body) cfg;
  OK tt.


(** The following code is used for printing the result of borrow
checking, which is not used in the top-level soundness proof. *)

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** 1. Run abstract interpreter *)
  do abs_env <- borrow_check_interpret ce f cfg entry;
  (** 2. Collect result of the borrow checking ! *)
  collect_borrow_check_result ce f cfg abs_env.

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
