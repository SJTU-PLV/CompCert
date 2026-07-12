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

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on Polonius, interpreted with diagnostics logs.

    This version keeps the original Polonius loan domain and liveness
    pruning, but records alarms during transfer instead of returning
    [Error] from the transfer used by the dataflow solver.  The solver
    ignores logs for equality and convergence; the final checking pass
    replays the transfer at each CFG point and reports the replayed log. *)

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

Definition value {A: Type} (x: mon A) : A := fst x.

Definition log {A: Type} (x: mon A) : errmsg := snd x.

End Log.

Declare Scope log_monad_scope.

Notation "'logdo' X <- A ; B" := (Log.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : log_monad_scope.

Notation "'logdo' ( X , Y ) <- A ; B" := (Log.bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : log_monad_scope.

Open Scope log_monad_scope.

Definition alarm_if (b: bool) (msg: errmsg) : errmsg :=
  if b then msg else nil.

Definition borrowed_place_error (action site: string) (p: place) : errmsg :=
  [MSG action; MSG " place "]
  ++ errmsg_of_place p
  ++ [MSG " because it is borrowed; this error occurs in ";
      MSG site].

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at pc "; POS pc; MSG " : "].

Module LoansLogEnv <: SEMILATTICE.

  Inductive t' := | Bot | State (org_env: LOrgEnv.t) (log: errmsg).

  Definition t := t'.

  Definition eq (x y: t) : Prop :=
    match x, y with
    | Bot, Bot => True
    | State oe1 _, State oe2 _ => LOrgEnv.eq oe1 oe2
    | _, _ => False
    end.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => false
    | State oe1 _, State oe2 _ => LOrgEnv.beq oe1 oe2
    | _, _ => false
    end.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    | State oe1 _, State oe2 _ => LOrgEnv.ge oe1 oe2
    end.

  Definition bot := Bot.

  Definition lub (x y: t) :=
    match x, y with
    | _, Bot => x
    | Bot, _ => y
    | State oe1 _, State oe2 _ =>
        State (LOrgEnv.lub oe1 oe2) nil
    end.

  Axiom eq_refl: forall x, eq x x.
  Axiom eq_sym: forall x y, eq x y -> eq y x.
  Axiom eq_trans: forall x y z, eq x y -> eq y z -> eq x z.

  Axiom beq_correct: forall x y, beq x y = true -> eq x y.

  Axiom ge_refl: forall x y, eq x y -> ge x y.
  Axiom ge_trans: forall x y z, ge x y -> ge y z -> ge x z.

  Axiom ge_bot: forall x, ge x bot.

  Axiom ge_lub_left: forall x y, ge (lub x y) x.
  Axiom ge_lub_right: forall x y, ge (lub x y) y.

End LoansLogEnv.

Section COMP_ENV.

Variable (ce: composite_env).

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

Fixpoint transfer_pure_expr (e: LOrgEnv.t) (pe: pexpr) : Log.mon LOrgEnv.t :=
  match pe with
  | Eplace p ty =>
      Log.with_log e
        (alarm_if (illegal_access e p Adeep ARead)
          (borrowed_place_error "cannot access" "Eplace of transfer_pure_expr" p))
  | Eref org mut p ty =>
      let ak := mut_to_access_kind mut in
      let msg :=
        alarm_if (illegal_access e p Adeep ak)
          (borrowed_place_error "cannot access" "Eref of transfer_pure_expr" p) in
      let support_orgs := support_origins p in
      let org_st := LOrgEnv.aggregate_origin_states e support_orgs in
      let s' := LOrgLnSt.lub org_st (LOrgLnSt.Live (LoanSet.singleton (Lintern mut p))) in
      Log.with_log (LOrgEnv.add org s' e) msg
  | Ecktag p id =>
      Log.with_log e
        (alarm_if (illegal_access e p Ashallow ARead)
          (borrowed_place_error "cannot access" "Ecktag of transfer_pure_expr" p))
  | Eunop _ pe _ =>
      transfer_pure_expr e pe
  | Ebinop _ pe1 pe2 _ =>
      logdo e' <- transfer_pure_expr e pe1;
      transfer_pure_expr e' pe2
  | _ => Log.ret e
  end.

Definition transfer_expr (oe: LOrgEnv.t) (e: expr) : Log.mon LOrgEnv.t :=
  match e with
  | Emoveplace p ty =>
      Log.with_log oe
        (alarm_if (illegal_access oe p Adeep AWrite)
          (borrowed_place_error "cannot access" "Emoveplace of transfer_expr" p))
  | Epure pe =>
      transfer_pure_expr oe pe
  end.

Fixpoint transfer_exprlist (oe: LOrgEnv.t) (l: list expr) : Log.mon LOrgEnv.t :=
  match l with
  | [] => Log.ret oe
  | e :: l' =>
      logdo oe' <- transfer_expr oe e;
      transfer_exprlist oe' l'
  end.

Definition check_shallow_write_place (e: LOrgEnv.t) (p: place) : errmsg :=
  alarm_if (illegal_access e p Ashallow AWrite)
    (borrowed_place_error "cannot write to" "shallow_write_place" p).

Definition kill_place_related_loans (p: place) (st: LOrgLnSt.t) : LOrgLnSt.t :=
  match st with
  | LOrgLnSt.Live ls =>
      LOrgLnSt.Live (LoanSet.filter (fun elt => match elt with
                              | Lintern _ p' => negb (is_prefix p p')
                              | _ => true
                              end) ls)
  | LOrgLnSt.Dead => LOrgLnSt.Dead
  end.

Definition kill_loans (e: LOrgEnv.t) (p: place) : LOrgEnv.t :=
  LOrgEnv.map1 (kill_place_related_loans p) e.

Definition transfer_assignment (oe: LOrgEnv.t) (p: place) (e: expr) : Log.mon LOrgEnv.t :=
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  logdo oe1 <- transfer_expr oe e;
  logdo _ <- Log.with_log tt (check_shallow_write_place oe1 p);
  let oe2 := kill_loans oe1 p in
  Log.ret (LOrgEnv.flow_loans oe2 ty_src ty_dest Covariant).

Definition transfer_assign_variant (oe: LOrgEnv.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : Log.mon LOrgEnv.t :=
  match typeof_place p with
  | Tvariant orgs_dest vid =>
      match ce!vid with
      | Some co =>
          match field_type fid (co_members co) with
          | OK ty_i =>
              let ty_src := typeof e in
              let orgs_src := co.(co_generic_origins) in
              let ty_dest := replace_origin_in_type ty_i (combine orgs_src orgs_dest) in
              logdo oe1 <- transfer_expr oe e;
              logdo _ <- Log.with_log tt (check_shallow_write_place oe1 p);
              let oe2 := kill_loans oe1 p in
              Log.ret (LOrgEnv.flow_loans oe2 ty_src ty_dest Covariant)
          | _ => Log.ret oe
          end
      | _ => Log.ret oe
      end
  | _ => Log.ret oe
  end.

Definition transfer_Sbox (oe: LOrgEnv.t) (p: place) (e: expr) : Log.mon LOrgEnv.t :=
  let ty_dest := typeof_place p in
  let ty_src := Tbox (typeof e) in
  logdo oe1 <- transfer_expr oe e;
  logdo _ <- Log.with_log tt (check_shallow_write_place oe1 p);
  let oe2 := kill_loans oe1 p in
  Log.ret (LOrgEnv.flow_loans oe2 ty_src ty_dest Covariant).

Definition flow_loans_origin_to_origin (se te: LOrgEnv.t) (src tgt: origin) : LOrgEnv.t :=
  LOrgEnv.set tgt (LOrgLnSt.lub (LOrgEnv.get src se) (LOrgEnv.get tgt te)) te.

Definition after_call (fe: LOrgEnv.t) (rels: list origin_rel) : LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               flow_loans_origin_to_origin fe acc src tgt) rels fe.

Fixpoint no_sameclass (uf: UFD.t) (l : list origin) : bool :=
  match l with
  | [] => true
  | x :: xs =>
      forallb (fun y => negb (peq (UFD.repr uf x) (UFD.repr uf y))) xs
      && no_sameclass uf xs
  end.

Definition transfer_function_call (oe1: LOrgEnv.t) (p: place) (ef: expr) (args: list expr) : Log.mon LOrgEnv.t :=
  match (typeof ef) with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let args_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      logdo oe2 <- transfer_exprlist oe1 args;
      let oe3 := LOrgEnv.flow_loans_list oe2 args_tyl sig_tyl Covariant in
      let msg :=
        if no_sameclass (LOrgEnv.uf oe3) orgs then
          nil
        else
          [MSG "There is some generic region that may not be a singleton when calling a function"] in
      logdo _ <- Log.with_log tt msg;
      let oe4 := after_call oe3 org_rels in
      logdo _ <- Log.with_log tt (check_shallow_write_place oe4 p);
      let oe5 := kill_loans oe4 p in
      Log.ret (LOrgEnv.flow_loans oe5 rty tgt_rety Covariant)
  | _ => Log.ret oe1
  end.

End COMP_ENV.

Definition transfer_storagedead (f: function) (oe1: LOrgEnv.t) (id: ident) : Log.mon LOrgEnv.t :=
  match find_elt id f.(fn_vars) with
  | Some ty =>
      let p := Plocal id ty in
      Log.with_log (kill_loans oe1 p) (check_shallow_write_place oe1 p)
  | None => Log.ret oe1
  end.

Definition transfer_drop (oe1: LOrgEnv.t) (p: place) : Log.mon LOrgEnv.t :=
  Log.with_log oe1
    (alarm_if (illegal_access oe1 p Adeep AWrite)
      (borrowed_place_error "cannot drop" "check_drop" p)).

Definition live_origin (st: LOrgLnSt.origin_state) : bool :=
  match st with
  | LOrgLnSt.Live _ => true
  | LOrgLnSt.Dead => false
  end.

Definition absence_of_internal_loans (st: LOrgLnSt.t) : bool :=
  match st with
  | LOrgLnSt.Live ls =>
      LoanSet.for_all (fun ln => match ln with
                              | Lintern _ _ => false
                              | Lextern _ => true
                              end) ls
  | _ => true
  end.

Definition check_dangling (f: function) (e: LOrgEnv.t) : bool :=
  forallb (fun org => absence_of_internal_loans (LOrgEnv.get org e)) f.(fn_generic_origins).

Definition check_generic_origins_relations (f: function) (e: LOrgEnv.t) : bool :=
  forallb (fun org1 =>
             forallb
               (fun org2 =>
                  if Pos.eqb org1 org2 then true
                  else match LOrgEnv.get org1 e with
                       | LOrgLnSt.Live ls1 =>
                           if LoanSet.mem (Lextern org2) ls1 then
                             in_dec origin_rel_eq_dec (org2, org1) f.(fn_origins_relation)
                           else true
                       | _ => false
                       end) f.(fn_generic_origins)) f.(fn_generic_origins).

Fixpoint check_storagedead_list (l: list (ident * type)) (e: LOrgEnv.t) : errmsg :=
  match l with
  | nil => nil
  | (id, ty) :: l' =>
      check_shallow_write_place e (Plocal id ty) ++ check_storagedead_list l' e
  end.

Fixpoint kill_loans_list (e: LOrgEnv.t) (l: list (ident * type)) : LOrgEnv.t :=
  match l with
  | nil => e
  | (id, ty) :: l' =>
      kill_loans_list (kill_loans e (Plocal id ty)) l'
  end.

Definition transfer_return (f: function) (oe1: LOrgEnv.t) (p: place) : Log.mon LOrgEnv.t :=
  let msg0 :=
    alarm_if (illegal_access oe1 p Adeep ARead)
      (borrowed_place_error "cannot return" "transfer_return" p) in
  let oe2 := LOrgEnv.flow_loans oe1 (typeof_place p) f.(fn_return) Covariant in
  let generic_regions := regset_fun f in
  let oe3 := LOrgEnv.apply_liveness generic_regions oe2 in
  let msg1 := check_storagedead_list (f.(fn_vars) ++ f.(fn_params)) oe3 in
  let oe4 := kill_loans_list oe3 (f.(fn_vars) ++ f.(fn_params)) in
  let msg2 :=
    if check_dangling f oe4 then
      nil
    else
      [MSG "Dangling pointer! There should not be internal loans in the generic regions at the function return"] in
  let msg3 :=
    if check_generic_origins_relations f oe4 then
      nil
    else
      [MSG "some relations in function return are not declared in the function signature"] in
  Log.with_log oe4 (msg0 ++ msg1 ++ msg2 ++ msg3).

Definition transfer_stmt ce f oe s : LOrgEnv.t * errmsg :=
  match s with
  | Sassign p e =>
      transfer_assignment oe p e
  | Sassign_variant p enum_id fid e =>
      transfer_assign_variant ce oe p enum_id fid e
  | Sbox p e =>
      transfer_Sbox oe p e
  | Scall p e l =>
      transfer_function_call oe p e l
  | Sstoragedead id =>
      transfer_storagedead f oe id
  | Sdrop p =>
      transfer_drop oe p
  | Sreturn p =>
      transfer_return f oe p
  | _ => (oe, nil)
  end.

Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (live: liveness_info) (pc: node) (before: LoansLogEnv.t) : LoansLogEnv.t :=
  match before with
  | LoansLogEnv.Bot => before
  | LoansLogEnv.State oe _ =>
      (* apply liveness result before transfer *)
      (** Should we clear dead loans before the transfer? *)
      let '(live_before, live_after) := PMap.get pc live in
      let oe := LOrgEnv.apply_liveness live_before oe in
      (* Why should we apply liveness before and after the transfer
      function? Consider a snapshot of CFG like this:

                            N1
                          N2   N3
                            N4

      (1) we need to apply liveness before the transfer because for
      the transfer on N2 and N3, if we do not apply liveness, then we
      just use the liveness result of N1 (the result of applying
      live_after on N1), which is imprecise because this liveness
      result is the join of N2 and N3. So we need to separately apply
      liveness before the transfer. This is also required in the
      checking;

      (2) we need to apply liveness after the transfer. Consider the
      transfer result of N2 and N3, if we do not apply live_after to
      them, then the result of N4 is the join result of N2 and N3 and
      then be applied to liveness. This case may cause imprecision
      because the merged node may join two equality into one equality
      (e.g., a=b and b=c would become a=b=c, if b is dead, then we
      still get a=c which is imprecise.

     Related test cases: 20.rs, 26.rs, 30.rs, 33.rs, 35.rs,
     46_aeneas_example.rs
 *)
      let finish_transfer (st: Log.mon LOrgEnv.t) := LoansLogEnv.State (LOrgEnv.apply_liveness live_after (Log.value st)) (Log.log st) in
      (* let finish_transfer oe := (LoansEnv.State oe) in *)
      match cfg ! pc with
      | None => LoansLogEnv.Bot
      | Some (Inop _) => before
      | Some (Icond e _ _) => finish_transfer (transfer_expr oe e)
      | Some Iend => before
      | Some (Isel sel next) =>
          match select_stmt f.(fn_body) sel with
          | None => LoansLogEnv.Bot
          | Some s =>
              finish_transfer (transfer_stmt ce f oe s)
          end
      end
  end.

Module LoansFlowInterp := Dataflow_Solver(LoansLogEnv)(NodeSetForward).

Definition init_function (f: function) : LOrgEnv.t :=
  let oe1 := fold_left (fun acc elt =>
                          let os := LOrgLnSt.Live (LoanSet.singleton (Lextern elt)) in
                          LOrgEnv.set elt os acc) f.(fn_generic_origins) LOrgEnv.bot in
  LOrgEnv.flow_loans_list oe1 f.(fn_param_types) (map snd f.(fn_params)) Covariant.

Definition loans_flow_analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (liveness_info * (PMap.t LoansLogEnv.t)) :=
  let generic_regions := regset_fun f in
  match RegionLiveness.analyze f cfg with
  | Some live_after =>
      let live := build_liveness_info f cfg generic_regions live_after in
      let init_oe := init_function f in
      match LoansFlowInterp.fixpoint cfg successors_instr (transfer ce f cfg live) entry (LoansLogEnv.State init_oe nil) with
      | Some m => OK (live, m)
      | None =>
          Error [MSG "The loans-flow analysis fails with unknown reason"]
      end
  | None =>
      Error [MSG "The loans-flow analysis fails due to the failure of liveness analysis"]
  end.

Definition borrow_check_stmt_aux ce (f: function) (le: LoansLogEnv.t) (stmt: statement) : res unit :=
  match le with
  | LoansLogEnv.State oe _ =>
      let (_, msg) := transfer_stmt ce f oe stmt in
      match msg with
      | nil => OK tt
      | _ => Error msg
      end
  | _ => OK tt
  end.

Definition borrow_check_stmt ce (f: function) (le: LoansLogEnv.t) (stmt: statement) : res statement :=
  do _ <- borrow_check_stmt_aux ce f le stmt;
  OK stmt.

Definition borrow_check_cond_expr (ce: composite_env) (le: LoansLogEnv.t) (e: expr) : res unit :=
  match le with
  | LoansLogEnv.State oe _ =>
      let st := transfer_expr oe e in
      match Log.log st with
      | nil => OK tt
      | _ => Error (Log.log st)
      end
  | _ => OK tt
  end.

Definition get_borck_result (live_loan_env: (liveness_info * (PMap.t LoansLogEnv.t))) (pc: node) : LoansLogEnv.t :=
  let (live, loan_env) := live_loan_env in
  match loan_env !! pc with
  | LoansLogEnv.Bot => LoansLogEnv.Bot
  | LoansLogEnv.State oe _ =>
      (* Why do we need to apply liveness here to do transfer?
      Transfer function already applies liveness, isn't it? Because we
      do not invoke transfer in the checking phase, we apply
      transfer_stmt due to the limitation of transl_on_cfg. So we need
      to ad-hocly simulate how transfer is implemented *)
      let '(live_before, live_after) := PMap.get pc live in
      LoansLogEnv.State (LOrgEnv.apply_liveness live_before oe) nil
  end.

Definition collect_borrow_check_result ce (f: function) (cfg: rustcfg) (loans_flow_res: (liveness_info * (PMap.t LoansLogEnv.t))) : res unit :=
  do _ <- transl_on_cfg get_borck_result (loans_flow_res) (borrow_check_stmt ce f) (borrow_check_cond_expr ce) f.(fn_body) cfg;
  OK tt.

Definition borrow_check_function (ce: composite_env) (f: function) : Errors.res unit :=
  do (entry, cfg) <- generate_cfg f.(fn_body);
  let generic_regions := regset_fun f in
  do loans_flow_res <- loans_flow_analyze ce f cfg entry;
  collect_borrow_check_result ce f cfg loans_flow_res.

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

Definition borrow_check_program (p: program) : res unit :=
  do _ <- transform_partial_program2 (transf_fundef p.(prog_comp_env)) transl_globvar p;
  OK tt.
