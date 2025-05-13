Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR RustIRcfg.
Require Import Errors.
Require Import BorrowCheckDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on Polonius (dataflow analysis) *)

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at pc "; POS pc; MSG " : "].


(** Initialization *)

Definition init_function (f: function) : AE.t :=
  let live_loans := fold_left (fun acc elt => LoanSet.add (Lextern elt) acc) f.(fn_generic_origins) LoanSet.empty in
  let init_origin_env := fold_left (fun acc elt =>
                                let os := Live (LoanSet.singleton (Lextern elt)) in
                                LOrgEnv.set elt os acc) f.(fn_generic_origins) (PTree.empty LOrgSt.t) in
  AE.State live_loans init_origin_env LAliasGraph.bot.

(* initialize the variable origins *)

Definition init_variables (ae: AE.t) (f: function) : res AE.t :=
  match ae with
  | AE.Err _ _ => Error (msg "Unknown error occurs before initialize variables' origin environment")
  | AE.Bot =>
      let tys := map snd f.(fn_vars) in
      (* For all origins in the variable type, set its state to Live(∅) *)
      let orgs := concat (map origins_of_type tys) in
      let oe := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs (PTree.empty LOrgSt.t) in
      OK (AE.State LoanSet.empty oe LAliasGraph.bot)
  | AE.State ls oe a =>
      let tys := map snd f.(fn_vars) in
      (* For all origins in the variable type, set its state to Live(∅) *)
      let orgs := concat (map origins_of_type tys) in
      let oe' := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs oe in
      OK (AE.State ls oe' a)
  end.

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


Fixpoint transfer_pure_expr (pc: node) (live: LoanSet.t) (e: LOrgEnv.t) (pe: pexpr) : res (LoanSet.t * LOrgEnv.t) :=
  match pe with
  | Eplace p ty =>
      (* simple type check *)
      if type_eq (typeof_place p) ty then
        (* check all the loans in this place are not invalidated *)
        if valid_access e p then
          (* invalide origins contain loans relevant to [p] *)
          let ls := relevant_loans live p Adeep in
          let e' := invalidate_origins ls Aread e in
          OK (live, e')
        else
          Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG " in Eplace"])
      else
        Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Eplace"])
  | Eref org mut p ty =>
      (* simple type check *)
      match ty with
      | Treference org' mut' _ =>
          (* type checking *)
          if Pos.eqb org org' && mutkind_eq mut mut' then
            (* mut' = Mutable implies (mutable_place p), i.e., mutability checking *)
            if negb (mutkind_eq mut' Mutable) || mutable_place p then
              let ak := match mut with | Mutable => Awrite | Immutable => Aread end in
              (* check all the loans in this place are not
              invalidated, i.e., borrow checking *)
              if valid_access e p then
                (* invalide origins contain loans relevant to [p] *)
                let ls := relevant_loans live p Adeep in
                let e' := invalidate_origins ls ak e in
                (* add Lintern(mut,p) to live loans *)
                let live' := LoanSet.add (Lintern mut p) live in
                (* handle reborrow: add all the loans in the support
              prefix to org *)
                let support_orgs := support_origins p in
                (* aggregate the loans in the support origins *)
                let org_st := aggregate_origin_states e' support_orgs in
                (* FIXME: is it correct to just combine two state? *)
                let s' := LOrgSt.lub org_st (Live (LoanSet.singleton (Lintern mut p))) in
                let e'' := LOrgEnv.set org s' e' in
                OK (live', e'')
                (* match org_st with *)
                (* | Dead => Error (error_msg pc ++ [MSG "there is invalid origin in the support prefixes of ";CTX (local_of_place p)]) *)
                (* | Live s => *)
                (*     (* Don't forget to add {Lintern mut p} *) *)
                (*     let s' := LoanSet.add (Lintern mut p) s in *)
                (*     let e'' := LOrgEnv.set org (Live s') e' in *)
                (*     OK (live', e'') *)
                (* end *)
              else
                Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p)])
            else Error (error_msg pc ++ [MSG "try to create a mutable reference of an immutable place (transfer_pure_expr)"])
          else
            Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Eref"])
      | _ => Error (error_msg pc ++ [MSG "reference expression is not of reference type in Eref"])
      end
  | Ecktag p id =>
      (* simple type check *)
      match typeof_place p with
      | Tvariant _ _ =>
          if valid_access e p then
            (* invalide origins contain loans relevant to [p] *)
            let ls := relevant_loans live p Ashallow in
            let e' := invalidate_origins ls Aread e in
            OK (live, e')
          else
            Error (error_msg pc ++ [MSG "access an invalid place "; CTX (local_of_place p); MSG "in Ecktag"])
      | _ => Error (error_msg pc ++ [MSG "type of operand is not Tvariant in Ecktag"])
      end
  | Eunop _ pe _ =>
      transfer_pure_expr pc live e pe
  | Ebinop _ pe1 pe2 _ =>
      do (live', e') <- transfer_pure_expr pc live e pe1;
      transfer_pure_expr pc live' e' pe2
  (* Other constants *)
  | _ => OK (live, e)
  end.                      

(* transfer expression *)

Definition transfer_expr (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (e: expr) : res (LoanSet.t * LOrgEnv.t) :=
  match e with
  | Emoveplace p ty =>
      (* simple type check *)
      if type_eq (typeof_place p) ty then
        (* check all the loans in this place are not invalidated *)
        if valid_access oe p then
          (* invalide origins contain loans relevant to [p] *)
          let ls := relevant_loans live p Adeep in
          (* move a place is a deep write access *)
          let oe' := invalidate_origins ls Awrite oe in
          OK (live, oe')
        else
          Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG " in Emoveplace"])
      else
        Error (error_msg pc ++ [MSG "mismatch between expression type and place type in Emoveplace"])
  | Epure pe =>
      transfer_pure_expr pc live oe pe
  end.

Fixpoint transfer_exprlist (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (l: list expr) : res (LoanSet.t * LOrgEnv.t) :=
  match l with
  | [] => OK (live, oe)
  | e :: l' =>
      do (live', oe') <- transfer_expr pc live oe e;
      transfer_exprlist pc live' oe' l'
  end.


(* Flowing loans from source type to destination type *)

Inductive flow_kind : Type := ByVal | ByRef.

Fixpoint flow_loans (pc: node) (e: LOrgEnv.t) (g: LAliasGraph.t) (s d: type) (k: flow_kind) : res (LOrgEnv.t * LAliasGraph.t) :=
  match s,d with
  | Treference org1 _ ty1, Treference org2 _ ty2 =>
      do (e', g1) <- flow_loans pc e g ty1 ty2 ByRef;      
      let g2 := match k with | ByVal => g1 | ByRef => set_alias org1 org2 g1 end in
      let st := LOrgSt.lub (LOrgEnv.get org1 e') (LOrgEnv.get org2 e') in
      (* flow st1 to st2 *)
      match st with
      | Live ls =>
          let e'' := set_loans_with_alias org2 ls e' g2 in
          OK (e'', g2)
      | Obot =>
          Error (error_msg pc ++ [MSG "the src/dest origin is bot in flow_loans: source org is "; CTX org1; MSG " target org is "; CTX org2])
      | Dead =>
          Error (error_msg pc ++ [MSG "the src/dest origin is invalid in flow_loans: source org is "; CTX org1; MSG " target org is "; CTX org2])
      end
  | Tbox ty1, Tbox ty2 =>
      flow_loans pc e g ty1 ty2 ByRef
  | Tstruct orgs1 id1, Tstruct orgs2 id2 
  | Tvariant orgs1 id1 , Tvariant orgs2 id2 =>
      if Nat.eqb (length orgs1) (length orgs2) then
        let orgs := combine orgs1 orgs2 in
        (* set alias between orgs1 and orgs2 *)
        let g' := match k with
                  | ByVal => g
                  | ByRef =>
                      fold_left
                        (fun acc '(org1, org2) => set_alias org1 org2 acc)
                        orgs g
                  end in
        (* flow loans from orgs1 to orgs2 *)
        let stl := map (fun '(org1, org2) => LOrgSt.lub (LOrgEnv.get org1 e) (LOrgEnv.get org2 e)) orgs in
        do e' <- fold_left
                    (fun acc '(org, st) =>
                       do acc' <- acc;
                       match st with
                       | Live ls =>
                           OK (set_loans_with_alias org ls acc' g')
                       | _ =>
                           Error (error_msg pc ++ [CTX org; MSG "the src/dest origin is invalid in (flow_loans Tvariant/Tstruct): target org is "; CTX org])
                       end) (combine orgs2 stl) (OK e);
        OK (e', g')
      else Error (error_msg pc ++ [MSG "mismatch between the length of origins in type"; CTX id1])
  (* scalar type *)
  | _, _ => OK (e, g)
  end.
      
          
(* Shallow write a place *)

Definition shallow_write_place (f: function) (pc: node) (live: LoanSet.t) (e: LOrgEnv.t) (g: LAliasGraph.t) (p: place) : res (LOrgEnv.t * LAliasGraph.t) :=
  let ls := relevant_loans live p Ashallow in
  let e' := invalidate_origins ls Awrite e in
  (* let e' := e in *)
  match p with
  | (Plocal id ty) =>
      (* no need to check the valid access, because id will be overwrited *)
      if in_dec ident_eq id (var_names f.(fn_vars)) then
        (* this place is a local variable, we can kill its loans *)          
        (* remove the loans and alias edges for the origin in the type of p *)
        let orgs := origins_of_type ty in
        (* remove loans *)
        let e'' := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs e' in
        (* remove alias *)
        let g' := fold_left (fun acc elt => remove_alias elt acc) orgs g in
        OK (e'', g')
      else
        OK (e', g)
  | _ =>
      if valid_access e p then
        OK (e', g)
      else  Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG " in (shallow_write_place)"])    
  end.


(* Auxilary functions for transition of statements *)

Definition kill_loans (live: LoanSet.t) (p: place) : LoanSet.t :=
  LoanSet.filter (fun elt => match elt with
                          | Lintern _ p' => negb (is_prefix p p')
                          | _ => true
                          end) live.

(* Borrow check an assign statement *)

Definition check_assignment (f: function) (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (ag: LAliasGraph.t) (p: place) (e: expr) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  (* simple type checking *)
  let ty_dest := typeof_place p in
  let ty_src := typeof e in
  if type_eq_except_origins ty_dest ty_src && mutable_place p then
    (* check the expression *)
    do (live1, oe1) <- transfer_expr pc live oe e;
    (* shallow write to the place, it will check the validity of p *)
    do (oe2, ag1) <- shallow_write_place f pc live1 oe1 ag p;
    (* kill the loans of which [p] is prefix *)
    let live2 := kill_loans live1 p in
    (* flows the loans from src type to dest type *)
    do (oe3, ag2) <- flow_loans pc oe2 ag1 ty_src ty_dest ByVal;
    OK (live2, oe3, ag2)
  else
    Error (error_msg pc ++ [MSG "type checking error in assignment"])
.      


Definition check_assign_variant (ce: composite_env) (f: function) (pc: node) (live: LoanSet.t) (oe: LOrgEnv.t) (ag: LAliasGraph.t) (p: place) (enum_id: ident) (fid: ident) (e: expr) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  match typeof_place p with
  | Tvariant orgs_dest vid =>
      if Pos.eqb enum_id vid then
        match ce!vid with
        | Some co =>
            match find (fun '(Member_plain fid' _) => Pos.eqb fid fid') co.(co_members) with
            | Some memb =>
                let ty_i := type_member memb in
                let ty_src := typeof e in
                if type_eq_except_origins ty_src ty_i then
                  let orgs_src := co.(co_generic_origins) in
                  let ty_dest := replace_origin_in_type ty_i (combine orgs_src orgs_dest) in
                  if mutable_place p then
                    (* check the expression *)
                    do (live1, oe1) <- transfer_expr pc live oe e;
                    (* shallow write to the place, it will check the validity of p *)
                    do (oe2, ag1) <- shallow_write_place f pc live1 oe1 ag p;
                    (* kill the loans of which [p] is prefix *)
                    let live2 := kill_loans live1 p in
                    (* flows the loans from src type to dest type *)
                    do (oe3, ag2) <- flow_loans pc oe2 ag1 ty_src ty_dest ByVal;
                    OK (live2, oe3, ag2)
                  else
                    Error (error_msg pc ++ [MSG "place is not mutable in check_assign_variant"])
                else
                  Error (error_msg pc ++ [MSG "type checking error in check_assign_variant"])
            | _ =>
                Error (error_msg pc ++ [MSG "cannot find the field of this variant (check_assign_variant)"])
            end
        | _ =>
            Error (error_msg pc ++ [MSG "cannot find the variant (check_assign_variant)"])
        end
      else Error (error_msg pc ++ [MSG "enum id mismatch between LHS and RHS (check_assign_variant)"])
  | _ =>
      Error (error_msg pc ++ [MSG "target is not a variant (check_assign_variant)"])
  end.
  
(* bind the origins in two type *)
Fixpoint bind_type_origins (pc: node) (ty1 ty2: type) (fk: flow_kind) : res (list (origin * origin * flow_kind)) :=
  match ty1, ty2 with
  | Treference org1 _ ty1, Treference org2 _ ty2 =>
      do l' <- bind_type_origins pc ty1 ty2 ByRef;
      OK ((org1, org2, fk) :: l')
  | Tbox ty1, Tbox ty2 =>
      bind_type_origins pc ty1 ty2 ByRef
  | Tstruct orgs1 id1, Tstruct orgs2 id2
  | Tvariant orgs1 id1, Tvariant orgs2 id2 =>
      if Nat.eqb (length orgs1) (length orgs2) then
        let len := length orgs1 in
        OK (combine (combine orgs1 orgs2) (repeat fk len))
      else
        Error (error_msg pc ++ [MSG "mismatch between the length of origins in type"; CTX id1; MSG "(bind_type_origins)"])
  | _, _ => OK []
  end.


Definition flow_loans_origin_to_origin (pc: node) (se te: LOrgEnv.t) (src tgt: origin) : res LOrgEnv.t :=
  match LOrgEnv.get src se, LOrgEnv.get tgt te with
  | Live ls1, Live ls2 =>
      let te' := LOrgEnv.set tgt (Live (LoanSet.union ls1 ls2)) te in
      OK te'
  | _, _ =>
      Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin"])
  end.

Definition flow_loans_origin_to_origin_with_alias (pc: node) (ag: LAliasGraph.t) (se te: LOrgEnv.t) (src tgt: origin) : res LOrgEnv.t :=
  match LOrgEnv.get src se, LOrgEnv.get tgt te with
  | Live ls1, Live ls2 =>
      let te' := set_loans_with_alias tgt (LoanSet.union ls1 ls2) te ag in
      OK te'
  | _, _ =>
      Error (error_msg pc ++ [CTX src; CTX tgt; MSG "flow_loans_origin_to_origin_with_alias"])
  end.

Definition flow_loans_bind_acc (pc: node) (se: LOrgEnv.t) (acc: res (LOrgEnv.t * list origin_rel)) (elt: origin * origin * flow_kind) : res (LOrgEnv.t * list origin_rel) :=
  let '(src, tgt, fk) := elt in
  do (te, rels) <- acc;
  do te' <- flow_loans_origin_to_origin pc se te src tgt;
  match fk with
  | ByRef =>
      OK (te', (tgt, src) :: rels)
  | ByVal =>
      OK (te', rels)
  end.
                                        

Definition bind_param_origins (pc: node) (e: LOrgEnv.t) (fe: LOrgEnv.t) (tyl ftyl: list type) : res (LOrgEnv.t * list origin_rel) :=
  if Nat.eqb (length ftyl) (length tyl) then    
    do bind_pairs <- fold_left (fun acc '(src_ty, tgt_ty) =>
                                 do acc' <- acc;
                                 do l <- bind_type_origins pc src_ty tgt_ty ByVal;
                                 OK (acc' ++ l)) (combine tyl ftyl) (OK []);    
    fold_left (flow_loans_bind_acc pc e) bind_pairs (OK (fe, nil))
  else
    Error (error_msg pc ++ [MSG "mismatch between the lengths of types (bind_param_origins)"]).
    
Definition after_call (pc: node) (e: LOrgEnv.t) (rels: list origin_rel) : res LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               do acc' <- acc;
               (* it may be less efficient *)
               flow_loans_origin_to_origin pc acc' acc' src tgt) rels (OK e).

Definition flow_alias_after_call (pc: node) (ag: LAliasGraph.t) (rels: list origin_rel) (se te: LOrgEnv.t) : res LOrgEnv.t :=
  fold_left (fun acc '(src, tgt) =>
               do acc' <- acc;
               flow_loans_origin_to_origin_with_alias pc ag se acc' src tgt)
            rels (OK te).

  
Definition flow_return_after_call (pc: node) (ag: LAliasGraph.t) (se te: LOrgEnv.t) (frety tgt_ty: type) : res LOrgEnv.t :=
  do l <- bind_type_origins pc frety tgt_ty ByVal;
  (* we do not care the alias relation *)
  do (te', _) <- fold_left (flow_loans_bind_acc pc se) l (OK (te, nil));
  OK te'.


Definition check_function_call (f: function) (pc: node) (live1: LoanSet.t) (oe1: LOrgEnv.t) (ag1: LAliasGraph.t) (p: place) (fty: type) (args: list expr) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  match fty with
  | Tfunction orgs org_rels tyl rty cc =>
      let sig_tyl := type_list_of_typelist tyl in
      let arg_tyl := map typeof args in
      let tgt_rety := (typeof_place p) in
      (* check the arguments *)
      do (live2, oe2) <- transfer_exprlist pc live1 oe1 args;
      (* consider variant argument length function (just printf for now) *)
      match cc.(cc_vararg) with
      | Some _ =>
          (* Adhoc: If this function has variant-length arguments, we ignore it *)
          OK (live2, oe2, ag1)
      | None =>
          if forallb (fun '(ty1, ty2) => type_eq_except_origins ty1 ty2) (combine arg_tyl sig_tyl) && type_eq_except_origins tgt_rety rty then
            (* construct empty origin environments for function origins *)
            let foe1 := fold_left (fun acc elt => LOrgEnv.set elt (Live LoanSet.empty) acc) orgs (PTree.empty LOrgSt.t) in
            do (foe2, rels) <- bind_param_origins pc oe2 foe1 arg_tyl sig_tyl;
            (* use the origin relation to simulate the flow of loans
               in the caller. foe2 is the initial env in the callee,
               foe3 is the final env *)
            do foe3 <- after_call pc foe2 org_rels;
            (* shallow write to p *)
            do (oe3, ag2) <- shallow_write_place f pc live2 oe2 ag1 p;
            (* kill relevant loans *)
            let live3 := kill_loans live2 p in
            (* flow loans to the return type and update alias *)
            do oe4 <- flow_alias_after_call pc ag2 rels foe3 oe3;
            do oe5 <- flow_return_after_call pc ag2 foe3 oe4 rty tgt_rety;
            OK (live3, oe5, ag2)
          else
            Error (error_msg pc ++ [MSG "type checking fails in check_function_call"])
      end
  | _ => Error (error_msg pc ++ [MSG "it is not a function type in check_function_call"])      
  end.
          

Definition check_drop (f: function) (pc: node) (live1: LoanSet.t) (oe1: LOrgEnv.t) (ag1: LAliasGraph.t) (p: place) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  if valid_access oe1 p then
    let ls := relevant_loans live1 p Adeep in
    let oe2 := invalidate_origins ls Awrite oe1 in
    OK (live1, oe2, ag1)
  else Error (error_msg pc ++ [MSG "access an invalidated place "; CTX (local_of_place p); MSG "in (check_drop)"]).


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

Definition check_generic_origins_relations (f: function) (e: LOrgEnv.t) : bool :=
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
                             (* generic origins must be live *)
                             | _, _ => false
                             end) f.(fn_generic_origins)) f.(fn_generic_origins).
  

Definition check_return_expr (pc: node) (live1: LoanSet.t) (oe1: LOrgEnv.t) (ag1: LAliasGraph.t) (e: expr) (rety: type) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  let ty_src := typeof e in
  if type_eq_except_origins ty_src rety then
    do (live2, oe2) <- transfer_expr pc live1 oe1 e;
    do (oe3, ag2) <- flow_loans pc oe2 ag1 ty_src rety ByVal;
    OK (live2, oe3, ag2)
  else
    Error (error_msg pc ++ [MSG "type error in function return"]).


Definition check_return (f: function) (pc: node) (live1: LoanSet.t) (oe1: LOrgEnv.t) (ag1: LAliasGraph.t) (e: option expr) (rety: type) : res (LoanSet.t * LOrgEnv.t * LAliasGraph.t) :=
  match e with
  | Some e =>      
      do r <- check_return_expr pc live1 oe1 ag1 e rety;
      let '(live2, oe2, ag2) := r in     
      OK (live2, oe2, ag2)
  | None =>
      (* simple type checking *)
      if type_eq Tunit f.(fn_return) then
        OK (live1, oe1, ag1)
      else
        Error (error_msg pc ++ [MSG "no return value but return type is not Tunit!"])
  end.


Definition finish_check (pc: node) (r: res (LoanSet.t * LOrgEnv.t * LAliasGraph.t)) : AE.t :=
  match r with
  | OK (live, oe, ag) => AE.State live oe ag
  | Error msg =>
      AE.Err pc msg
  end.

(* Transition of statements *)
        
Definition transfer (ce: composite_env) (f: function) (cfg: rustcfg) (pc: node) (before: AE.t) : AE.t :=
  match before with
  | AE.Bot => AE.Bot
  | AE.Err pc' msg =>
      (* Error propagation: pc' is the source of this error *)
      AE.Err pc' msg
  | AE.State live oe ag =>
      match cfg ! pc with
      | None => AE.bot
      | Some (Inop _) => before
      | Some (Icond e _ _) =>
          match transfer_expr pc live oe e with
          | OK (live', oe') =>
              AE.State live' oe' ag
          | Error msg =>
              AE.Err pc msg
          end
      | Some Iend =>
          if check_generic_origins_relations f oe then
            before
          else
            AE.Err pc [MSG "some relations in function return are not declared in the function sigature"]
      | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => AE.bot
          | Some s =>
              match s with
              | Sassign p e =>
                  let check_result := check_assignment f pc live oe ag p e in
                  finish_check pc check_result
              | Sassign_variant p enum_id fid e =>
                  let check_result := check_assign_variant ce f pc live oe ag p enum_id fid e in
                  finish_check pc check_result
              | Scall p e l =>
                  match e with
                  | Epure (Eplace (Plocal fid fty) _) =>
                      let check_result := check_function_call f pc live oe ag p fty l in
                      finish_check pc check_result
                  | _ => AE.Err pc [MSG "unsupported function call"]
                  end
              | Sstoragedead id =>
                  match find_elt id f.(fn_vars) with
                  | Some ty =>
                      match shallow_write_place f pc live oe ag (Plocal id ty) with
                      | OK (oe', ag') => AE.State live oe' ag'
                      | Error msg => AE.Err pc msg
                      end
                  | None =>
                      AE.Err pc [CTX id; MSG "no such variable in storagedead"]
                  end
              | Sdrop p =>
                  let check_result := check_drop f pc live oe ag p in
                  finish_check pc check_result
              | Sreturn e =>
                  let check_result := check_return f pc live oe ag e f.(fn_return) in
                  (* check origin relation. We cannot check it in Iend
                  because it would not update the final AE because
                  there is not successor for Iend. Or we can move it
                  the borrow_check function, but for now we want to
                  see the analysis result in CFG *)
                  match check_result with
                  | OK (live, oe, ag) =>
                      if check_generic_origins_relations f oe then
                        AE.State live oe ag
                      else
                        AE.Err pc [MSG "some relations in function return are not declared in the function signature"]
                  | Error msg =>
                      AE.Err pc msg
                  end
              | _ => before
              end
          end
      end
  end.


(** Run Borrow Checking! *)

Module DS := Dataflow_Solver(AE)(NodeSetForward).

Definition borrow_check (ce: composite_env) (f: function) : res (PTree.t AE.t) :=
  let ae := init_function f in
  do ae' <- init_variables ae f;
  (* generate cfg *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** forward dataflow *)
  match DS.fixpoint cfg successors_instr (transfer ce f cfg) entry ae' with
  | Some (_, r) =>
      (** TODO: check origin relations  *)
      OK r
  | None =>
      Error [MSG "The borrow check fails with unknown reason"]
  end.


Definition do_borrow_check (ce: composite_env) (f: function) : res unit :=
  do t <- borrow_check ce f;
  let l := PTree.elements t in
  (* find the first error message *)
  match find (fun '(pc, am) => match am with | AE.Err _ _ => true | _ => false end) l with
  | Some (_, AE.Err _ msg) =>
      Error msg
  | _ =>
      OK tt
  end.

Definition transf_fundef (ce: composite_env) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match do_borrow_check ce f with
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
