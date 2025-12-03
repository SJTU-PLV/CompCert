Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import FSetWeakList DecidableType.
Require Import Lattice Kildall.
Require Import Rusttypes Rustlight RustIR.
Require Import Errors.
Require Import StkborDomain.

Import ListNotations.
Open Scope error_monad_scope.

(** ** Borrow checking based on abstract interpretation *)

Module RUST_TYPE <: EQUALITY_TYPE.
  Definition t := type.
  Definition eq := type_eq.
End RUST_TYPE.
  
Module TyMap := EMap(RUST_TYPE).

Definition error_msg (pc: node) : errmsg :=
  [MSG "error at "; CTX pc; MSG " : "].


(** Abstract environment which records the block id for each owner place *)

Record aenv := build_aenv
{ aenv_symbtbl: PlaceMap.t (option positive);
  aenv_nextblock: positive; }.

Definition init_aenv := build_aenv (PlaceMap.init (@None positive)) 1%positive.

Section COMPOSITE_ENV.

Variable ce: composite_env.

(* [p] is an owner or a slice of an owner. If [p] stores a location to
another owner (heap memory block in our setting) then add [*p] to the
result *)
Fixpoint owner_places' (fuel: nat) (p: place) : res (list place) :=
  match fuel with
  | O => Error [CTX (local_of_place p); MSG ": running out of fuel (owenr_places')"]
  | S fuel' =>
      let rec := owner_places' fuel' in
      match typeof_place p with
      | Tbox ty' _ =>
          (* [*p] is an owner *)
          let p' := Pderef p ty' in
          do l <- rec p';
          OK (p' :: l)
      | Tstruct id _ =>
          match ce!id with
          | Some co =>
              let fields := map (fun '(Member_plain fid ty') => Pfield p fid ty') co.(co_members) in
              do l <- fold_right_bind fields rec;
              OK (concat l)
          | None => Error [CTX id; MSG ": there is no struct with this ident (owner_place')"]
          end
      | _ => OK nil
      end
  end.

Definition owner_place (var: ident * type) :=
  let (id, ty) := var in
  let p := Plocal id ty in
  do l <- owner_places' (PTree_Properties.cardinal ce) p;
  OK (p :: l).


(* add a place which occupies a heap memory block *)
Definition add_place (env: aenv) (p: place') : aenv :=
  build_aenv (PlaceMap.set p (Some env.(aenv_nextblock)) env.(aenv_symbtbl)) (Pos.succ env.(aenv_nextblock)).

Definition add_variable (env: aenv) (var : ident * type) :=
  do places <- owner_place var;
  OK (fold_left add_place places env).

(* allocate ablocks for all variables *)
Definition add_variables (env: aenv) (vars : list (ident * type)) :=
  fold_left (fun acc elt => do acc' <- acc; add_variable acc' elt) vars (OK env).

End COMPOSITE_ENV.


Section ANEV.

Variable (ae: aenv).  

Section SHALLOW_INIT.

Let t := TyMap.t (option ablock) ->
         place' ->
         type ->
         ablock ->
         path ->
         amem ->
         positive ->
         positive ->
         res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)).
  
Variable ce: composite_env.
  
Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> t.

Definition shallow_initialize' (shr_map: TyMap.t (option ablock)) (p: place') (ty: type) (b: ablock) (ph: path) (m: amem) (next_extern: positive) (next_tag: positive) :  res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)) :=
  match ty with
  | Tunit
  | Tint _ _ _
  | Tlong _ _
  | Tfloat _ _
  | Tfunction _ _ _ =>
      do m' <- store m b ph Scalar;
      OK (m', next_extern, next_tag, shr_map, [])
  | Tbox ty' _ =>
      (* Find the Heap block id for [*p] *)
      match PlaceMap.get (Pderef p ty') ae.(aenv_symbtbl) with
      | Some heap_id =>
          (* allocate the [Heap id] *)
          do (b', m1) <- alloc_heap_block ce m ty' heap_id;
          (* the abstract owned pointer is (b', []) *)
          let av := Own b' in
          do m2 <- store m1 b ph av;
          (* initialize b' *)
          OK (m2, next_extern, next_tag, shr_map, [(b', ty')])          
      | None =>
          Error [CTX (local_of_place' p); MSG ": cannot find the heap block for this place (shallow_initialize')"]
      end      
  | Treference ty' Mutable _ =>
      (* allocate an external block for ty' *)
      do (b', m1) <- alloc_external_block ce m ty' next_extern;
      (* update the borrow tree in b' *)
      do (ap, m2) <- create_reference_from_owner Mutable b' [] (Textern next_tag) m1;
      (* the abstract pointer is (b', [], Textern next_tag) *)
      let av := Ptr (Aptrs.singleton ap) in
      do m3 <- store m2 b ph av;
      (* initialize b' *)
      OK (m3, Pos.succ next_extern, Pos.succ next_tag, shr_map, [(b', ty')])
  | Treference ty' Immutable _ =>
      (* if [&ty'] has appeared and has been allocated *)
      match TyMap.get ty' shr_map with
      | Some b' =>
          (* update the borrow tree in b' *)
          (** TODO: here we do not consider annoated origins and
              there subset relation, so we just push tag on top of the
              onwer. If we have t1 ⊆ t2 then we can push t2 on top of
              t1 *)
          do (ap, m') <- create_reference_from_owner Immutable b' [] (Textern next_tag) m;
          let av := Ptr (Aptrs.singleton ap) in
          do m'' <- store m' b ph av;
          (** FIXME: do we need to update the contents in b'? I
              think we do not need to do that because b' must be
              already initialized *)
          OK (m'', next_extern, Pos.succ next_tag, shr_map, [])
      | None =>
          (* allocate an external block for ty' *)
          do (b', m1) <- alloc_external_block ce m ty' next_extern;
          (* update the borrow tree in b' *)
          do (ap, m2) <- create_reference_from_owner Immutable b' ph (Textern next_tag) m1;
          (* the abstract pointer is (b', [], Textern next_tag) *)
          let av := Ptr (Aptrs.singleton ap) in
          do m3 <- store m2 b [] av;
          (* initialize b', remember to use a new shr_map *)              
          OK (m3, Pos.succ next_extern, Pos.succ next_tag, TyMap.set ty' (Some b') shr_map, [(b', ty')])
      end
  | Tstruct id _ =>
      match @get_composite ce id with
      | co_some _ i co P =>
          let f acc '(Member_plain fid ty') :=
            do r1 <- acc;              
            let '(m1, next_extern1, next_tag1, shr_map1, l1) := r1 in
            (* shallow initialize this field *)
            do r2 <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) shr_map (Pfield p fid ty') ty' b (ph ++ [Rfield fid]) m1 next_extern1 next_tag1;
            let '(m2, next_extern2, next_tag2, shr_map2, l2) := r2 in
            OK (m2, next_extern2, next_tag2, shr_map2, l1 ++ l2) in
          fold_left f co.(co_members) (OK (m, next_extern, next_tag, shr_map, []))
      | co_none _ =>
          Error [CTX id; MSG ": cannot get this struct type, maybe it is used in a wrong recursive manner? (shallow initialize)"]
      end
  | Tvariant id _ =>
      match @get_composite ce id with
      | co_some _ i co P =>
          let f acc '(Member_plain fid ty') :=
            do r1 <- acc;              
            let '(m1, next_extern1, next_tag1, shr_map1, l1) := r1 in
            (* shallow initialize this field *)
            do r2 <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) shr_map ty' b (ph ++ [Renum fid]) m1 next_extern1 next_tag1;
            let '(m2, next_extern2, next_tag2, shr_map2, l2) := r2 in
            OK (m2, next_extern2, next_tag2, shr_map2, l1 ++ l2) in
          fold_left f co.(co_members) (OK (m, next_extern, next_tag, shr_map, []))
      | co_none _ =>
          Error [CTX id; MSG ": cannot get this enum type, maybe it is used in a wrong recursive manner? (shallow initialize)"]
      end
  end.          

End SHALLOW_INIT.

Import Wfsimpl.

Definition shallow_initialize ce : TyMap.t (option ablock) ->
                                   place' ->
                                   type ->
                                   ablock ->
                                   path ->
                                   amem ->
                                   positive ->
                                   positive ->
                                   res (amem * positive * positive * TyMap.t (option ablock) * list (ablock * type)) :=
  Fixm (@PTree_Properties.cardinal composite) shallow_initialize' ce.

Section COMPOSITE_ENV.

Variable ce: composite_env.  

(** Deeply initialize an abstract block [b] for a function parameter
with type [ty]. Do not know how to specify the recursive parameters *)

Fixpoint deep_initialize (fuel: nat) (shr_map: TyMap.t (option ablock)) (rec_map: TyMap.t (option aval)) (p: place') (ty: type) (b: ablock) (m: amem) (next_extern: positive) (next_tag: positive) : res (amem * positive * positive * TyMap.t (option ablock)) :=
  match fuel with
  | O => Error [MSG "Running out of fuel (deep_initialize)"]
  | S fuel' =>
      (* check whether ty is a recursive type and is associated with an
         initial abstract value *)
      match TyMap.get ty rec_map with
      | Some v =>
          (* use v to initialize b *)
          do m' <- store m b [] v;
          OK (m', next_extern, next_tag, shr_map)
      | None =>       
          (* invoke shallow initialize *)
          do r <- shallow_initialize ce shr_map ty b [] m next_extern next_tag;
          let '(m1, next_extern1, next_tag1, shr_map1, l) := r in
          (* update the recursive map if [ty] is a composite *)
          do recv <- load m1 b [];
          let rec_map1 := match ty with
                          | Tstruct _ _
                          | Tvariant _ _ => TyMap.set ty (Some recv) rec_map
                          | _ => rec_map
                          end in
          (* recursively deep initialize the (b, ty) in l *)
          let f acc '(b, ty) :=
            do r1 <- acc;
            let '(m1, next_extern1, next_tag1, shr_map1) := r1 in
            deep_initialize fuel' shr_map1 rec_map1 ty b m1 next_extern1 next_tag1 in
          fold_left f l (OK (m1, next_extern1, next_tag1, shr_map1))
      end
  end.
            
Definition deep_fuel := 100%nat.             


(* initialize the parameters *)

Definition init_param (m: amem) (param: ident * type) (shr_map: TyMap.t (option ablock)) (next_extern: positive) (next_tag: positive) : res (amem * positive * positive * TyMap.t (option ablock)) :=
  let (id, ty) := param in
  (* allocate a stack block for param so that we can use id to get the
  content of this parameter *)
  do (b, m') <- alloc_stack_block ce m ty id;
  (* deep initialize this parameter *)
  deep_initialize deep_fuel shr_map (TyMap.init None) ty b m' next_extern next_tag.

Definition init_params_acc acc (param: ident * type) :=
  do r1 <- acc;
  let '(m1, next_extern1, next_tag1, shr_map1) := r1 in
  init_param m1 param shr_map1 next_extern1 next_tag1.

Definition init_params (m: amem) (params: list (ident * type)) : res amem :=
  do r <- fold_left init_params_acc params (OK (m, 1%positive, 1%positive, TyMap.init None));
  let '(m', _, _, _) := r in
  OK m'.

(* allocation of abstract stack blocks with undefined values *)

Definition allocate_vars (m: amem) (vars: list (ident * type)) : res amem :=
  fold_left (fun acc '(id, ty) => do m <- acc; do (_, m') <- alloc_stack_block ce m ty id; OK m') vars (OK m).

(** transfer function (place, pure expression, expression and statement *)

Definition aptr_of_aval (v: aval) : option LAptrs.t :=
  match v with
  | Ptr l => Some l
  | _ => None
  end.
  

(* There may be many possiblity for the memory location of a place.
[access] is the later action (e.g., the case that [p] in the RHS of a
assignment, [access] would be Awrite) for Print . *)
(* The return abstract value may beV top (an example is that a field
of a enum is not initialized but in fact it is impossible to evaluate
this branch) but we do not report use of undefined value in the
bastract interpretation, because it is irrelevant issue *)
(** After investigating Miri, I find that the evaluation of place is
considered a read access *)
Fixpoint transfer_place' (pc: node) (p: place') (m: amem) : res ((aval + (ablock * path)) * amem) :=
  match p with
  | Plocal id ty =>
      (* p is an owner, we do not need to check its permission *)
      (* The block local variable is always stack block *)
      OK (inr (Stack id,[]), m)
  | Pderef p' ty =>
      (* get the (block,path) of p' *)
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          (* It means that [p'] is accessed by these pointers (an
          example is [**a], here *a is an abstract pointer, its
          evaluation return ptrs). If we want to write [p], these
          pointers must have writable permission for [p']. So the we
          load values (by checking the permissin [access]) from all
          the abstract pointers. *)
          (** Follow Miri: read access  *)
          do (v', m'') <- load_aval m' v Aread;
          OK (inl v', m'')
          (* match aptr_of_aval v with *)
          (* | Some ptrs' => OK (inl ptrs', m'') *)
          (* (* We can also ignore this error, but for now, we report it *) *)
          (* | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"]) *)
          (* end *)
      | inr (b, ph) =>
          (* It means that p' is an owner *)
          do (v, m'') <- load_owner m' b ph Aread;
          OK (inl v, m'')
          (* match aptr_of_aval v with *)
          (* | Some l => OK (inl l, m'') *)
          (* | None => Error (error_msg pc ++ [MSG "expected abstract pointer (transfer_place)"]) *)
          (* end *)
      end
  | Pfield p' fid ty =>
      (* we do not perform access when evaluating field *)
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          match v with
          | Ptr ptrs =>
              (* we want to update the path in each pointer but we have no *)
              (* map function for Aptrs.t, so we use fold function *)
              let ptrs' := Aptrs.fold (fun '(b, ph, t) ptrs => Aptrs.add (b, ph ++ [Rfield fid], t) ptrs) ptrs Aptrs.empty in
              OK (inl (Ptr ptrs'), m')
          | _ =>
              (* Impossible ! Type error or enter dead code. *)
              OK (inl Vbot, m')
          end
      | inr (b, ph) =>
          OK (inr (b, ph ++ [Rfield fid]), m')
      end
  end.

Definition transfer_place (pc: node) (p: place) (m: amem) : res ((aval + (ablock * path)) * amem) :=
  match p with
  | Place p' =>
      transfer_place' pc p' m
  | Pdowncast p' fid ty =>
      do (l, m') <- transfer_place' pc p' m;
      match l with
      | inl v =>
          match v with
          | Ptr ptrs =>
              (* we want to update the path in each pointer but we have no *)
              (* map function for Aptrs.t, so we use fold function *)
              let ptrs' := Aptrs.fold (fun '(b, ph, t) ptrs => Aptrs.add (b, ph ++ [Renum fid], t) ptrs) ptrs Aptrs.empty in
              OK (inl (Ptr ptrs'), m')
          | _ =>
              (* Impossible ! Type error or enter dead code. *)
              OK (inl Vbot, m')
          end
      | inr (b, ph) =>
          OK (inr (b, ph ++ [Renum fid]), m')
      end
  end.

(* return an abstract value and the updated abstract memory *)
Fixpoint transfer_pure_expr (pc: node) (pe: pexpr) (m: amem) : res (aval * amem) :=
  match pe with
  | Eunit
  | Econst_int _ _
  | Econst_float _ _
  | Econst_single _ _
  | Econst_long _ _ => OK (Scalar, m)
  | Eplace p ty =>
      (** Do we need to check that whether we should move this place
      instead of copy it, e.g., p is of box type. Or it requires a
      separate checking? *)
      (* evaluate this place. Why the access is read? *)
      do (r, m') <- transfer_place pc p m;
      match r with
      | inl v =>
          (* the location of p is obtained from pointers *)
          load_aval m' v Aread
      | inr (b,ph) =>
          (* p is an owner *)
          match load_owner m' b ph Aread with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      end
  | Eref p mut ty =>
      (* create a reference with tag [Tintern pc], so it means that
      there must be at most one reference be created in a pc *)
      (* evaluate place with access [mut] *)
      do (r, m') <- transfer_place pc p m;
      let new_tag := Tintern pc in
      match r with
      | inl v =>
          (* if v is not pointer, the Eref is evaluated to Vbot *)
          match v with
          | Ptr ptrs =>
              (* for each (b,ph,t) ∈ ptrs, create a new ptr (b,ph,new_tag)
                 from tag [t] *)
              do (ptrs', m'') <- create_reference_from_ptrs mut ptrs new_tag m';
              OK (Ptr ptrs', m'')
          | _ =>
              (* Impossible ! Type error or enter dead code. *)
              OK (Vbot, m')
          end
      | inr (b, ph) =>
          (* create a pointer (b,ph, new_tag) *)
          do (ptr, m'') <- create_reference_from_owner mut b ph new_tag m';
          OK (Ptr (Aptrs.singleton ptr), m'')
      end
  | Ecktag p _ _ =>
      (** Is match statement is considered an access to the place? The
      answer is yes in Rust borrow checker (see borrowck_enum.rs). But
      here we do not consider it be a read access to the field. And we
      assume that the tag is a defined value. *)      
      OK (Scalar, m)
  | Eunop uop pe _ =>
      do (v, m') <- transfer_pure_expr pc pe m;
      (* uop can only be applied to scalar *)
      match v with
      | Scalar => OK (Scalar, m')
      | _ =>
          (* if we enter an dead branch, we may get a Vbot and
          evaluate it *)
          OK (Vbot, m')
      end
  | Ebinop binop pe1 pe2 _ =>
      do (v1, m1) <- transfer_pure_expr pc pe1 m;
      do (v2, m2) <- transfer_pure_expr pc pe2 m1;
      match v1, v2 with
      | Scalar, Scalar => OK (Scalar, m2)
      | _, _ => OK (Vbot, m2)
      end          
  end.


Definition transfer_expr (pc: node) (e: expr) (m: amem) : res (aval * amem) :=
  match e with
  | Epure pe =>
      transfer_pure_expr pc pe m
  | Emoveplace p ty =>
      (* In the abstract interpretation, move is considered a normal
      copy operation and we do not perform any operation in its
      children. We do not have retag like stacked borrow, does it
      matter? *)
      do (r, m') <- transfer_place pc p m;
      match r with
      | inl v =>
          (* the location of p is obtained from pointers *)
          load_aval m' v Aread
      | inr (b,ph) =>
          (* p is an owner *)
          match load_owner m' b ph Aread with
          | OK (v, m'') => OK (v, m'')
          | Error msg => Error (error_msg pc ++ msg)
          end
      end
  end.

(* Store the value [rhs] to a location (either abstract pointers or an
owner) plus an offset, treated as a write access *)
Definition storev (pc: node) (lhs: aval + (ablock * path)) (ofs: path) (rhs: aval) (m: amem) : res amem :=
  match lhs with
  | inl v =>
      (* write to the abstract pointers *)
      match v with
      | Ptr ptrs =>
          let f '(b, ph, t) acc :=
            do m <- acc;
            (* write access *)
            do m1 <- access Awrite b (ph ++ ofs) (Some t) m;
            (* store rhs to (b,ph) *)
            do m2 <- store m1 b (ph ++ ofs) rhs;
            OK m2 in
          do m' <- Aptrs.fold f ptrs (OK m);
          OK m'
      | Vbot =>
          (** Impossible behavior because we store a aval to a
              Vbot. But in match statement, some unreachable branch
              may cause such error *)
          OK m
      | _ =>
          Error [CTX pc; MSG ": the evaluation of a place is not a pointer"]                                   
      end
  | inr (b, ph) =>
      (* write to the owner *)
      do m' <- access Awrite b (ph ++ ofs) None m;
      do m'' <- store m' b (ph ++ ofs) rhs;
      OK m''
  end.


Definition transfer_assign (pc: node) (p: place') (e: expr) (m: amem) : res amem :=
  (* a simple type checking *)
  if type_eq (typeof_place' p) (typeof e) then
    (* evaluate the expression *)
    do (rhs, m1) <- transfer_expr pc e m;     
    (* evaluate the place *)
    do (lhs, m2) <- transfer_place' pc p m1;
    storev pc lhs [] rhs m2
  else
    Error [CTX pc; MSG ": mismatch type of lhs and rhs in assignment"]
.

Definition transfer_assign_variant (pc: node) (p: place') (fid: ident) (e: expr) (m: amem) : res amem :=
  (* evaluate the expression *)
  do (rhs, m1) <- transfer_expr pc e m;
  (* evaluate the place *)
  do (lhs, m2) <- transfer_place' pc p m1;
  storev pc lhs [Renum fid] rhs m2
.

Definition transfer_box (pc: node) (p: place') (e: expr) (m: amem) : res amem :=
  (* a simple type checking *)
  match typeof_place' p with
  | Tbox ty1 _ =>
      if type_eq ty1 (typeof e) then
        (* evaluate the expression *)
        do (rhs, m1) <- transfer_expr pc e m;
        (* allocate a heap block with id [Heap pc], so this block may
           have been allocated in the last iteration.  *)
        (** This allocation would clear the value and borrow tree in
        [Heap pc], is it correct?  *)
        do (b, m2) <- alloc_heap_block ce m1 (typeof e) pc;        
        (* store rhs to (b,[]) *)
        do m3 <- store m2 b [] rhs;
        (* evaluate the place *)
        do (lhs, m4) <- transfer_place' pc p m3;
        (* store (b, [], Tintern pc) to lhs *)
        (** FIXME: If [e] is also a reference (e.g., p = Box(&v)). The
        tag of p and &v are the same!! So how to generate a new tag?
        Or we can let the expression in the box statement contains no
        reference *)
        storev pc lhs [] (Ptr (Aptrs.singleton (b, [], Tintern pc))) m4
      else
        Error [CTX pc; MSG ": mismatch type of lhs and rhs in Sbox"]
  | _ =>
      Error [CTX pc; MSG ": The type of LHS is not a Tbox (Sbox)"]
  end.

(* perform write access to p *)
Definition transfer_drop (pc: node) (p: place') (m: amem) : res amem :=
  do (lhs, m1) <- transfer_place' pc p m;
  match lhs with
  | inl v =>
      match v with
      | Ptr ptrs =>
          let f '(b, ph, t) acc :=
            do m <- acc;
            (* write access *)
            do m1 <- access Awrite b ph (Some t) m;
            OK m1 in
          do m' <- Aptrs.fold f ptrs (OK m);
          OK m'
      | Vbot =>
          (** Impossible behavior because we store a aval to a
              Vbot. But in match statement, some unreachable branch
              may cause such error *)
          OK m
      | _ =>
          Error [CTX pc; MSG ": the evaluation of a place is not a pointer (transfer_drop) "]
      end
  | inr (b, ph) =>
      (* write to the owner *)
      do m' <- access Awrite b ph None m;
      OK m'
  end.

(** TODO: the alias of the return value depends on the annotated
origins and the types. For example, f: &'a mut i32 -> &'b mut i32 ->
&'c mut i32, it is not well formed, 'c must be related to 'a and 'b
because they may alias. For other example, g: &'a mut i32 -> &'b mut S
-> &'c mut i32, the second argument must not alias with the return
value. [tyf] is the type of this function (internal or external) *)
Definition transfer_call (pc: node) (p: place') (tyf: type) (al: list expr) (m: amem) : res amem :=
  (* evaluate the argument list *)
  do (l, m1) <- fold_right (fun elt acc => do (l, m) <- acc; do (v, m') <- transfer_expr pc elt m; OK (v::l, m')) (OK ([], m)) al;
  (* evaluate the [p] *)
  do (lhs, m2) <- transfer_place' pc p m1;
  (* Because we need to guess the alias relation between the return
  value and the arguments based on their type (type-based alias
  analysis!), the difficult part is the generation of the return
  value. It is the rely condition. *)
  (** TODO: specify the return value (Vtop for now) *)
  storev pc lhs [] Vtop m2.
  
Definition finish_transfer (pc: node) (r: res amem) : AM.t :=
  match r with
  | OK m => AM.State m
  | Error msg => AM.Err pc msg
  end.

Definition transfer (f: function) (cfg: rustcfg) (pc: node) (before: AM.t) : AM.t :=
  match before with
  (* If pred is unreacable, so this pc is unreacable, set to Bot *)
  | AM.Bot => AM.Bot
  | AM.Err pc' msg =>
      (* Error propagation: pc' is the source of this error *)
      AM.Err pc' msg
  | AM.State m =>
      (* Update the abstract state *)
      match cfg ! pc with
      | None => AM.bot
      | Some (Inop _) => before
      | Some (Icond e _ _) =>
          match transfer_expr pc e m with
          | OK (_, m') => AM.State m'
          | Error msg => AM.Err pc msg
          end
      | Some Iend => before
      | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => AM.bot
          | Some s =>
              match s with
              | Sassign p e =>
                  finish_transfer pc (transfer_assign pc p e m)
              | Sassign_variant p fid e =>
                  finish_transfer pc  (transfer_assign_variant pc p fid e m)
              | Sbox p e =>
                  finish_transfer pc (transfer_box pc p e m)
              | Sstoragedead id =>
                  (* ownership write access to the stack block [Stack id] *)
                  finish_transfer pc (access Awrite (Stack id) [] None m)
              | Sdrop p =>
                  (* ownership write access to the location of this place *)
                  finish_transfer pc (transfer_drop pc p m)
              | Scall p f al =>
                  finish_transfer pc (transfer_call pc p (typeof f) al m)
              | Sbuiltin p ef tyl al =>
                  (** TODO *)
                  before
              | Sreturn (Some e) =>
                  match transfer_expr pc e m with
                  | OK (_, m') => AM.State m'
                  | Error msg => AM.Err pc msg
                  end
              | _ => before
              end
          end
      end
  end.

End COMPOSITE_ENV.

Module DS := Dataflow_Solver(AM)(NodeSetForward).

Definition borrow_check (ce: composite_env) (f: function) : res unit :=
  (* initialize amem *)
  do m1 <- init_params ce init_amem f.(fn_params);
  (* allocate stack block for undefined variables *)
  do m2 <- allocate_vars ce m1 f.(fn_vars);
  (* generate cfg *)
  do (entry, cfg) <- generate_cfg f.(fn_body);
  (** forward dataflow *)
  match DS.fixpoint cfg successors_instr (transfer ce f cfg) entry (AM.State m2) with
  | Some r =>
      let (_, t) := r in
      let l := PTree.elements t in
      (* find the first error message *)
      match find (fun '(pc, am) => match am with | AM.Err _ _ => true | _ => false end) l with
      | Some (_, AM.Err _ msg) =>
          Error msg
      | _ => OK tt
      end
  | None =>
      Error [MSG "The borrow check fails with unknown reason"]
  end.


Definition transf_fundef (ce: composite_env) (id: ident) (fd: fundef) : Errors.res fundef :=
  match fd with
  | Internal f =>
      match borrow_check ce f with
      | OK _ => OK (Internal f)
      | Error msg => Error ([MSG "In function "; CTX id; MSG " , in pc "] ++ msg)
      end
  | External _ ef targs tres cconv => Errors.OK (External function ef targs tres cconv)
  end.

Definition transl_globvar (id: ident) (ty: type) := OK ty.

(* borrow check the whole module *)

Definition transl_program (p: program) : res program :=
  do p1 <- transform_partial_program2 (transf_fundef p.(prog_comp_env)) transl_globvar p;
  Errors.OK {| prog_defs := AST.prog_defs p1;
              prog_public := AST.prog_public p1;
              prog_main := AST.prog_main p1;
              prog_types := prog_types p;
              prog_comp_env := prog_comp_env p;
              prog_comp_env_eq := prog_comp_env_eq p |}.
