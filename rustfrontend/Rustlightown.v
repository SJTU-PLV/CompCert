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
Require Import Cop RustOp.
Require Import Ctypes Rusttypes Rustlight.
Require Import LanguageInterface.
Require Import InitDomain.

Local Open Scope error_monad_scope.
Import ListNotations.

(** Generate drop glue map like RustIR *)


(* Extract composite id to drop glue id list *)
Definition extract_drop_id (g: ident * globdef fundef type) : ident * ident :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => (comp_id, glue_id)
      | None => (1%positive, glue_id)
      end
  | _ => (1%positive, glue_id)
  end.

Definition check_drop_glue (g: ident * globdef fundef type) : bool :=
  let (glue_id, def) := g in
  match def with
  | Gfun (Internal f) =>
      match f.(fn_drop_glue) with
      | Some comp_id => true
      | None => false
      end
  | _ => false
  end.

Definition generate_dropm (p: program) :=
  let drop_glue_ids := map extract_drop_id (filter check_drop_glue p.(prog_defs)) in
  PTree_Properties.of_list drop_glue_ids.


(** * Operational Semantics  *)

(** ** Global environment  *)

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env; genv_dropm :> PTree.t ident }.
  
Definition globalenv (se: Genv.symtbl) (p: program) :=
  {| genv_genv := Genv.globalenv se p; genv_cenv := p.(prog_comp_env); genv_dropm := generate_dropm p |}.

(** ** Local environment  *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** ** Ownership environment  *)


(** Ownership environment: a pair of deep owned place set and
shallow owned place set (TODO: it should be defined in Rustlight) *)
    
(** own_env is actually init environment which is used to check
every used is initialized. Maybe we should change the name?  *)

(** TODO: add some properties in own_env such as init ∪ unint =
universe, init ∩ uninit = ∅ and etc *)
Record own_env :=
  mkown { own_init: PathsMap.t;
          own_uninit: PathsMap.t;
          own_universe: PathsMap.t;

          (* algebraic properties of own_env *)
          own_consistent: forall id,
            LPaths.eq (Paths.union (PathsMap.get id own_init) (PathsMap.get id own_uninit)) (PathsMap.get id own_universe);
          own_disjoint: forall id,
            LPaths.eq (Paths.inter (PathsMap.get id own_init) (PathsMap.get id own_uninit)) Paths.empty;
                        
          (* The following two properties require move checking to guarantee *)
          
          (* ∀ p ∈ I → ∀ p' ∈ W, is_prefix p' p → p' ∈ I *)
          (* own_wf_init: forall id, *)
          (*   let init := PathsMap.get id own_init in *)
          (*   let universe := PathsMap.get id own_universe in *)
          (*   Paths.For_all (fun p => Paths.For_all *)
          (*                          (fun p' => if is_prefix p' p *)
          (*                                  then Paths.mem p' init = true *)
          (*                                  else True) universe) init; *)

          (* ∀ p ∈ U → ∀ p' ∈ W, is_prefix p p' → p' ∈ U *)
          (* own_wf_uninit: forall id, *)
          (*   let uninit := PathsMap.get id own_uninit in *)
          (*   let universe := PathsMap.get id own_universe in *)
          (*   Paths.For_all (fun p => Paths.For_all *)
          (*                          (fun p' => if is_prefix p p' *)
          (*                                  then Paths.mem p' uninit = true *)
          (*                                  else True) universe) uninit; *)
    }.

Lemma PathsMap_beq_bot: forall s,
    PathsMap.beq PathsMap.bot s = true ->
    s = PathsMap.bot.
Proof.
  intros. unfold PathsMap.beq, PTree.beq in H.
  simpl in H.
  destruct s; try congruence.
  auto.
Qed.


Definition in_universe (own: own_env) (p: place) : bool :=
  let id := local_of_place p in
  let universe := PathsMap.get id own.(own_universe) in
  Paths.mem p universe.

Lemma in_universe_eq: forall own1 own2 p,
    PathsMap.eq (own_universe own1) (own_universe own2) ->
    in_universe own1 p = in_universe own2 p.
Proof.
  intros. unfold in_universe.
  generalize (H (local_of_place p)). intros EQ.
  destruct (Paths.mem p (PathsMap.get (local_of_place p) (own_universe own1))) eqn: A;
    destruct (Paths.mem p (PathsMap.get (local_of_place p) (own_universe own2))) eqn: B;
    auto.
  eapply Paths.mem_2 in A. rewrite <- B. symmetry.
  eapply Paths.mem_1. rewrite <- EQ. auto.
  eapply Paths.mem_2 in B. rewrite <- A. 
  eapply Paths.mem_1. rewrite EQ. auto.
Qed.

(* is_owned means that the location of p is initialized (assuming that
the location of p is valid) *)
(* Definition is_owned (own: own_env) (p: place): bool := *)
(*   let id := local_of_place p in *)
(*   let init := PathsMap.get id own.(own_init) in *)
(*   let universe := PathsMap.get id own.(own_universe) in *)
(*   (* ∀ p' ∈ universe, is_prefix p' p \/ is_shallow_prefix p p' → p' ∈ mustinit *) *)
(*   Paths.for_all (fun p' => Paths.mem p' init) *)
(*     (Paths.filter (fun p' => is_shallow_prefix p p') universe). *)

(* It is only used for place that is in the universe (e.g., the place obtained from split_drop_places) *)
Definition is_init (own: own_env) (p: place): bool :=
  let id := local_of_place p in
  let init := PathsMap.get id own.(own_init) in
  Paths.mem p init.


Definition is_movable (own: own_env) (p: place) : bool :=
  (* the place itself and its children are all owned *)
  let id := local_of_place p in
  let universe := PathsMap.get id (own_universe own) in
  (** Only check those in the universe  *)
  Paths.exists_ (is_prefix p) universe &&
  Paths.for_all (is_init own) (Paths.filter (is_prefix p) universe).


Fixpoint own_check_pexpr (own: own_env) (pe: pexpr) : bool :=
  match pe with
  | Eplace p _
  | Ecktag p _
  | Eref _ _ p _ =>
      (* we only check p which represents/owns a memory location *)
      if place_owns_loc p then
        (* copy/reference a place also requires that the place is
        movable (all its children are owned, otherwise it is not
        memory safe because the unowned block may be deallocated *)
        is_movable own p
      else
        (* This checking is left for borrow checker *)
        true
  | Eunop _ pe _ =>
      own_check_pexpr own pe
  | Ebinop _ pe1 pe2 _ =>
      own_check_pexpr own pe1 && own_check_pexpr own pe2
  | _ => true
end.          
  

Lemma move_place_consistent: forall IM UM WM i p
    (CON: forall id, LPaths.eq
                  (Paths.union (PathsMap.get id IM) (PathsMap.get id UM))
                  (PathsMap.get id WM)),
    LPaths.eq (Paths.union (PathsMap.get i (remove_place p IM)) (PathsMap.get i (add_place WM p UM)))
      (PathsMap.get i WM).
Proof.
  intros.
  unfold remove_place, add_place.
  generalize (CON i). intros WP.
  set (pid := (local_of_place p)) in *.
  do 2 erewrite PathsMap.gsspec.
  destruct (peq i pid).
  - subst.    
    red. red. intros.
    set (I := (PathsMap.get pid IM)) in *.
    set (U := (PathsMap.get pid UM)) in *.
    set (W := (PathsMap.get pid WM)) in *.
    split.
    + intros IN.
      eapply WP. 
      eapply Paths.union_1 in IN. destruct IN as [IN1 | IN2].
      * eapply Paths.filter_1 in IN1.
        eapply Paths.union_2.
        auto.        
        red. Morphisms.solve_proper.
      * eapply Paths.union_1 in IN2. destruct IN2 as [IN3 | IN4].
        -- eapply Paths.union_3. auto.
        -- eapply Paths.filter_1 in IN4.
           eapply WP. auto.
           red. Morphisms.solve_proper.
    + intros IN.
      eapply WP in IN. eapply Paths.union_1 in IN.
      destruct IN as [IN1 | IN2].
      * destruct (negb (is_prefix p a)) eqn: FL.
        -- eapply Paths.union_2.
           eapply Paths.filter_3; auto.
           red. Morphisms.solve_proper.
        -- eapply Paths.union_3. eapply Paths.union_3.
           eapply negb_false_iff in FL.
           eapply Paths.filter_3; auto.
           red. Morphisms.solve_proper.
           eapply WP. eapply Paths.union_2. auto.
      * eapply Paths.union_3.
        eapply Paths.union_2. auto.
  - auto.
Qed.

Lemma add_place_consistent: forall IM UM WM i p
    (CON: forall id, LPaths.eq
                  (Paths.union (PathsMap.get id IM) (PathsMap.get id UM))
                  (PathsMap.get id WM)),
    LPaths.eq (Paths.union (PathsMap.get i (add_place WM p IM)) (PathsMap.get i (remove_place p UM)))
      (PathsMap.get i WM).
Proof.
  intros.
  eapply LPaths.eq_trans.
  - instantiate (1 := (Paths.union (PathsMap.get i (remove_place p UM))
                       (PathsMap.get i (add_place WM p IM)))).
    red. red. intros.
    split; intros IN.
    + eapply Paths.union_1 in IN.
      destruct IN.
      eapply Paths.union_3. auto.
      eapply Paths.union_2. auto.
    + eapply Paths.union_1 in IN.
      destruct IN.
      eapply Paths.union_3. auto.
      eapply Paths.union_2. auto.
  - eapply move_place_consistent.
    intros. eapply LPaths.eq_trans; try eapply CON.
    red. red. intros.
    split; intros IN.
    + eapply Paths.union_1 in IN.
      destruct IN.
      eapply Paths.union_3. auto.
      eapply Paths.union_2. auto.
    + eapply Paths.union_1 in IN.
      destruct IN.
      eapply Paths.union_3. auto.
      eapply Paths.union_2. auto.
Qed.
    
Program Definition move_place (own: own_env) (p: place) : own_env :=
  {| own_init := (remove_place p own.(own_init));
    own_uninit := (add_place own.(own_universe) p own.(own_uninit));
    own_universe := own.(own_universe) |}.
Next Obligation.
  eapply move_place_consistent.
  eapply own_consistent.
Defined.           
Next Obligation.
  destruct own. simpl.
  unfold remove_place, add_place.
  set (pid := (local_of_place p)) in *.
  generalize (own_disjoint0 pid). intros DIS.
  generalize (own_consistent0 pid). intros CON.
  do 2 erewrite PathsMap.gsspec.
  destruct (peq id pid).
  - subst. red. red. intros.    
    split.
    + intros IN. exfalso.
      eapply Paths.empty_1. eapply DIS.
      instantiate (1 := a).
      eapply Paths.inter_3.
      * eapply Paths.inter_1 in IN.
        eapply Paths.filter_1 in IN. auto.
        red. Morphisms.solve_proper.
      * exploit Paths.inter_1;eauto. intros IN1.
        exploit Paths.inter_2;eauto. intros IN2.
        eapply Paths.union_1 in IN2.
        destruct IN2 as [IN3|IN4].
        -- auto.
        (* IN1 and IN4 are contradict *)
        -- eapply Paths.filter_2 in IN1.
           eapply Paths.filter_2 in IN4.
           rewrite IN4 in IN1. simpl in IN1. congruence.
           red. Morphisms.solve_proper.
           red. Morphisms.solve_proper.
    + intros IN. exfalso.
      eapply Paths.empty_1. eauto.
  - auto.
Defined.


Definition move_place_option (own: own_env) (p: option place) : own_env :=
  match p with
  | None => own
  | Some p => move_place own p
  end.

Fixpoint move_place_list (own: own_env) (l: list place) : own_env :=
  match l with
  | nil => own
  | p :: l' =>
      move_place_list (move_place own p) l'
  end.

Lemma move_place_eq_universe: forall own p,
    PathsMap.eq (own_universe own) (own_universe (move_place own p)).
Proof.
  intros.
  unfold move_place.
  simpl. eapply PathsMap.eq_refl.
Qed.  

Lemma move_place_option_eq_universe: forall own p,
    PathsMap.eq (own_universe own) (own_universe (move_place_option own p)).
Proof.
  intros.
  unfold move_place_option.
  destruct p. simpl.
  eapply PathsMap.eq_refl. eapply PathsMap.eq_refl.
Qed.  


(* (* ownership transfer of an expression *) *)
(* Definition own_transfer_expr (own: own_env) (e: expr) : own_env := *)
(*   match e with *)
(*   | Emoveplace p ty => *)
(*       let p := valid_owner p in *)
(*       move_place own p *)
(*   | Epure pe => *)
(*       own *)
(*   end. *)


(* Move to Rustlight: Check the ownership of expression *)
Definition own_check_expr (own: own_env) (e: expr) : bool :=
  match e with
  | Emoveplace p ty =>
      (** FIXME: when to use valid_owner? *)
      (* consider [a: Box<Box<Box<i32>>>] and we move [*a]. [a] becomes
         partial owned *)
      (* remove p from init and add p and its children to uninit *)      
      let p := valid_owner p in
      is_movable own p
  | Epure pe =>
      true
  end.

(* Fixpoint own_transfer_exprlist (own: own_env) (l: list expr) : own_env := *)
(*   match l with *)
(*   | nil => own *)
(*   | e :: l' => *)
(*       own_transfer_exprlist (own_transfer_expr own e) l' *)
(*   end. *)


Definition own_check_exprlist (own: own_env) (l: list expr) : bool :=
  forallb (own_check_expr own) l.


(* The dominator of a place [p]: the place's demonator decide the
location of this place (e.g., if p is of type enum, then it is the
dominator of all its downcast *)

(* Unused *)
Fixpoint place_dominator (p: place) : option place :=
  match p with
  | Pderef p' _ => Some p'
  | Pfield p' _ _ => place_dominator p'
  | Pdowncast p' _ _ => Some p'
  | Plocal _ _ => None
  | Pparenthesize _ _ _ => None
  | PparenthesizeV _ _ _ _ => None
  | ParrayIndex p' _ _ => Some p'
  end.

Fixpoint place_dominators (p: place) : list place :=
  match p with
  | Pderef p' _ => p' :: place_dominators p'
  | Pfield p' _ _ => place_dominators p'
  | Pdowncast p' _ _ =>
      let po := valid_owner p' in
      po :: place_dominators po
  | Plocal _ _ => nil
  | Pparenthesize _ _ _ => nil
  | PparenthesizeV _ _ _ _ => nil
  | ParrayIndex p' _ _ => place_dominators p'
  end.

Definition dominators_is_init (own: own_env) (p: place) : bool :=
  forallb (is_init own) (place_dominators p).

(* A place's dominator is owned means that this place is the owner of
the location it resides in *)
(* Definition place_dominator_own (own: own_env) (p: place) : bool := *)
(*   match place_dominator p with *)
(*   | Some p' => is_owned own p' *)
(*   | None => true *)
(*   end. *)

(* We can use the following function to ensure that the block place
[p] resides in is in the domain of abstracter *)
(* Definition place_dominator_shallow_own (own: own_env) (p: place) : bool := *)
(*   match place_dominator p with *)
(*   | Some p' => is_shallow_owned own p' *)
(*   | None => true *)
(*   end. *)


(* initialize a place *)
Program Definition init_place (own: own_env) (p: place) : own_env :=
  {| own_init := (add_place own.(own_universe) p own.(own_init));
    own_uninit := (remove_place p own.(own_uninit));
    own_universe := own.(own_universe) |}.
Next Obligation.
  eapply add_place_consistent.
  eapply own_consistent.
Defined.
Next Obligation.
  destruct own. simpl.
  unfold remove_place, add_place.
  set (pid := (local_of_place p)) in *.
  generalize (own_disjoint0 pid). intros DIS.
  generalize (own_consistent0 pid). intros CON.
  do 2 erewrite PathsMap.gsspec.
  destruct (peq id pid).
  - subst. red. red. intros.    
    split.
    + intros IN. exfalso.
      eapply Paths.empty_1. eapply DIS.
      instantiate (1 := a).
      eapply Paths.inter_3.
      * exploit Paths.inter_1; eauto. intros IN1.
        exploit Paths.inter_2; eauto. intros IN2.
        eapply Paths.union_1 in IN1.
        destruct IN1 as [IN3|IN4].
        -- auto.
        (* IN1 and IN4 are contradict *)
        -- eapply Paths.filter_2 in IN2.
           eapply Paths.filter_2 in IN4.
           rewrite IN4 in IN2. simpl in IN2. congruence.
           red. Morphisms.solve_proper.
           red. Morphisms.solve_proper.
      * eapply Paths.inter_2 in IN.
        eapply Paths.filter_1 in IN. auto.
        red. Morphisms.solve_proper.
    + intros IN. exfalso.
      eapply Paths.empty_1. eauto.
  - auto.
Defined.

Definition init_place_list (own: own_env) (l: list place) : own_env :=
  fold_left init_place l own.

(* Definition own_check_assign (own: own_env) (p: place) : bool := *)
(*   (* check that the dominator of p is owned (initialized) because we *)
(*   need to compute the address of [p] *) *)
(*   place_dominator_own own p. *)

Lemma is_init_in_universe: forall p own,
    is_init own p = true ->
    in_universe own p = true.
Proof.
  intros. unfold is_init, in_universe in *.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in H.
  eapply own_consistent.
  eapply Paths.union_2. auto.
Qed.

(* Update the ownership environment when assigning to p. We must
ensure that p is not deeply owned because p must be dropped before
this assignment. *)
Definition own_transfer_assign (own: own_env) (p: place) : own_env :=  
  init_place own p.
     
(** Deference a location based on the type  *)

Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs (Vptr b ofs).

(** Memory error in deref_loc  *)

Inductive deref_loc_mem_error (ty: type) (m: mem) (b: block) (ofs: ptrofs) : Prop :=
  | deref_loc_value_error: forall chunk,
      access_mode ty = By_value chunk ->
      ~ Mem.valid_access m chunk b (Ptrofs.unsigned ofs) Readable ->
      deref_loc_mem_error ty m b ofs.


(** Assign a value to a location  *)

Inductive assign_loc (ce: composite_env) (ty: type) (m: mem) (b: block) (ofs: ptrofs): val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      complete_type ce ty = true ->
      (* consider a = b ( a and b are struct ) *)
      (* evaluate b is (Vptr b' ofs'), evaluate a is (b,ofs) *)      
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      (* a and b are disjoint or equal *)
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
             \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs (Vptr b' ofs') m'.

(** Memory error in assign_loc  *)

Inductive assign_loc_mem_error (ce : composite_env) (ty : type) (m : mem) (b : block) (ofs : ptrofs) : val -> Prop :=
| assign_loc_value_mem_error: forall v chunk,
    access_mode ty = By_value chunk ->
    ~ Mem.valid_access m chunk b (Ptrofs.unsigned ofs) Writable ->
    assign_loc_mem_error ce ty m  b ofs v
| assign_loc_copy_mem_error1: forall b' ofs',
    (* the memory location of the struct to be copied is not readable *)
    access_mode ty = By_copy ->
    ~ Mem.range_perm m b' (Ptrofs.unsigned ofs') ((Ptrofs.unsigned ofs') + (sizeof ce ty)) Cur Readable ->
    assign_loc_mem_error ce ty m b ofs (Vptr b' ofs')
| assign_loc_copy_mem_error2: forall v,
    (* the memory location of the struct to be stored is not writable *)
    access_mode ty = By_copy ->
    ~ Mem.range_perm m b (Ptrofs.unsigned ofs) ((Ptrofs.unsigned ofs) + (sizeof ce ty)) Cur Writable ->
    assign_loc_mem_error ce ty m b ofs v.

Lemma assign_loc_det ce : forall ty m b ofs v m1 m2,
    assign_loc ce ty m b ofs v m1 ->
    assign_loc ce ty m b ofs v m2 ->
    m1 = m2.
Proof.
  intros. inv H; inv H0; auto; try congruence.
Qed.

Lemma assign_loc_progress_no_mem_error: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    assign_loc_mem_error ce ty m1 b ofs v ->
    False.
Proof.
  intros. inv H; inv H0; try congruence; eauto.
  - rewrite H1 in H. inv H.
    eapply H3. eapply Mem.store_valid_access_3; eauto.
  - eapply H10. eapply Mem.loadbytes_range_perm; eauto.
  - eapply H8.    
    eapply Mem.storebytes_range_perm in H7.
    red. intros. eapply H7.
    exploit Mem.loadbytes_length; eauto. intros.
    rewrite H9. rewrite Z2Nat.id. auto.
    generalize (sizeof_pos ce ty). lia.
Qed.

Definition do_deref_loc ty m b ofs : option val :=
  match access_mode ty with
  | By_value chunk =>
      Mem.loadv chunk m (Vptr b ofs)
  | By_reference | By_copy => Some (Vptr b ofs)
  | By_nothing => None
  end.

Lemma do_deref_loc_sound: forall ty m b ofs v,
    do_deref_loc ty m b ofs = Some v ->
    deref_loc ty m b ofs v.
Proof.
  unfold do_deref_loc.
  destruct ty; intros; simpl in *.
  - econstructor; eauto. simpl. eauto.
  - DestructCases; econstructor; simpl; eauto.
  - econstructor; simpl; eauto.
  - DestructCases; econstructor; simpl; eauto.
  - inv H. eapply deref_loc_reference; eauto.
  - econstructor; simpl; eauto.
  (* - econstructor; simpl; eauto. *)
  - econstructor; simpl; eauto.
  - econstructor; simpl; eauto.
  - inv H. eapply deref_loc_reference; eauto.
  - econstructor; simpl; eauto.
  - inv H. eapply deref_loc_copy; eauto.
  - inv H. eapply deref_loc_copy; eauto.
Qed.

(* copy from Cexe *)
Definition assign_copy_ok ce (ty: type) (b: block) (ofs: ptrofs) (b': block) (ofs': ptrofs) : Prop :=
  (alignof_blockcopy ce ty | Ptrofs.unsigned ofs') /\ (alignof_blockcopy ce ty | Ptrofs.unsigned ofs) /\
  (b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
           \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
           \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs').

Remark check_assign_copy:
  forall ce (ty: type) (b: block) (ofs: ptrofs) (b': block) (ofs': ptrofs),
  { assign_copy_ok ce ty b ofs b' ofs' } + {~ assign_copy_ok ce ty b ofs b' ofs' }.
Proof with try (right; intuition lia).
  intros. unfold assign_copy_ok.
  destruct (Zdivide_dec (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs')); auto...
  destruct (Zdivide_dec (alignof_blockcopy ce ty) (Ptrofs.unsigned ofs)); auto...
  assert (Y: {b' <> b \/
              Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs'} +
           {~(b' <> b \/
              Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs \/
              Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs')}).
  destruct (eq_block b' b); auto.
  destruct (zeq (Ptrofs.unsigned ofs') (Ptrofs.unsigned ofs)); auto.
  destruct (zle (Ptrofs.unsigned ofs' + sizeof ce ty) (Ptrofs.unsigned ofs)); auto.
  destruct (zle (Ptrofs.unsigned ofs + sizeof ce ty) (Ptrofs.unsigned ofs')); auto.
  right; intuition lia.
  destruct Y... left; intuition lia.
Defined.

Definition do_assign_loc ce ty m b ofs v : option mem :=
  match access_mode ty with
  | By_value chunk =>
      Mem.storev chunk m (Vptr b ofs) v
  | By_copy =>
      match v with
      | Vptr b' ofs' =>
          if complete_type ce ty then
            if check_assign_copy ce ty b ofs b' ofs' then
              match Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) with
              | Some bytes =>
                  Mem.storebytes m b (Ptrofs.unsigned ofs) bytes
              | _ => None
              end
            else None
          else None
      | _ => None
      end
  | _ => None
  end.

Lemma do_assign_loc_sound: forall ce ty m b ofs v m',
    do_assign_loc ce ty m b ofs v = Some m' ->
    assign_loc ce ty m b ofs v m'.
Proof.
  unfold do_assign_loc. intros.
  destruct (access_mode ty) eqn: MODE; try congruence.
  - econstructor; eauto.
  - destruct v; try congruence.
    destruct complete_type eqn: COM; try congruence.
    destruct check_assign_copy; try congruence. inv a.
    destruct Mem.loadbytes eqn: LOAD; try congruence.
    destruct H1 as (A1 & A2).
    eapply assign_loc_copy; eauto.
Qed.
    
Section SEMANTICS.
  
(** ** Evaluation of expressions *)

Section EXPR.

Variable ce: composite_env.
Variable e: env.
Variable m: mem.

(* similar to eval_lvalue in Clight.v *)
Inductive eval_place : place -> block -> ptrofs -> Prop :=
| eval_Plocal: forall id b ty,
    (** TODO: there is no global variable, so we do not consider the
    gloabl environment *)
    e!id = Some (b, ty) ->
    eval_place (Plocal id ty) b Ptrofs.zero
| eval_Pfield_struct: forall p ty b ofs delta id i co orgs,
    eval_place p b ofs ->
    typeof_place p = Tstruct orgs id ->
    ce ! id = Some co ->
    field_offset ce i (co_members co) = OK delta ->
    eval_place (Pfield p i ty) b (Ptrofs.add ofs (Ptrofs.repr delta))
| eval_Pdowncast: forall  p b ofs fofs id fid fty co orgs tag,
    eval_place p b ofs ->
    typeof_place p = Tvariant orgs id ->
    ce ! id = Some co ->
    (* check tag and fid. If we want to remove this check, we need to
    show co_members are not repeated in MoveCheckingSafe to make sure
    wt_place and wt_footprint relate the same field ident. Without this checking, I don't know how to relate the (fid, fty) in footprint of bmatch and (fid, fty) in the place *)
    Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag) ->
    list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty) ->
    variant_field_offset ce fid (co_members co) = OK fofs ->
    (* fty and ty must be equal? *)
    eval_place (Pdowncast p fid fty) b (Ptrofs.add ofs (Ptrofs.repr fofs))
| eval_Pderef: forall p ty l ofs l' ofs',
    eval_place p l ofs ->
    deref_loc (typeof_place p) m l ofs (Vptr l' ofs') ->
    eval_place (Pderef p ty) l' ofs'.


Lemma deref_loc_det: forall ty m b ofs v1 v2,
    deref_loc ty m b ofs v1 ->
    deref_loc ty m b ofs v2 ->
    v1 = v2.
Proof.
  destruct ty; intros.
  all: try (inv H; inv H0; simpl in *; try congruence).
Qed.

(* eval_place is determinate *)
Lemma eval_place_det: forall p b1 ofs1 b2 ofs2,
    eval_place p b1 ofs1 ->
    eval_place p b2 ofs2 ->
    b1 = b2 /\ ofs1 = ofs2.
Proof.
  induction p; intros.
  - inv H. inv H0.
    rewrite H4 in H5. inv H5. auto.
  - inv H. inv H0. rewrite H5 in H6. inv H6.
    rewrite H8 in H11. inv H11.
    rewrite H9 in H12. inv H12.
    exploit IHp. eapply H4. eauto. intros (A1 & A2). subst.
    eauto.
  - inv H. inv H0. exploit IHp. eapply H3. eauto.
    intros (A1 & A2). subst.
    exploit deref_loc_det. eapply H6. eauto. intros A1. inv A1.
    eauto.
  - inv H. inv H0. rewrite H5 in H8. inv H8.
    rewrite H6 in H9. inv H9.
    exploit IHp. eapply H4. eauto. intros (A1 & A2). subst.
    rewrite H7 in H12. inv H12.
    rewrite H10 in H15. inv H15.
    rewrite H11 in H16. inv H16. auto.
Admitted.
    
Inductive eval_place_mem_error : place -> Prop :=
| eval_Pfield_error: forall p ty i,
    eval_place_mem_error p ->
    eval_place_mem_error (Pfield p i ty)
| eval_Pdowncast_error1: forall p ty fid,
    eval_place_mem_error p ->
    eval_place_mem_error (Pdowncast p fid ty)
| eval_Pdowncast_error2: forall p ty fid b ofs,
    eval_place p b ofs ->
    ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    eval_place_mem_error (Pdowncast p fid ty)
| eval_Pderef_error1: forall p ty,
    eval_place_mem_error p ->
    eval_place_mem_error (Pderef p ty)
| eval_Pderef_error2: forall p l ofs ty,
    eval_place p l ofs ->
    deref_loc_mem_error (typeof_place p) m l ofs ->
    eval_place_mem_error (Pderef p ty)
.


Lemma deref_loc_progress_no_mem_error: forall m b ofs ty v,
    deref_loc ty m b ofs v ->
    deref_loc_mem_error ty m b ofs ->
    False.
Proof.
  intros. inv H0. apply H2.
  inv H.
  - rewrite H1 in H0. inv H0. eapply Mem.load_valid_access; eauto.
  - rewrite H1 in H0. inv H0.
  - rewrite H1 in H0. inv H0.
Qed.


Lemma eval_place_progress_no_mem_error: forall p b ofs
    (ERR: eval_place_mem_error p)
    (EVAL: eval_place p b ofs),
    False.
Proof.
  induction p; intros; inv EVAL; inv ERR; eauto.
  - exploit eval_place_det. eapply H1. eauto. intros (A1 & A2).
    subst.
    eapply deref_loc_progress_no_mem_error; eauto.
  - exploit eval_place_det. eapply H2. eauto. intros (A1 & A2).
    subst.
    eapply H7. eapply Mem.load_valid_access; eauto.
Qed.

Inductive eval_place_list : list place -> list block -> list ptrofs -> Prop :=
| eval_Pnil: eval_place_list nil nil nil
| eval_Pcons: forall p b ofs lp lb lofs,
    eval_place p b ofs ->
    eval_place_list lp lb lofs ->    
    eval_place_list (p :: lp) (b :: lb) (ofs :: lofs).


Definition int_val_casted (v: val) (ty: type) : Prop :=
  match v, ty with
  | Vint n, Tint sz sg =>
      cast_int_int sz sg n = n
  | _, _ => True
  end.

(* Evaluation of pure expression *)

Inductive eval_pexpr (se: Genv.symtbl) : pexpr -> val ->  Prop :=
| eval_Eunit:
    eval_pexpr se Eunit (Vint Int.zero)
| eval_Econst_int:   forall i ty,
    eval_pexpr se (Econst_int i ty) (Vint i)
| eval_Econst_float:   forall f ty,
    eval_pexpr se (Econst_float f ty) (Vfloat f)
| eval_Econst_single:   forall f ty,
    eval_pexpr se (Econst_single f ty) (Vsingle f)
| eval_Econst_long:   forall i ty,
    eval_pexpr se (Econst_long i ty) (Vlong i)
| eval_Eunop:  forall op a ty v1 v aty,
    eval_pexpr se a v1 ->
    (* Note that to_ctype Tbox = None *)
    to_ctype (typeof_pexpr a) = aty ->
    (** TODO: define a rust-specific sem_unary_operation  *)
    sem_unary_operation op v1 aty m = Some v ->
    eval_pexpr se (Eunop op a ty) v
| eval_Ebinop: forall op a1 a2 ty v1 v2 v ty1 ty2,
    eval_pexpr se a1 v1 ->
    eval_pexpr se a2 v2 ->
    to_ctype (typeof_pexpr a1) = ty1 ->
    to_ctype (typeof_pexpr a2) = ty2 ->
    sem_binary_operation_rust op v1 ty1 v2 ty2 m = Some v ->
    (* For now, we do not return moved place in binary operation *)
    eval_pexpr se (Ebinop op a1 a2 ty) v
| eval_Eplace: forall p b ofs ty v,
    eval_place p b ofs ->
    deref_loc ty m b ofs v ->
    (* adhoc: cast int if v is Vint. This premise is only useful if ty
    is type_bool and v is i8 which may be non-zero and non-one
    value. But we want to prove that it is one or zero *)
    (* int_val_casted v ty -> *)
    eval_pexpr se (Eplace p ty) v
| eval_Ecktag: forall (p: place) b ofs tag tagz id fid co orgs
    (EVALP: eval_place p b ofs)
    (* load the tag *) 
    (LOADTAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (PTY: typeof_place p = Tvariant orgs id)
    (CO: ce ! id = Some co)                 
    (FTAG: field_tag fid co.(co_members) = Some tagz)
    (* adhoc: the range checking in the semantics is used to make sure
    that if the execution passes this check, the downcast evalution in
    the match arms must be successful *)
    (RANGE: Int.unsigned tag < list_length_z co.(co_members)),
    eval_pexpr se (Ecktag p fid) (Val.of_bool (Int.eq tag (Int.repr tagz)))
| eval_Eref: forall p b ofs mut ty org,
    eval_place p b ofs ->
    eval_pexpr se (Eref org mut p ty) (Vptr b ofs)
(* Evaluation of global variables which is used to support function
call *)
| eval_Eglobal: forall id ty b v
    (GADDR: Genv.find_symbol se id = Some b)
    (DEF: deref_loc ty m b Ptrofs.zero v),
    eval_pexpr se (Eglobal id ty) v
.

      
(* expression evaluation has two phase: evaluate the value and produce
the moved-out place *)
Inductive eval_expr (se: Genv.symtbl) : expr -> val -> Prop :=
| eval_Emoveplace: forall p ty v,
    eval_pexpr se (Eplace p ty) v ->
    eval_expr se (Emoveplace p ty) v
(* | eval_Emoveget: forall p fid ty v, *)
(*     eval_pexpr (Eget p fid ty) v -> *)
(*     eval_expr (Emoveget p fid ty) v *)
| eval_Epure: forall pe v,
    eval_pexpr se pe v ->
    eval_expr se (Epure pe) v.

Inductive eval_exprlist se : list expr -> typelist -> list val -> Prop :=
| eval_Enil:
  eval_exprlist se nil Tnil nil
| eval_Econs:   forall a bl ty tyl v1 v2 vl,
    eval_expr se a v1 ->
    sem_cast v1 (typeof a) ty = Some v2 ->
    eval_exprlist se bl tyl vl ->
    eval_exprlist se (a :: bl) (Tcons ty tyl) (v2 :: vl).

(* determinism of eval_expr *)

Lemma eval_pexpr_det se: forall pe v1 v2,
    eval_pexpr se pe v1 ->
    eval_pexpr se pe v2 ->
    v1 = v2.
Proof.
  induction pe; intros until v2; intros E1 E2; inv E1; inv E2; try (econstructor; eauto).
  - exploit eval_place_det. eapply H1. eapply H2. intros (A1 & A2). subst.
    eapply deref_loc_det; eauto.
  - exploit eval_place_det. eapply EVALP. eapply EVALP0. intros (A1 & A2). subst.
    rewrite PTY in PTY0. inv PTY0.
    rewrite CO in CO0. inv CO0.
    rewrite LOADTAG in LOADTAG0. inv LOADTAG0.
    rewrite FTAG in FTAG0. inv FTAG0. auto.
  - exploit eval_place_det. eapply H4. eapply H5. intros (A1 & A2). subst.    
    auto.
  - exploit IHpe. eapply H2. eapply H3. intros. subst.
    rewrite H5 in H7. inv H7. auto.
  - exploit IHpe1. eapply H3. eapply H5. intros. subst.
    exploit IHpe2. eapply H4. eapply H6. intros. subst.
    rewrite H8 in H11. inv H11. auto.
  - rewrite GADDR in GADDR0. inv GADDR0.
    eapply deref_loc_det; eauto.
Qed.

Lemma eval_expr_det se: forall e v1 v2,
    eval_expr se e v1 ->
    eval_expr se e v2 ->
    v1 = v2.
Proof.
  intros. inv H; inv H0.
  eapply eval_pexpr_det; eauto.
  eapply eval_pexpr_det; eauto.
Qed.

Lemma eval_exprlist_det se: forall el tyl vl1 vl2,
    eval_exprlist se el tyl vl1 ->
    eval_exprlist se el tyl vl2 ->
    vl1 = vl2.
Proof.
  induction el; intros until vl2; intros E1 E2; inv E1; inv E2; eauto.
  f_equal; eauto.
  exploit eval_expr_det. eapply H1. eapply H6. intros. subst.
  rewrite H2 in H8. inv H8. auto.
Qed.

    
(** Memory error in evaluation of expression  *)


Inductive eval_pexpr_mem_error : pexpr ->  Prop :=
| eval_Eunop_error:  forall op a ty,
    eval_pexpr_mem_error a ->
    eval_pexpr_mem_error (Eunop op a ty)
| eval_Ebinop_error: forall op a1 a2 ty,
    (eval_pexpr_mem_error a1 \/ eval_pexpr_mem_error a2) ->
    eval_pexpr_mem_error (Ebinop op a1 a2 ty)
| eval_Eplace_error1: forall p ty,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Eplace p ty)
| eval_Eplace_error2: forall p b ofs ty,
    eval_place p b ofs->
    deref_loc_mem_error ty m b ofs ->
    eval_pexpr_mem_error (Eplace p ty)
| eval_Ecktag_error1: forall p fid,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Ecktag p fid)
| eval_Ecktag_error2: forall p b ofs fid, 
    eval_place p b ofs ->
    (* tag is not readable *)
    ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable ->
    eval_pexpr_mem_error (Ecktag p fid)
| eval_Eref_error: forall p org mut ty,
    eval_place_mem_error p ->
    eval_pexpr_mem_error (Eref org mut p ty).

Inductive eval_expr_mem_error : expr -> Prop :=
| eval_Emoveplace_error: forall p ty,
    eval_pexpr_mem_error (Eplace p ty) ->
    eval_expr_mem_error (Emoveplace p ty)
| eval_Epure_mem_error: forall pe,
    eval_pexpr_mem_error pe ->
    eval_expr_mem_error (Epure pe).

Inductive eval_exprlist_mem_error se: list expr -> typelist -> Prop :=
| eval_Econs_mem_error1: forall a bl ty tyl,
    eval_expr_mem_error a ->
    eval_exprlist_mem_error se (a :: bl) (Tcons ty tyl)
| eval_Econs_mem_error2: forall a bl ty tyl v1,
    eval_expr se a v1 ->
    eval_exprlist_mem_error se bl tyl ->
    eval_exprlist_mem_error se (a :: bl) (Tcons ty tyl)
.

(* If eval_expr succeeds, then eval_expr has no memory error *)

Lemma eval_pexpr_progress_no_mem_error se: forall pe v,
    eval_pexpr se pe v ->
    eval_pexpr_mem_error pe ->
     False.
Proof.
  induction pe; intros v A1 A2; inv A1; inv A2; try congruence; eauto.
  - eapply eval_place_progress_no_mem_error; eauto.
  - exploit eval_place_det. eapply H1. eauto. intros (B1 & B2).
    subst.
    eapply deref_loc_progress_no_mem_error; eauto.
  - eapply eval_place_progress_no_mem_error; eauto.
  - exploit eval_place_det. eapply EVALP. eauto. intros (B1 & B2).
    subst. eapply H2.
    eapply Mem.load_valid_access; eauto.
  - eapply eval_place_progress_no_mem_error; eauto.
  - destruct H0; eauto.
Qed.

Lemma eval_expr_progress_no_mem_error se: forall a v,
    eval_expr se a v ->
    eval_expr_mem_error a ->
     False.
Proof.
  intros. inv H; inv H0.
  - eapply eval_pexpr_progress_no_mem_error; eauto.
  - eapply eval_pexpr_progress_no_mem_error; eauto.
Qed.

Lemma eval_exprlist_progress_no_mem_error se: forall al tl vl,
    eval_exprlist se al tl vl ->
    eval_exprlist_mem_error se al tl ->
     False.
Proof.
  induction al; intros until vl; intros E1 E2; inv E1; inv E2; try congruence; eauto.
  eapply eval_expr_progress_no_mem_error; eauto.
Qed.

  
End EXPR.

(** Some definitions of dropplace and dropstate *)


(** Substate for member drop *)
Inductive drop_member_state : Type :=
| drop_member_comp
    (fid: ident)
    (fty: type)
    (co_ty: type)
    (tys: list type): drop_member_state   
| drop_member_box
    (fid: ident)
    (fty: type)
    (tys: list type): drop_member_state
.

Fixpoint split_fully_own_place (p: place) (ty: type) :=
  match ty with
  | Tbox ty'  =>
      split_fully_own_place (Pderef p ty') ty' ++ [p]
  | Tstruct _ _
  | Tvariant _ _  =>
      [p]
  | _ => nil
  end.

(* Drop place state *)

Inductive drop_place_state : Type :=
| drop_fully_owned_comp
    (* drop the composite and then drop the box *)
    (p: place) (l: list place) : drop_place_state
| drop_fully_owned_box
    (l: list place) : drop_place_state
.

Definition gen_drop_place_state (p: place) : drop_place_state :=
  match split_fully_own_place p (typeof_place p) with
  | nil => drop_fully_owned_box nil
  | p' :: l =>
      match typeof_place p' with
      | Tstruct _ _
      | Tvariant _ _ =>
          drop_fully_owned_comp p' l
      | _ =>
          drop_fully_owned_box (p' :: l)
      end
  end.


(** Continuation *)

(* The insertion for drops have two cases: one for the reassignment
and the other for those variables are about to be out-of-scope *)
Inductive drop_insert_kind : Type :=
| drop_reassign: place -> drop_insert_kind
| drop_escape_before: list (ident * type) -> drop_insert_kind
(* after exectuing the drop for id, we need to execute its storagedead
statement. This after constructor is used to model it *)
| drop_escape_after: ident -> list (ident * type) -> drop_insert_kind
(* drop insertion for the parameters which do not require storagedead anaotations *)
| drop_return: list (ident * type) -> drop_insert_kind
| drop_end: drop_insert_kind.


(* TODO: use some kbreak, kcontinue and kassign etc to record the stmt
after drop. lots of drops before break and continue can be extracted
from continuation *)

(* The action actually need to do after the inserted drop *)
Inductive dropcont : Type :=
(* for [p := q], we insert drop(p) to get [drop(p); p:=q] and the
assignment after this drop is recorded in this Dassign *)
(* Reassign drop insertion *)
| Dassign: place -> expr -> dropcont
| Dassign_variant : place -> ident -> ident -> expr -> dropcont
| Dbox: place -> expr -> dropcont
| Dcall: place -> expr -> list expr -> dropcont
(* Escape-scope drop insertion *)
| Dbreak
| Dcontinue
(* Dreturn records the return value *)
| Dreturn: place -> dropcont
| Dendlet
.

Inductive cont : Type :=
| Kstop: cont
| Kseq: statement -> cont -> cont
| Kloop: statement -> cont -> cont
| Kcall: place -> function -> env -> own_env -> cont -> cont
| Kdropinsert: drop_insert_kind -> dropcont -> cont -> cont
(* used to record Dropplace state *)
| Kdropplace: function -> option drop_place_state -> list (place * bool) -> env -> own_env -> cont -> cont
| Kdropcall: ident -> val -> option drop_member_state -> members -> cont -> cont
| Klet: ident -> type -> cont -> cont
.


(** Pop continuation until a call or stop *)

(* Return from dropstate, dropplace and dropinsert is UB *)
Fixpoint call_cont (k: cont) : option cont :=
  match k with
  | Kseq _ k => call_cont k
  | Kloop _ k => call_cont k
  | Klet _ _ k => call_cont k
  | Kdropplace _ _ _ _ _ _ => None
  | Kdropcall _ _ _ _ _  => None
  | Kdropinsert _ _ _ => None
  | _ => Some k
  end.


Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(* compute to drop places from continuation: simulate vars in
transl_stmt in RustIRgen *)

Fixpoint cont_vars (k: cont) : list (list (ident * type)) :=
  match k with
  | Klet id ty k1 =>
      list_list_cons (id, ty) (cont_vars k1)
  (* A new scope (which can be continue and break) is introduced from
  a loop statement *)
  | Kloop _ k1 =>
      [] :: cont_vars k1
  | Kseq _ k1
  | Kdropinsert _ _ k1
  | Kdropcall _ _ _ _ k1
  | Kdropplace _ _ _ _ _ k1 =>
      cont_vars k1
  (* Stop at the last stack frame *)
  | Kcall _ _ _ _ _
  | Kstop =>
      []
  end.


(** States *)

Inductive state: Type :=
| State
    (f: function)
    (s: statement)
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Callstate
    (vf: val)
    (args: list val)
    (k: cont)
    (m: mem) : state
| Returnstate
    (res: val)
    (k: cont)
    (m: mem) : state
(* Simulate drop insertion. The list of variables are to be dropped or
to be out-of-scope place, depending on the type of dropcont *)
| Dropinsert
    (f: function)    
    (st: drop_insert_kind)
    (dk: dropcont)
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
(* Simulate elaborate drop *)
| Dropplace
    (f: function)
    (s: option drop_place_state)
    (l: list (place * bool))
    (k: cont)
    (e: env)
    (own: own_env)
    (m: mem) : state
| Dropstate
    (* composite name *)
    (c: ident)
    (v: val)
    (ds: option drop_member_state)
    (ms: members)
    (k: cont)
    (m: mem): state
.


(** Allocate memory blocks for function parameters/variables and build
the local environment *)
Inductive alloc_variables (ce: composite_env) : env -> mem ->
                                                list (ident * type) ->
                                                env -> mem -> Prop :=
| alloc_variables_nil:
  forall e m,
    alloc_variables ce e m nil e m
| alloc_variables_cons:
  forall e m id ty vars m1 b1 m2 e2,
    Mem.alloc m 0 (sizeof ce ty) = (m1, b1) ->
    alloc_variables ce (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
    alloc_variables ce e m ((id, ty) :: vars) e2 m2.


Lemma alloc_variables_app: forall ce m1 m2 m3 l1 l2 e1 e2 e3,
    alloc_variables ce e1 m1 l1 e2 m2 ->
    alloc_variables ce e2 m2 l2 e3 m3 ->
    alloc_variables ce e1 m1 (l1 ++ l2) e3 m3.
Proof. 
  induction 1; intros.
  - auto.
  - simpl. econstructor; eauto.
Qed.

(** Assign the values to the memory blocks of the function parameters  *)
Inductive bind_parameters (ce: composite_env) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ce e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ce ty m b Ptrofs.zero v1 m1 ->
      bind_parameters ce e m1 params vl m2 ->
      bind_parameters ce e m ((id, ty) :: params) (v1 :: vl) m2.

Inductive bind_parameters_mem_error (ce: composite_env) (e: env) : mem -> list (ident * type) -> list val -> Prop :=
| bind_parameters_mem_error_cons1: forall m id ty params v1 vl b,
    e ! id = Some (b, ty) ->
    assign_loc_mem_error ce ty m b Ptrofs.zero v1 ->
    bind_parameters_mem_error ce e m ((id, ty) :: params) (v1 :: vl)
| bind_parameters_mem_error_cons2: forall m id ty params v1 vl b m1,
    e ! id = Some (b, ty) ->
    assign_loc ce ty m b Ptrofs.zero v1 m1 ->
    bind_parameters_mem_error ce e m1 params vl ->
    bind_parameters_mem_error ce e m ((id, ty) :: params) (v1 :: vl).

Lemma alloc_variables_det ce: forall l e1 m1 e2 m2 e3 m3,
    alloc_variables ce e1 m1 l e2 m2 ->
    alloc_variables ce e1 m1 l e3 m3 ->
    e2 = e3 /\ m2 = m3.
Proof.
  induction l; intros until m3; intros A1 A2; inv A1; inv A2; auto.
  rewrite H3 in H8. inv H8. eauto.
Qed.

Lemma bind_parameters_det ce: forall l vl e m m1 m2,
    bind_parameters ce e m l vl m1 ->
    bind_parameters ce e m l vl m2 ->
    m1 = m2.
Proof.
  induction l; intros until m2; intros B1 B2; inv B1; inv B2; auto.
  rewrite H1 in H9. inv H9.
  exploit assign_loc_det. eapply H3. eauto. intros. subst.
  eapply IHl; eauto.
Qed.

Fixpoint do_alloc_variables ce e m l : (env * mem) :=
  match l with
  | nil => (e, m)
  | (id, ty) :: l' =>
      let (m1, b) := Mem.alloc m 0 (sizeof ce ty) in
      do_alloc_variables ce (PTree.set id (b, ty) e) m1 l'
  end.

Lemma do_alloc_variables_sound: forall l ce e1 m1 e2 m2,
    do_alloc_variables ce e1 m1 l = (e2, m2) ->
    alloc_variables ce e1 m1 l e2 m2.
Proof.
  induction l; intros; simpl in *.
  inv H. econstructor; eauto.
  destruct a. destruct Mem.alloc eqn: ALLOC in H. econstructor; eauto.
Qed.


Fixpoint do_bind_parameters ce e m tyl al {struct tyl} : option mem :=
  match tyl, al with
  | nil, nil => Some m
  | (id, ty1) :: tyl', v :: al' =>
      match e ! id with
      | Some (b, ty2) =>
          if type_eq ty1 ty2 then
            match do_assign_loc ce ty1 m b Ptrofs.zero v with
            | Some m1 =>
                do_bind_parameters ce e m1 tyl' al'
            | _ => None
            end
          else None
      | _ => None
      end
  | _, _ => None
  end.

Lemma do_bind_parameters_sound: forall ce tyl al e m1 m2,
    do_bind_parameters ce e m1 tyl al = Some m2 ->
    bind_parameters ce e m1 tyl al m2.
Proof.  
  induction tyl; destruct al; intros; simpl in *; try congruence.
  - inv H. econstructor.
  - destruct a. try congruence.
  - destruct a. destruct (e!p) eqn: E; try congruence.
    destruct p0. destruct type_eq in H; try congruence. subst.
    destruct do_assign_loc eqn: ASS in H; try congruence.
    econstructor; eauto.
    eapply do_assign_loc_sound; eauto.
Qed.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (ce: composite_env) (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ce ty) end.

Definition blocks_of_env (ce: composite_env) (e: env) : list (block * Z * Z) :=
  List.map (block_of_binding ce) (PTree.elements e).

(** Return the list of places in local environment  *)

Definition place_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (Plocal id ty) end.

Definition places_of_env (e:env) : list place :=
  List.map place_of_binding (PTree.elements e).


(* Some functions used in generating initial own environment *)

Section WITH_CE.

Variable ce: composite_env.

Fixpoint collect_stmt (s: statement) (m: PathsMap.t) : PathsMap.t :=
  match s with
  | Sassign_variant p _ _ e
  | Sassign p e
  | Sbox p e =>
      collect_place ce p (collect_expr ce e m)
  | Scall p _ al =>
      collect_place ce p (collect_exprlist ce al m)
  | Sreturn p =>
      collect_place ce p m
  | Ssequence s1 s2 =>
      collect_stmt s1 (collect_stmt s2 m)
  | Sifthenelse e s1 s2 =>
      collect_stmt s1 (collect_stmt s2 (collect_expr ce e m))
  | Sloop s =>
      collect_stmt s m
  | Slet _ _ s =>
      collect_stmt s m
  | _ => m
  end.

Definition collect_func (f: function) : Errors.res PathsMap.t :=
  let vars := f.(fn_params) ++ f.(fn_vars) in  
  (* if list_norepet_dec ident_eq (map fst vars) then *)
    let l := map (fun elt => (Plocal (fst elt) (snd elt))) vars in
    (** TODO: add all the parameters and variables to l (may be useless?) *)
    let init_map := fold_right (collect_place ce) (PTree.empty LPaths.t) l in
    OK (collect_stmt f.(fn_body) init_map).
  (* else *)
  (*   Errors.Error (MSG "Repeated identifiers in variables and parameters: collect_func" :: nil). *)

End WITH_CE.

Definition inter_opt :=
  (fun a b : option LPaths.t =>
     match a with
     | Some u => match b with
                | Some v => Some (Paths.inter u v)
                | None => Some LPaths.bot
                end
     | None => None
     end).

(* extract it into lemma which is used in funciton_entry_sound in InitAnalysis *)
Lemma PathsMap_lub_union: forall id whole init uninit,
    PathsMap.eq whole (PathsMap.lub init uninit) ->
    LPaths.eq (Paths.union (PathsMap.get id init) (PathsMap.get id uninit))
      (PathsMap.get id whole).
Proof.
  intros until uninit. intros A.
  eapply LPaths.eq_sym.
  eapply LPaths.eq_trans. eapply A.
  red. red. intros a.
  unfold PathsMap.lub.
  set (g:=(fun a b : option LPaths.t =>
             match a with
             | Some u => match b with
                        | Some v => Some (LPaths.lub u v)
                        | None => a
                        end
             | None => b
             end)) in *.
  assert (C: g None None = None) by auto.
  exploit (PathsMap.gcombine g C init uninit).  
  instantiate (1 := id).
  intros OPTEQ.
  split; intros IN.
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine g init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      destruct (init ! id) eqn: INIT; destruct (uninit ! id) eqn: UNINIT; simpl in *; try contradiction.
      * eapply OPTEQ. auto.
      * eapply Paths.union_2.
        eapply OPTEQ. auto.
      * eapply Paths.union_3.
        eapply OPTEQ. auto.
    + simpl in OPTEQ.
      destruct (init ! id) eqn: INIT; destruct (uninit ! id) eqn: UNINIT; simpl in *; try contradiction.
      exfalso.
      eapply Paths.empty_1. eauto.
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine g init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      destruct (init ! id) eqn: INIT; destruct (uninit ! id) eqn: UNINIT; simpl in *; try contradiction.
      * eapply OPTEQ. auto.
      * eapply Paths.union_1 in IN.
        destruct IN.
        eapply OPTEQ. auto.
        exfalso. eapply Paths.empty_1. eauto.
      * eapply Paths.union_1 in IN.
        destruct IN.
        exfalso. eapply Paths.empty_1. eauto.
        eapply OPTEQ. auto.
    + simpl in OPTEQ.
      destruct (init ! id) eqn: INIT; destruct (uninit ! id) eqn: UNINIT; simpl in *; try contradiction.
      eapply Paths.union_1 in IN.
      destruct IN; auto.
Qed.

Definition places_of_locals (l: list (ident * type))  : list place :=
  map (fun elt => Plocal (fst elt) (snd elt)) l.

Definition check_own_env_consistency empty_pathmap init uninit whole : bool :=
  PathsMap.beq whole (PathsMap.lub init uninit) &&
    PathsMap.beq empty_pathmap (PathsMap.combine inter_opt init uninit).

(* Initialize the ownership environment by adding all the variables
and parameters to the uninit set. Then we initialize the parameters
with init_place function in step_internal_function to match
function_entry. *)
Program Definition init_own_env (ce: composite_env) (f: function) : Errors.res own_env :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  (* let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in *)
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let init := empty_pathmap in
  (* initialize maybeUninit with the variables and parameters *)
  let vl := places_of_locals (f.(fn_params) ++ f.(fn_vars)) in
  let uninit := add_place_list whole vl empty_pathmap in
  (** Is it reasonable? Translation validation: check (whole = init ∪
  uninit) and (∅ = init ∩ uninit) *)
  match check_own_env_consistency empty_pathmap init uninit whole with
  | true =>
      OK {| own_init := init;
           own_uninit := uninit;
           own_universe := whole |}
  | _ =>
      Error (msg "validation fail in init_own_env")
  end.
Next Obligation.
  symmetry in Heq_anonymous.
  eapply andb_true_iff in Heq_anonymous.
  destruct Heq_anonymous as (A & B).
  eapply PathsMap.beq_correct in A.
  eapply PathsMap.beq_correct in B.
  (* set (init:= (add_place_list whole *)
  (*             (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f)) *)
  (*             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *. *)
  (* set (whole := (collect_func ce f)) in *. *)
  set (init:= (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole)) in *.
  set (uninit :=(add_place_list whole
             (map (fun elt : ident * type => Plocal (fst elt) (snd elt))
                (fn_params f ++ fn_vars f))
             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *.
  clear B.
  eapply PathsMap_lub_union.
  auto.
Defined.
Next Obligation.
  symmetry in Heq_anonymous.
  eapply andb_true_iff in Heq_anonymous.
  destruct Heq_anonymous as (A & B).
  eapply PathsMap.beq_correct in A.
  eapply PathsMap.beq_correct in B.
  (* set (init:= (add_place_list whole *)
  (*             (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f)) *)
  (*             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *. *)
  (* set (whole := (collect_func ce f)) in *. *)
  set (init:= (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole)) at 1.
  fold init in A ,B.
  set (uninit :=(add_place_list whole
             (places_of_locals (f.(fn_params) ++ f.(fn_vars)))
             (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))) in *.
  red in B.
  generalize (B id). intros EQ.
  assert (EQ1: LPaths.eq (PathsMap.get id
                       (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) whole))
                    Paths.empty).  
  {  unfold PathsMap.get in *.
     erewrite PTree.gmap in *.
     destruct (whole ! id). simpl. eapply LPaths.eq_refl.
     simpl. eapply LPaths.eq_refl. }  
  eapply LPaths.eq_trans; eauto.
  (* core proof *)
  eapply LPaths.eq_sym.
  eapply LPaths.eq_trans. eapply B.
  red. red. intros a.
  assert (C: inter_opt None None = None) by auto.
  exploit (PathsMap.gcombine inter_opt C init uninit).  
  instantiate (1 := id).
  intros OPTEQ. clear EQ EQ1.
  (* init is the same as empty map, we need to take care of them *)
  unfold init at 2. fold uninit.
  split; intros IN.
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine inter_opt init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      (* Set Printing All. *)
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      * eapply OPTEQ. auto.
      * exfalso. eapply Paths.empty_1.
        eapply OPTEQ. eauto.                 
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      exfalso.
      eapply Paths.empty_1. eauto.
      exfalso.
      eapply Paths.empty_1. eauto.      
  - unfold PathsMap.get in *.
    destruct (PathsMap.combine inter_opt init uninit) ! id eqn: GC.
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      * eapply OPTEQ. auto.
      * eapply Paths.inter_2 in IN.
        exfalso. eapply Paths.empty_1. eauto.
    + simpl in OPTEQ.
      destruct (@PTree.get LPaths.t id init) eqn: INIT; destruct (@PTree.get LPaths.t id uninit) eqn: UNINIT; try contradiction.
      eapply Paths.inter_1 in IN.
      exfalso. eapply Paths.empty_1. eauto.
      eapply Paths.inter_1 in IN. auto.
Defined.  

(* Use extract_vars to extract the local variables *)

Inductive function_entry (ce: composite_env) (f: function) (vargs: list val) (m: mem) (e: env) (m2: mem) : Prop :=
| function_entry_intro: forall m1
    (* (VARS: vars = extract_vars f.(fn_body)) *)
    (NOREP: list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)))
    (ALLOC: alloc_variables ce empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1)
    (BIND: bind_parameters ce e m1 f.(fn_params) vargs m2),
    function_entry ce f vargs m e m2.


Section DROPMEMBER.

Variable ge: genv.

(** Some definitions for dropstate and dropplace *)
(* list of ownership types which are the children of [ty] *)
Fixpoint drop_glue_children_types (ty: type) : list type :=
  match ty with
  | Tbox ty' =>
      drop_glue_children_types ty' ++ [ty]
  | Tstruct _ id 
  | Tvariant _ id  => ty::nil
  | _ => nil
  end.

(* It corresponds to drop_glue_for_member in Clightgen *)
Definition type_to_drop_member_state (fid: ident) (fty: type) : option drop_member_state :=
  if own_type ge fty then
    let tys := drop_glue_children_types fty in
    match tys with
    | nil => None
    | ty :: tys' =>
        match ty with       
        | Tvariant _ id
        | Tstruct _ id =>
            (* provide evidence for the simulation *)
            match ge.(genv_dropm) ! id with
            | Some _ =>
                Some (drop_member_comp fid fty ty tys')
            | None => None
            end
        | _ => Some (drop_member_box fid fty tys)
        end
    end
  else None.

(* Load the value of [ty1] with the address of the starting block
(with type ty_k) from [ty1;ty2;ty3;...;ty_k] where ty_n points to
ty_{n-1} *)
Inductive deref_loc_rec (m: mem) (b: block) (ofs: ptrofs) : list type -> val -> Prop :=
| deref_loc_rec_nil:
    deref_loc_rec m b ofs nil (Vptr b ofs)
| deref_loc_rec_cons: forall ty tys b1 ofs1 v,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 v ->
    deref_loc_rec m b ofs (ty::tys) v
.

Inductive deref_loc_rec_mem_error (m: mem) (b: block) (ofs: ptrofs) : list type -> Prop :=
| deref_loc_rec_error1: forall ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
| deref_loc_rec_error2: forall ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc_mem_error ty m b1 ofs1 ->
    deref_loc_rec_mem_error m b ofs (ty::tys)
.


Lemma Vptrofs_det: forall sz1 sz2,
    Vptrofs sz1 = Vptrofs sz2 ->
    sz1 = sz2.
Proof.
  unfold Vptrofs.
  intros.  destruct Archi.ptr64 eqn: P.
  - destruct (Ptrofs.to_int64 sz1) eqn: S1.
    destruct (Ptrofs.to_int64 sz2) eqn: S2.
    inv H.
    unfold Ptrofs.to_int64 in *.
    Transparent Int64.repr.
    unfold Int64.repr in *. inv S1. inv S2.
    erewrite !Int64.Z_mod_modulus_eq in *.
    generalize (Ptrofs.unsigned_range sz1).
    generalize (Ptrofs.unsigned_range sz2).
    intros. rewrite !Ptrofs.modulus_eq64 in *; auto.
    erewrite !Z.mod_small in *; try lia.
    destruct sz1. destruct sz2. eapply Ptrofs.mkint_eq.
    simpl in H0. auto.
  - destruct (Ptrofs.to_int sz1) eqn: S1.
    destruct (Ptrofs.to_int sz2) eqn: S2.
    inv H.
    unfold Ptrofs.to_int in *.
    Transparent Int.repr.
    unfold Int.repr in *. inv S1. inv S2.
    erewrite !Int.Z_mod_modulus_eq in *.
    generalize (Ptrofs.unsigned_range sz1).
    generalize (Ptrofs.unsigned_range sz2).
    intros. rewrite !Ptrofs.modulus_eq32 in *; auto.
    erewrite !Z.mod_small in *; try lia.
    destruct sz1. destruct sz2. eapply Ptrofs.mkint_eq.
    simpl in H0. auto.
Qed.

Lemma extcall_free_sem_det se: forall m1 t v1 v2 v3 m2 m3,
    extcall_free_sem se v1 m1 t v2 m2 ->
    extcall_free_sem se v1 m1 t v3 m3 ->
    v2 = v3 /\ m2 = m3.
Proof.
  intros.
  inv H.
  - inv H0. rewrite H1 in H5.
    destruct (Val.eq (Vptrofs sz) (Vptrofs sz0)); try congruence.
    eapply Vptrofs_det in e. subst.
    rewrite H3 in H8. inv H8.
    auto.
  - inv H0. auto.
Qed.

(* big step to recursively drop boxes [Tbox (Tbox (Tbox
...))]. (b,ofs) is the address of the starting block *)
Inductive drop_box_rec (b: block) (ofs: ptrofs) : mem -> list type -> mem -> Prop :=
| drop_box_rec_nil: forall m,
    drop_box_rec b ofs m nil m
| drop_box_rec_cons: forall m m1 m2 b1 ofs1 ty tys b2 ofs2,
    (* (b1, ofs1) is the address of [ty], we want to free the memory
    location stored in (b1,ofs1). TODO: To prevent the complexity of deref_loc, we can use deref_loc_rec (ty::tys) instead of just tys, but we also need to change drop_glue_for_box_rec in Clightgen *)
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    (* if the result of deref_loc is not a pointer, it must be memory
    error!!! It is because in Compcert memory model, freeing a nullptr
    is not considerd U.B. Or we can just prove that drop_box_rec is
    total (has no any UB) ? *)
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    (* if v is nullptr, can we treat it as memory error? *)
    extcall_free_sem ge [(Vptr b2 ofs2)] m E0 Vundef m1 ->
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m (ty :: tys) m2
.


Lemma deref_loc_rec_det: forall tys b ofs m v1 v2,
    deref_loc_rec m b ofs tys v1 ->
    deref_loc_rec m b ofs tys v2 ->
    v1 = v2.
Proof.
  induction tys; intros.
  - inv H. inv H0. auto.
  - inv H. inv H0. exploit IHtys. eapply H3. eapply H2. intros A.
    inv A. eapply deref_loc_det; eauto.
Qed.


(* drop_box_rec is deterministic *)
Lemma drop_box_rec_det: forall tys b ofs m1 m2 m3,
    drop_box_rec b ofs m1 tys m2 ->
    drop_box_rec b ofs m1 tys m3 ->
    m2 = m3.
Proof.
  induction tys; intros.
  - inv H. inv H0. auto.
  - inv H. inv H0.
    exploit deref_loc_rec_det. eapply H3. eapply H2.
    intros A. inv A.
    exploit deref_loc_det. eapply H4. eapply H5. intros B. inv B.
    exploit extcall_free_sem_det. eapply H6. eapply H9.
    intros (C1 & C2). subst.
    eauto.
Qed.


Inductive extcall_free_sem_mem_error: list val -> mem -> Prop :=
| extcall_free_error1: forall (b : block) (lo : ptrofs) (m : mem),
    ~ Mem.valid_access m Mptr b (Ptrofs.unsigned lo - size_chunk Mptr) Readable ->
    extcall_free_sem_mem_error [Vptr b lo] m
| extcall_free_error2: forall (b : block) (lo sz : ptrofs) (m : mem),
    Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) = Some (Vptrofs sz) ->
    Ptrofs.unsigned sz > 0 ->
    ~ Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable ->
    extcall_free_sem_mem_error [Vptr b lo] m.


Inductive drop_box_rec_mem_error (b: block) (ofs: ptrofs) : mem -> list type -> Prop :=
| drop_box_rec_error1: forall m ty tys,
    deref_loc_rec_mem_error m b ofs tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error2: forall m ty tys b1 ofs1,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc_mem_error ty m b1 ofs1 ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error3: forall m ty tys b1 ofs1 b2 ofs2,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    extcall_free_sem_mem_error [Vptr b2 ofs2] m ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
| drop_box_rec_error4: forall m m1 ty tys b1 ofs1 b2 ofs2,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    deref_loc ty m b1 ofs1 (Vptr b2 ofs2) ->
    extcall_free_sem ge [Vptr b2 ofs2] m E0 Vundef m1 ->
    drop_box_rec_mem_error b ofs m1 tys ->
    drop_box_rec_mem_error b ofs m (ty :: tys)
.

End DROPMEMBER.

Section SMALLSTEP.

Variable ge: genv.
  
(* Mostly the same as RustIRsem *)
Inductive step_drop : state -> trace -> state -> Prop :=
| step_dropstate_init: forall id b ofs fid fty membs k m,
    step_drop (Dropstate id (Vptr b ofs) None ((Member_plain fid fty) :: membs) k m) E0 (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) membs k m)
| step_dropstate_struct: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (STRUCT: co2.(co_sv) = Struct),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) None co2.(co_members) (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid fty tys)) membs k) m)
| step_dropstate_enum: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fid2 fty2 fofs tag orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr cb cofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co2.(co_members) (Int.unsigned tag) = Some (Member_plain fid2 fty2)),
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m) E0
      (Dropstate id2 (Vptr cb cofs) (type_to_drop_member_state ge fid2 fty2) nil (Kdropcall id1 (Vptr b1 ofs1) (Some (drop_member_box fid1 fty1 tys)) membs k) m)
| step_dropstate_box: forall b ofs id co fid fofs m m' tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (DROPB: drop_box_rec ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys m'),
    step_drop
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m) E0
      (Dropstate id (Vptr b ofs) None membs k m')
| step_dropstate_return1: forall b ofs id m f e own k ps s,
    step_drop
      (* maybe we should separate step_dropstate_return to reuse
      step_drop because of the mismatch between Kdropplace and Kcall
      in RustIRown and RUstIRsem *)
      (Dropstate id (Vptr b ofs) None nil (Kdropplace f s ps e own k) m) E0
      (Dropplace f s ps k e own m)
| step_dropstate_return2: forall b1 b2 ofs1 ofs2 id1 id2 m k membs s,
    step_drop
      (Dropstate id1 (Vptr b1 ofs1) None nil (Kdropcall id2 (Vptr b2 ofs2) s membs k) m) E0
      (Dropstate id2 (Vptr b2 ofs2) s membs k m)
.

Inductive step_drop_mem_error : state -> Prop :=
| step_dropstate_struct_error: forall id1 id2 co1 b1 ofs1 tys m k membs fid fty fofs orgs
    (* step to another struct drop glue *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid fty (Tstruct orgs id2) tys)) membs k m)
| step_dropstate_enum_error1: forall id1 id2 co1 b1 ofs1 tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* error in loading the address of the composite *)
    (DEREF: deref_loc_rec_mem_error m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys),
    step_drop_mem_error
    (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)
| step_dropstate_enum_error2: forall id1 id2 co1 co2 b1 ofs1 cb cofs tys m k membs fid1 fty1 fofs orgs
    (* step to another enum drop glue: remember to evaluate the switch statements *)
    (CO1: ge.(genv_cenv) ! id1 = Some co1)
    (* evaluate the value of the argument for the drop glue of id2 *)
    (FOFS: match co1.(co_sv) with
           | Struct => field_offset ge fid1 co1.(co_members)
           | TaggedUnion => variant_field_offset ge fid1 co1.(co_members)
           end = OK fofs)
    (* (cb, cofs is the address of composite id2) *)
    (DEREF: deref_loc_rec m b1 (Ptrofs.add ofs1 (Ptrofs.repr fofs)) tys (Vptr cb cofs))
    (CO2: ge.(genv_cenv) ! id2 = Some co2)
    (ENUM: co2.(co_sv) = TaggedUnion)
    (* error in loading the tag *)
    (TAG: ~ Mem.valid_access m Mint32 cb (Ptrofs.unsigned cofs) Readable),
    step_drop_mem_error
      (Dropstate id1 (Vptr b1 ofs1) (Some (drop_member_comp fid1 fty1 (Tvariant orgs id2) tys)) membs k m)      
| step_dropstate_box_error: forall b ofs id co fid fofs m tys k membs fty
    (CO1: ge.(genv_cenv) ! id = Some co)
    (* evaluate the value of the argument of the drop glue for id2 *)
    (FOFS: match co.(co_sv) with
           | Struct => field_offset ge fid co.(co_members)
           | TaggedUnion => variant_field_offset ge fid co.(co_members)
           end = OK fofs)
    (* error in dropping the box chain *)
    (DROPB: drop_box_rec_mem_error ge b (Ptrofs.add ofs (Ptrofs.repr fofs)) m tys),
    step_drop_mem_error
      (Dropstate id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k m)
.


Inductive step_dropplace : state -> trace -> state -> Prop :=
| step_dropplace_init1: forall f p ps k le own m full
    (* p is not owned, so just skip it (How to relate this case with
    RustIRsem because drop elaboration removes this place earlier in
    generate_drop_flag) *)
    (NOTOWN: is_init own p = false),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f None ps k le own m)
| step_dropplace_init2: forall f p ps k le own m st (full: bool)
    (OWN: is_init own p = true)
    (NOTSCALAR: scalar_type (typeof_place p) = false)
    (DPLACE: st = (if full then gen_drop_place_state p else drop_fully_owned_box [p])),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f (Some st) ps k le (move_place own p) m)
(* split_drop_place may generate some places which have scalar type,
in the semantics, we skip this drop placs and in the compilation, we
generate Sskip for them *)
| step_dropplace_scalar: forall f p ps k le own m full
    (OWN: is_init own p = true)
    (SCALAR: scalar_type (typeof_place p) = true),
    step_dropplace (Dropplace f None ((p, full) :: ps) k le own m) E0
      (Dropplace f None ps k le (move_place own p) m)    
| step_dropplace_box: forall le m m' k ty b' ofs' f b ofs p own ps l
    (* simulate step_drop_box in RustIRsem *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (* If the result of deref_loc is not a pointer, it is also a case of memory error!!! *)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* Simulate free semantics *)
    (FREE: extcall_free_sem ge [Vptr b' ofs'] m E0 Vundef m'),
    (* We are dropping p. fp is the fully owned place which is split into p::l *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m) E0
      (Dropplace f (Some (drop_fully_owned_box l)) ps k le own m')
| step_dropplace_struct: forall m k orgs co id p b ofs f le own ps l
    (* It corresponds to the call step to the drop glue of this struct *)
    (PTY: typeof_place p = Tstruct orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COSTRUCT: co.(co_sv) = Struct)
    (PADDR: eval_place ge le m p b ofs),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) None co.(co_members) (Kdropplace f (Some (drop_fully_owned_box l)) ps le own  k) m)
| step_dropplace_enum: forall m k p orgs co id fid fty tag b ofs f le own ps l
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* big step to evaluate the switch statement *)
    (* load tag  *)
    (TAG: Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint tag))
    (* use tag to choose the member *)
    (MEMB: list_nth_z co.(co_members) (Int.unsigned tag) = Some (Member_plain fid fty)),
    (* update the ownership environment in continuation *)
    step_dropplace (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m) E0
      (Dropstate id (Vptr b ofs) (type_to_drop_member_state ge fid fty) nil (Kdropplace f (Some (drop_fully_owned_box l)) ps le own k) m)
| step_dropplace_next: forall f ps k le own m,
    step_dropplace (Dropplace f (Some (drop_fully_owned_box nil)) ps k le own m) E0
      (Dropplace f None ps k le own m)
(* return to the dropinsert state because all the dropplace states
come from dropinsert *)
| step_dropplace_return: forall f k le own m l dk,
    step_dropplace (Dropplace f None nil (Kdropinsert l dk k) le own m) E0
      (Dropinsert f l dk k le own m)
.

Inductive step_dropplace_mem_error: state -> Prop :=
| step_dropplace_box_error1: forall le m k f p own ps l
    (* eval_place error *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error2: forall le m k f p own ps l b ofs ty
    (* deref_loc error *)
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc_mem_error (Tbox ty) m b ofs),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_box_error3: forall le m k f p own ps l b ofs ty b' ofs'
    (PADDR: eval_place ge le m p b ofs)
    (PTY: typeof_place p = Tbox ty)
    (PVAL: deref_loc (Tbox ty) m b ofs (Vptr b' ofs'))
    (* free error *)
    (FREE: extcall_free_sem_mem_error [Vptr b' ofs'] m),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_box (p :: l))) ps k le own m)
| step_dropplace_struct_error: forall m k p f le own ps l orgs id co
    (TYP: typeof_place p = Tstruct orgs id)
    (CO: (genv_cenv ge) ! id = Some co)
    (STRUCT: co_sv co = Struct)
    (* p is struct or enum *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
| step_dropplace_enum_error1: forall m k p f le own ps l orgs id co
    (TYP: typeof_place p = Tvariant orgs id)
    (CO: (genv_cenv ge) ! id = Some co)
    (STRUCT: co_sv co = TaggedUnion)
    (* p is struct or enum *)
    (PADDR: eval_place_mem_error ge le m p),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
| step_dropplace_enum_error2: forall m k p orgs co id b ofs f le own ps l
    (PTY: typeof_place p = Tvariant orgs id)
    (SCO: ge.(genv_cenv) ! id = Some co)
    (COENUM: co.(co_sv) = TaggedUnion)
    (PADDR: eval_place ge le m p b ofs)
    (* error in loading the tag *)
    (ERR: ~ Mem.valid_access m Mint32 b (Ptrofs.unsigned ofs) Readable),
    step_dropplace_mem_error (Dropplace f (Some (drop_fully_owned_comp p l)) ps k le own m)
.


Definition function_not_drop_glue fd : Prop :=
  match fd with
  | Internal f =>
    match fn_drop_glue f with
    | None => True
    | Some _ => False
    end
  | External _ _ EF _ _ _ =>
    match EF with
    | EF_malloc => False
    | EF_free => False
    | _ => True
    end
  end.

(* small step in dropinsert *)
Inductive step_dropinsert : state -> trace -> state -> Prop :=
(* simulate step_to_dropplace in RustIRown *)
| step_dropinsert_to_dropplace_escape: forall f id ty le own m drops k universe dk l
    (UNI: PathsMap.get id own.(own_universe) = universe)
    (OWNTY: own_type ge ty = true)
    (SPLIT: split_drop_place ge universe (Plocal id ty) ty = OK drops),
    (* get the owned place to drop *)
    step_dropinsert (Dropinsert f (drop_escape_before ((id, ty) :: l)) dk k le own m) E0
      (Dropplace f None drops (Kdropinsert (drop_escape_after id l) dk k) le own m)
| step_dropinsert_to_dropplace_reassign: forall f p le own m drops k universe dk
    (UNI: PathsMap.get (local_of_place p) own.(own_universe) = universe)
    (OWNTY: own_type ge (typeof_place p) = true)
    (SPLIT: split_drop_place ge universe p (typeof_place p) = OK drops),
    (* get the owned place to drop *)
    step_dropinsert (Dropinsert f (drop_reassign p) dk k le own m) E0
      (Dropplace f None drops (Kdropinsert drop_end dk k) le own m)
| step_dropinsert_skip_escape: forall f id ty le own m k dk l
    (OWNTY: own_type ge ty = false),
    step_dropinsert (Dropinsert f (drop_escape_before ((id, ty) :: l)) dk k le own m) E0
      (Dropinsert f (drop_escape_after id l) dk k le own m)
| step_dropinsert_skip_reassign: forall f p le own m k dk
    (OWNTY: own_type ge (typeof_place p) = false),
    step_dropinsert (Dropinsert f (drop_reassign p) dk k le own m) E0
      (Dropinsert f drop_end dk k le own m)
(* drop the parameters *)
| step_dropinsert_to_dropplace_return: forall f id ty le own m drops k universe dk l
    (UNI: PathsMap.get id own.(own_universe) = universe)
    (OWNTY: own_type ge ty = true)
    (SPLIT: split_drop_place ge universe (Plocal id ty) ty = OK drops),
    (* get the owned place to drop *)
    step_dropinsert (Dropinsert f (drop_return ((id, ty) :: l)) dk k le own m) E0
      (Dropplace f None drops (Kdropinsert (drop_return l) dk k) le own m)
| step_dropinsert_skip_return: forall f id ty le own m k dk l
    (OWNTY: own_type ge ty = false),
    step_dropinsert (Dropinsert f (drop_return ((id, ty) :: l)) dk k le own m) E0
      (Dropinsert f (drop_return l) dk k le own m)
(* simulate the storagedead *)
| step_dropinsert_escape_to_after: forall f id le own m k dk l,
    step_dropinsert (Dropinsert f (drop_escape_after id l) dk k le own m) E0
      (Dropinsert f (drop_escape_before l) dk k le own m)
| step_dropinsert_to_drop_end: forall f le own m k dk
    (NOTRETURN: (forall p, dk <> Dreturn p) /\ dk <> Dendlet),
    step_dropinsert (Dropinsert f (drop_escape_before []) dk k le own m) E0
      (Dropinsert f drop_end dk k le own m)
      
| step_dropinsert_assign: forall f e p k le m1 m2 b ofs v v1 own1 own2 own3
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (TYP: forall orgs id, typeof_place p <> Tvariant orgs id),
    (* get the location of the place *)
    eval_place ge le m1 p b ofs ->
    (* evaluate the expr, return the value *)
    eval_expr ge le m1 ge e v ->
    (* sem_cast to simulate Clight *)
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    (* assign to p *)
    assign_loc ge (typeof_place p) m1 b ofs v1 m2 ->
    step_dropinsert (Dropinsert f drop_end (Dassign p e) k le own1 m1) E0
                    (State f Sskip k le own3 m2)
| step_dropinsert_assign_variant: forall f e p ty k le m1 m2 m3 b ofs b1 ofs1 v v1 tag co fid enum_id orgs own1 own2 own3 fofs
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3)
    (* necessary for clightgen simulation *)
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (* evaluate the expr, return the value *)
    (EXPR: eval_expr ge le m1 ge e v)
    (* evaluate the location of the variant in p (in memory m1) *)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (* sem_cast to simulate Clight *)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* set the value *)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (** different from normal assignment: update the tag and assign value *)
    (TAG: field_tag fid co.(co_members) = Some tag)
    (* eval the location of the tag: to simulate the target statement:
    because we cannot guarantee that store value in m1 does not change    the address of p! (Non-interference is a difficult problem!) *)
    (PADDR2: eval_place ge le m2 p b1 ofs1)
    (* set the tag *)
    (STAG: Mem.storev Mint32 m2 (Vptr b1 ofs1) (Vint (Int.repr tag)) = Some m3),
    step_dropinsert (Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own1 m1) E0 (State f Sskip k le own3 m3)
| step_dropinsert_box: forall f e p ty k le m1 m2 m3 m4 m5 b v v1 pb pofs own1 own2 own3
    (* check ownership *)
    (TFEXPR: move_place_option own1 (moved_place e) = own2)
    (TFASSIGN: own_transfer_assign own2 p = own3),
    typeof_place p = Tbox ty ->
    (* Simulate malloc semantics to allocate the memory block *)
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* evaluate the expression after malloc to simulate*)
    eval_expr ge le m3 ge e v ->
    (* sem_cast the value to simulate function call in Clight *)
    sem_cast v (typeof e) ty = Some v1 ->
    (* assign the value to the allocated location *)
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* assign the address to p *)
    eval_place ge le m4 p pb pofs ->
    assign_loc ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) m5 ->
    step_dropinsert (Dropinsert f drop_end (Dbox p e) k le own1 m1) E0 (State f Sskip k le own3 m5)
| step_dropinset_call: forall f a al k le m vargs tyargs vf fd cconv tyres p orgs org_rels own1 own2
    (TFEXPRLIST: move_place_list own1 (moved_place_list al) = own2),    
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    eval_expr ge le m ge a vf ->
    eval_exprlist ge le m ge al tyargs vargs ->
    Genv.find_funct ge vf = Some fd ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    function_not_drop_glue fd ->
    step_dropinsert (Dropinsert f drop_end (Dcall p a al) k le own1 m) E0 (Callstate vf vargs (Kcall p f le own2 k) m)
| step_dropinsert_break_seq: forall f s k le own m,
    step_dropinsert (Dropinsert f drop_end Dbreak (Kseq s k) le own m) E0
      (Dropinsert f (drop_end) Dbreak k le own m)
| step_dropinsert_break_let: forall f k le own m id ty,
    (* this variable has been dropped when we meet the break statement *)
    step_dropinsert (Dropinsert f (drop_end) Dbreak (Klet id ty k) le own m) E0
      (Dropinsert f (drop_end) Dbreak k le own m)
| step_dropinsert_break_loop: forall f s k le own m,
    step_dropinsert (Dropinsert f (drop_end) Dbreak (Kloop s k) le own m) E0
      (State f Sskip k le own m)
| step_dropinsert_continue_seq: forall f s k le own m,
    step_dropinsert (Dropinsert f (drop_end) Dcontinue (Kseq s k) le own m) E0
      (Dropinsert f(drop_end) Dcontinue k le own m)
| step_dropinsert_continue_let: forall f k le own m id ty,
    (* This variable declare in the scope that Scontinue should escape *)
    step_dropinsert (Dropinsert f (drop_end) Dcontinue (Klet id ty k) le own m) E0
      (Dropinsert f (drop_end) Dcontinue k le own m)
| step_dropinsert_continue_loop: forall f s k le own m,
    step_dropinsert (Dropinsert f (drop_end) Dcontinue (Kloop s k) le own m) E0
      (State f s (Kloop s k) le own m)
(* drop_escape before dropping the parameters *)
| step_dropinsert_return_before: forall f p k le own m1,
    (* use this step  *)
    step_dropinsert (Dropinsert f (drop_escape_before []) (Dreturn p) k le own m1) E0
    (Dropinsert f (drop_return f.(fn_params)) (Dreturn p) k le own m1)
| step_dropinsert_return_after: forall f p v v1 k ck le own m1 m2 lb
    (EXPR: eval_expr ge le m1 ge (Epure (Eplace p (typeof_place p))) v)
    (* sem_cast to the return type *)
    (CAST: sem_cast v (typeof_place p) f.(fn_return) = Some v1)
    (CONT: call_cont k = Some ck),
    (* free stack blocks *)
    blocks_of_env ge le = lb ->
    Mem.free_list m1 lb = Some m2 ->    
    step_dropinsert (Dropinsert f (drop_return []) (Dreturn p) k le own m1) E0
      (Returnstate v1 ck m2)
| step_dropinsert_endlet: forall f k le own m,
    (* adhoc: not use drop_end here is to make sure that target cound make a step *)
  step_dropinsert (Dropinsert f (drop_escape_before []) Dendlet k le own m) E0
      (State f Sskip k le own m)
.

Inductive step_dropinsert_mem_error : state -> Prop :=
| step_dropinsert_assign_error1: forall f e p k le m own,    
    eval_expr_mem_error ge le m e ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign p e) k le own m)
| step_dropinsert_assign_error2: forall f e p k le m own v,
    eval_expr ge le m ge e v ->
    eval_place_mem_error ge le m p ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign p e) k le own m)
| step_dropinsert_assign_error3: forall f e p k le m b ofs v v1 own,
    eval_place ge le m p b ofs ->
    eval_expr ge le m ge e v ->
    sem_cast v (typeof e) (typeof_place p) = Some v1 ->
    assign_loc_mem_error ge (typeof_place p) m b ofs v1 ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign p e) k le own m)
| step_dropinsert_assign_variant_error1: forall f e p k le m enum_id fid own,
    (* error in evaluating the expression *)
    eval_expr_mem_error ge le m e ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own m)
| step_dropinsert_assign_variant_error2: forall f e p k le v m enum_id fid own,
    eval_expr ge le m ge e v ->
    (* error in evaluating lhs *)
    eval_place_mem_error ge le m p ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own m)
| step_dropinsert_assign_variant_error3: forall f e p ty k le m1 b ofs v v1 co fid enum_id orgs own fofs
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (* error in assigning the value to the enum body *)
    (ERR: assign_loc_mem_error ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1),
    step_dropinsert_mem_error(Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own m1)
| step_dropinsert_assign_variant_error4: forall f e p ty k le m1 m2 b ofs v v1 co fid enum_id orgs own fofs
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (* error in evaluating the place in the second time *)
    (ERR: eval_place_mem_error ge le m2 p),
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own m1)
| step_dropinsert_assign_variant_error5: forall f e p ty k le m1 m2 b ofs b1 ofs1 v v1 co fid enum_id orgs own fofs tag
    (TYP: typeof_place p = Tvariant orgs enum_id)
    (CO: ge.(genv_cenv) ! enum_id = Some co)
    (FTY: field_type fid co.(co_members) = OK ty)
    (EXPR: eval_expr ge le m1 ge e v)
    (PADDR1: eval_place ge le m1 p b ofs)
    (FOFS: variant_field_offset ge fid co.(co_members) = OK fofs)
    (CAST: sem_cast v (typeof e) ty = Some v1)
    (AS: assign_loc ge ty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v1 m2)
    (PADDR: eval_place ge le m2 p b1 ofs1)
    (TAG: field_tag fid (co_members co) = Some tag)
    (* error in storing the tag *)
    (ERR: ~ Mem.valid_access m2 Mint32 b1 (Ptrofs.unsigned ofs1) Writable),
    step_dropinsert_mem_error (Dropinsert f drop_end (Dassign_variant p enum_id fid e) k le own m1)
| step_dropinsert_box_error1: forall le e p k m1 m2 f b ty own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    (* error in storing the size *)
    ~ Mem.valid_access m2 Mptr b (- size_chunk Mptr) Writable ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dbox p e) k le own m1)
| step_dropinsert_box_error2: forall le e p k m1 m2 m3 f b ty own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    (* error in evaluating the rhs *)
    eval_expr_mem_error ge le m3 e ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dbox p e) k le own m1)
| step_dropinsert_box_error3: forall le e p k m1 m2 m3 f b ty v v1 own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    (* error in storing the rhs *)
    assign_loc_mem_error ge ty m3 b Ptrofs.zero v1 ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dbox p e) k le own m1)
| step_dropinsert_box_error4: forall le e p k m1 m2 m3 m4 f b ty v v1 own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    (* error in evaluating the address of lhs *)
    eval_place_mem_error ge le m4 p ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dbox p e) k le own m1)
| step_dropinsert_box_error5: forall le e p k m1 m2 m3 m4 f b ty v v1 pb pofs own,
    typeof_place p = Tbox ty ->
    Mem.alloc m1 (- size_chunk Mptr) (sizeof ge (typeof e)) = (m2, b) ->
    Mem.store Mptr m2 b (- size_chunk Mptr) (Vptrofs (Ptrofs.repr (sizeof ge (typeof e)))) = Some m3 ->
    eval_expr ge le m3 ge e v ->
    sem_cast v (typeof e) ty = Some v1 ->
    assign_loc ge ty m3 b Ptrofs.zero v1 m4 ->
    eval_place ge le m4 p pb pofs ->
    (* error in assigning the allocated block to the lhs *)
    assign_loc_mem_error ge (typeof_place p) m4 pb pofs (Vptr b Ptrofs.zero) ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dbox p e) k le own m1)
| step_dropinsert_call_error1: forall f a al k le m p own,
    (* error in evaluating the function pointer *)
    eval_expr_mem_error ge le m a ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dcall p a al) k le own m)
| step_dropinsert_call_error2: forall f a al k le m  tyargs vf p own tyres cconv,
    eval_expr ge le m ge a vf ->
    classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
    (* error in evaluating the expression list *)
    eval_exprlist_mem_error ge le m ge al tyargs ->
    step_dropinsert_mem_error (Dropinsert f drop_end (Dcall p a al) k le own m)
| step_dropinsert_return_error1: forall f p k le m own,
    eval_expr_mem_error ge le m (Epure (Eplace p (typeof_place p)))->
    step_dropinsert_mem_error (Dropinsert f (drop_return []) (Dreturn p) k le own m)
| step_dropinsert_return_error2: forall f p k le m own,
    Mem.free_list m (blocks_of_env ge le) = None ->
    step_dropinsert_mem_error (Dropinsert f (drop_return []) (Dreturn p) k le own m)

.


Inductive step : state -> trace -> state -> Prop :=
| step_assign: forall f e p k le m own,
    step (State f (Sassign p e) k le own m) E0 (Dropinsert f (drop_reassign p) (Dassign p e) k le own m)
| step_assign_variant: forall f e p k le m own enum_id fid,
    step (State f (Sassign_variant p enum_id fid e) k le own m) E0 (Dropinsert f (drop_reassign p) (Dassign_variant p enum_id fid e) k le own m)         
| step_box: forall f e p k le m own,
    step (State f (Sbox p e) k le own m) E0 (Dropinsert f (drop_reassign p) (Dbox p e) k le own m)
| step_let: forall f ty id own m k s le,
    step (State f (Slet id ty s) k le own m) E0 (State f s (Klet id ty k) le own m)
(* End of a let statement, drop the place *)
| step_end_let: forall f id ty k le m own,
    step (State f Sskip (Klet id ty k) le own m) E0 (Dropinsert f (drop_escape_before [(id,ty)]) Dendlet k le own m)

(** dynamic drop semantics: simulate the drop elaboration *)
| step_in_dropinsert: forall f l dk k le own m E S
    (SDROP: step_dropinsert (Dropinsert f l dk k le own m) E S),
    step (Dropinsert f l dk k le own m) E S
| step_in_dropplace: forall f s ps k le own m E S
    (SDROP: step_dropplace (Dropplace f s ps k le own m) E S),
    step (Dropplace f s ps k le own m) E S
| step_dropstate: forall id v s membs k m S E
    (SDROP: step_drop (Dropstate id v s membs k m) E S),
    step (Dropstate id v s membs k m) E S

| step_call: forall f a al k le m own p,
    step (State f (Scall p a al) k le own m) E0 (Dropinsert f (drop_reassign p) (Dcall p a al) k le own m)

| step_internal_function: forall vf f vargs k m e m' own1 own2
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (NORMAL: f.(fn_drop_glue) = None)
    (ENTRY: function_entry ge f vargs m e m')
    (* initialize own_env *)
    (INITOWN: init_own_env ge f = OK own1)
    (INITPARAMS: init_place_list own1 (places_of_locals f.(fn_params)) = own2),
    step (Callstate vf vargs k m) E0 (State f f.(fn_body) k e own2 m')

| step_external_function: forall vf vargs k m m' cc ty typs ef v t orgs org_rels
    (FIND: Genv.find_funct ge vf = Some (External orgs org_rels ef typs ty cc))
    (NORMAL: ef <> EF_malloc /\ ef <> EF_free),
    external_call ef ge vargs m t v m' ->
    step (Callstate vf vargs k m) t (Returnstate v k m')

(** Return cases: for now, we do not allow return None (i.e., a
function has void return type). All functions must have some return
type, at least unit type. *)
(* | step_return_0: forall e f k own drops param_drops m *)
(*     (VARDROPS: drops = vars_to_drops ge (concat (cont_vars k))) *)
(*     (PARAMDROPS: param_drops = vars_to_drops ge f.(fn_params)), *)
(*     step (State f (Sreturn p) k e own m) E0 (Dropinsert f (drops++param_drops) (Dreturn Vundef) k e own m) *)
| step_return_1: forall le p m f k own1 (* drops param_drops *),
    step (State f (Sreturn p) k le own1 m) E0 (Dropinsert f (drop_escape_before (concat (cont_vars k))) (Dreturn p) k le own1 m)

(** no return statement but reach the end of the function. How to
support it in rust semantics? How to compile it to Clight? In Clight,
return nothing is only valid in void function! *)
(* | step_skip_call: forall e f k own drops param_drops m *)
(*     (CALLCONT: is_call_cont k) *)
(*     (VARDROPS: drops = vars_to_drops ge (concat (cont_vars k))) *)
(*     (PARAMDROPS: param_drops = vars_to_drops ge f.(fn_params)), *)
(*     step (State f Sskip k e own m) E0 (Dropinsert f (drops++param_drops) (Dreturn Vundef) k e own m) *)
  
| step_returnstate: forall p v b ofs m1 m2 e f k own1 own2
    (TFASSIGN: own_transfer_assign own1 p = own2),
    eval_place ge e m1 p b ofs ->
    val_casted v (typeof_place p) ->
    assign_loc ge (typeof_place p) m1 b ofs v m2 ->    
    step (Returnstate v (Kcall p f e own1 k) m1) E0 (State f Sskip k e own2 m2)

(* Control flow statements *)
| step_seq:  forall f s1 s2 k e m own,
    step (State f (Ssequence s1 s2) k e own m)
      E0 (State f s1 (Kseq s2 k) e own m)
| step_skip_seq: forall f s k e m own,
    step (State f Sskip (Kseq s k) e own m)
      E0 (State f s k e own m)
| step_continue_insert_drops: forall f k e m own,
    (* get the places to insert drop *)
    step (State f Scontinue k e own m)
      E0 (Dropinsert f (drop_escape_before (hd nil (cont_vars k))) Dcontinue k e own m)
| step_break_insert_drops: forall f k e m own,
    (* get the places to insert drop *)
    step (State f Sbreak k e own m)
      E0 (Dropinsert f (drop_escape_before (hd nil (cont_vars k))) Dbreak k e own m)
| step_ifthenelse:  forall f a s1 s2 k e m v1 b ty own1,
    (* there is no receiver for the moved place, so it must be None *)
    eval_expr ge e m ge a v1 ->
    to_ctype (typeof a) = ty ->
    bool_val v1 ty m = Some b ->
    step (State f (Sifthenelse a s1 s2) k e own1 m)
      E0 (State f (if b then s1 else s2) k e own1 m)
| step_loop: forall f s k e m own,
    step (State f (Sloop s) k e own m)
      E0 (State f s (Kloop s k) e own m)
| step_skip_or_continue_loop: forall f x s k e m own,
     x = Sskip \/ x = Scontinue ->
    step (State f x (Kloop s k) e own m)
      E0 (State f s (Kloop s k) e own m)
.



(** Open semantics *)

Inductive initial_state: rust_query -> state -> Prop :=
| initial_state_intro: forall vf f targs tres tcc vargs m orgs org_rels,
    Genv.find_funct ge vf = Some (Internal f) ->
    type_of_function f = Tfunction orgs org_rels targs tres tcc ->
    (* This function must not be drop glue *)
    f.(fn_drop_glue) = None ->
    (* how to use it? *)
    val_casted_list vargs targs ->
    (* Mem.sup_include (Genv.genv_sup ge) (Mem.support m) -> *)
    initial_state (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres tcc ge) vargs m)
      (Callstate vf vargs Kstop m).
    
Inductive at_external: state -> rust_query -> Prop:=
| at_external_intro: forall vf name args k m targs tres cconv orgs org_rels,
    Genv.find_funct ge vf = Some (External orgs org_rels (EF_external name (signature_of_type targs tres cconv)) targs tres cconv) ->
    at_external (Callstate vf args k m) (rsq vf (mksignature orgs org_rels (type_list_of_typelist targs) tres cconv ge) args m).

Inductive after_external: state -> rust_reply -> state -> Prop:=
| after_external_intro: forall vf args k m m' v,
    after_external
      (Callstate vf args k m)
      (rsr v m')
      (Returnstate v k m').

Inductive final_state: state -> rust_reply -> Prop:=
| final_state_intro: forall v m,
    final_state (Returnstate v Kstop m) (rsr v m).

(* memory error state *)

Inductive function_entry_mem_error (f: function) (vargs: list val) (m: mem) (e: env) : Prop :=
  | function_entry_mem_error_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters_mem_error ge e m1 f.(fn_params) vargs ->
      function_entry_mem_error f vargs m e.

Inductive step_mem_error : state -> Prop :=
| step_dropinsert_error: forall f l dk k le own m,
    step_dropinsert_mem_error (Dropinsert f l dk k le own m) ->
    step_mem_error (Dropinsert f l dk k le own m)
| step_dropplace_error: forall f st ps k le own m,
    step_dropplace_mem_error (Dropplace f st ps k le own m) ->
    step_mem_error (Dropplace f st ps k le own m)

| step_dropstate_error: forall id v s membs k m,
    step_drop_mem_error (Dropstate id v s membs k m) ->
    step_mem_error (Dropstate id v s membs k m)
| step_internal_function_error: forall vf f vargs k m e own1 own2
    (FIND: Genv.find_funct ge vf = Some (Internal f))
    (OWN1: init_own_env ge f = OK own1)
    (OWN2: init_place_list own1 (places_of_locals (fn_params f)) = own2),
    function_entry_mem_error f vargs m e ->
    step_mem_error (Callstate vf vargs k m)
(* | step_return_0_error: forall f k le m own, *)
(*     Mem.free_list m (blocks_of_env ge le) = None -> *)
(*     step_mem_error (State f (Sreturn p) k le own m) *)
| step_returnstate_error1: forall p v m f k e own,
    eval_place_mem_error ge e m p ->
    step_mem_error (Returnstate v (Kcall p f e own k) m)
| step_returnstate_error2: forall p v m f k e b ofs ty own,
    ty = typeof_place p ->
    eval_place ge e m p b ofs ->
    assign_loc_mem_error ge ty m b ofs v ->
    step_mem_error (Returnstate v (Kcall p f e own k) m)
| step_ifthenelse_error:  forall f a s1 s2 k e m own,
    eval_expr_mem_error ge e m a ->
    step_mem_error (State f (Sifthenelse a s1 s2) k e own m)
.


End SMALLSTEP.

End SEMANTICS.

Definition mem_error (p: program) (se: Genv.symtbl) (s: state) : Prop :=
  step_mem_error (globalenv se p) s.
  
Definition semantics (p: program) :=
  Semantics_gen step initial_state at_external (fun _ => after_external) (fun _ => final_state) globalenv p.

(** Receptive *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros p se. unfold semantics. simpl.
  set (ge := globalenv se p). constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step ge s t2 s2).
  intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  inversion SDROP; subst; auto.
  inversion SDROP; subst; auto.
  inversion SDROP; subst; auto.  
  (* external *)
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]].
  exists (Returnstate vres2 k m2). econstructor; eauto.
  (* trace length *)
  red; simpl; intros. inv H; try inv SDROP; simpl; try lia.
  eapply external_call_trace_length; eauto.
Qed.
 
