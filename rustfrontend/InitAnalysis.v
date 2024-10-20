Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustIR RustIRcfg RustIRown.
Require Import InitDomain.

Import ListNotations.
Local Open Scope list_scope.


(* S is the whole set, flag = true indicates that it computes the MaybeInit set *)
Definition transfer (S: PathsMap.t) (flag: bool) (f: function) (cfg: rustcfg) (pc: node) (before: IM.t) : IM.t :=
  match before with
  | IM.Bot => IM.Bot
  | IM.State before =>
      match cfg ! pc with
      | None => IM.Bot
      | Some (Inop _) => IM.State before
      | Some (Icond _ _ _) => IM.State before
      | Some Iend => IM.State before
      | Some (Isel sel _) =>
          match select_stmt f.(fn_body) sel with
          | None => IM.Bot
          | Some s =>
              match s with
              | Sassign p e
              | Sassign_variant p _ _ e
              | Sbox p e =>
                  let p' := moved_place e in
                  if flag then
                    IM.State (add_place S p (remove_option p' before))
                  else
                    IM.State (remove_place p (add_option S p' before))
              | Scall p _ al =>
                  let pl := moved_place_list al in
                  if flag then
                    IM.State (add_place S p (remove_place_list pl before))
                  else
                    IM.State (remove_place p (add_place_list S pl before))
              | Sreturn (Some e) =>
                  let p' := moved_place e in
                  if flag then
                    IM.State (remove_option p' before)
                  else
                    IM.State (add_option S p' before)
              | Sdrop p =>
                  if flag then
                    IM.State (remove_place p before)
                  else
                    IM.State (add_place S p before)
              | _ => IM.State before
              end
          end
      end
  end.

Module DS := Dataflow_Solver(IM)(NodeSetForward).

Local Open Scope error_monad_scope.

(* The analyze returns the MaybeInit and MaybeUninit sets along with
the universe set *)
Definition analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t IM.t * PMap.t IM.t * PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* initialize maybeInit set with parameters *)
  let pl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_params) in
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  let maybeInit := add_place_list whole pl empty_pathmap in
  (* initialize maybeUninit with the variables *)
  let vl := map (fun elt => Plocal (fst elt) (snd elt)) f.(fn_vars) in
  let maybeUninit := add_place_list whole vl empty_pathmap in
  (* generate selector-based CFG for analysis *)
  (* do (entry, cfg) <- generate_cfg f.(fn_body); *)
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry (IM.State maybeInit) in
  let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry (IM.State maybeUninit) in
  match initMap, uninitMap with
  (* we only want the PTree because [None] represent the unreachable node *)
  | Some initMap, Some uninitMap =>
      (** check consistence  *)
          if IM.beq (IM.State whole) (IM.lub initMap!!entry uninitMap!!entry) then
            Errors.OK (initMap, uninitMap, whole)
          else
            Errors.Error (msg "consistence checking error in analyze")
  | _, _ => Errors.Error (msg "Error in initialize analysis")
  end.

(* instance of [get_an] *)
Definition get_init_info (an: (PMap.t IM.t * PMap.t IM.t * PathsMap.t)) (pc: node) : IM.t * IM.t * PathsMap.t :=
  let '(mayinit, mayuninit, universe) := an in
  (mayinit!!pc, mayuninit!!pc, universe).

(** Definitions of must_owned and may_owned used in Drop elaboration *)

(* Definition must_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool := *)
(*   let id := local_of_place p in *)
(*   let init := PathsMap.get id initmap in *)
(*   let uninit := PathsMap.get id uninitmap in *)
(*   let universe := PathsMap.get id universemap in *)
(*   let mustinit := Paths.diff init uninit in *)
(*   (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mustinit *) *)
(*   Paths.for_all (fun p' => Paths.mem p' mustinit) *)
(*     (Paths.filter (fun p' => is_prefix p' p) universe). *)

(* (* place that needs drop flag *) *)
(* Definition may_owned (initmap uninitmap universemap: PathsMap.t) (p: place) : bool := *)
(*   let id := local_of_place p in *)
(*   let init := PathsMap.get id initmap in *)
(*   let uninit := PathsMap.get id uninitmap in *)
(*   let universe := PathsMap.get id universemap in *)
(*   let mayinit := Paths.inter init uninit in *)
(*   (* ∀ p' ∈ universe, is_prefix p' p → p' ∈ mayinit *) *)
(*   Paths.for_all (fun p' => Paths.mem p' mayinit) *)
(*     (Paths.filter (fun p' => is_prefix p' p) universe). *)

(* static version of is_init *)

Definition must_init (initmap uninitmap universe: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let mustinit := Paths.diff init uninit in
  (* We also check p is in the universe to do some validation *)
  Paths.mem p mustinit && Paths.mem p (PathsMap.get (local_of_place p) universe).

(* place that needs drop flag *)
Definition may_init (initmap uninitmap universe: PathsMap.t) (p: place) : bool :=
  let id := local_of_place p in
  let init := PathsMap.get id initmap in
  let uninit := PathsMap.get id uninitmap in
  let mayinit := Paths.inter init uninit in
  Paths.mem p mayinit && Paths.mem p (PathsMap.get (local_of_place p) universe).

(** Used in static move checking: it is now defined in MoveChecking.v *)
(* Definition must_movable (initmap uninitmap universemap: PathsMap.t) (p: place) : bool := *)
(*   let id := local_of_place p in *)
(*   let init := PathsMap.get id initmap in *)
(*   let uninit := PathsMap.get id uninitmap in *)
(*   let universe := PathsMap.get id universemap in *)
(*   let mustinit := Paths.diff init uninit in *)
(*   (* ∀ p' ∈ universe, is_prefix p p' → must_init p' *) *)
(*   Paths.exists_ (is_prefix p) universe && *)
(*   Paths.for_all (must_init initmap uninitmap universemap) (Paths.filter (is_prefix p) universe). *)

(* Do we need to check that all the dominators of p is must_init (in
init set and in universe) ? *)
Definition dominators_must_init (initmap uninitmap universe: PathsMap.t) (p: place) : bool :=
  forallb (must_init initmap uninitmap universe) (place_dominators p).


(** **  Properties used in ElaborateDropProof and MoveCheckingSafe  *)


(* auxilary functions for own_env *)
Fixpoint collect_children_in (s: PathsMap.t) (l: list place) : Paths.t :=
  match l with
  | nil => Paths.empty
  | p :: l' =>            
      let id := local_of_place p in
      let ps := PathsMap.get id s in
      Paths.union (Paths.filter (fun elt => is_prefix p elt) ps) (collect_children_in s l')
  end.

Lemma collect_children_in_exists: forall l own p,
    Paths.In p (collect_children_in own l) ->
    exists p', In p' l /\ is_prefix p' p = true.
Proof.
  induction l; intros own p IN; simpl in *.
  exfalso. eapply Paths.empty_1. eauto.
  eapply Paths.union_1 in IN. destruct IN as [IN1|IN2].
  - eapply Paths.filter_2 in IN1. exists a. auto.
    red. solve_proper.
  - eapply IHl in IN2.
    destruct IN2 as (p' & IN1 & PRE).
    eauto.
Qed.

Lemma collect_children_in_implies: forall l p1 p2 own,
    In p1 l ->
    is_prefix p1 p2 = true ->
    Paths.In p2 (PathsMap.get (local_of_place p2) own) ->
    Paths.In p2 (collect_children_in own l).
Proof.
  induction l; intros p1 p2 own IN1 PRE IN2; simpl in *.
  contradiction.
  destruct IN1; subst.
  - eapply Paths.union_2.
    eapply Paths.filter_3. red. solve_proper.
    erewrite is_prefix_same_local; eauto.
    auto.
  - eapply Paths.union_3.
    eapply IHl; eauto.
Qed.

Definition remove_paths_in (s: PathsMap.t) (id: ident) (ps: Paths.t) :=
  let l := PathsMap.get id s in
  PathsMap.set id (Paths.diff l ps) s.

(* just update PathsMap *)
Fixpoint move_split_places_uncheck (own: PathsMap.t) (l: list (place * bool)) : PathsMap.t :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      move_split_places_uncheck (remove_place p own) l'
  end.

Fixpoint add_split_places_uncheck (universe: PathsMap.t) (uninit: PathsMap.t) (l: list (place * bool)) : PathsMap.t :=
  match l with
  | nil => uninit
  | (p,_) :: l' =>
      add_split_places_uncheck universe (add_place universe p uninit) l'
  end.

(* update Paths.t *)
Fixpoint filter_split_places_uncheck (own: Paths.t) (l: list (place * bool)) : Paths.t :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      filter_split_places_uncheck (Paths.filter (fun elt => negb (is_prefix p elt)) own) l'
  end.

Lemma filter_split_places_uncheck_more: forall l u1 u2,
    LPaths.ge u1 u2 ->
    LPaths.ge (filter_split_places_uncheck u1 l) (filter_split_places_uncheck u2 l).
Proof.
  induction l; simpl; auto.
  intros u1 u2 GE. destruct a.
  eapply IHl.
  red. red. intros a IN.
  eapply Paths.filter_3.
  red. solve_proper.
  eapply GE. eapply Paths.filter_1; eauto.
  red. solve_proper.
  eapply Paths.filter_2 in IN.
  auto.
  red. solve_proper.
Qed.

Lemma filter_split_places_uncheck_unchange: forall l p own,
    Paths.In p (filter_split_places_uncheck own l) ->
    Paths.In p own.
Proof.
  induction l; simpl; auto.
  intros p own IN. destruct a.
  eapply IHl. 
  eapply filter_split_places_uncheck_more; eauto.
  red. red.
  intros a IN1.
  eapply Paths.filter_1; eauto.
  red. solve_proper.
Qed.

  
Lemma move_split_places_uncheck_more: forall l u1 u2,
    PathsMap.ge u1 u2 ->
    PathsMap.ge (move_split_places_uncheck u1 l) (move_split_places_uncheck u2 l).
Proof.
  induction l; intros; simpl; auto.
  destruct a. eapply IHl.
  red. intros id.
  unfold remove_place.
  red. do 2 rewrite PathsMap.gsspec.
  destruct (peq id (local_of_place p)); subst.
  - red. intros a A.
    eapply Paths.filter_3. red. solve_proper.
    apply H.
    eapply Paths.filter_1; eauto. red. solve_proper.
    eapply Paths.filter_2 in A. auto.
    red. solve_proper.
  - eapply H.
Qed.
  
Lemma add_split_places_uncheck_more: forall l w u1 u2,
    PathsMap.ge u1 u2 ->
    PathsMap.ge (add_split_places_uncheck w u1 l) (add_split_places_uncheck w u2 l).
Proof.
  induction l; intros; simpl; auto.
  destruct a. eapply IHl.
  red. intros id.
  unfold add_place.
  red. do 2 rewrite PathsMap.gsspec.
  destruct (peq id (local_of_place p)); subst.
  - red. intros a A.
    eapply Paths.union_1 in A.
    destruct A.
    eapply Paths.union_2. eapply H. auto.
    eapply Paths.union_3. auto.
  - eapply H.
Qed.

    
(* equivalent (just ge for now because it is enough) between
get-filter-set and get-set-get-set ... -get-set mode *)
Lemma filter_move_split_places_ge: forall l id init
    (NAME: forall p b, In (p, b) l -> local_of_place p = id),
    PathsMap.ge (PathsMap.set id (filter_split_places_uncheck (PathsMap.get id init) l) init) (move_split_places_uncheck init l).
Proof.
  induction l; simpl; intros.
  red. intros p. red. rewrite PathsMap.gsspec.
  destruct (peq p id); subst. apply LPaths.ge_refl.
  apply LPaths.eq_refl.
  apply LPaths.ge_refl. apply LPaths.eq_refl.
  destruct a.
  generalize (IHl id (remove_place p init)).
  intros GE.
  eapply PathsMap.ge_trans.
  2: eauto.
  red. intros p1. red.
  do 2 rewrite PathsMap.gsspec.
  destruct (peq p1 id); subst.
  - eapply filter_split_places_uncheck_more.
    (* core of proof *)
    red. red. erewrite <- NAME; eauto.
    unfold remove_place.
    intros a IN. rewrite PathsMap.gsspec in IN.
    destruct (peq (local_of_place p) (local_of_place p)); try congruence.
  - red. unfold remove_place.
    intros a IN. rewrite PathsMap.gsspec in IN.
    destruct (peq p1 (local_of_place p)); subst.
    eapply Paths.filter_1; eauto. red. solve_proper.
    auto.
Qed.

Lemma filter_split_places_subset_collect_children: forall l p1 p2 own,
    Paths.In p1 (filter_split_places_uncheck own l) ->
    In p2 (map fst l) ->
    is_prefix p2 p1 = false.
Proof.
  induction l; simpl; intros p1 p2 own IN1 IN2.
  contradiction.
  destruct a. 
  destruct (split l) eqn: SPLIT. simpl in *.
  destruct IN2; subst.
  - eapply filter_split_places_uncheck_unchange in IN1.
    eapply Paths.filter_2 in IN1.
    eapply negb_true_iff; auto.
    red. solve_proper.
  - eapply IHl; eauto.
Qed.


(** Properties of is_init and must_init *)

Lemma move_place_not_init: forall p own,
    is_init (move_place own p) p = false.
Proof.
  intros. unfold move_place, is_init.
  simpl. unfold remove_place.
  erewrite PathsMap.gsspec.
  destruct peq; try congruence.
  eapply not_true_is_false.
  intro. eapply Paths.mem_2 in H.
  eapply Paths.filter_2 in H.
  erewrite is_prefix_refl in H. simpl in H.
  congruence.
  red. solve_proper.
Qed.

Lemma move_place_still_not_owned: forall p1 p2 own,
    is_init own p1 = false ->
    is_init (move_place own p2) p1 = false.
Proof.
  intros. unfold is_init, move_place in *.
  simpl. unfold remove_place.
  eapply not_true_iff_false. eapply not_true_iff_false in H. 
  intro. apply H. clear H.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in H0.
  erewrite PathsMap.gsspec in H0.
  destruct peq.
  - rewrite e.
    eapply Paths.filter_1; eauto.
    red. solve_proper.
  - auto.
Qed.    

Lemma move_irrelavent_place_still_owned: forall p1 p2 own,
    is_init own p1 = true ->
    is_prefix p2 p1 = false ->
    is_init (move_place own p2) p1 = true.
Proof.
  intros p1 p2 own INIT PRE.
  unfold is_init in *.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in INIT.
  unfold move_place, remove_place. simpl.
  erewrite PathsMap.gsspec.
  destruct peq.
  - rewrite <- e.
    eapply Paths.filter_3.
    red. solve_proper.
    auto. eapply negb_true_iff. auto.
  - auto.
Qed.

Lemma init_irrelavent_place_still_not_owned: forall p1 p2 own,
    is_init own p1 = false ->
    is_prefix p2 p1 = false ->
    is_init (init_place own p2) p1 = false.
Proof.
  intros p1 p2 own INIT PRE.
  eapply not_true_iff_false.  eapply not_true_iff_false in INIT.
  intro INIT1. apply INIT. clear INIT.
  unfold is_init in *.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in INIT1.
  unfold init_place, add_place in *. simpl in *.
  erewrite PathsMap.gsspec in INIT1.
  destruct peq.
  - rewrite e.
    eapply Paths.union_1 in INIT1.
    destruct INIT1 as [A|B].
    auto.
    eapply Paths.filter_2 in B; eauto. congruence.
    red. solve_proper.
  - auto.
Qed.


Lemma move_prefix_not_init: forall p1 p2 own,
    (* this premise is important to prevent that p1 and p2 *)
(*        does not exists in universe so that move p1 has no *)
(*        effect *)
    (* Paths.In p2 (PathsMap.get (local_of_place p1) own.(own_universe)) -> *)
    is_prefix p1 p2 = true ->
    is_init (move_place own p1) p2 = false.
Proof.
  intros p1 p2 own PRE.
  unfold is_init, move_place, remove_place.
  simpl. erewrite <- is_prefix_same_local.
  2: eauto.
  rewrite PathsMap.gsspec.
  destruct peq; try congruence.
  eapply not_true_iff_false. intro.
  eapply not_false_iff_true in PRE.
  eapply Paths.mem_2 in H.
  apply PRE.
  eapply Paths.filter_2 in H. eapply negb_true_iff.
  auto.
  red. solve_proper.
Qed.
  
Lemma init_prefix_init: forall p1 p2 own,
    Paths.In p2 (PathsMap.get (local_of_place p1) own.(own_universe)) ->
    is_prefix p1 p2 = true ->
    is_init (init_place own p1) p2 = true.
Proof.
  intros p1 p2 own IN PRE.
  unfold is_init, init_place, add_place.
  simpl. erewrite <- is_prefix_same_local.
  2: eauto.
  rewrite PathsMap.gsspec.
  destruct peq; try congruence.
  eapply Paths.mem_1.
  eapply Paths.union_3.
  eapply Paths.filter_3; eauto.
  red. solve_proper.
Qed.
  
Lemma init_owned_place_still_owned: forall p1 p2 own,
    is_init own p1 = true ->
    is_init (init_place own p2) p1 = true.
Proof.
  intros p1 p2 own INIT.
  unfold is_init, init_place, add_place in *.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in INIT.
  simpl.
  rewrite PathsMap.gsspec.
  destruct peq.
  - rewrite <- e.
    eapply Paths.union_2. auto.
  - auto.
Qed.

(* all the children has been moved out. It is used to prove move_split_places_uncheck_sound *)
Inductive move_ordered_split_places_spec : own_env -> list place -> Prop :=
| ordered_in_own_nil: forall own,
    move_ordered_split_places_spec own nil
| ordered_in_own_cons: forall p l own
    (PRES: forall p', is_prefix_strict p p' = true -> is_init own p' = false)
    (MORD: move_ordered_split_places_spec (if is_init own p then move_place own p else own) l),
    move_ordered_split_places_spec own (p :: l).


Lemma ordered_and_complete_split_places_meet_spec: forall drops own
    (COMPLETE: forall p a, In p drops -> is_prefix p a = true -> Paths.In a (PathsMap.get (local_of_place a) own.(own_universe)) -> In a drops \/ is_init own a = false)
    (ORDER: split_places_ordered drops),   
    move_ordered_split_places_spec own drops.
Proof.
  induction drops; simpl; intros.
  constructor.
  econstructor.
  - intros.
    destruct (Paths.mem p' (PathsMap.get (local_of_place a) (own_universe own))) eqn: UNI.
    + eapply Paths.mem_2 in UNI.      
      (* p' must be equal to a? *)
      exploit COMPLETE. left. eauto.
      instantiate (1 := p'). eapply is_prefix_strict_implies; auto.
      eauto. erewrite <- is_prefix_same_local. eauto.
      eapply is_prefix_strict_implies; auto.
      auto. intros [[A|B]|C].
      * subst. erewrite is_prefix_strict_not_refl in H.
        congruence.
      * inv ORDER. eapply Forall_forall with (x:=p') in H2.
        eapply is_prefix_strict_iff in H. destruct H.
        congruence.
        auto.
      * auto. (* destruct (is_init own a); auto. *)
        (* eapply move_place_still_not_owned. auto. *)
    (* easy because p' is not in universe *)
    + eapply not_true_iff_false.
      intro. eapply not_true_iff_false in UNI.
      apply UNI.
      erewrite is_prefix_same_local.
      eapply is_init_in_universe. auto.
      eapply is_prefix_strict_implies. auto.
  - inv ORDER. eapply IHdrops; eauto.
    assert (UNIEQ: PathsMap.eq (own_universe (if is_init own a then move_place own a else own)) (own_universe own)).
    { destruct is_init.
      unfold move_place. simpl. apply PathsMap.eq_refl.
      apply PathsMap.eq_refl. }
    intros. exploit COMPLETE.
    right. eauto.
    eauto.
    eapply UNIEQ. eauto.
    intros [[A | B]| C].
    + subst. right.
      destruct (is_init own a0) eqn: INIT.
      eapply move_place_not_init.
      auto.
    + auto.
    + right.
      destruct (is_init own a) eqn: INIT.
      eapply move_place_still_not_owned. auto.
      auto.
Qed.

(* relation of moveing split places *)
Fixpoint move_split_places (own :own_env) (l: list (place * bool)) : own_env :=
  match l with
  | nil => own
  | (p,_) :: l' =>
      move_split_places (if is_init own p then move_place own p else own) l'
  end.


Lemma move_split_places_uncheck_sound: forall drops own own'
    (SPEC: move_ordered_split_places_spec own (map fst drops)),
    move_split_places own drops = own' ->
    PathsMap.ge (move_split_places_uncheck (own_init own) drops) (own_init own')
    /\ PathsMap.ge (add_split_places_uncheck (own_universe own) (own_uninit own) drops) (own_uninit own')
    /\ PathsMap.eq (own_universe own) (own_universe own').
Proof.
  induction drops; intros; subst; simpl.
  - split. apply PathsMap.ge_refl. eapply PathsMap.eq_refl.
    split. apply PathsMap.ge_refl. eapply PathsMap.eq_refl.
    apply PathsMap.eq_refl.
  - destruct a.
    simpl in SPEC. inv SPEC.
    destruct (is_init own p) eqn: OWN.
    + exploit (IHdrops (move_place own p)); eauto.
    (* p is not owned, so remove it has no effect *)
    + exploit (IHdrops own); eauto.
      intros (A & B & C).
      split; try split. 3: auto.
      2: { eapply PathsMap.ge_trans; eauto.
           eapply add_split_places_uncheck_more.
           red. intros id. unfold add_place.
           red. rewrite PathsMap.gsspec.
           destruct (peq id (local_of_place p)); subst.
           + red. intros a D. eapply Paths.union_2. auto.
           + eapply LPaths.ge_refl. apply LPaths.eq_refl. }
      (* core proof *)
      eapply PathsMap.ge_trans; eauto.
      assert (CORE: PathsMap.ge (remove_place p (own_init own)) (own_init own)).
      { red. intros id. unfold remove_place. red.
        rewrite PathsMap.gsspec.
        destruct (peq id (local_of_place p)); subst.
        + red. intros a IN.
          eapply Paths.filter_3. red. solve_proper.
          auto.
          (* key to prove: a is not a child of p. From opposite side, *)
          (* if a is a strict children of p or p is equal to a, then
          is_init own a = false which is a contradiction of IN or
          OWN *)
          destruct (place_eq p a). subst.
          * rewrite is_prefix_refl. simpl.
            erewrite <- OWN.            
            unfold is_init. 
            eapply Paths.mem_1 in IN. auto.
          * apply Is_true_eq_true.
            apply negb_prop_intro.
            intro PRE. apply Is_true_eq_true in PRE.
            assert (PRES1: is_prefix_strict p a = true).
            { eapply is_prefix_strict_iff. auto. }
            exploit PRES; eauto.
            unfold is_init. intros INIT.
            eapply Paths.mem_1 in IN.
            erewrite is_prefix_same_local in IN; eauto.
            congruence.
        + eapply LPaths.ge_refl. apply LPaths.eq_refl. }
      eapply move_split_places_uncheck_more; eauto.
Qed.


(* move it to a new file *)

(** * Soundness of Initial Analysis *)

Inductive tr_cont : statement -> rustcfg -> cont -> node -> option node -> option node -> node -> Prop :=
| tr_Kseq: forall body cfg s pc next cont brk nret k
    (STMT: tr_stmt body cfg s pc next cont brk nret)
    (CONT: tr_cont body cfg k next cont brk nret),
    tr_cont body cfg (Kseq s k) pc cont brk nret
| tr_Kstop: forall body cfg nret
    (RET: cfg ! nret = Some Iend),
    tr_cont body cfg Kstop nret None None nret
| tr_Kloop: forall body cfg s body_start loop_jump_node exit_loop nret cont brk k
    (STMT: tr_stmt body cfg s body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (SEL: cfg ! loop_jump_node = Some (Inop body_start))
    (CONT: tr_cont body cfg k exit_loop cont brk nret),
    tr_cont body cfg (Kloop s k) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret
| tr_Kdropplace: forall body cfg k pc cont brk nret f st l le own entry
    (CONT: tr_cont body cfg k pc cont brk nret)
    (TRFUN: tr_fun f nret entry cfg),
    tr_cont body cfg (Kdropplace f st l le own k) pc cont brk nret
| tr_Kdropcall: forall body cfg k pc cont brk nret st membs b ofs id
    (CONT: tr_cont body cfg k pc cont brk nret),
    tr_cont body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret
| tr_Kcall: forall body cfg k nret f le own p
    (STK: tr_stacks (Kcall p f le own k))
    (RET: cfg ! nret = Some Iend),
    tr_cont body cfg (Kcall p f le own k) nret None None nret

(* Used to restore tr_cont in function calls *)
with tr_stacks: cont -> Prop :=
| tr_stacks_stop:
  tr_stacks Kstop
| tr_stacks_call: forall f nret cfg pc cont brk k own p le entry
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret),
    tr_stacks (Kcall p f le own k).


Record sound_own (own: own_env) (init uninit universe: PathsMap.t) : Type :=
  { sound_own_init: PathsMap.ge init own.(own_init);
    
    sound_own_uninit: PathsMap.ge uninit own.(own_uninit);

    sound_own_universe: PathsMap.eq universe own.(own_universe);

    (** This property is impossible to be proved due to
    analyze_succ. init and uninit in the range of universe is a
    universal property which is not guaranteed by Kildall.v *)
    (* sound_own_consistent: forall id, *)
    (*   LPaths.eq (Paths.union (PathsMap.get id init) (PathsMap.get id uninit)) (PathsMap.get id universe); *)
  }.

(* Properties of sound_own *)

(* Lemma sound_own_must_init (own: own_env) (init uninit universe: PathsMap.t) id: *)
(*   sound_own own init uninit universe -> *)
(*   LPaths.ge (PathsMap.get id (own_init own)) (Paths.diff (PathsMap.get id init) (PathsMap.get id uninit)). *)
(* Proof. *)
(*   intros OWN. *)
(*   red. red. intros a IN. *)
(*   generalize IN. intros IN1. *)
(*   eapply Paths.diff_1 in IN. *)
(*   eapply Paths.diff_2 in IN1. *)
(*   destruct (Paths.mem a (PathsMap.get id (own_init own))) eqn: MEM. *)
(*   eapply Paths.mem_2. auto. *)
(*   exfalso. eapply IN1. clear IN1. *)
(*   eapply sound_own_universe in UNI; eauto. *)
(*   eapply own_consistent in UNI. *)
(*   eapply Paths.union_1 in UNI. destruct UNI. *)
(*   eapply Paths.mem_1 in H. congruence. *)
(*   eapply sound_own_uninit; eauto. *)
(* Qed. *)

(** We can only consider those places are in the universe because
init/uninit may be contain some places not in the universe *)
Lemma must_init_sound (own: own_env) (init uninit universe: PathsMap.t) p:
  sound_own own init uninit universe ->
  (* Paths.In p (PathsMap.get (local_of_place p) universe) -> *)
  must_init init uninit universe p = true ->
  is_init own p = true.
Proof.
  intros OWN IN. unfold is_init, must_init in *.
  eapply andb_true_iff in IN. destruct IN as (IN & UNI).
  eapply Paths.mem_2 in UNI.
  eapply Paths.mem_2 in IN.
  generalize IN. intros IN1.
  eapply Paths.diff_1 in IN.
  eapply Paths.diff_2 in IN1.
  destruct (Paths.mem p (PathsMap.get (local_of_place p) (own_init own))) eqn: MEM; auto.
  exfalso. eapply IN1. clear IN1.
  eapply sound_own_universe in UNI; eauto.
  eapply own_consistent in UNI.
  eapply Paths.union_1 in UNI. destruct UNI.
  eapply Paths.mem_1 in H. congruence.
  eapply sound_own_uninit; eauto.
Qed.  
  
Lemma must_not_init_sound (own: own_env) (init uninit universe: PathsMap.t) p:
    sound_own own init uninit universe ->
    must_init init uninit universe p = false ->
    may_init init uninit universe p = false ->
    is_init own p = false.
Proof.
  intros. unfold must_init, may_init, is_init in *.
  destruct (Paths.mem p (PathsMap.get (local_of_place p) universe)) eqn: UNI.
  erewrite  andb_true_r in *.
  destruct (Paths.mem p (PathsMap.get (local_of_place p) (own_init own))) eqn: MEM; auto.
  eapply Paths.mem_2 in MEM.
  eapply sound_own_init in MEM; eauto.
  exfalso.
  eapply not_true_iff_false in H0. apply H0.
  clear H0.
  eapply Paths.mem_1.
  eapply Paths.diff_3. auto.
  eapply not_true_iff_false in H1. intro.
  eapply H1.
  eapply Paths.mem_1.
  eapply Paths.inter_3; auto.
  (* not int universe *)
  eapply not_true_iff_false. intro.
  eapply not_true_iff_false in UNI. eapply UNI.
  eapply Paths.mem_1. eapply Paths.mem_2 in H2.
  eapply sound_own_universe. eauto.
  eapply own_consistent. eapply Paths.union_2. auto.
Qed.


Lemma move_place_sound: forall own init uninit universe p
    (OWN: sound_own own init uninit universe),
    sound_own (move_place own p) (remove_place p init) (add_place universe p uninit) universe.
Proof.
  intros. inv OWN.
  constructor.
  - unfold move_place, remove_place, add_place.
    simpl. red. intros.
    red.
    do 2 erewrite PathsMap.gsspec.
    destruct peq. subst.
    red. intros. eapply Paths.filter_3.
    red. solve_proper.
    eapply sound_own_init0. eapply Paths.filter_1; eauto.
    red. solve_proper.
    eapply Paths.filter_2 in H. eauto.
    red. solve_proper.
    eapply sound_own_init0.
  - unfold move_place, remove_place, add_place.
    simpl. red. intros.
    red.
    do 2 erewrite PathsMap.gsspec.
    destruct peq. subst.
    red. intros. eapply Paths.union_1 in H.
    destruct H.
    eapply Paths.union_2. eapply sound_own_uninit0. auto.
    eapply Paths.union_3. eapply Paths.filter_3.
    red. solve_proper.
    eapply sound_own_universe0.    
    eapply Paths.filter_1; eauto.
    red. solve_proper.
    eapply Paths.filter_2 in H. eauto.
    red. solve_proper.
    eapply sound_own_uninit0.
  - simpl. eapply sound_own_universe0.
Qed.

Lemma move_option_place_sound: forall own init uninit universe p
    (OWN: sound_own own init uninit universe),
    sound_own (move_place_option own p) (remove_option p init) (add_option universe p uninit) universe.
Proof.
  intros. destruct p.
  simpl. eapply move_place_sound. auto.
  auto.
Qed.

Lemma move_place_list_sound :forall l own init uninit universe
    (OWN: sound_own own init uninit universe),
    sound_own (move_place_list own l) (remove_place_list l init) (add_place_list universe l uninit) universe.
Proof.
  induction l; intros; simpl.
  auto.
  eapply IHl. eapply move_place_sound.
  auto.
Qed.

Lemma init_place_sound: forall own init uninit universe p
    (OWN: sound_own own init uninit universe),
    sound_own (init_place own p) (add_place universe p init) (remove_place p uninit) universe.
Proof.
  intros. inv OWN.  
  constructor.
  - unfold init_place, remove_place, add_place.
    simpl. red. intros.
    red.
    do 2 erewrite PathsMap.gsspec.
    destruct peq. subst.
    red. intros. eapply Paths.union_1 in H.
    destruct H.
    eapply Paths.union_2. eapply sound_own_init0. auto.
    eapply Paths.union_3. eapply Paths.filter_3.
    red. solve_proper.
    eapply sound_own_universe0.    
    eapply Paths.filter_1; eauto.
    red. solve_proper.
    eapply Paths.filter_2 in H. eauto.
    red. solve_proper.
    eapply sound_own_init0.
  - unfold init_place, remove_place, add_place.
    simpl. red. intros.
    red.
    do 2 erewrite PathsMap.gsspec.
    destruct peq. subst.
    red. intros. eapply Paths.filter_3.
    red. solve_proper.
    eapply sound_own_uninit0. eapply Paths.filter_1; eauto.
    red. solve_proper.
    eapply Paths.filter_2 in H. eauto.
    red. solve_proper.
    eapply sound_own_uninit0.
  - simpl. eapply sound_own_universe0.
Qed.


      
(** ** Semantic invariant *)


Inductive get_IM_state : IM.t -> IM.t -> option (PathsMap.t * PathsMap.t) -> Prop :=
| get_IM_bot1: forall s,
    get_IM_state IM.bot s None
| get_IM_bot2: forall s,
    get_IM_state s IM.bot None
| get_IM_some: forall init uninit,
    get_IM_state (IM.State init) (IM.State uninit) (Some (init, uninit)).
    
    
Section SOUNDNESS.

Variable prog: program.
Variable se: Genv.symtbl.

Let ge := RustIR.globalenv se prog.
Let ce := ge.(genv_cenv).

Inductive sound_cont: cont -> Prop :=
| sound_cont_stop: sound_cont Kstop
| sound_cont_seq: forall s k,
    sound_cont k ->
    sound_cont (Kseq s k)
| sound_cont_loop: forall s k,
    sound_cont k ->
    sound_cont (Kloop s k)
| sound_cont_call: forall f initMap uninitMap pc mayinit mayuninit universe entry cfg k own1 own2 le p cont brk nret
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (IM: get_IM_state initMap!!pc uninitMap!!pc (Some (mayinit, mayuninit)))
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)                   
    (OWN: sound_own own2 mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_cont (Kcall p f le own1 k)
| sound_cont_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe  cfg k own1 own2 le st l cont brk nret entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (IM: get_IM_state initMap!!pc uninitMap!!pc  (Some (mayinit, mayuninit)))
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (MOVESPLIT: move_split_places own1 l = own2)
    (CONT: sound_cont k),
    sound_cont (Kdropplace f st l le own1 k)
| sound_cont_dropcall: forall id b ofs st membs k,
    sound_cont k ->
    sound_cont (Kdropcall id (Vptr b ofs) st membs k)
.

  
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f initMap uninitMap pc mayinit mayuninit universe cfg s k own le m nret next cont brk entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (IM: get_IM_state initMap!!pc uninitMap!!pc (Some (mayinit, mayuninit)))
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret entry cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc next cont brk nret)
    (* k may be contain some statement not located in [next], e.g.,
    statements after continue and break *)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (OWN: sound_own own mayinit mayuninit universe),
    sound_state (State f s k le own m)
| sound_callstate: forall vf args k m
    (CONT: sound_cont k)
    (TRSTK: tr_stacks k),
    sound_state (Callstate vf args k m) 
| sound_returnstate: forall v k m
    (CONT: sound_cont k)
    (TRSTK: tr_stacks k),
    sound_state (Returnstate v k m)
| sound_dropplace: forall f initMap uninitMap pc mayinit mayuninit universe cfg k own1 own2 le st l m nret cont brk entry
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (IM: get_IM_state initMap!!pc uninitMap!!pc (Some (mayinit, mayuninit)))
    (* invariant of generate_cfg *)
    (TRFUN: tr_fun f nret entry cfg)
    (TRCONT: tr_cont f.(fn_body) cfg k pc cont brk nret)
    (* small-step move_place to simulate big-step move_place in
    transfer. maybe difficult to prove *)
    (MOVESPLIT: move_split_places own1 l = own2)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (CONT: sound_cont k),
    sound_state (Dropplace f st l k le own1 m)
| sound_dropstate: forall id b ofs st membs k m
    (CONT: sound_cont k),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
.
    
(* soundness of function entry: use fixpoint_entry to prove it *)
Lemma sound_function_entry: forall f initMap uninitMap universe entry cfg own
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (FENTRY: init_own_env ce f = OK own),
  exists init uninit,
    get_IM_state initMap!!entry uninitMap!!entry (Some (init, uninit)) /\
      sound_own own init uninit universe.
Proof.
  intros until own. intros AN CFG. unfold analyze in AN.
  unfold init_own_env.  
  Errors.monadInv AN.
  rewrite EQ. simpl.
  set (initParams := (add_place_list x
              (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f))
              (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x))) in *.
  set (uninitVars := (add_place_list x
                  (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_vars f))
                  (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x))) in *.
  (* generalize the beq  as Clightgenproof does *)
  set (flag := PathsMap.beq x (PathsMap.lub initParams uninitVars) &&
    PathsMap.beq (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)
      (PathsMap.combine inter_opt initParams uninitVars)).
  generalize (eq_refl flag).
  generalize flag at 1 3.
  intros flag0 E. destruct flag0; try congruence.
  intros FENTRY. inv FENTRY.
  destruct (DS.fixpoint cfg successors_instr (transfer x true f cfg) entry (IM.State initParams)) eqn: initAN; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer x false f cfg) entry (IM.State uninitVars)) eqn: uninitAN; try congruence.
  destruct (IM.beq (IM.State x) (IM.lub t !! entry t0 !! entry)) eqn: CON; try congruence.
  inv EQ0.
  eapply DS.fixpoint_entry in initAN.
  eapply DS.fixpoint_entry in uninitAN.
  unfold DS.L.ge in *.
  destruct (uninitMap !! entry); try contradiction.
  destruct (initMap !! entry); try contradiction.
  do 2 eexists. split.
  econstructor.
  constructor; auto.
  simpl. eapply PathsMap.eq_refl.
  (* sound_own_consistent by translation validation *)
  (* eapply PathsMap.beq_correct in CON. *)
  (* exploit PathsMap_lub_union; eauto. *)  
Qed.


(* Some properties of call_cont *)
Lemma sound_call_cont: forall k,
    sound_cont k -> sound_cont (call_cont k).
Proof.
  intros k SOUND.
  induction k; inv SOUND; simpl; try econstructor; eauto.
Qed.

Lemma tr_stacks_call_cont: forall k body cfg pc cont brk nret
    (SOUND: tr_cont body cfg k pc cont brk nret),
  tr_stacks (call_cont k).
Proof.
  induction k; intros; inv SOUND; simpl; try (econstructor; eauto; fail).
  - eapply IHk. eauto.
  - eapply IHk. eauto.
  - inv STK. econstructor; eauto.
  - eapply IHk. eauto.
  - eapply IHk. eauto.
Qed.

  
(* use fixpoint_soulution to prove that the final abstract env
approximates more than the abstract env computed by transfer
function *)
Lemma analyze_successor: forall f initMap uninitMap (* mayinit1 *) mayinit2 (* mayuninit1 *) mayuninit2 universe cfg entry instr pc1 pc2
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (* (INIT: initMap !! pc1 = (IM.State mayinit1)) *)
    (* (UNINIT: uninitMap !! pc1 = (IM.State mayuninit1)) *)
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 initMap !! pc1 = mayinit2)
    (TFUNINIT: transfer universe false f cfg pc1 uninitMap !! pc1 = mayuninit2),
    IM.ge (initMap !! pc2) mayinit2
    /\ IM.ge (uninitMap !! pc2) mayuninit2
.
Proof.  (* use fixpoint_solution *)
  unfold analyze; intros. 
  Errors.monadInv AN.
  set (params_init := (add_place_list x
               (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f))
               (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x))) in *.
  set (vars_uninit := (add_place_list x
                   (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_vars f))
                   (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x))) in *.

  destruct (DS.fixpoint cfg successors_instr (transfer x true f cfg) entry
              (IM.State params_init)) eqn: INITMAP; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer x false f cfg) entry
              (IM.State vars_uninit)) eqn: UNINITMAP; try congruence.
  destruct (IM.beq (IM.State x) (IM.lub t !! entry t0 !! entry)) eqn: CON; try congruence.
  inv EQ0.
  split.
  - eapply DS.fixpoint_solution; eauto.
    (** TODO: transfer bot to bot *)
    intros. simpl. auto.
  - eapply DS.fixpoint_solution; eauto.
    intros. simpl. auto.
Qed.

         
(* use transfer to act as the bridge to construct the succ abstract
env *)
Lemma analyze_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr own2 pc1 pc2
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: get_IM_state (initMap !! pc1) (uninitMap !! pc1) (Some (mayinit1, mayuninit1)))
    (SEL: cfg ! pc1 = Some instr)
    (PC: In pc2 (successors_instr instr))
    (TFINIT: transfer universe true f cfg pc1 initMap!!pc1 = (IM.State mayinit2))
    (TFUNINIT: transfer universe false f cfg pc1 uninitMap!!pc1 = (IM.State mayuninit2))
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
  exists mayinit3 mayuninit3,
    get_IM_state initMap!!pc2 uninitMap!!pc2 (Some (mayinit3, mayuninit3))
    /\ sound_own own2 mayinit3 mayuninit3 universe.
  (* show that PathsMap.ge ae1 ae2 and sound_own ae1 implies sound_own
  ae2 *)
Proof.
  intros. exploit analyze_successor; eauto.
  intros (A & B).
  unfold DS.L.ge in *.
  destruct (uninitMap !! pc2); try contradiction.
  destruct (initMap !! pc2); try contradiction.  
  exists m0, m.
  split; auto.
  econstructor.
  destruct OWN.
  constructor.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.ge_trans; eauto.
  - eapply PathsMap.eq_trans; eauto.
    apply PathsMap.eq_refl.
Qed.


Lemma sound_state_succ: forall f initMap uninitMap mayinit1 mayinit2 mayuninit1 mayuninit2 universe entry cfg instr1 own2 pc1 pc2 s k m le nret next cont brk
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (INIT: get_IM_state (initMap !! pc1) (uninitMap !! pc1) (Some (mayinit1, mayuninit1)))
    (SEL1: cfg ! pc1 = Some instr1)
    (PC: In pc2 (successors_instr instr1))
    (TRFUN: tr_fun f nret entry cfg)
    (TRSTMT: tr_stmt f.(fn_body) cfg s pc2 next cont brk nret)
    (TRCONT: tr_cont f.(fn_body) cfg k next cont brk nret)
    (CONT: sound_cont k)
    (TFINIT: transfer universe true f cfg pc1 initMap!!pc1 = (IM.State mayinit2))
    (TFUNINIT: transfer universe false f cfg pc1 uninitMap!!pc1 = (IM.State mayuninit2))
    (OWN: sound_own own2 mayinit2 mayuninit2 universe),
    sound_state (State f s k le own2 m).
Proof.
  intros. exploit analyze_succ; eauto.
  intros (mayinit3 & mayuninit3 & (A & B)).
  econstructor; eauto.
Qed.  


(* Key point: match the small step ownership transfer and the big step
analysis in transfer function of Sdrop *)
Lemma sound_step_dropplace: forall s t s',
    step_dropplace ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  - econstructor; eauto.
    simpl in OWN.
    rewrite NOTOWN in OWN. auto.
  - simpl in OWN0.
    econstructor; eauto.
    rewrite OWN in OWN0. auto.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor. 
Qed.

Lemma sound_step_dropstate: forall s t s',
    step_drop ge s t s' ->
    sound_state s ->
    sound_state s'.
Proof.
  intros s t s' STEP SOUND.
  inv STEP; inv SOUND.
  - econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto.
  - inv CONT.
    econstructor; eauto.
  - econstructor; eauto.
    inv CONT. auto.
Qed.

(** TODO: where to put it *)
(* We can generate cfg for all analyzed functions. This property is
guaranteed by the compilation pass which actually uses the analyze
function *)
Hypothesis function_analyzed: forall (v : val) (f: function),
    Genv.find_funct ge v = Some (Internal f) ->
    exists entry cfg nret initMap uninitMap universe,
      tr_fun f nret entry cfg /\
      analyze ce f cfg entry = OK (initMap, uninitMap, universe).


(* Theorem sound_step: forall s t s', *)
(*     step ge s t s' -> *)
(*     sound_state s -> *)
(*     sound_state s'. *)
(* Proof. *)
(*   intros s t s' STEP SOUND. *)
(*   inv STEP; inv SOUND. *)
(*   (* step_assign *) *)
(*   - inv TRSTMT. inv TRFUN. *)
(*     eapply sound_state_succ with (pc1:= pc); eauto. *)
(*     simpl. eauto. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (* prove sound_own *) *)
(*     inv OWN. *)
(*     unfold transfer. inv IM. *)
(*     rewrite SEL. rewrite STMT. eauto. *)
(*     unfold transfer. inv IM. *)
(*     rewrite SEL. rewrite STMT. eauto. *)
(*     (* maybe easy *) *)
(*     admit.     *)
    
    
(*   (* step_assign_variant *) *)
(*   - inv TRSTMT. inv TRFUN. *)
(*     eapply sound_state_succ with (pc1:= pc); eauto. *)
(*     simpl. auto. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (* prove sound_own *) *)
(*     inv OWN. *)
(*     unfold transfer. rewrite SEL. rewrite STMT. *)
(*     admit. *)
(*   (* step_box *) *)
(*   - inv TRSTMT. inv TRFUN. *)
(*     eapply sound_state_succ with (pc1:= pc); eauto. *)
(*     simpl. auto. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (* prove sound_own *) *)
(*     inv OWN. *)
(*     unfold transfer. rewrite SEL. rewrite STMT. *)
(*     admit. *)
(*   (* step_to_dropplace *) *)
(*   - eapply sound_dropplace; eauto. *)
(*   (** Difficult part: prove split_drop_place small-step simulates the *)
(*   analysis *) *)
(*     admit. *)
(*   (* step_in_dropplace *) *)
(*   - eapply sound_step_dropplace; eauto. *)
(*     econstructor; eauto. *)
(*   (* step_dropstate *) *)
(*   - eapply sound_step_dropstate; eauto. *)
(*     econstructor; eauto. *)
(*   (* step_storagelive *) *)
(*   - inv TRSTMT. inv TRFUN. *)
(*     eapply sound_state_succ with (pc1:= pc); eauto. *)
(*     simpl. auto. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (* prove sound_own *) *)
(*     unfold transfer. rewrite SEL. rewrite STMT. *)
(*     move_place_sound *)
    
(*     Lemma  *)
    
(* admit.     *)
(*     auto. *)
(*   (* step_storagedead *) *)
(*   - inv TRSTMT. inv TRFUN. *)
(*     eapply sound_state_succ with (pc1:= pc); eauto. *)
(*     simpl. auto. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(*     (* prove sound_own *) *)
(*     unfold transfer. rewrite SEL. rewrite STMT. *)
(*     auto. *)
(*   (* step_call *) *)
(*   - inv TRSTMT. econstructor. *)
(*     inv TRFUN. *)
(*     econstructor; eauto. *)
(*     exploit analyze_succ. 1-3: eauto. eapply SEL. *)
(*     instantiate (1 :=next). simpl. auto. eauto. eauto. *)
(*     (* prove sound_own *) *)
(*     instantiate (1 := (init_place (move_place_list own1 (moved_place_list al)) p)). admit. *)
(*     intros (mayinit3 & mayuninit3 & A & B & C). subst. auto. *)
(*     econstructor; eauto. *)
(*   (* step_internal_function *) *)
(*   - exploit function_analyzed; eauto. *)
(*     intros (entry & cfg & nret & initMap & uninitMap & universe & TRFUN & AN). *)
(*     inv TRFUN. *)
(*     inv ENTRY. *)
(*     exploit sound_function_entry; eauto. *)
(*     intros SOUND_INIT. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     (* intros (nret & TRFUN). *) *)
(*     (* tr_cont *) *)
(*     inv TRSTK. *)
(*     econstructor. auto. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*   (* step_external_function *)     *)
(*   - econstructor; eauto. *)
(*   (* step_return_0 *) *)
(*   - econstructor. *)
(*     apply sound_call_cont; auto. *)
(*     eapply tr_stacks_call_cont; eauto. *)
(*   (* step_return_1 *) *)
(*   - econstructor. *)
(*     apply sound_call_cont; auto. *)
(*     eapply tr_stacks_call_cont; eauto. *)
(*   (* step_skip_call *) *)
(*   - econstructor. *)
(*     apply sound_call_cont; auto. *)
(*     eapply tr_stacks_call_cont; eauto. *)
(*   (* step_returnstate *) *)
(*   - (** TODO: problem between the nodes in tr_stacks and sound_cont *) *)
(*     (* inv TRSTK. inv CONT. *) *)
(*     (* inv TRFUN. *) *)
(*     (* rewrite CFG in CFG0. inv CFG0. *) *)
(*     (* clear TRCONT. *) *)
(*     (* econstructor; eauto. *) *)
(*     (* econstructor; eauto. *) *)
(*     (* econstructor. *) *)
(*     (* prove sound_own *) *)
(*     admit. *)
(*   (* step_seq *) *)
(*   - inv TRSTMT. simpl in TRCONT. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*   (* step_skip_seq *) *)
(*   - inv TRSTMT. inv TRCONT. *)
(*     econstructor; eauto. *)
(*     inv CONT. auto. *)
(*   (* step_continue_seq *) *)
(*   - inv TRSTMT. inv TRCONT. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     inv CONT. auto. *)
(*   (* step_break_seq *) *)
(*   - inv TRSTMT. inv TRCONT. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     inv CONT. auto. *)
(*   (* step_ifthenelse *) *)
(*   - inv TRSTMT. *)
(*     econstructor; eauto. *)
(*     destruct b; auto. *)
(*     (** TODO: ifthenelse must use pure expression *) *)
(*     admit. admit. *)
(*   (* step_loop *) *)
(*   - inv TRSTMT. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     econstructor; eauto. *)
(*     inv TRFUN. *)
(*     exploit analyze_succ. 1-3: eauto. eapply SEL. *)
(*     simpl. eauto. *)
(*     unfold transfer. rewrite SEL. eauto. *)
(*     unfold transfer. rewrite SEL. eauto. *)
(*     eauto. *)
(*     intros (mayinit3 & mayuninit3 & A & B & C). *)
(*     subst. auto. *)
(*   (* step_skip_or_continue_loop *) *)
(*   - inv TRCONT. *)
(*     econstructor; eauto.     *)
(*     econstructor; eauto. *)
(*     inv TRFUN. *)
(*     destruct H; inv H. *)
(*     + inv TRSTMT. *)
(*       exploit analyze_succ. 1-3: eauto. eapply SEL. *)
(*       simpl. eauto. *)
(*       unfold transfer. rewrite SEL. eauto. *)
(*       unfold transfer. rewrite SEL. eauto. *)
(*       eauto. *)
(*       intros (mayinit3 & mayuninit3 & A & B & C). *)
(*       subst. auto. *)
(*     + inv TRSTMT. *)
(*       exploit analyze_succ. 1-3: eauto. eapply SEL. *)
(*       simpl. eauto. *)
(*       unfold transfer. rewrite SEL. eauto. *)
(*       unfold transfer. rewrite SEL. eauto. *)
(*       eauto. *)
(*       intros (mayinit3 & mayuninit3 & A & B & C). *)
(*       subst. auto. *)
(*   (* step_break_loop *) *)
(*   - inv TRSTMT. inv TRCONT. inv CONT. *)
(*     econstructor; eauto. *)
(*     econstructor. *)
(* Admitted. *)

End SOUNDNESS.

