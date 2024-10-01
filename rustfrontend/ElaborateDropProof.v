Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import InitDomain InitAnalysis ElaborateDrop.
Require Import Rustlight Rustlightown RustIR RustOp.
Require Import RustIRsem RustIRown RustIRcfg.
Require Import Errors.

(* ro_acc *)
Require ValueAnalysis.
(* injp_acc_local *)
Require SimplLocalsproof.

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

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
    
(* all the children has been moved out *)
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

(* analysis result and flag map types *)
Definition AN : Type := (PMap.t IM.t * PMap.t IM.t * PathsMap.t).
Definition FM : Type := PTree.t (list (place * ident)).

Definition match_glob (ctx: composite_env) (gd tgd: globdef fundef type) : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar eq v1 v2
  | Gfun fd1, Gfun fd2 =>
      transf_fundef ctx fd1 = OK fd2
  | _, _ => False
  end.

(* We do not want to introduce link_order in match_states so we do not
use match_program_gen *)
Record match_prog (p tp: RustIR.program) : Prop :=
  {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_types:
    tp.(prog_types) = p.(prog_types);
    match_prog_def:
    forall id, Coqlib.option_rel (match_glob p.(prog_comp_env)) ((prog_defmap p)!id) ((prog_defmap tp)!id);
    match_prog_skel:
    erase_program tp = erase_program p;
  }.

Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  intros. unfold transl_program in H. monadInv H. unfold transform_partial_program in EQ.
  destruct p. simpl in *. unfold transform_partial_program2 in EQ. 
Admitted. 

(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: program.
Variable tp: program.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Let ce := prog_comp_env p.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob ce) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob ce) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob ce)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None ))).
  (* adhoc generalize because types are the same *)
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None) at 1 3.
    generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None).
    induction Hd as [ | [id1 g1] l1 [id2 g2] l2 [Hi Hg] Hl IH]; cbn in *; eauto.
    intros t1 t2 Ht. eapply IH. eauto. rewrite Hi.
    eapply Genv.add_globdef_match; eauto.
  - unfold NMap.get. rewrite !NMap.gi. constructor.
Qed.

Theorem find_def_match:
  forall b tb delta g,
  Genv.find_def (Genv.globalenv se p) b = Some g ->
  j b = Some (tb, delta) ->
  exists tg,
  Genv.find_def (Genv.globalenv tse tp) tb = Some tg /\
  match_glob ce g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ transf_fundef ce f = OK tf.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v. inv H0.
  rewrite Genv.find_funct_find_funct_ptr in H. unfold Genv.find_funct_ptr in H.
  destruct Genv.find_def as [[|]|] eqn:Hf; try congruence. inv H.
  edestruct find_def_match as (tg & ? & ? & ?); eauto. subst.
  simpl in H0. destruct tg.
  rewrite Genv.find_funct_find_funct_ptr. unfold Genv.find_funct_ptr. rewrite H. eauto.
  contradiction.
Qed.


Theorem find_funct_none:
  forall v tv,
  Genv.find_funct (globalenv se p) v = None ->
  Val.inject j v tv ->
  v <> Vundef ->
  Genv.find_funct (globalenv tse tp) tv = None.
Proof.
  intros v tv Hf1 INJ Hv. destruct INJ; auto; try congruence.
  destruct (Mem.sup_dec b1 se.(Genv.genv_sup)).
  - edestruct Genv.mge_dom; eauto. rewrite H1 in H. inv H.
    rewrite Ptrofs.add_zero. revert Hf1.
    unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    generalize (Genv.mge_defs globalenvs_match b1 H1). intros REL. simpl.
    inv REL. auto.
    destruct x. congruence. simpl in H2.
    destruct y. contradiction. auto.    
  - unfold Genv.find_funct, Genv.find_funct_ptr, Genv.find_def.
    destruct Ptrofs.eq_dec; auto.
    destruct NMap.get as [[|]|] eqn:Hdef; auto. exfalso.
    apply Genv.genv_defs_range in Hdef.
    eapply Genv.mge_separated in H; eauto. cbn in *.
    apply n,H,Hdef.
Qed.

Theorem is_internal_match :
  (forall f tf, transf_fundef ce f = OK tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold fundef.
    simpl. rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.


(* Definitions used in match_cont and match_states *)

Inductive match_drop_place_state : option drop_place_state -> statement -> Prop :=
| match_dps_none:
  match_drop_place_state None Sskip
| match_dps_comp: forall p l,
    (* step_dropplace_init2 has simulated the drop flag condition
    checking *)
    match_drop_place_state (Some (drop_fully_owned_comp p l)) (Ssequence (Sdrop p) (makeseq (map (fun p => Sdrop p) l)))
| match_dps_box: forall l,
    match_drop_place_state (Some (drop_fully_owned_box l)) (makeseq (map (fun p => Sdrop p) l))
.

(* Because in dropplace state we do not know the pc, so we use own_env
to establish the relation between split drop places and target
statement. This relation should be proved when we enter Dropplace
state *)
Inductive match_split_drop_places flagm : own_env -> list (place * bool) -> statement -> Prop :=
| match_sdp_nil: forall own,
    match_split_drop_places flagm own nil Sskip
| match_sdp_cons_flag: forall p flag own l ts full
    (FLAG: get_dropflag_temp flagm p = Some flag)
    (SPLIT: match_split_drop_places flagm (if is_init own p then move_place own p else own) l ts),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full (Some flag)) ts)
| match_sdp_cons_must_init: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_init own p = true),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full None) ts)
| match_sdp_cons_must_uninit: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm own l ts)
    (OWN: is_init own p = false),
    (* how to ensure that p is owned in own_env *)
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
.


(* Invariant of generate_drop_flags *)

Definition sound_flagm ce (body: statement) (cfg: rustcfg) (flagm: FM) (init uninit: PMap.t IM.t) (universe: PathsMap.t) :=
  forall pc next p p1 sel drops mayinit mayuninit,
    cfg ! pc = Some (Isel sel next) ->
    select_stmt body sel = Some (Sdrop p) ->
    split_drop_place ce (PathsMap.get (local_of_place p) universe) p (typeof_place p) = OK drops ->
    In p1 (map fst drops) ->
    get_dropflag_temp flagm p1 = None ->
    get_IM_state init!!pc uninit!!pc (Some (mayinit, mayuninit)) ->
    (* must owned *)
    (must_init mayinit mayuninit p1 = true \/
       (* must unowned *)
       may_init mayinit mayuninit p1 = false).

(** IMPORTANT TODO  *)
Lemma generate_flag_map_sound: forall mayinitMap mayuninitMap universe ce f cfg flags
    (GEN: generate_drop_flags mayinitMap mayuninitMap universe ce f cfg = OK flags),
    sound_flagm ce f.(fn_body) cfg (generate_place_map flags) mayinitMap mayuninitMap universe.
Admitted.


Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Hypothesis TRANSL: match_prog prog tprog.
Variable w: injp_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := globalenv tse tprog.
Let ce := ge.(genv_cenv).

Hypothesis GE: match_stbls injp w se tse.

Let match_stmt (ae: AN) (flagm: FM) := match_stmt get_init_info ae (elaborate_stmt flagm ce).


Lemma match_stbls_incr : forall j m1 m2 MEM,
    injp_acc w (injpw j m1 m2 MEM) ->
    Genv.match_stbls j ge tge.
Proof.
  intros.
  exploit CKLR.match_stbls_acc. 2: apply GE.
  simpl. eauto. intro. simpl in H0. inv H0. eauto.
Qed.

Lemma comp_env_preserved:
  genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. inv TRANSL. simpl in *.
  congruence.
Qed.

Lemma dropm_preserved:
  genv_dropm tge = genv_dropm ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. destruct TRANSL as [_ EQ]. simpl in EQ.
  unfold generate_dropm. simpl.
Admitted.


Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef ce fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. destruct x2. destruct p.
  monadInv EQ2.
  simpl; unfold type_of_function; simpl. auto.
Qed.


Definition wf :=
  match w with
    injpw j m1 m2 Hm => j
  end.

Definition wm1 :=
  match w with
    injpw j m1 m2 Hm => m1
  end.

Definition wm2 :=
  match w with
    injpw j m1 m2 Hm => m2
  end.


Record match_envs (j: meminj) (e: env) (m: mem) (lo hi: Mem.sup) (te: env) (tm: mem) (tlo thi: Mem.sup) : Type :=
  { me_vars: forall id b ty,
      e ! id = Some (b, ty) ->
      exists tb, te ! id = Some (tb, ty)
            /\ j b = Some (tb, 0);

    me_tinj: forall id1 b1 ty1 id2 b2 ty2,
      te!id1 = Some(b1, ty1) -> te!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    
    me_range: forall id b ty,
      e ! id = Some (b, ty) ->
      ~ sup_In b lo /\ sup_In b hi;

    (* local injp_acc breaks when changing the drop flags, but we can
    use me_trange to say that we do not change valid block in the
    incoming world because lo is larger than the support of incoming
    world *)
    me_trange: forall id b ty,
      te ! id = Some (b, ty) ->
      ~ sup_In b tlo /\ sup_In b thi;

    me_tinitial:
      Mem.sup_include (Mem.support wm2) tlo;
    
    me_incr:
      Mem.sup_include lo hi;
    me_tincr:
      Mem.sup_include tlo thi;
                                         
    (* use out_of_reach to protect the drop flags *)
    me_protect: forall id b ty,
      e ! id = None ->
      te ! id = Some (b, ty) ->
      (* used in free_list *)
      Mem.range_perm tm b 0 (size_chunk Mint8unsigned) Cur Freeable
      /\ (forall ofs, loc_out_of_reach j m b ofs);  
  }.

(* relation between source env and target env including the own_env
and invariant of flags map. [(t)lo] is caller stack blocks and [t(hi)]
is callee stack blocks (including heap blocks), so [(t)lo] ⊆
[(t)[hi]] *)
Record match_envs_flagm (j: meminj) (own: own_env) (e: env) (m: mem) (lo hi: Mem.sup) (te: env) (flagm: FM) (tm: mem) (tlo thi: Mem.sup) : Type :=
  { me_wf_flagm: forall p id,
      get_dropflag_temp flagm p = Some id ->
      exists tb v, te ! id = Some (tb, type_bool)
              /\ e ! id = None
              /\ Mem.load Mint8unsigned tm tb 0 = Some (Vint v)
              (* TODO: add a rust bool_val *)
              /\ negb (Int.eq v Int.zero) = is_init own p;

    me_flagm_inj: forall p1 p2 id1 id2,
      get_dropflag_temp flagm p1 = Some id1 ->
      get_dropflag_temp flagm p2 = Some id2 ->
      p1 <> p2 ->
      id1 <> id2;
    
    me_envs: match_envs j e m lo hi te tm tlo thi;
  }.


(* empty env match *)
Lemma match_empty_envs: forall j m tm lo hi tlo thi,
    Mem.sup_include lo hi ->
    Mem.sup_include tlo thi ->
    Mem.sup_include (Mem.support wm2) tlo ->
    match_envs j empty_env m lo hi empty_env tm tlo thi.
Proof.
  intros.
  constructor; intros.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  auto.
  auto. auto.
  erewrite PTree.gempty in *. congruence.
  (* erewrite PTree.gempty in *. congruence. *)
Qed.

Lemma match_envs_injp_acc: forall j1 j2 le m1 m2 lo hi tle tm1 tm2 tlo thi Hm1 Hm2
    (MENV: match_envs j1 le m1 lo hi tle tm1 tlo thi)
    (INJP: injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2))
    (INCL1: Mem.sup_include hi (Mem.support m1))
    (INCL2: Mem.sup_include thi (Mem.support tm1)),
    match_envs j2 le m2 lo hi tle tm2 tlo thi.
Proof.
  intros.
  inv MENV.
  econstructor;eauto.
  intros. exploit me_vars0;eauto.
  intros (tb & A & B).
  exists tb. split; auto.
  inv INJP.
  eapply H12. auto.
  (* me_protect *)
  intros. exploit me_protect0; eauto.
  intros (A & B). inv INJP.  
  split.
  red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
  eapply Mem.perm_valid_block; eauto.
  intros.
  eapply loc_out_of_reach_incr; eauto.
  eapply Mem.DOMIN. eauto.
  eapply Mem.perm_valid_block; eauto. eapply A.
  instantiate (1 := 0). simpl. lia.
Qed.
  
(** Properties of match_envs_flagm: use match_envs_injp_acc to prove this *)
Lemma match_envs_flagm_injp_acc: forall j1 j2 own le m1 m2 lo hi tle flagm tm1 tm2 tlo thi Hm1 Hm2
    (MENV: match_envs_flagm j1 own le m1 lo hi tle flagm tm1 tlo thi)
    (INJP: injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2))
    (INCL1: Mem.sup_include hi (Mem.support m1))
    (INCL2: Mem.sup_include thi (Mem.support tm1)),
    match_envs_flagm j2 own le m2 lo hi tle flagm tm2 tlo thi.
Proof.
  intros.
  econstructor.
  intros. exploit me_wf_flagm; eauto.
  intros (tb & v & A1 & A2 & A3 & A4).
  exists tb,v. repeat apply conj; auto.
  exploit me_protect. eapply me_envs; eauto.
  eauto. eauto. intros (PERM & REACH).
  inv INJP.
  eapply Mem.load_unchanged_on. eauto.
  intros. eapply REACH. auto.
  eapply me_flagm_inj. eauto.
  eapply match_envs_injp_acc; eauto.
  eapply me_envs. eauto.
Qed.

Lemma match_envs_flagm_incr_bounds: forall j own le m lo hi1 hi2 tle flagm tm tlo thi1 thi2
   (MENV: match_envs_flagm j own le m lo hi1 tle flagm tm tlo thi1)
   (INCR: Mem.sup_include hi1 hi2)
   (TINCR: Mem.sup_include thi1 thi2),
    match_envs_flagm j own le m lo hi2 tle flagm tm tlo thi2.
Proof.
  intros. inv MENV.
  econstructor; eauto.
  inv me_envs0; econstructor; eauto.
  intros. exploit me_range0;eauto.
  intros (A & B). split; auto.
  intros. exploit me_trange0;eauto.
  intros (A & B). split; auto.
Qed.  
  
(* unused *)
(* Lemma match_envs_flagm_bound_unchanged: forall j own le m1 m2 lo hi tle flagm tm1 tm2 tlo thi , *)
(*     match_envs_flagm j own le m1 lo hi tle flagm tm1 tlo thi -> *)
(*     Mem.unchanged_on (fun b _ => ~ Mem.sup_In b hi) m1 m2 -> *)
(*     Mem.unchanged_on (fun b _ => ~ Mem.sup_In b thi) tm1 tm2 -> *)
(*     match_envs_flagm j own le m2 lo hi tle flagm tm2 tlo thi. *)
(* Proof. *)
(* Admitted.  *)

(* establish match_envs after the allocation of the drop flags in the
target programs *)
Lemma alloc_drop_flags_match: forall j1 m1 tm1 e1 lo hi te1 tlo thi (flags: list (place * ident)) Hm1
    (MENV: match_envs j1 e1 m1 lo hi te1 tm1 tlo thi)
    (SINCR: Mem.sup_include thi (Mem.support tm1))
    (DISJOINT: forall p id, In (p, id) flags -> e1 ! id = None),
  exists te2 tm2 Hm2,
    alloc_variables tge te1 tm1 (combine (map snd flags) (repeat type_bool (length flags))) te2 tm2
    /\ injp_acc (injpw j1 m1 tm1 Hm1) (injpw j1 m1 tm2 Hm2)
    (* wf_dropm *)
    /\ (forall p id, In (p, id) flags ->
               exists b, te2 ! id = Some (b, type_bool)
                    /\ e1 ! id = None)
    /\ match_envs j1 e1 m1 lo hi te2 tm2 tlo (Mem.support tm2).
Admitted.

(* allocate the same variables inject *)
Lemma alloc_variables_match: forall e1 te1 m1 tm1 vars e2 m2 lo hi tlo thi j1 Hm1
    (ALLOC: alloc_variables ge e1 m1 vars e2 m2)
    (MENV: match_envs j1 e1 m1 lo hi te1 tm1 tlo thi)
    (INCL: Mem.sup_include hi (Mem.support m1))
    (TINCL: Mem.sup_include thi (Mem.support tm1)),
  exists j2 tm2 Hm2 te2,
    alloc_variables tge te1 tm1 vars te2 tm2
    /\ match_envs j2 e2 m2 lo (Mem.support m2) te2 tm2 tlo (Mem.support tm2)
    /\ injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2).
Admitted.

Lemma alloc_variables_app: forall ce m1 m2 m3 l1 l2 e1 e2 e3,
    alloc_variables ce e1 m1 l1 e2 m2 ->
    alloc_variables ce e2 m2 l2 e3 m3 ->
    alloc_variables ce e1 m1 (l1 ++ l2) e3 m3.
Admitted.

Lemma bind_parameters_injp_acc: forall params e te m1 m2 vl tvl j lo hi tlo thi tm1 Hm1
    (STORE: bind_parameters ge e m1 params vl m2)
    (MENV: match_envs j e m1 lo hi te tm1 tlo thi)
    (VINJS: Val.inject_list j vl tvl),
  exists tm2 Hm2,
    bind_parameters tge te tm1 params tvl tm2
    /\ injp_acc (injpw j m1 tm1 Hm1) (injpw j m2 tm2 Hm2).
Admitted.

Inductive match_cont (j: meminj) : AN -> FM -> statement -> rustcfg -> cont -> RustIRsem.cont -> node -> option node -> option node -> node -> mem -> mem -> sup -> sup -> Prop :=
| match_Kseq: forall an flagm body cfg s ts k tk pc next cont brk nret m tm bound tbound
    (MSTMT: match_stmt an flagm body cfg s ts pc next cont brk nret)
    (MCONT: match_cont j an flagm body cfg k tk next cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kseq s k) (RustIRsem.Kseq ts tk) pc cont brk nret m tm bound tbound
| match_Kstop: forall an flagm body cfg nret m tm bound tbound
    (RET: cfg ! nret = Some Iend),
    match_cont j an flagm body cfg Kstop RustIRsem.Kstop nret None None nret m tm bound tbound
| match_Kloop: forall an flagm body cfg s ts k tk body_start loop_jump_node exit_loop nret contn brk m tm bound tbound
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an flagm body cfg s ts body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: match_cont j an flagm body cfg k tk exit_loop contn brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kloop s k) (RustIRsem.Kloop ts tk) loop_jump_node (Some loop_jump_node) (Some exit_loop) nret m tm bound tbound
| match_Kcall: forall an flagm body cfg k tk nret f tf le tle own p m tm bound tbound
    (MSTK: match_stacks j (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) m tm bound tbound)
    (RET: cfg ! nret = Some Iend),
    (* in the end of a function. an and body are not important, those
    in match_stacks are important *)
    match_cont j an flagm body cfg (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) nret None None nret m tm bound tbound
| match_Kdropcall: forall an flagm body cfg k tk pc cont brk nret st membs b tb ofs tofs id m tm bound tbound
    (INJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (MCONT: match_cont j an flagm body cfg k tk pc cont brk nret m tm bound tbound),
    match_cont j an flagm body cfg (Kdropcall id (Vptr b ofs) st membs k) (RustIRsem.Kdropcall id (Vptr tb tofs) st membs tk) pc cont brk nret m tm bound tbound
| match_Kdropplace: forall f tf st l k tk e te own1 own2 flagm cfg nret cont brk pc ts1 ts2 m tm lo tlo hi thi maybeInit maybeUninit universe entry mayinit mayuninit
    (** Do we need match_stacks here?  *)
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MSTK: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc cont brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (ORDERED: move_ordered_split_places_spec own1 (map fst l))
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (MOVESPLIT: move_split_places own1 l = own2),
    (* source program: from dropplace to droopstate, target: from
    state to dropstate. So Kdropplace matches Kcall *)
    match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg (Kdropplace f st l e own1 k) (RustIRsem.Kcall None tf te (RustIRsem.Kseq ts1 (RustIRsem.Kseq ts2 tk))) pc cont brk nret m tm hi thi

with match_stacks (j: meminj) : cont -> RustIRsem.cont -> mem -> mem -> sup -> sup -> Prop :=
| match_stacks_stop: forall m tm bound tbound,
    match_stacks j Kstop (RustIRsem.Kstop) m tm bound tbound
| match_stacks_call: forall flagm f tf nret cfg pc contn brk k tk own1 own2 p le tle m tm lo tlo hi thi maybeInit maybeUninit universe entry stmt mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (* callee use stacks hi and thi, so caller f uses lo and tlo*)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk pc contn brk nret m tm lo tlo)
    (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (STMT: add_dropflag flagm ce universe p true = OK stmt),
    match_stacks j (Kcall p f le own1 k) (RustIRsem.Kcall (Some p) tf tle (RustIRsem.Kseq stmt tk)) m tm hi thi
.

(** Properties of match_cont  *)

Lemma match_cont_injp_acc: forall k tk j1 j2 an fm body cfg pc cont brk nret m1 m2 tm1 tm2 lo tlo Hm1 Hm2
    (MCONT: match_cont j1 an fm body cfg k tk pc cont brk nret m1 tm1 lo tlo)
    (INJP: injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2))
    (INCL1: Mem.sup_include lo (Mem.support m1))
    (INCL2: Mem.sup_include tlo (Mem.support tm1)),
    match_cont j2 an fm body cfg k tk pc cont brk nret m2 tm2 lo tlo.
Proof.
  induction k; intros; inv MCONT.
  - constructor. auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - inv MSTK.
    econstructor; eauto.
    econstructor; eauto.
    eapply IHk. eauto.
    eauto.
    eapply Mem.sup_include_trans. eapply me_incr.
    eapply me_envs; eauto. auto.
    eapply Mem.sup_include_trans. eapply me_tincr.
    eapply me_envs; eauto. auto.
    eapply match_envs_flagm_injp_acc. eauto.
    eauto. auto. auto.
  - econstructor; eauto.
    eapply IHk. eauto.
    eauto.
    eapply Mem.sup_include_trans. eapply me_incr.
    eapply me_envs; eauto. auto.
    eapply Mem.sup_include_trans. eapply me_tincr.
    eapply me_envs; eauto. auto.
    eapply match_envs_flagm_injp_acc. eauto.
    eauto. auto. auto.
  - econstructor; eauto.
    inv INJ.
    econstructor; auto. inv INJP.
    eapply H12. auto.
Qed.


Lemma match_cont_incr_bounds: forall k tk j1 an fm body cfg pc cont brk nret m1 tm1 lo tlo lo' tlo'
    (MCONT: match_cont j1 an fm body cfg k tk pc cont brk nret m1 tm1 lo tlo)
    (INCL1: Mem.sup_include lo lo')
    (INCL2: Mem.sup_include tlo tlo'),
    match_cont j1 an fm body cfg k tk pc cont brk nret m1 tm1 lo' tlo'.
Proof.
  induction 1; try econstructor; eauto.
  inv MSTK. econstructor;eauto.
  eapply match_envs_flagm_incr_bounds; eauto.
  eapply match_envs_flagm_incr_bounds; eauto.
Qed.



Lemma match_stacks_injp_acc: forall k tk j1 j2 m1 m2 tm1 tm2 lo tlo Hm1 Hm2
    (MCONT: match_stacks j1 k tk m1 tm1 lo tlo)
    (INJP: injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2))
    (INCL1: Mem.sup_include lo (Mem.support m1))
    (INCL2: Mem.sup_include tlo (Mem.support tm1)),
    match_stacks j2 k tk m2 tm2 lo tlo.
Proof.
  intros. inv MCONT.
  econstructor.
  assert (SUP1: Mem.sup_include lo0 (Mem.support m1)).
  { eapply Mem.sup_include_trans. eapply me_incr.
    eapply me_envs; eauto. auto. }
  assert (SUP2: Mem.sup_include tlo0 (Mem.support tm1)).
  { eapply Mem.sup_include_trans. eapply me_tincr.
    eapply me_envs; eauto. auto. }
  econstructor; eauto.
  eapply match_cont_injp_acc; eauto.
  eapply match_envs_flagm_injp_acc; eauto.
Qed.
  
Lemma match_stacks_incr_bounds: forall k tk j1 m1 tm1 lo tlo lo' tlo'
    (MCONT: match_stacks j1 k tk m1 tm1 lo tlo)
    (INCL1: Mem.sup_include lo lo')
    (INCL2: Mem.sup_include tlo tlo'),
    match_stacks j1 k tk m1 tm1 lo' tlo'.
Proof.
  intros. inv MCONT; econstructor; eauto.
  eapply match_envs_flagm_incr_bounds; eauto.
Qed.

(** Only support m1 unchanged: because we cannot ensure that the
out_of_reach block becomes mapped in m1 *)
Lemma match_cont_bound_unchanged: forall k tk j an fm body cfg pc cont brk nret m1 tm1 tm2 lo tlo
   (MCONT:match_cont j an fm body cfg k tk pc cont brk nret m1 tm1 lo tlo)   
   (UNC: Mem.unchanged_on (fun b _ => Mem.sup_In b tlo) tm1 tm2),
    match_cont j an fm body cfg k tk pc cont brk nret m1 tm2 lo tlo.
Proof.
  induction k; intros; inv MCONT.
  - constructor. auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - inv MSTK.
    econstructor; eauto.
    econstructor; eauto.
    eapply IHk; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply me_tincr. eapply me_envs; eauto. auto.
    (* match_envs_flagm *)
    generalize MENV. intros MENV1.
    inv MENV.
    econstructor; eauto.
    (* wf_flagm *)
    intros. exploit me_wf_flagm0; eauto.
    intros (tb & v & A1 & A2 & A3 & A4).
    exists tb, v. repeat apply conj; auto.
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    (* mathc_envs *)
    inv me_envs0.
    constructor; eauto.
    intros. exploit me_protect0; eauto.
    intros (B1 & B2).
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    eapply Mem.perm_valid_block; eauto.
    (* out_of_reach *)
    auto.
  - econstructor; eauto.
    eapply IHk; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply me_tincr. eapply me_envs; eauto. auto.
    (* match_envs_flagm *)
    generalize MENV. intros MENV1.
    inv MENV.
    econstructor; eauto.
    (* wf_flagm *)
    intros. exploit me_wf_flagm0; eauto.
    intros (tb & v & A1 & A2 & A3 & A4).
    exists tb, v. repeat apply conj; auto.
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    (* mathc_envs *)
    inv me_envs0.
    constructor; eauto.
    intros. exploit me_protect0; eauto.
    intros (B1 & B2).
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    eapply Mem.perm_valid_block; eauto.
    (* out_of_reach *)
    auto.
  - econstructor; eauto.
Qed.

Inductive match_states : state -> RustIRsem.state -> Prop := 
| match_regular_state:
  forall f s k e own m tf ts tk te tm j flagm maybeInit maybeUninit universe cfg nret cont brk next pc Hm lo tlo hi thi entry mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MSTMT: match_stmt (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg s ts pc next cont brk nret)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* well-formedness of the flag map *)
    (MENV: match_envs_flagm j own e m lo hi te flagm tm tlo thi)
    (* property of flagm when encounting drop statement *)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* Put sound_own here which may be inevitable due to the
    flow-insensitiveness of RustIR semantics.*)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (SOUNDOWN: sound_own own mayinit mayuninit universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (State f s k e own m) (RustIRsem.State tf ts tk te tm)
| match_dropplace: forall f tf st l k tk e te own1 own2 m tm j flagm  maybeInit maybeUninit universe cfg nret cont brk next ts1 ts2 Hm lo tlo hi thi entry mayinit mayuninit
    (AN: analyze ce f cfg entry= OK (maybeInit, maybeUninit, universe))
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk next cont brk nret m tm lo tlo)
    (MDPS: match_drop_place_state st ts1)
    (MSPLIT: match_split_drop_places flagm own1 l ts2)
    (* update one flag does not affect other flags *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst l))
    (MINJ: injp_acc w (injpw j m tm Hm))
    (* maybe difficult: transition of own is small step! *)
    (MENV: match_envs_flagm j own1 e m lo hi te flagm tm tlo thi)
    (SFLAGM: sound_flagm ce f.(fn_body) cfg flagm maybeInit maybeUninit universe)
    (* small-step move_place to simulate big-step move_place in
    transfer. maybe difficult to prove *)
    (MOVESPLIT: move_split_places own1 l = own2)
    (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (BOUND: Mem.sup_include hi (Mem.support m))
    (TBOUND: Mem.sup_include thi (Mem.support tm)),
    match_states (Dropplace f st l k e own1 m) (RustIRsem.State tf ts1 (RustIRsem.Kseq ts2 tk) te tm)
| match_dropstate: forall k tk m tm j flagm maybeInit maybeUninit universe body cfg nret cont brk next b ofs tb tofs st membs id lo tlo Hm
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm body cfg k tk next cont brk nret m tm lo tlo)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (* no new stacks block in dropstate *)
    (BOUND: Mem.sup_include lo (Mem.support m))
    (TBOUND: Mem.sup_include tlo (Mem.support tm)),
    match_states (Dropstate id (Vptr b ofs) st membs k m) (RustIRsem.Dropstate id (Vptr tb tofs) st membs tk tm)
| match_callstate: forall j vf tvf m tm vargs tvargs k tk Hm
    (VINJ: Val.inject j vf tvf)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (AINJ: Val.inject_list j vargs tvargs)
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Callstate vf vargs k m) (RustIRsem.Callstate tvf tvargs tk tm)
| match_returnstate: forall j v tv m tm k tk Hm
    (VINJ: Val.inject j v tv)
    (MINJ: injp_acc w (injpw j m tm Hm))
    (MCONT: match_stacks j k tk m tm (Mem.support m) (Mem.support tm)),
    match_states (Returnstate v k m) (RustIRsem.Returnstate tv tk tm)
. 

(** This property is difficult to prove! *)
Inductive wf_split_drop_places flagm (init uninit universe: PathsMap.t) : own_env -> list (place * bool) -> Prop :=
| wf_sdp_nil: forall own,
    wf_split_drop_places flagm init uninit universe own nil
| wf_sdp_flag: forall own b id l p
    (FLAG: get_dropflag_temp flagm p = Some id)
    (WF: wf_split_drop_places flagm init uninit universe (if is_init own p then (move_place own p) else own) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
| wf_sdp_must: forall own b l p
    (FLAG: get_dropflag_temp flagm p = None)
    (OWN: must_init init uninit p = is_init own p)
    (WF: wf_split_drop_places flagm init uninit universe (if is_init own p then (move_place own p) else own) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
.


(** IMPORTANT TODO  *)
Lemma ordered_split_drop_places_wf:
  forall drops own init uninit universe flagm
    (ORDER: split_places_ordered (map fst drops))
    (OWN: forall p full, In (p, full) drops ->
                    must_init init uninit p = true ->
                    is_init own p = true)
    (NOTOWN: forall p, must_init init uninit p = false ->
                  may_init init uninit p = false ->
                  is_init own p = false)
    (UNI: PathsMap.eq universe (own_universe own))
    (FLAG: forall p full,
        In (p, full) drops ->
        get_dropflag_temp flagm p = None ->
        must_init init uninit p = true
        \/ may_init init uninit p = false),
    wf_split_drop_places flagm init uninit universe own drops.
Proof.
  induction drops; simpl; intros.
  constructor.
  destruct a.
  assert (A: wf_split_drop_places flagm init uninit universe
               (if is_init own p then move_place own p else own) drops).
  { inv ORDER.
    eapply IHdrops. eauto.
    (* prove own *)
    + intros p1 full1 IN1 MUSTOWN1. 
      (* show that p1 is still owned after removing p which is not a
    pare nt of p1 from the own_env *)
      exploit OWN. right. eauto. auto. intros POWN1.
      destruct (is_init own p) eqn: POWN; auto.
      eapply Forall_forall with (x:= p1) in H1; auto.
      (* use H1 POWN1 to prove this goal *)
      eapply move_irrelavent_place_still_owned; eauto.
      eapply in_map_iff. exists (p1, full1). auto.
    + intros p1 MUSTOWN1 MAYOWN1.
      exploit NOTOWN. eauto. eauto.
      intros NOTOWNP1.
      destruct (is_init own p) eqn: POWN; auto.
      apply move_place_still_not_owned; auto.      
    + eapply PathsMap.eq_trans; eauto.
      unfold move_place. destruct (is_init own p) eqn: POWN; apply PathsMap.eq_refl.
    + intros. eapply FLAG; eauto. }
  
  (* p has drop flag or not *)
  destruct (get_dropflag_temp flagm p) eqn: PFLAG.
  - econstructor; eauto.
  - exploit FLAG. left; eauto.
    auto. intros MOWN.
    eapply wf_sdp_must. eauto. 2: auto.
    destruct (must_init init uninit p) eqn: MUSTOWN.
    + symmetry. eapply OWN; eauto.
    + destruct MOWN. congruence.
      symmetry. eapply NOTOWN.
      auto. auto.
Qed.      

    
Lemma elaborate_drop_match_drop_places:
  forall drops flagm own init uninit universe
    (** we need some restriction on drops!! *)
    (* (INUNI: forall p, In p (map fst drops) -> in_universe own p = true) *)
    (WFDROPS: wf_split_drop_places flagm init uninit universe own drops),
    match_split_drop_places flagm own drops (elaborate_drop_for_splits init uninit universe flagm drops).
Proof.
  induction drops; intros.
  econstructor.
  simpl. destruct a.
  destruct (get_dropflag_temp flagm p) eqn: FLAG.
  - econstructor. auto.
    eapply IHdrops.
    inv WFDROPS.
    auto. congruence.
  - inv WFDROPS. congruence.
    destruct (must_init init uninit p) eqn: MUST.
    (* must_owned = true *)
    + rewrite <- OWN in WF.
      econstructor; auto.
    (* must_owned = false *)
    + rewrite <- OWN in WF.
      econstructor; auto.
Qed.

Lemma deref_loc_inject: forall ty m b ofs v tm j tb tofs,
    deref_loc ty m b ofs v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr tb tofs) ->
    exists tv, deref_loc ty tm tb tofs tv /\ Val.inject j v tv.
Proof.
    intros. inv H. 
    - (*by value*)
      exploit Mem.loadv_inject; eauto. intros [tv [A B]].
      exists tv. split. econstructor. 
      instantiate (1:= chunk). 
      destruct ty; simpl in *; congruence.
      auto. auto.
    - (* by ref*)
      exists ((Vptr tb tofs)). split. 
      eapply deref_loc_reference. 
      destruct ty; simpl in *; congruence.
      auto. 
    - (*by copy*)
      exists (Vptr tb tofs). split. eapply deref_loc_copy.
      destruct ty; simpl in *; congruence.
      auto.
  Qed. 

Lemma eval_place_inject: forall le tle m tm p b ofs j own lo hi tlo thi flagm,
    eval_place ge le m p b ofs ->
    Mem.inject j m tm ->
    match_envs_flagm j own le m lo hi tle flagm tm tlo thi ->
    exists b' ofs', eval_place tge tle tm p b' ofs' /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Proof. 
  induction 1; intros. 
  - exploit me_vars; eauto. eapply me_envs; eauto.
    intros (tb & TE & J). eexists. eexists. split. eapply eval_Plocal; eauto. 
    eapply Val.inject_ptr; eauto.
  - exploit IHeval_place; eauto. intros (b' & ofs' & EV & INJ).  
    rewrite comp_env_preserved in *. 
    inv INJ. eexists. eexists. split. econstructor; eauto.
    eapply Val.inject_ptr; eauto.  
    repeat rewrite Ptrofs.add_assoc. f_equal.  
    rewrite Ptrofs.add_commut. eauto. 
  - exploit IHeval_place; eauto. intros (b' & ofs' & EV & INJ). 
    exploit Mem.loadv_inject; eauto. intros [v' [A B]]. inv B.
    rewrite comp_env_preserved in *. 
    eexists. eexists. split. econstructor; eauto. 
    inv INJ. econstructor; eauto. 
    repeat rewrite Ptrofs.add_assoc. f_equal.  
    rewrite Ptrofs.add_commut. eauto. 
  - exploit IHeval_place; eauto. 
    intros (b' & ofs'0 & EV & INJ). 
    exploit deref_loc_inject; eauto. intros [v' [A B]]. inv B. 
    eexists. eexists. split. econstructor; eauto. econstructor; eauto. 
Qed. 

Lemma deref_loc_rec_inject: forall j m tm b ofs tb tofs tyl v,
    deref_loc_rec m b ofs tyl v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr tb tofs) ->
    exists tv, deref_loc_rec tm tb tofs tyl tv /\ Val.inject j v tv.
Proof. 
  induction 1. 
  - intros. eexists. split. econstructor. auto. 
  - intros A B. exploit IHderef_loc_rec; eauto. intros (tv & C & D).
    inv D. exploit deref_loc_inject; eauto. intros (tv' & E & F). 
    eexists. split. econstructor; eauto. auto.
Qed. 
  
Lemma drop_box_rec_injp_acc: forall m1 m2 tm1 j Hm b ofs tb tofs tyl ge tge
        (DROP: drop_box_rec ge b ofs m1 tyl m2)
        (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)),
      exists tj tm2 tHm,
        drop_box_rec tge tb tofs tm1 tyl tm2
        /\ injp_acc (injpw j m1 tm1 Hm) (injpw tj m2 tm2 tHm).
Proof. 
  
Admitted. 



Lemma eval_pexpr_inject:
  forall e le m v tm tle own lo hi flagm tlo thi j
    (EVAL: eval_pexpr ge le m e v)
    (MINJ: Mem.inject j m tm)
    (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
    exists tv, eval_pexpr tge tle tm e tv /\ Val.inject j v tv.
Proof. 
  induction 1; intros. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - eexists. split. econstructor. eauto. 
  - exploit IHEVAL; eauto. intros (tv & A & B).
    exploit Cop.sem_unary_operation_inject; eauto. intros (tv' & C & D). 
    eexists. split. 
    econstructor; eauto. eauto. 
  - exploit IHEVAL1; eauto. intros (tv1 & A1 & B1).
    exploit IHEVAL2; eauto. intros (tv2 & A2 & B2).
    exploit Cop.sem_binary_operation_rust_inject; eauto. intros (tv' & C & D). 
    eexists. split. 
    econstructor; eauto. unfold Cop.sem_binary_operation_rust. 
    destruct op; eauto.
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    exploit deref_loc_inject; eauto. intros (tv & TDEREF & VINJ).
    eexists. split. econstructor; eauto. auto. 
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    inv INJ. exploit Mem.loadv_inject; eauto. intros (tv & A & B). inv B. 
    eexists. split. econstructor; eauto. 
    rewrite comp_env_preserved; auto. 
    destruct (Int.eq tag (Int.repr tagz)); simpl; econstructor. 
  - exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ).  
    eexists. split. econstructor; eauto. auto.
Qed. 


Lemma eval_expr_inject: forall e le m v tm tle own lo hi flagm tlo thi j
        (EVAL: eval_expr ge le m e v)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tv, eval_expr tge tle tm e tv /\ Val.inject j v tv.
Proof. 
  destruct e; intros. 
  - inv EVAL. inv H2. exploit eval_place_inject; eauto. intros (b' & ofs' & EV & INJ). 
    exploit deref_loc_inject; eauto. intros (tv & TDEREF & VINJ). 
    eexists. split. econstructor. eapply eval_Eplace; eauto. eauto. 
  - inv EVAL. exploit eval_pexpr_inject; eauto. intros (tv & A & B). 
    eexists. split. econstructor. eauto. auto. 
Qed.

Ltac TrivialInject :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
  | [ |- exists v', Some ?v = Some v' /\ _ ] => exists v; split; auto
  | _ => idtac
  end.


Lemma sem_cast_inject: forall v ty1 ty2 j tv v' own le m lo hi tle flagm tm tlo thi
        (CAST: sem_cast v ty1 ty2 = Some v')
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi)
        (MINJ: Mem.inject j m tm)
        (VINJ: Val.inject j v tv),
        exists tv', sem_cast tv ty1 ty2  = Some tv' /\ Val.inject j v' tv'. 
Proof.
  unfold sem_cast; intros; destruct (classify_cast ty1 ty2); inv VINJ; TrivialInject.  
  - econstructor; eauto. 
  - destruct (ident_eq id1 id2) eqn: EQ; inv CAST. 
    eexists. split. eauto. econstructor; eauto. 
  - destruct (ident_eq id1 id2); inv CAST; eauto. 
Qed.

Lemma eval_exprlist_inject: forall le m args vl tm tle own lo hi flagm tlo thi j tyl
        (EVAL: eval_exprlist ge le m args tyl vl)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tvl, eval_exprlist tge tle tm args tyl tvl /\ Val.inject_list j vl tvl.
Proof. 
  induction 1; intros. 
  - eexists. split. econstructor. eauto. 
  - exploit eval_expr_inject; eauto. intros (tv & A & B). 
    exploit IHEVAL; eauto. intros (tvl & C & D).
    exploit sem_cast_inject; eauto. intros (tv' & E & F). 
    eexists. split. econstructor; eauto. 
    econstructor; eauto. 
Qed. 

(* same as that in SimplLocalProof *)
Lemma assign_loc_support: forall ge ty m b ofs v m',
    assign_loc ge ty m b ofs v m' -> Mem.support m' = Mem.support m.
Admitted.


Lemma assign_loc_injp_acc: forall f ty m loc ofs v m' tm loc' ofs' v' Hm,
    assign_loc ge ty m loc ofs v m' ->
    Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
    Val.inject f v v' ->
    exists f' tm' Hm',
      assign_loc tge ty tm loc' ofs' v' tm'
      /\ injp_acc (injpw f m tm Hm) (injpw f' m' tm' Hm').
Admitted.


Lemma type_to_drop_member_state_eq: forall id ty,
    type_to_drop_member_state ge id ty = type_to_drop_member_state tge id ty.
Proof.
  intros. unfold type_to_drop_member_state.
  erewrite comp_env_preserved; eauto. auto.
  erewrite dropm_preserved; eauto.
Qed.


(** Properties of assignment of drop flags *)

Lemma eval_set_drop_flag: forall flag te id tb tm1 m1 j1 tf k
    (TE: te ! id = Some (tb, type_bool))
    (MINJ: Mem.inject j1 m1 tm1)
    (PERM: Mem.range_perm tm1 tb 0 (size_chunk Mint8unsigned) Cur Freeable)
    (REACH: forall ofs : Z, loc_out_of_reach j1 m1 tb ofs),
    exists tm2,
      RustIRsem.step tge (RustIRsem.State tf (set_dropflag id flag) k te tm1) E0 (RustIRsem.State tf Sskip k te tm2)
      /\ Mem.inject j1 m1 tm2                   
      /\ Mem.load Mint8unsigned tm2 tb 0 = Some (Val.of_bool flag)
      (* unchanged properties *)
      /\ ValueAnalysis.ro_acc tm1 tm2
      /\ Mem.unchanged_on (fun b _ => b <> tb) tm1 tm2
      (* permission in b is unchanged *)
      /\ Mem.range_perm tm2 tb 0 (size_chunk Mint8unsigned) Cur Freeable.
Proof.
  intros.
    unfold set_dropflag.
    (* construct storev *)
    assert (VALID: Mem.valid_access tm1 Mint8unsigned tb 0 Writable).
    { red. split.
      rewrite Z.add_0_l. eapply Mem.range_perm_implies; eauto.
      constructor. apply Z.divide_0_r. }
    generalize (Mem.valid_access_store tm1 Mint8unsigned tb 0 (Vint  (if Int.eq (if flag then Int.one else Int.zero) Int.zero then Int.zero else Int.one)) VALID).
    intros (tm2 & STORE).
    (* establish new injection *)
    exploit Mem.store_outside_inject; eauto.
    intros. eapply REACH. eauto.
    eapply Mem.perm_cur_max.
    instantiate (1 := ofs' + delta).
    replace (ofs' + delta - delta) with ofs' by lia.
    eapply Mem.perm_implies; eauto. constructor.
    intros MINJ1.
    (* ro_acc *)
    assert (RO1: ValueAnalysis.ro_acc m1 m1). eapply ValueAnalysis.ro_acc_refl.
    assert (RO2: ValueAnalysis.ro_acc tm1 tm2). { eapply ValueAnalysis.ro_acc_store; eauto. }
    exists tm2.
    repeat apply conj; auto.
    (* step *)
    econstructor.
    econstructor; eauto.
    econstructor. econstructor.
    simpl.
    (* maybe we should prove cast_val_casted *)
    unfold sem_cast. simpl. eauto. 
    econstructor. simpl. eauto.
    eauto.
    erewrite Mem.load_store_same; eauto.
    f_equal. simpl. destruct flag; auto.
    (* unchanged_on *)
    eapply Mem.store_unchanged_on; eauto.
    red. intros. eapply Mem.perm_store_1; eauto.
Qed.

Lemma eval_init_drop_flag_wf: forall te id tb tm1 m1 j1 init uninit universe p stmt own tf k 
   (TE: te ! id = Some (tb, type_bool))
   (MINJ: Mem.inject j1 m1 tm1)
   (PERM: Mem.range_perm tm1 tb 0 (size_chunk Mint8unsigned) Cur Freeable)
   (REACH: forall ofs : Z, loc_out_of_reach j1 m1 tb ofs)
   (STMT: init_drop_flag init uninit p id = OK stmt)
   (OWN: sound_own own init uninit universe)
   (IN: Paths.In p (PathsMap.get (local_of_place p) universe)),
  exists tm2 v,
    star RustIRsem.step tge (RustIRsem.State tf stmt k te tm1) E0 (RustIRsem.State tf Sskip k te tm2)
    /\ Mem.inject j1 m1 tm2 
    /\ Mem.load Mint8unsigned tm2 tb 0 = Some (Vint v)
    /\ negb (Int.eq v Int.zero) = is_init own p
    /\ ValueAnalysis.ro_acc tm1 tm2
    /\ Mem.unchanged_on (fun b _ => b <> tb) tm1 tm2
    /\ Mem.range_perm tm2 tb 0 (size_chunk Mint8unsigned) Cur Freeable.
Proof.
  intros.  
  unfold init_drop_flag in STMT.
  destruct (must_init init uninit p) eqn: MUST.
  - inv STMT.
    exploit (eval_set_drop_flag true); eauto.
    instantiate (1 := k). instantiate (1 := tf).
    intros (tm2 & A & B & C & D & E & F). simpl in *.
    unfold Vtrue in C.
    exists tm2, Int.one.
    repeat apply conj; auto.
    eapply star_step. eauto.
    eapply star_refl. auto.
    erewrite must_init_sound; eauto.
  - destruct (may_init init uninit p) eqn: MAY; try congruence.
    inv STMT.
    exploit (eval_set_drop_flag false); eauto.
    instantiate (1 := k). instantiate (1 := tf).
    intros (tm2 & A & B & C & D & E & F). simpl in *.
    unfold Vfalse in C.
    exists tm2, Int.zero.
    repeat apply conj; auto.
    eapply star_step. eauto.
    eapply star_refl. auto.    
    erewrite must_not_init_sound; eauto.
Qed.


(* no injp_acc *)
Lemma eval_init_drop_flags_wf: forall flags init uninit universe init_stmt j1 e m1 lo hi te tm1 tlo thi own tf k
  (STMT: init_drop_flags init uninit flags = OK init_stmt)
  (OWN: sound_own own init uninit universe)
  (MINJ: Mem.inject j1 m1 tm1)
  (WF: forall p id, In (p, id) flags ->
               exists tb, te ! id = Some (tb, type_bool)
                       /\ e ! id = None)
  (MENV: match_envs j1 e m1 lo hi te tm1 tlo thi)
  (* we require that te is injective *)
  (INJ: forall id1 b1 ty1 id2 b2 ty2, te!id1 = Some(b1, ty1) -> te!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2)
  (* idents in flags are norepet *)
  (NOREPET: list_norepet (map snd flags))
  (INUNI: forall p, In p (map fst flags) -> Paths.In p (PathsMap.get (local_of_place p) universe)),
  exists tm2,
    star RustIRsem.step tge (RustIRsem.State tf init_stmt k te tm1) E0 (RustIRsem.State tf Sskip k te tm2)
    /\ Mem.inject j1 m1 tm2
    (* establish me_wf_flagm *)
    /\ (forall p id, In (p, id) flags ->
             exists tb v, te ! id = Some (tb, type_bool)
                     /\ e ! id = None
                     /\ Mem.load Mint8unsigned tm2 tb 0 = Some (Vint v)
                     /\ negb (Int.eq v Int.zero) = is_init own p)
    /\ match_envs j1 e m1 lo hi te tm2 tlo thi
    (* we only change the blocks of drop flags *)
    /\ Mem.unchanged_on (fun b _ => forall p id tb ty, In (p, id) flags -> te ! id = Some (tb, ty) -> b <> tb) tm1 tm2
    /\ ValueAnalysis.ro_acc tm1 tm2.
Proof.
  induction flags; intros; simpl in *.
  - inv STMT. exists tm1.
    generalize (ValueAnalysis.ro_acc_refl tm1). intros RO.
    repeat apply conj.
    eapply star_refl.
    auto. 
    intros. contradiction.
    auto.
    eapply Mem.unchanged_on_refl.
    auto.
 - destruct a. monadInv STMT.
    (* evaluate x0 *)
    generalize (WF p i (or_introl (eq_refl _))).
    intros (tb & TE & ENONE).
    exploit me_protect; eauto.
    intros (PERM & REACH). 
    (* we can only show that load and negb in the memory after
    evaluating x0 but we cannot preserve its in the final memory *)
    exploit eval_init_drop_flag_wf; eauto.
    instantiate (1 := (RustIRsem.Kseq x k)). instantiate (1 := tf).
    intros (tm2 & v & A & B & C & D & E & F & G).
    inv NOREPET.    
    exploit IHflags; eauto.
    (* prove match_env *)
    inv MENV.          
    econstructor; eauto.
    intros.   
    exploit me_protect0; eauto.
    intros (PERM1 & REACH1). split; auto.
    destruct (eq_block b tb); subst. auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    instantiate (1 := k). instantiate (1 := tf).
    intros (tm3 & STAR & MINJ3 & WFFLAG3 & MENV3 & UNC3 & RO3).
    exists tm3.
    repeat apply conj.
    (* step *)
    eapply star_step. econstructor.
    eapply star_trans. eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eauto.
    1-3: eauto.
    eauto.
    (* prove wf_flagm *)
    intros. destruct H. inv H.
    exists tb, v. repeat apply conj; auto.
    (* important: tb is not changed in tm2->tm3 *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. intros.
    (* proved by injective *)
    eapply INJ; eauto.
    intro. subst. eapply H1.
    eapply in_map_iff. exists (p,id0). split; auto.
    eapply WFFLAG3. auto.
    auto.
    (* unchanged_on *)
    eapply Mem.unchanged_on_trans.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply H.
    left. eauto. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. intros.
    eapply H. right. eauto. eauto.
    (* ro_acc *)
    eapply ValueAnalysis.ro_acc_trans; eauto.
Qed. 


(* Very difficult *)
Lemma eval_split_dropflag_match: forall drops j own1 own2 le tle lo hi tlo thi flagm m tm1 (flag: bool) p tk tf
  (MENV: match_envs j le m lo hi tle tm1 tlo thi)
  (MINJ: Mem.inject j m tm1)
  (OWN: own2 = if flag then init_place own1 p else move_place own1 p)
  (WFFLAG: forall p id,
      get_dropflag_temp flagm p = Some id ->
      exists tb v, tle ! id = Some (tb, type_bool)
              /\ le ! id = None
              /\ Mem.load Mint8unsigned tm1 tb 0 = Some (Vint v)
              (* weaker than wf_flagm *)
              /\ (In p drops -> negb (Int.eq v Int.zero) = is_init own1 p)
              (* proved by split_complete *)
              /\ (~ In p drops -> negb (Int.eq v Int.zero) = is_init own2 p))
  (FMINJ: forall (p1 p2 : place) (id1 id2 : ident),
      get_dropflag_temp flagm p1 = Some id1 ->
      get_dropflag_temp flagm p2 = Some id2 -> p1 <> p2 -> id1 <> id2)
  (NOREPET: list_norepet drops)
  (* prove by split_sound *)
  (SPLITSOUND: forall a, In a drops -> Paths.In a (PathsMap.get (local_of_place p) own1.(own_universe)) /\ is_prefix p a = true),
  exists tm2,
    (** What properties do we need for drops? *)
    star RustIRsem.step tge (RustIRsem.State tf (set_dropflag_for_splits flagm drops flag) tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)
    /\ Mem.inject j m tm2
    /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
    (* only unchange the blocks outside the drop flag, enough? *)
    /\ Mem.unchanged_on (fun b _ => forall p id tb ty, In p drops -> get_dropflag_temp flagm p = Some id -> tle ! id = Some (tb, ty) -> b <> tb) tm1 tm2
    /\ ValueAnalysis.ro_acc tm1 tm2.
Proof.
  induction drops; simpl; intros.
  - exists tm1.
    repeat apply conj.
    eapply star_refl. eauto.
    constructor; eauto.
    intros. exploit WFFLAG; eauto.
    intros (tb & v & A & B & C & D & E).
    exists tb,v. repeat apply conj; auto.
    eapply Mem.unchanged_on_refl.
    eapply ValueAnalysis.ro_acc_refl.
  - destruct (get_dropflag_temp flagm a) eqn: FLAG.
    + simpl.
      exploit WFFLAG; eauto.
      intros (tb & v & A1 & A2 & A3 & A4 & A5).
      exploit eval_set_drop_flag; eauto.
      eapply me_protect; eauto.
      eapply me_protect; eauto.
      instantiate (1 := flag). instantiate (1 := (RustIRsem.Kseq (set_dropflag_for_splits flagm drops flag) tk)).
      instantiate (1 := tf).
      intros (tm2 & B1 & B2 & B3 & B4 & B5 & B6).
      (* establish WFFLAG for I.H. *)
      assert (WFG: forall p id,
                 get_dropflag_temp flagm p = Some id ->
                 exists tb v, tle ! id = Some (tb, type_bool)
                         /\ le ! id = None
                         /\ Mem.load Mint8unsigned tm2 tb 0 = Some (Vint v)
                         (* weaker than wf_flagm *)
                         /\ (In p drops -> negb (Int.eq v Int.zero) = is_init own1 p)
                         (* proved by split_complete *)
                         /\ (~ In p drops -> negb (Int.eq v Int.zero) = is_init own2 p)).
      { intros p0 id GET.
        destruct (place_eq p0 a). subst.
        (* p0 = a *)
        * rewrite GET in FLAG. inv FLAG.
          exists tb, (if flag then Int.one else Int.zero).
          repeat apply conj; auto.
          rewrite B3. f_equal. destruct flag; simpl; auto.
          (* a cannot appear in drops *)
          intros. inv NOREPET. congruence.
          intros.
          (* use split_sound to relate p and a *)
          exploit SPLITSOUND. left; eauto. intros (INU & PRE).
          destruct flag.
          -- erewrite init_prefix_init; eauto.
          -- erewrite move_prefix_not_init; eauto.
        (* p0 <> a *)
        * exploit WFFLAG; eauto.
          intros (tb0 & v0 & C1 & C2 & C3 & C4 & C5).
          exists tb0, v0. repeat apply conj; auto.
          (* load value unchanged *)
          eapply Mem.load_unchanged_on; eauto.
          intros. simpl. eapply me_tinj; eauto.
          intros. eapply C5. intro.
          destruct H0; try congruence. }
      assert (MENV2: match_envs j le m lo hi tle tm2 tlo thi).
      { generalize MENV. intros D. inv D.
        constructor; eauto.
        intros. exploit me_protect0; eauto.
        intros (D1 & D2).
        split; auto.
        destruct (peq id i). subst.
        (* id = i *)
        - rewrite A1 in H0. inv H0.
          auto.
        (* id <> i *)
        - red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
          simpl. eapply me_tinj; eauto. eapply Mem.perm_valid_block. eauto. }
      exploit IHdrops; eauto.
      inv NOREPET. auto.
      instantiate (1 := tk). instantiate (1 := tf).
      intros (tm3 & C1 & C2 & C3 & C4 & C5).
      exists tm3.
      repeat apply conj.
      eapply star_step. econstructor.
      eapply star_trans. eapply star_step. eauto.
      eapply star_step. eapply RustIRsem.step_skip_seq.
      eauto. 1-2: eauto.
      eapply star_refl. eauto. auto.
      (* inject *)
      auto.
      (* match_envs_flagm *)
      auto.
      (* unchanged_on *)
      eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. eapply H. left. eauto. eauto. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intros. simpl. eapply H.
      right. eauto. eauto. eauto.
      (* ro_acc *)
      eapply ValueAnalysis.ro_acc_trans; eauto.
    + simpl.
      exploit IHdrops; eauto.
      (* WFFLAG *)
      intros.
      destruct (place_eq p0 a). subst.
      congruence.
      exploit WFFLAG; eauto.
      intros (tb0 & v0 & C1 & C2 & C3 & C4 & C5).
      exists tb0, v0. repeat apply conj; auto.
      intros. eapply C5. intro.
      destruct H1; try congruence. 
      inv NOREPET. auto.
      instantiate (1 := tk). instantiate (1 := tf).
      intros (tm2 & A1 & A2 & A3 & A4 & A5).
      exists tm2.
      repeat apply conj; auto.
      eapply star_step. econstructor.
      eapply star_step. eapply RustIRsem.step_skip_seq.
      eauto. 1-2: eauto.
      (* unchanged_on *)
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intros.
      eapply H. right. eauto. eauto. eauto.
Qed.      
      

Lemma not_init_cases: forall own p,
    is_init own p = false ->
    ~ Paths.In p (PathsMap.get (local_of_place p) own.(own_universe))
    \/ (Paths.In p (PathsMap.get (local_of_place p) own.(own_universe)) /\ ~ Paths.In p (PathsMap.get (local_of_place p) own.(own_init))).
Proof.
  intros.
  unfold is_init in H.
  destruct (Paths.mem p (PathsMap.get (local_of_place p) (own_universe own))) eqn: UNI.
  - apply Paths.mem_2 in UNI.
    right. split; auto. intro.
    eapply not_true_iff_false in H. apply H.
    eapply Paths.mem_1. auto.
  - left. eapply not_true_iff_false in UNI. intro.
    apply UNI.     eapply Paths.mem_1. auto.
Qed.

Lemma is_init_in_universe: forall own p,
    is_init own p = true ->
    in_universe own p = true.
Proof.
  intros. unfold is_init in H. unfold in_universe.
  eapply Paths.mem_1.
  eapply Paths.mem_2 in H.
  apply own_consistent. eapply Paths.union_2. auto.
Qed.

(** important *)
Lemma eval_dropflag_match: forall j own1 own2 le tle lo hi tlo thi flagm m tm1 (flag: bool) p tk tf stmt universe
  (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm1 tlo thi)
  (MINJ: Mem.inject j m tm1)
  (* how to ensure that update ownership of p does not change other place ownership *)
  (OWN: own2 = if flag then init_place own1 p else move_place own1 p)
  (DROPS: add_dropflag flagm ge universe p flag = OK stmt)
  (UNI: PathsMap.eq own1.(own_universe) universe),
  exists tm2,
    star RustIRsem.step tge (RustIRsem.State tf stmt tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)
    /\ Mem.inject j m tm2
    /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
    (* only unchange the blocks outside the drop flag, enough? *)
    /\ Mem.unchanged_on (fun b _ => forall p id tb ty, get_dropflag_temp flagm p = Some id -> tle ! id = Some (tb, ty) -> b <> tb) tm1 tm2
    /\ ValueAnalysis.ro_acc tm1 tm2.
Proof.
  intros. unfold add_dropflag in DROPS.
  monadInv DROPS. rename x into drops.
  exploit split_drop_place_meet_spec; eauto. intros SPEC.
  exploit eval_split_dropflag_match.
  eapply me_envs; eauto. auto.
  exact (eq_refl (if flag then init_place own1 p else move_place own1 p)).
  instantiate (1:= (map fst drops)). instantiate (1 := flagm).
  (* prove weaker wf_flagm *)
  { intros. exploit me_wf_flagm; eauto.
    intros (tb & v & A1 & A2 & A3 & A4).
    exists tb, v. repeat apply conj.
    auto. auto. auto.
    intros. auto.
    (* p0 not in drops so modify the ownership of drops does not
    change the ownership of p0 *)
    intros. rewrite A4. symmetry.
    destruct (is_init own1 p0) eqn: INIT.
    - destruct flag.
      + eapply init_owned_place_still_owned. auto.
      + eapply move_irrelavent_place_still_owned.
        auto.
        eapply not_true_is_false. intro. apply H0.
        eapply split_complete; eauto.
        unfold is_init in INIT. erewrite is_prefix_same_local; eauto.
        eapply UNI.
        eapply own_consistent. eapply Paths.union_2.
        eapply Paths.mem_2. auto.
    - apply not_init_cases in INIT as INIT'.
      destruct INIT' as [INIT1 | (INIT2 & INIT3)].
      + apply not_true_iff_false.
        intro. apply INIT1.
        eapply is_init_in_universe in H1.
        unfold in_universe in H1.
        apply Paths.mem_2 in H1.
        destruct flag; simpl in H1; auto.
      + destruct flag.
        * eapply init_irrelavent_place_still_not_owned. auto.
          eapply not_true_is_false. intro. apply H0.
          eapply split_complete; eauto.
          erewrite is_prefix_same_local; eauto.
          apply UNI. auto.
        * eapply move_place_still_not_owned.
          auto. }
  eapply me_flagm_inj. eauto.
  eapply split_norepet. eauto.
  eapply split_sound. eapply split_drop_place_meet_spec.
  erewrite split_drop_place_eq_universe. eauto.
  eapply UNI.
  instantiate (1 := tk). instantiate (1 := tf).
  (* end of eval_split_dropflag_match premise *)
  intros (tm2 & A1 & A2 & A3 & A4 & A5).
  exists tm2. repeat apply conj; auto.
  (* unchanged_on *)
  eapply Mem.unchanged_on_implies; eauto.
  intros. simpl. intros.
  eapply H. eauto. eauto.
Qed.

Lemma eval_dropflag_option_match: forall j own1 own2 le tle lo hi tlo thi flagm m tm1 p tk tf stmt universe
  (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm1 tlo thi)
  (MINJ: Mem.inject j m tm1)
  (* how to ensure that update ownership of p does not change other place ownership *)
  (OWN: own2 = move_place_option own1 p)
  (DROPS: add_dropflag_option flagm ge universe p false = OK stmt)
  (UNI: PathsMap.eq own1.(own_universe) universe),
  exists tm2,
    star RustIRsem.step tge (RustIRsem.State tf stmt tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)
    /\ Mem.inject j m tm2
    /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
    (* only unchange the blocks outside the drop flag, enough? *)
    /\ Mem.unchanged_on (fun b _ => forall p id tb ty, get_dropflag_temp flagm p = Some id -> tle ! id = Some (tb, ty) -> b <> tb) tm1 tm2
    /\ ValueAnalysis.ro_acc tm1 tm2.
Proof.
  intros. destruct p; simpl in *.
  subst. exploit eval_dropflag_match; eauto.
  inv DROPS.
  exists tm1. repeat apply conj; eauto.
  eapply star_refl. eapply Mem.unchanged_on_refl.
  eapply ValueAnalysis.ro_acc_refl.
Qed.
  
  
(* only consider move_place *)
Lemma eval_dropflag_list_match: forall al j own1 own2 le tle lo hi tlo thi flagm m tm1 universe stmt tk tf
    (MENV: match_envs_flagm j own1 le m lo hi tle flagm tm1 tlo thi)
    (MINJ: Mem.inject j m tm1)
    (* how to ensure that update ownership of p does not change other place ownership *)
    (OWN: own2 = move_place_list own1 (moved_place_list al))
    (DROPS: add_dropflag_list flagm ge universe (moved_place_list al) false = OK stmt)
    (UNI: PathsMap.eq own1.(own_universe) universe),
  exists tm2,
    star RustIRsem.step tge (RustIRsem.State tf stmt tk tle tm1) E0 (RustIRsem.State tf Sskip tk tle tm2)
    /\ Mem.inject j m tm2
    /\ match_envs_flagm j own2 le m lo hi tle flagm tm2 tlo thi
    /\ Mem.unchanged_on (fun b _ => forall p id tb ty, get_dropflag_temp flagm p = Some id -> tle ! id = Some (tb, ty) -> b <> tb) tm1 tm2
    /\ ValueAnalysis.ro_acc tm1 tm2.
Proof.
  induction al; simpl; intros.
  - subst. inv DROPS.
    exists tm1. repeat apply conj; auto.
    eapply star_refl.
    eapply Mem.unchanged_on_refl.
    eapply ValueAnalysis.ro_acc_refl.
  - destruct (moved_place a) eqn: MP.
    + simpl in DROPS. monadInv DROPS.
      exploit eval_dropflag_match; eauto.
      instantiate (1 := RustIRsem.Kseq x0 tk).
      instantiate (1 := tf).
      intros (tm2 & A1 & A2 & A3 & A4 & A5).
      exploit IHal; eauto.
      instantiate (1 := tk).
      instantiate (1 := tf).
      intros (tm3 & B1 & B2 & B3 & B4 & B5).
      exists tm3. repeat apply conj; auto.
      eapply star_step. econstructor.
      eapply star_trans. eauto.
      eapply star_step. eapply RustIRsem.step_skip_seq.
      eauto. 1-3: eauto.
      (* match_envs_flagm *)
      unfold moved_place in MP. 
      destruct a; try congruence.
      (* unchanged_on *)
      eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      (* ro_acc *)
      eapply ValueAnalysis.ro_acc_trans; eauto.
    + exploit IHal; eauto.
Qed.

(** prove a simple injp_acc_local  *)
Lemma injp_acc_local_simple:  forall f0 wm wtm Htm j1 m1 tm1 Hm1 tm2 Hm2,
    injp_acc (injpw f0 wm wtm Htm) (injpw j1 m1 tm1 Hm1) ->
    Mem.ro_unchanged tm1 tm2 ->    
    injp_max_perm_decrease tm1 tm2 ->
    Mem.unchanged_on (fun b ofs => Mem.valid_block wtm b /\ loc_out_of_reach f0 wm b ofs) tm1 tm2 ->
    injp_acc (injpw f0 wm wtm Htm) (injpw j1 m1 tm2 Hm2).
Proof.
  intros.
  exploit (ValueAnalysis.ro_acc_refl). instantiate (1 := m1). intros RO.
  inv RO.
  eapply SimplLocalsproof.injp_acc_local; eauto.
  inv H. eauto.
  eapply Mem.unchanged_on_refl.
Qed.

    
Lemma match_envs_flagm_sync_step: forall j own le m lo hi te flagm tm tm1 tlo thi id tb p
  (MENV: match_envs_flagm j own le m lo hi te flagm tm tlo thi)
  (FLAG: get_dropflag_temp flagm p = Some id)
  (TLE: te ! id = Some (tb, type_bool))
  (LE: le ! id = None)
  (UNC: Mem.unchanged_on (fun b _ => b <> tb) tm tm1)
  (LOAD: Mem.load Mint8unsigned tm1 tb 0 = Some (Vint Int.zero))
  (ORDERED: (forall p', is_prefix_strict p p' = true ->
                   is_init own p' = false))
  (PERM: Mem.range_perm tm1 tb 0 (size_chunk Mint8unsigned) Cur Freeable),
    match_envs_flagm j (move_place own p) le m lo hi te flagm tm1 tlo thi.
Proof.
  intros. econstructor.
  intros p0 id0 GET.
  destruct (place_eq p p0). subst.
  (* p = p0 *)
  * rewrite GET in FLAG. inv FLAG.
    exists tb, Int.zero.
    repeat apply conj; auto.
    erewrite move_place_not_init.
    auto.
  (* p <> p0 *)
  * exploit me_wf_flagm; eauto.
    intros (tb0 & v0 & C1 & C2 & C3 & C4).
    exists tb0, v0. repeat apply conj; auto.
    (* load value unchanged *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. eapply me_tinj. eapply me_envs; eauto.
    eauto. eauto.
    eapply me_flagm_inj; eauto.
    destruct (is_prefix_strict p p0) eqn: PRE.
    -- eapply ORDERED in PRE. rewrite C4. rewrite PRE.
       symmetry. eapply move_place_still_not_owned. auto.
    -- destruct (is_init own p0) eqn: OWNP.
       ++ rewrite C4. symmetry.
          eapply move_irrelavent_place_still_owned. auto.
          (** IMPORTANT TODO: is_prefix_strict false and neq imply is_prefix false *)
          eapply not_true_iff_false. intro.
          eapply not_true_iff_false in PRE. apply PRE.
          eapply is_prefix_strict_iff; auto.
       ++ rewrite C4. symmetry.
          eapply move_place_still_not_owned. auto.
  * eapply me_flagm_inj. eauto.
  * inv MENV. inv me_envs0.
    econstructor; eauto.
    intros. exploit me_protect0; eauto.
    intros (A & B). split; auto.
    destruct (peq id id0). subst.
    -- erewrite TLE in H0. inv H0.
       auto.
    -- red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
       simpl. eapply me_tinj0; eauto.
       eapply Mem.perm_valid_block; eauto.
Qed.

Lemma match_envs_flagm_move_no_flag_place: forall j own le m lo hi te flagm tm tlo thi p
  (MENV: match_envs_flagm j own le m lo hi te flagm tm tlo thi)
  (FLAG: get_dropflag_temp flagm p = None)
  (ORDERED: (forall p', is_prefix_strict p p' = true ->
                   is_init own p' = false)),
    match_envs_flagm j (move_place own p) le m lo hi te flagm tm tlo thi.
Proof.
  intros. econstructor.
  intros p0 id0 GET.
  destruct (place_eq p p0). subst.
  (* p = p0 *)
  * rewrite GET in FLAG. inv FLAG.
  (* p <> p0 *)
  * exploit me_wf_flagm; eauto.
    intros (tb0 & v0 & C1 & C2 & C3 & C4).
    exists tb0, v0. repeat apply conj; auto.
    destruct (is_prefix_strict p p0) eqn: PRE.
    -- eapply ORDERED in PRE. rewrite C4. rewrite PRE.
       symmetry. eapply move_place_still_not_owned. auto.
    -- destruct (is_init own p0) eqn: OWNP.
       ++ rewrite C4. symmetry.
          eapply move_irrelavent_place_still_owned. auto.
          (** IMPORTANT TODO: is_prefix_strict false and neq imply is_prefix false *)
          eapply not_true_iff_false. intro.
          eapply not_true_iff_false in PRE. apply PRE.
          eapply is_prefix_strict_iff; auto.
       ++ rewrite C4. symmetry.
          eapply move_place_still_not_owned. auto.
  * eapply me_flagm_inj. eauto.
  * inv MENV. inv me_envs0.
    econstructor; eauto.
Qed.


(* difficult part is establish simulation (match_split_drop_places)
when entering dropplace state *)
Lemma step_dropplace_simulation:
  forall S1 t S2, step_dropplace ge S1 t S2 ->
   forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropplace_init1 *)
  - inv MDPS.
    simpl in ORDERED. inv ORDERED.
    (** Two cases of skipping this drop: one is must uninit and the
    other is drop flag is false *)
    inv MSPLIT. 
    (* there is drop flag and the value of drop flag is false *)
    + exploit me_wf_flagm; eauto.
      intros (tb & v & LE & TLE & LOAD & ISOWN).
      simpl in *. rewrite NOTOWN in *.
      apply negb_false_iff in ISOWN.
      exploit Int.eq_spec. erewrite ISOWN. intro. subst.
      eexists. split.
      (* step in target *)
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      (* evaluate if then else *)
      eapply star_step. econstructor.
      econstructor. econstructor. econstructor.
      eauto. econstructor. simpl. eauto.
      eauto. simpl. eauto.
      unfold Cop.bool_val. simpl. eauto.
      rewrite Int.eq_true. simpl.
      eapply star_refl.
      1-3: eauto.
      (* match_states *)
      econstructor; eauto.
      econstructor.
    + congruence.
    (* no drop flag, must_unowned *)
    + rewrite NOTOWN in *.
      eexists. split.
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      eapply star_refl. auto. auto.
      (* match_states *)
      econstructor; eauto.
      econstructor; eauto.
      simpl in OWN.
      rewrite NOTOWN in OWN. auto.
  (* step_dropplace_init2 *)
  - inv MDPS. inv MSPLIT.
    simpl in ORDERED. inv ORDERED.
    (* there is a drop flag *)
    + exploit me_wf_flagm; eauto.
      intros (tb & v & LE & TLE & LOAD & ISOWN).
      simpl in *. rewrite OWN in *.
      eapply negb_true_iff in ISOWN.
      (* evaluate step_dropflag *)
      exploit me_protect. eapply me_envs; eauto.
      eauto. eauto. intros (PERM & REACH).
      exploit eval_set_drop_flag; eauto.
      instantiate (3 := tf). instantiate (1 := false).
      intros (tm2 & SETFLAG & MINJ1 & LOAD1 & RO1 & UNC1 & PERM1).
      (* injp *)
      assert (INJP1: injp_acc w (injpw j m tm2 MINJ1)).
      { generalize me_tinitial. intros TINIT.
        unfold wm2 in TINIT.
        destruct w. inv RO1.
        eapply injp_acc_local_simple. eauto.
        auto. auto.
        eapply Mem.unchanged_on_implies. eauto.
        intros. simpl. destruct H2.
        intro. subst.
        eapply me_trange. eapply me_envs; eauto. eauto.                
        eapply TINIT. eapply me_envs; eauto. auto. }
      eexists. split.
      (* step in target *)
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      (* evaluate if then else *)
      eapply star_step. econstructor.
      econstructor. econstructor. econstructor.
      eauto. econstructor. simpl. eauto.
      eauto. simpl. eauto.
      unfold Cop.bool_val. simpl. eauto.
      rewrite Int.eq_false. simpl.
      (* evaluate step_dropflag *)
      eapply star_step. econstructor.
      eapply star_step. eauto.
      eapply star_step. eapply RustIRsem.step_skip_seq.            
      eapply star_refl. 
      1-7: eauto.
      intro. subst. rewrite Int.eq_true in ISOWN. congruence.
      (* match_states *)
      econstructor. eauto.
      (* match_cont *)
      eapply match_cont_bound_unchanged. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intro. subst.
      eapply me_trange. eapply me_envs; eauto. eauto. auto.
      (** TODO: match_drop_place_state and gen_drop_place_state *)
      admit.
      auto. eauto. eauto.
      (* match_envs_flagm *)
      eapply match_envs_flagm_sync_step; eauto.
      auto.
      eauto.
      inv IM. econstructor.
      auto.
      auto. eapply Mem.sup_include_trans. eauto.
      eapply Mem.unchanged_on_support. eauto.      
    (* must_owned *)
    + inv ORDERED.
      rewrite OWN in *.
      eexists. split.
      econstructor. eapply RustIRsem.step_skip_seq.
      eapply star_step. econstructor.
      eapply star_refl. 1-2: eauto.
      (* match_states *)
      econstructor; eauto.
      (** TODO: match_drop_place_state and gen_drop_place_state *)
      admit.
      (** move out a place which does not have drop flag has no
      effect on match_envs_flagm *)
      eapply match_envs_flagm_move_no_flag_place; eauto.
      (* sound_own *)
      simpl in OWN0.
      rewrite OWN in OWN0. auto.
    + congruence.
  (* step_dropplace_box *)
  - inv MDPS. simpl.
    (* hypotheses of step_drop_box *)
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    exploit deref_loc_inject; eauto.
    intros (tv & TDEREF & VINJ2). inv VINJ2.
    exploit extcall_free_injp; eauto.
    instantiate (1 := Hm). instantiate (1 := tge).
    intros (tm1 & Hm1 & TFREE & MINJ1).
    eexists. split.
    (* step *)
    econstructor. econstructor.
    (* step_drop_box *)
    eapply star_step. eapply RustIRsem.step_drop_box; eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_refl.
    1-3: eauto.
    (* match_states *)
    eapply match_dropplace with (hi:=hi) (thi:=thi).
    eauto. eauto.
    (* match_cont_injp_acc *)
    eapply match_cont_injp_acc. eapply MCONT.
    eauto.
    eapply Mem.sup_include_trans. eapply me_incr; eapply me_envs; eauto. auto.
    eapply Mem.sup_include_trans. eapply me_tincr; eapply me_envs; eauto. auto.
    (* match_drop_place_state *)
    econstructor.
    eauto.
    auto.
    etransitivity; eauto.
    (* match_envs_flagm *)
    eapply match_envs_flagm_injp_acc; eauto.
    auto. eauto.
    (* get_IM *)
    inv IM. econstructor.
    auto.
    (* sup include *)
    inv MINJ1. inv H10. inv H11.
    eapply Mem.sup_include_trans; eauto.
    inv MINJ1. inv H10. inv H11.
    eapply Mem.sup_include_trans; eauto.
  (* step_dropplace_struct *)
  - inv MDPS.
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    eexists. split.
    (* step_drop_struct *)
    econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_drop_struct; eauto.
    erewrite comp_env_preserved; eauto.
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    econstructor; eauto.
    econstructor; eauto.
    (* match_drop_place_state *)
    econstructor.
  (* step_dropplace_enum *)
  - inv MDPS.
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    (* load tag inject *)
    inv VINJ1.
    exploit Mem.load_inject; eauto.
    intros (v2 & TLOAD & VINJ2). inv VINJ2.
    eexists. split.
    (* step_drop_struct *)
    econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_drop_enum; eauto.
    erewrite comp_env_preserved; eauto.
    (* use address_inject due with overflow *)
    assert (PERM: Mem.perm m b (Ptrofs.unsigned ofs) Cur Nonempty).
    { exploit Mem.load_valid_access. eapply TAG.
      intros (A & B). eapply Mem.perm_implies.
      eapply A. simpl. lia. econstructor. }
    simpl. exploit Mem.address_inject; eauto.
    intros A. rewrite A. auto.    
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    rewrite type_to_drop_member_state_eq.
    econstructor; eauto.
    (* match_cont *)
    econstructor; eauto.
    (* match_drop_place_state *)
    econstructor.
  (* step_dropplace_next *)
  - inv MDPS. simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_refl. 1-2: eauto.
    econstructor; eauto.
    constructor.
  (* step_dropplace_return *)
  - inv MDPS. inv MSPLIT.
    eexists. split.
    (* step *)
    econstructor. eapply RustIRsem.step_skip_seq.
    eapply star_refl.
    auto.
    econstructor; eauto.
    econstructor.
Admitted.


Lemma step_dropstate_simulation:
  forall S1 t S2, step_drop ge S1 t S2 ->
   forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropstate_init *)
  - eexists. split.
    econstructor. econstructor.
    eapply RustIRsem.step_dropstate_init.
    eapply star_refl.
    auto.
    erewrite type_to_drop_member_state_eq; eauto.
    econstructor; eauto.
  (* step_dropstate_struct *)
  - inv VINJ.
    exploit deref_loc_rec_inject; eauto.
    intros (tv & DEREF1 & VINJ1). inv VINJ1.
    erewrite <- comp_env_preserved in *; eauto.
    eexists. split.
    econstructor. econstructor. econstructor; eauto.
    replace (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr delta)) (Ptrofs.repr fofs)) with (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr fofs)) (Ptrofs.repr delta)).
    eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    eapply star_refl.
    auto.
    (* match_states *)
    econstructor. econstructor.
    econstructor; eauto.
    eauto. eauto.
    econstructor; eauto.
    auto. auto.
  (* step_dropstate_enum *)
  - admit.
  (* step_dropstate_box *)
  - inv VINJ.
    exploit (drop_box_rec_injp_acc m m' tm); eauto.
    instantiate (1:= Hm). instantiate (1 := tge).
    intros (tj & tm2 & tHm & TDROP & INJP1).
    erewrite <- comp_env_preserved in *; eauto.
    eexists. split.
    (* step *)
    econstructor. econstructor. econstructor; eauto.
    replace (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta)) (Ptrofs.repr fofs)) with (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr fofs)) (Ptrofs.repr delta)).
    eauto.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    apply Ptrofs.add_commut.
    eapply star_refl.
    auto.
    (* match_states *)
    generalize INJP1. intros INJP2.
    inv INJP2.
    assert (BOUND1: Mem.sup_include lo (Mem.support m')).
    eapply Mem.sup_include_trans. eauto.
    eapply Mem.unchanged_on_support; eauto.
    assert (TBOUND1: Mem.sup_include tlo (Mem.support tm2)).
    eapply Mem.sup_include_trans. eauto.
    eapply Mem.unchanged_on_support; eauto.
    (* match_cont_injp_acc *)
    exploit match_cont_injp_acc; eauto.
    intros MCONT1.        
    econstructor; eauto.
    etransitivity. eauto. eauto.
  (* step_dropstate_return1 *)
  - inv MCONT.
    eexists. split.
    econstructor. econstructor. econstructor.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_refl.
    1-2: eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropstate_return2 *)
  - inv MCONT.
    eexists. split.
    econstructor. econstructor. econstructor.
    eapply star_refl.
    eauto.
    (* match_states *)
    econstructor; eauto.
Admitted.

(** To move  *)
Lemma sound_own_after_drop: forall own drops init uninit universe p
    (SOUND: sound_own own init uninit universe)
    (SPEC: split_drop_place_spec (PathsMap.get (local_of_place p) (own_universe own)) p drops)
    (ORDER: move_ordered_split_places_spec own (map fst drops)),
    sound_own (move_split_places own drops) (remove_place p init) (add_place universe p uninit) universe.
Proof.
  intros.
  (* move_ordered_split_places_spec *)
  (** sound_own: this proof is important. Make it a lemma!  *)
  assert (SOWN: sound_own (move_split_places own drops) (remove_place p init) (add_place universe p uninit) universe). 
  { exploit (move_split_places_uncheck_sound drops own); eauto.
    intros (INITGE & UNINITGE & UNIEQ1).      
    constructor.
    + (* step1 *)
      assert (STEP1: PathsMap.ge (move_split_places_uncheck own.(own_init) drops) (own_init (move_split_places own drops))) by auto.
      eapply PathsMap.ge_trans. 2: eapply STEP1.
      (* step2: one-time remove and recursively remove *)
      assert (STEP2: PathsMap.ge (remove_paths_in own.(own_init) (local_of_place p) (collect_children_in own.(own_init)  (map fst drops))) (move_split_places_uncheck (own_init own) drops)).
      { red. intros id.
        unfold remove_paths_in.
        (* reduce the steps of PathsMap.set in move_split_places_uncheck *)
        assert (A: PathsMap.ge (PathsMap.set (local_of_place p) (filter_split_places_uncheck (PathsMap.get (local_of_place p) (own_init own)) drops) (own_init own)) (move_split_places_uncheck (own_init own) drops)).
        { (* require that all places in drops are children of p *)
          eapply filter_move_split_places_ge.
          intros. symmetry. eapply is_prefix_same_local.
          eapply split_sound; eauto. eapply in_map_iff. exists (p0,b). auto. }
        eapply LPaths.ge_trans.
        2 : eapply A.
        assert (CORE: LPaths.ge (Paths.diff (PathsMap.get (local_of_place p) (own_init own))
                                   (collect_children_in (own_init own)  (map fst drops)))
                        (filter_split_places_uncheck (PathsMap.get (local_of_place p) (own_init own)) drops)).
        { (* any place in filter_split_places_uncheck is not a child of any place in drops (can be proved by induction), so this place is not in the collect_children_in. *)
          red. red. intros a IN.
          eapply Paths.diff_3.
          eapply filter_split_places_uncheck_unchange; eauto.
          (* prove by contradiction *)
          intros IN1.
          exploit collect_children_in_exists; eauto.
          intros (p' & IN' & PRE).                      
          exploit (filter_split_places_subset_collect_children drops a p'); eauto.
          intros. congruence. }
        (* unable to use setoid_rewrite *)
        red. do 2 rewrite PathsMap.gsspec.
        destruct (peq id (local_of_place p)); subst. auto.
        apply LPaths.ge_refl. apply LPaths.eq_refl.
      }        
      eapply PathsMap.ge_trans. 2: eapply STEP2.
      (* step3 *)
      { red. intros id. unfold remove_paths_in, remove_place.
        assert (CORE: LPaths.ge (Paths.filter (fun elt : Paths.elt => negb (is_prefix p elt))
             (PathsMap.get (local_of_place p) init)) (Paths.diff (PathsMap.get (local_of_place p) (own_init own)) (collect_children_in (own_init own) (map fst drops))) ).
        { red. red. intros a.
          intros IN.
          eapply Paths.diff_1 in IN as IN1.
          eapply Paths.diff_2 in IN as IN2.
          eapply Paths.filter_3. red. solve_proper.
          eapply sound_own_init; eauto.
          (* key of proof: [a] is not a children of p *)
          apply Is_true_eq_true. apply negb_prop_intro.
          red. intros ISPRE. eapply IN2. clear IN2.
          eapply Is_true_eq_true in ISPRE.
          (** TODO: show that a is in the universe and use
          split_drop_complete to show a ∈ drops *)
          eapply Paths.union_2 in IN1.
          eapply own_consistent in IN1; eauto.
          exploit split_complete; eauto. intros IN2.
          eapply collect_children_in_implies. eauto.
          apply is_prefix_refl.
          eapply Paths.diff_1. erewrite <- is_prefix_same_local; eauto. }
        red. do 2 rewrite PathsMap.gsspec.
        destruct (peq id (local_of_place p)); subst. auto.
        eapply sound_own_init; eauto. }
      (* uninit part: maybe easy? because there are less places to be
      added in own_env side *)
      + admit.
      (* universe equal *)
      + eapply PathsMap.eq_trans; eauto. eapply sound_own_universe; eauto.
Admitted.


Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 -> forall S1' (MS: match_states S1 S1'),
    exists S2', plus RustIRsem.step tge S1' t S2' /\ match_states S2 S2'.
Proof. 
  induction 1; intros; inv MS.
  (* step_assign *)
  - inv MSTMT. simpl in TR. inv IM.
    rewrite <- H4 in TR. rewrite <- H5 in TR.
    rename H4 into GETINIT. rename H5 into GETUNINIT.
    monadInv TR.
    set (own2:=(move_place_option own1 (moved_place e))).
    set (own3:=(own_transfer_assign own2 p)).
    (* evaluate x *)
    exploit eval_dropflag_option_match; eauto.
    eapply PathsMap.eq_sym. eapply sound_own_universe. eauto.
    instantiate (1 := (RustIRsem.Kseq (Ssequence x0 (Sassign p e)) tk)).
    instantiate (1 := tf).
    intros (tm2 & STEP1 & MINJ1 & MENV1 & UNC1 & RO1).
    (* evaluate x0 *)    
    exploit eval_dropflag_match; eauto.
    eapply PathsMap.eq_sym. eapply PathsMap.eq_trans.
    eapply sound_own_universe. eauto.
    eapply move_place_option_eq_universe.
    instantiate (1 := (RustIRsem.Kseq (Sassign p e) tk)).
    instantiate (1 := tf).
    intros (tm3 & STEP2 & MINJ2 & MENV2 & UNC2 & RO2).
    (* evaluate assign *)
    exploit eval_expr_inject; eauto.
    intros (tv & EXPR & VINJ).
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    exploit sem_cast_inject; eauto.
    intros (tv1 & CAST1 & VINJ2).
    exploit assign_loc_injp_acc; eauto.
    instantiate (1 := MINJ2).
    intros (j2 & tm4 & MINJ3 & ASSIGN & INJP2).
    (* match_envs_flagm *)
    assert (SUP1: Mem.sup_include thi (Mem.support tm3)).
    { eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. eauto.
      eapply Mem.unchanged_on_support. eauto. }    
    exploit match_envs_flagm_injp_acc. eapply MENV2. eauto.
    auto. auto.
    intros MENV3.
    (* match_cont *)
    assert (UNC13: Mem.unchanged_on (fun b _ => sup_In b tlo) tm tm3).
    { eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intros. intro.
      subst. eapply me_trange. eapply me_envs; eauto.
      eauto. auto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intros. intro.
      subst. eapply me_trange. eapply me_envs; eauto.
      eauto. auto. }    
    exploit match_cont_bound_unchanged;eauto.
    intros MCONT1.
    exploit match_cont_injp_acc. eauto. eauto.
    eapply Mem.sup_include_trans.
    eapply me_incr. eapply me_envs. eauto. auto.
    eapply Mem.sup_include_trans.
    eapply me_tincr. eapply me_envs. eauto. auto.
    intros MCONT2.
    (* injp_acc *)
    assert (RO3: ValueAnalysis.ro_acc tm tm3).
    { eapply ValueAnalysis.ro_acc_trans. eauto.
      auto. }
    assert (INJP1: injp_acc w (injpw j m1 tm3 MINJ2)).
    { generalize me_tinitial. intros TINIT.
      unfold wm2 in TINIT.
      destruct w. inv RO3.
      eapply injp_acc_local_simple. eauto.
      auto. auto.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. destruct H6.
      eapply TINIT. eapply me_envs; eauto. auto. }
    (* step *)
    eexists. split.
    econstructor. econstructor.
    eapply star_trans. eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_step. econstructor.
    eapply star_trans. eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_step. econstructor; eauto.
    eapply star_refl. 1-7: eauto.
    (* match_states *)
    assert (SUP2: Mem.sup_include hi (Mem.support m2)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eapply Mem.sup_include_refl.
      eauto. }
    assert (SUP3: Mem.sup_include thi (Mem.support tm4)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eapply Mem.sup_include_refl.
      eauto. }
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT. eauto.
    instantiate (1 := (init_place (move_place_option own1 (moved_place e)) p)).
    exploit move_option_place_sound; eauto.
    instantiate (1 := (moved_place e)). intros SOUND1.
    exploit init_place_sound; eauto.
    intros (mayinit3 & mayuninit3 & A & B).
    (* end of construct *)    
    econstructor; eauto. econstructor.
    etransitivity. eauto. eauto.
  (* step_assign_variant *)
  - admit.
  (* step_box *)
  - admit.
  (* step_to_dropplace *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    unfold elaborate_drop_for in TR.
    (** sound_own property *)
    assert (UNIEQ: PathsMap.eq (own_universe own) universe0) by admit.
    erewrite split_drop_place_eq_universe in TR.
    unfold ce in TR. erewrite SPLIT in TR.
    2: { symmetry. eapply UNIEQ. }
    inv TR.
    (* end of getting ts *)
    (* how to prevent stuttering? *)
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. eauto.
    (* match_states *)
    exploit split_drop_place_meet_spec; eauto.
    intros SPLIT_SPEC.
    assert (ORDER_SPEC: move_ordered_split_places_spec own (map fst drops)).
    { eapply ordered_and_complete_split_places_meet_spec.
      (* Complete *)
      intros. left.
      assert (PRE: is_prefix p a = true).
      { eapply is_prefix_trans. eapply split_sound; eauto. auto. }
      eapply split_complete. eauto.
      erewrite is_prefix_same_local. eauto.
      auto. auto.
      eapply split_ordered; eauto. }
    (* construct sound_own and get_IM *)
    exploit analyze_succ. 1-3: eauto. simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT. eauto.
    instantiate (1 := (move_split_places own drops)).    
    (** sound_own: this proof is important. Make it a lemma!  *)
    eapply sound_own_after_drop; eauto.    
    intros (mayinit3 & mayuninit3 & A & B).
    (* match_states *)
    econstructor; eauto.
    econstructor.
    (* match_split_drop_places *)
    eapply elaborate_drop_match_drop_places.
    (** IMPORTANT TODO: wf_split_drop_places *)
    erewrite <- split_drop_place_eq_universe in SPLIT.
    2: { eapply sound_own_universe. eauto. }
    exploit split_drop_place_meet_spec; eauto.
    intros SPEC.
    eapply ordered_split_drop_places_wf.
    eapply split_ordered. eauto.
    (* use sound_own properties, prove p0 is in the universe *)
    intros. eapply must_init_sound; eauto.
    exploit split_sound; eauto.
    eapply (in_map fst)in H. eauto.
    intros (C & D).
    erewrite <- is_prefix_same_local; eauto.
    intros. eapply must_not_init_sound; eauto.
    eapply sound_own_universe; eauto.
    intros. eapply SFLAGM; eauto.
    eapply in_map_iff. exists (p0, full). auto. 
  (* step_in_dropplace *)
  - eapply step_dropplace_simulation. eauto.
    econstructor; eauto.
  (* step_dropstate *)
  - eapply step_dropstate_simulation. eauto.
    econstructor; eauto.
  (* step_storagelive *)
  - admit.
  (* step_storagedead *)
  - admit.
  (* step_call *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H6 in TR. rewrite <- H7 in TR.
    rename H6 into GETINIT. rename H7 into GETUNINIT.
    monadInv TR.
    (* evaluate drop flag list of arguments *)
    exploit eval_dropflag_list_match; eauto.
    eapply PathsMap.eq_sym. eapply sound_own_universe; eauto.
    instantiate (2 := tf).
    intros (tm1 & A1 & A2 & A3 & A4 & A5).
    exploit eval_expr_inject; eauto.
    intros (tv & TEXPR & VINJ1).
    exploit eval_exprlist_inject; eauto.
    intros (tvl & TARGS & VINJ2).
    assert (GE1: Genv.match_stbls j se tse).
    { replace j with (mi injp (injpw j m tm Hm)) by auto.
      eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. }
    exploit find_funct_match; eauto.
    intros (tf1 & FINDFUN1 & TRANSF).
    (* injp_acc *)
    assert (INJP: injp_acc w (injpw j m tm1 A2)).
    { generalize me_tinitial. intros SUP.
      unfold wm2 in SUP.
      destruct w. 
      inv A5.
      eapply injp_acc_local_simple; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. destruct H8. intros.
      intro. subst.
      (* tb is not valid in m2 *)
      eapply me_trange. eapply me_envs; eauto.
      eauto. eapply SUP. eapply me_envs; eauto.
      eapply H8. }
      
    (* match_cont injp_acc *)
    (* exploit match_cont_injp_acc. eauto. *)
    (* eauto. *)
    (* eapply Mem.sup_include_trans. *)
    (* eapply me_incr. eapply me_envs. eauto. auto. *)
    (* eapply Mem.sup_include_trans. *)
    (* eapply me_tincr. eapply me_envs. eauto. auto. *)
    (* intros MCONT1.     *)
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_step. econstructor.
    eapply star_trans. eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eapply star_step.
    (* eval function call *)
    econstructor; eauto.
    erewrite type_of_fundef_preserved; eauto.
    (** TODO: add good_function in RustIRown *)
    admit.
    eapply star_refl.
    1-5: eauto.
    (* construct sound_own and get_IM *)
    exploit analyze_succ. 1-3: eauto.
    simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT. eauto.
    instantiate (1 := (init_place (move_place_list own1 (moved_place_list al)) p)).
    exploit move_place_list_sound; eauto.
    intros SOUND1.
    exploit init_place_sound; eauto.        
    intros (mayinit3 & mayuninit3 & GIM & SO).     
    (* match_states *)
    econstructor; eauto.
    (* match_stacks *)
    econstructor; eauto.
    (* match_cont *)
    eapply match_cont_bound_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. intros. intro. subst.
    eapply me_trange. eapply me_envs; eauto. eauto. auto.
    (* match_envs_flagm *)
    eapply match_envs_flagm_incr_bounds. eauto.
    auto.
    eapply Mem.sup_include_trans. eauto.
    eapply Mem.unchanged_on_support. eauto.
  (** DIFFICULT: step_internal_function *)
  - simpl in  FIND.
    assert (GE1: Genv.match_stbls j se tse).
    { replace j with (mi injp (injpw j m tm Hm)) by auto.
      eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. }    
    exploit find_funct_match; eauto.
    intros (tf & TFIND & TRFUN).
    (* destruct tf *)
    unfold transf_fundef in TRFUN.
    monadInv TRFUN. unfold transf_function in EQ.
    monadInv EQ. destruct x2 as [[mayinitMap mayuninitMap] universe].
    monadInv EQ2.
    (* use transl_on_cfg_meet_spec to get match_stmt in fuction entry *)
    exploit (@transl_on_cfg_meet_spec AN); eauto.
    intros (nret & MSTMT & IEND).
    (* own_env in function entry is sound *)
    exploit sound_function_entry. simpl. eauto.
    eauto. eauto. intros (einit & euninit & GIM & OWNENTRY).
    (** TODO: construct function entry in target program *)
    inv ENTRY.
    (* alloc the same variables and parameters in source and target *)
    exploit alloc_variables_match; eauto.
    eapply match_empty_envs.
    eapply Mem.sup_include_refl.
    instantiate (1 := tm). eapply Mem.sup_include_refl.
    unfold wm2. destruct w.
    inv MINJ. eapply Mem.unchanged_on_support.  eauto.    
    instantiate (1 := Hm).
    intros (j1 & tm1 & Hm1 & te1 & ALLOC1 & MENV1 & INJP1).
    (* alloc drop flag in the target program *)
    rename x2 into drop_flags.
    set (flags := combine (map snd drop_flags) (repeat type_bool (Datatypes.length drop_flags))) in *.
    exploit alloc_drop_flags_match; eauto.
    instantiate (1 := drop_flags).
    (* easy: added a norepet check in target program to ensure that
    source env does not contains identities of drop flags *)
    admit.
    instantiate (1 := Hm1).
    intros (te2 & tm2 & Hm2 & ALLOC2 & INJP2 & WFFLAG & MENV2).
    (* bind_parameters in target program *)
    exploit bind_parameters_injp_acc; eauto.
    eapply val_inject_list_incr.
    inv INJP1. eauto. eauto.
    instantiate (1 := Hm2).
    intros (tm3 & Hm3 & TBIND & INJP3).
    (* bind parameters does not change match_env *)
    exploit match_envs_injp_acc; eauto.
    intros MENV3.        
    (* require that init_own is equal to entry analysis result *)
    rename x4 into init_stmts. rename x3 into body.
    (* construct the state after the initialization of drop flags *)
    unfold init_drop_flags_bot in *. generalize GIM as GIM1. intros. inv GIM.
    rewrite <- H3 in EQ3. rewrite <- H4 in EQ3. clear H3 H4.
    exploit eval_init_drop_flags_wf; eauto.
    eapply me_tinj; eauto.
    (* norepet of drop_flags *)
    admit.
    (** prove p is in universe: properties of generate_dropflag *)
    intros p IN. admit.
    instantiate (1 := (RustIRsem.Kseq body tk)).
    intros (tm4 & INITFLAGS & MINJ4 & WFFLAGM & MENV4 & UNC1 & RO1).
    (** establish injp_acc (j,m,tm) ~-> (j2, m', tm4)  *)
    assert (INJP13: injp_acc (injpw j m tm Hm) (injpw j1 m' tm3 Hm3)).
    { etransitivity; eauto.
      etransitivity. eauto.
      etransitivity. eauto.
      reflexivity. }
    assert (INJP14: injp_acc (injpw j m tm Hm) (injpw j1 m' tm4 MINJ4)).
    { inv RO1.
      eapply injp_acc_local_simple; eauto.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. destruct H5.
      intro. subst.
      eapply me_trange; eauto. }
    eexists. split.
    (* step *)
    econstructor. econstructor; eauto.
    (* function entry *)
    econstructor; simpl.
    (* list_norepet *)
    admit.
    (* alloc_variables *)
    simpl. rewrite app_assoc.
    eapply alloc_variables_app; eauto.
    (* bind_parameters *)
    eauto.
    (** TODO: evaluate init statement *)
    simpl. eapply star_step.
    econstructor.
    eapply star_right. 
    eauto.
    eapply RustIRsem.step_skip_seq.
    1-3: eauto.
    (* match_states *)
    assert (INCR1: Mem.sup_include (Mem.support m1) (Mem.support m')).
    { inv INJP3. eapply Mem.unchanged_on_support; eauto. }    
    assert (INCR2: Mem.sup_include (Mem.support tm2) (Mem.support tm4)).
    { inv INJP3. inv RO1.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support; eauto.
      eapply Mem.unchanged_on_support; eauto. }
    econstructor; eauto.
    (* match_cont *)
    instantiate (1 := Mem.support tm).
    instantiate (1 := Mem.support m).
    inv MCONT. econstructor; eauto.
    econstructor. econstructor; eauto.
    eapply match_cont_injp_acc. eauto.
    eauto.
    (** TODO: match_cont implies sup_include lo (Mem.support m) *)
    admit. admit.
    (* match_envs_flagm in match_cont *)
    eapply match_envs_flagm_injp_acc; eauto.
    auto.
    etransitivity; eauto.
    (* this function match_envs_flagm *)    
    eapply match_envs_flagm_incr_bounds with (hi1 := Mem.support m1) (thi1:= Mem.support tm2); eauto.
    econstructor; auto.
    (* prove wf_flagm *)
    intros. eapply WFFLAGM.
    (* property of generate_place_map *)
    admit.
    (** injective of get_dropflag_temp of the generated flagm *)
    admit.
    (** sound_flagm *)
    eapply generate_flag_map_sound; eauto.
  (* step_external_function *)
  - admit.
    
  Admitted.

Lemma initial_states_simulation:
  forall q1 q2 S1, match_query (cc_rs injp) w q1 q2 -> initial_state ge q1 S1 ->
  exists S2, RustIRsem.initial_state tge q2 S2 /\ match_states S1 S2.
Proof.
  intros ? ? ? Hq HS.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq.
  subst. 
  inversion HS. clear HS. subst vf sg vargs m.
  exploit find_funct_match;eauto. eapply match_stbls_proj.
  eauto. eauto.
  intros (tf & FIND & TRF).
  (* inversion TRF to get tf *)
  simpl in TRF. monadInv TRF.
  eexists. split.
  - replace (prog_comp_env prog) with (genv_cenv ge); auto.
    erewrite <- comp_env_preserved.
    econstructor. eauto.
    (* type_of_function *)
    { unfold type_of_function.
      unfold transf_function in EQ.
      monadInv EQ. destruct x2 as [[i1 i2] i3].
      monadInv EQ2. simpl.
      unfold type_of_function in H4. inv H4.
      f_equal. }
    (* fn_drop_glue *)
    { unfold type_of_function.
      unfold transf_function in EQ.
      monadInv EQ. destruct x2 as [[i1 i2] i3].
      monadInv EQ2. simpl. auto. }
    eapply val_casted_inject_list;eauto.
    (* sup_include *)
    simpl. inv Hm. inv GE. simpl in *. auto.
  - inv Hm; cbn in *.
    econstructor.
    2: { instantiate (1:= Hm0). rewrite <- H. reflexivity. }
    all: eauto.
    rewrite <- H in *. eauto.
    rewrite <- H in *. eauto.
    econstructor.
Qed.                
    
Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, RustIRsem.final_state R r2 /\ match_reply (cc_rs injp) w r1 r2.
Proof.
  intros. inv H0. inv H.
  inv MCONT.
  eexists. split. econstructor; split; eauto.
  simpl.
  econstructor. split.
  eauto. econstructor. eauto.
  constructor; eauto.
Qed.


Lemma external_states_simulation:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, RustIRsem.at_external tge R q2 /\ match_query (cc_rs injp) wx q1 q2 /\ match_stbls injp wx se tse /\
  forall r1 r2 S', match_reply (cc_rs injp) wx r1 r2 -> after_external S r1 S' ->
              exists R', RustIRsem.after_external R r2 R' /\ match_states S' R'.
Proof.
  intros S R q1 HSR Hq1.
  destruct Hq1; inv HSR.
  exploit (match_stbls_acc injp). eauto. eauto. intros GE1.
  (* target find external function *)  
  simpl in H. exploit find_funct_match; eauto.
  inv GE1. simpl in *. eauto.
  intros (tf & TFINDF & TRFUN).
  simpl in TRFUN. inv TRFUN. 
  (* vf <> Vundef *)
  assert (Hvf: vf <> Vundef) by (destruct vf; try discriminate).
  eexists (injpw j m tm Hm), _. intuition idtac.
  - econstructor; eauto. 
  - erewrite <- comp_env_preserved.
    econstructor; eauto. constructor. 
  - inv H1. destruct H0 as (wx' & ACC & REP). inv ACC. inv REP. inv H12. eexists. split.
    + econstructor; eauto.
    + econstructor. instantiate (1 := f').
      eauto. etransitivity; eauto.
      instantiate (1 := Hm5).
      econstructor; eauto.
      exploit match_stacks_injp_acc; eauto.
      instantiate (1 := Hm5). instantiate (1 := Hm1).
      econstructor; eauto.
      intros MSTK1.
      exploit match_stacks_incr_bounds. eauto.
      eapply Mem.unchanged_on_support; eauto.
      eapply Mem.unchanged_on_support; eauto.
      auto.
Qed.

End PRESERVATION.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation (cc_rs injp) (cc_rs injp) (semantics prog) (RustIRsem.semantics tprog).
Proof.
  fsim eapply forward_simulation_plus; simpl in *. 
  - inv MATCH. simpl. auto. 
  - intros. inv H. simpl.
    assert (GE1: Genv.match_stbls (mi injp w) se1 se2).
    { eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. reflexivity. }    
    eapply is_internal_match; eauto.
    intros. destruct f; simpl in H.
    monadInv H. auto. inv H. auto.
  (* initial state *)
  - eapply initial_states_simulation;eauto.
  (* final state *)
  - eapply final_states_simulation; eauto.
  (* external state *)
  - eapply external_states_simulation; eauto.
  (* step *)
  - eapply step_simulation;eauto.
Qed.
