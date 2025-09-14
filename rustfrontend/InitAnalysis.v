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
              | Sreturn p =>
                  (* let p' := moved_place e in *)
                  (* if flag then *)
                  (*   IM.State (remove_option p' before) *)
                  (* else *)
                  (*   IM.State (add_option S p' before) *)
                  (** Do we need to move out the return place?  *)
                  IM.State before
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

Require Import BinPosDef.
Require Import String.
Require Import Ascii.

(* 数字转字符（0-9） *)
Definition digit_to_char (n: Z) : ascii :=
  ascii_of_nat (Z.to_nat (n + 10) mod 10 + 48). (* 安全处理负数 *)

(* 使用 Program Fixpoint 确保终止性 *)
Program Fixpoint z_to_digits_aux (n: Z) (acc: list ascii) 
  {measure (Z.to_nat (Z.abs n))} : list ascii :=
  match n with
  | Z0 => acc
  | _ =>
      let (q, r) := Z.quotrem n 10 in
      z_to_digits_aux q (digit_to_char r :: acc)
  end.
Next Obligation.
Admitted.

(* 处理符号和零 *)
Definition z_to_digits (z: Z) : list ascii :=
  match z with
  | Z0 => ["0"%char]
  | Zpos p => z_to_digits_aux (Zpos p) []
  | Zneg p => "-"%char :: z_to_digits_aux (Zpos p) []
  end.

(* 最终转换函数 *)
Definition z_to_string (z: positive) : string :=
  string_of_list_ascii (z_to_digits (Z.pos z)).

(* 测试 *)
Compute z_to_string 42.     (* "42" *)
Compute z_to_string 1.      (* "0" *)

(* Fixpoint positive_to_bin_string (p : positive) : string :=
  match p with
  | xH => "1"%string (* 1 *)
  | xO p' => append (positive_to_bin_string p') "0"%string (* 2*p → 加 "0" *)
  | xI p' => append (positive_to_bin_string p') "1"%string (* 2*p +1 → 加 "1" *)
  end. *)

(* 辅助函数：将place转为字符串 *)
Fixpoint show_place (p: place) : string :=
  match p with
  | Plocal id ty => "Plocal(" ++  z_to_string id ++ ")"
  | Pfield p' fid ty => "Pfield(" ++ show_place p' ++ ")"
  | Pderef p' ty => "Pderef(" ++ show_place p' ++ ")"
  | Pdowncast p' n ty => "Pdowncast(" ++ show_place p' ++ ")"
  | Pparenthesize id _ _ => "Pparen(" ++ z_to_string id ++ ")"
  | Ppair p1 p2 => "Ppair(" ++ show_place p1 ++ ", " ++ show_place p2 ++ ")"
  | ParrayIndex p' e ty => "ParrayIndex(" ++ show_place p' ++ ")"
  end.

(* 辅助函数：将Paths.t转为字符串 *)
Definition show_paths (ps: Paths.t) : string :=
  let l := Paths.elements ps in
  "{" ++ String.concat ", " (List.map show_place l) ++ "}".

(* 辅助函数：将PathsMap.t转为字符串 *)
Definition show_whole (whole: PathsMap.t) : string :=
  let l := PTree.elements whole in
  String.concat "; " (List.map 
  (fun '(id, ps) => 
    z_to_string id ++ ":" ++ show_paths ps)%string l).


(* 辅助函数：将PMap.t PathsMap.t转为字符串 *)
Definition show_map (m: PMap.t PathsMap.t) : string :=
  let l := PMap.elements m in
  String.concat " \n " (List.map (fun '(pc, pm) => 
    (String.append "pc " (String.append (z_to_string pc) (String.append ": " (show_whole pm))))
  ) l).

(* 辅助函数：将 DS.L.t 转为字符串 *)
Definition show_L (l: DS.L.t) : string :=
  match l with
  | IM.State pm => show_whole pm  (* 假设 IM.State 包含 PathsMap.t *)
  | _ => "<unknown L.t>"          (* 其他情况的默认处理 *)
  end.

(* 辅助函数：将 PMap.t DS.L.t 转为字符串 *)
Definition show_L_map (m: PMap.t DS.L.t) : string :=
  let l := PMap.elements m in
  String.concat "  \n  " (List.map (fun '(pc, pm) => 
    (String.append "pc " (String.append (z_to_string pc) (String.append ": " (show_L pm))))
  ) l).

(* The analyze returns the MaybeInit and MaybeUninit sets along with
the universe set *)
Definition analyze (ce: composite_env) (f: function) (cfg: rustcfg) (entry: node) : Errors.res (PMap.t IM.t * PMap.t IM.t * PathsMap.t) :=
  (* collect the whole set in order to simplify the gen and kill operation *)
  do whole <- collect_func ce f;
  (* It is necessary because we have to guarantee that the map is not
  PathMap.bot in the 'transfer' function *)
  let empty_pathmap := PTree.map (fun _ elt => Paths.empty) whole in
  (* uninit the parameters and variables *)
  let maybeUninit1 := add_place_list whole (places_of_locals (f.(fn_params) ++ f.(fn_vars))) empty_pathmap in
  let pl := places_of_locals f.(fn_params) in
  let maybeUninit2 := remove_place_list pl maybeUninit1 in
  (* initialize maybeInit set with parameters *)
  let maybeInit := add_place_list whole pl empty_pathmap in
  (* generate selector-based CFG for analysis *)
  (* do (entry, cfg) <- generate_cfg f.(fn_body); *)
  let initMap := DS.fixpoint cfg successors_instr (transfer whole true f cfg) entry (IM.State maybeInit) in
  let uninitMap := DS.fixpoint cfg successors_instr (transfer whole false f cfg) entry (IM.State maybeUninit2) in
  match initMap, uninitMap with
  
  (* we only want the PTree because [None] represent the unreachable node *)
  | Some initMap, Some uninitMap =>
      (** check consistence  *)
          if IM.beq (IM.State whole) (IM.lub initMap!!entry uninitMap!!entry) then
            Errors.OK (initMap, uninitMap, whole)
          else
          Errors.Error (msg ("consistence checking error in analyze\n" ++
          "whole: " ++ show_whole whole ++ "\n               " ++
          "initMap: " ++ show_L_map initMap ++ "\n            " ++
          "uninitMap: " ++ show_L_map uninitMap))
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


(* Invariant between own and (init, uninit, universe) *)
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

Lemma init_irrelavent_place_still_not_owned_inv: forall p1 p2 own,
    is_init (init_place own p2) p1 = true ->
    is_init own p1 = true \/ is_prefix p2 p1 = true.
Proof.
  intros.
  destruct (is_init own p1) eqn: A; auto.
  destruct (is_prefix p2 p1) eqn: B; auto.
  exploit init_irrelavent_place_still_not_owned; eauto.
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


Lemma move_place_init_is_init: forall p p1 own,
    is_init (move_place own p1) p = true ->
    is_init own p = true.
Proof.
  intros p p1 own INIT.
  unfold is_init, move_place, remove_place in *. simpl in *.
  eapply Paths.mem_2 in INIT.
  eapply Paths.mem_1.
  erewrite PathsMap.gsspec in INIT.
  destruct peq in INIT; auto.
  eapply Paths.filter_1 in INIT. rewrite e. auto.
  red. solve_proper.
Qed.
  
Lemma move_children_still_init: forall own p1 p2 p3,
    is_init (move_place own p1) p3 = true ->
    is_prefix p1 p2 = true ->
    is_init (move_place own p2) p3 = true.
Proof.
  intros own p1 p2 p3 INIT PRE.
  unfold is_init, move_place, remove_place in *. simpl in *.
  eapply Paths.mem_2 in INIT.
  eapply Paths.mem_1.
  erewrite PathsMap.gsspec in INIT.
  erewrite PathsMap.gsspec.
  erewrite (is_prefix_same_local p1)in INIT; eauto.
  destruct peq; auto.
  eapply Paths.filter_1 in INIT as A1.
  eapply Paths.filter_2 in INIT as A2. 
  eapply Paths.filter_3; auto.
  red. solve_proper.
  destruct (is_prefix p2 p3) eqn: A3; auto.
  erewrite is_prefix_trans in A2; eauto.
  red. solve_proper.
  red. solve_proper.
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

Lemma must_init_in_universe: forall init uninit universe p,
    must_init init uninit universe p = true ->
    Paths.In p (PathsMap.get (local_of_place p) universe).
Proof.
  intros. unfold must_init in H.
  eapply andb_true_iff in H as (A1 & A2).
  eapply Paths.mem_2 in A2.
  auto.
Qed.


(* all the children has been moved out (PRES). It is used to prove
move_split_places_uncheck_sound *)
Inductive move_ordered_split_places_spec : own_env -> list place -> Prop :=
| ordered_in_own_nil: forall own,
    move_ordered_split_places_spec own nil
| ordered_in_own_cons: forall p l own
    (* (PRES: forall p', is_prefix_strict p p' = true -> is_init own p' = false) *)
    (PRES: forall p', is_prefix p p' = true -> p <> p' -> is_init own p' = false)
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
  - intros p' PRES NEQ.
    destruct (Paths.mem p' (PathsMap.get (local_of_place a) (own_universe own))) eqn: UNI.
    + eapply Paths.mem_2 in UNI.
      (* p' must be equal to a? *)
      exploit COMPLETE. left. eauto.
      instantiate (1 := p'). auto. (* eapply is_prefix_strict_implies; auto. *)
      (* eauto. *) erewrite <- is_prefix_same_local. eauto. auto.
      
      (* eapply is_prefix_strict_implies; auto. *)
      auto. intros [[A|B]|C].
      * (* subst. erewrite is_prefix_strict_not_refl in H. *)
        congruence.
      * inv ORDER. eapply Forall_forall with (x:=p') in H1.
        (* eapply is_prefix_strict_implies in H1. destruct H. *)
        congruence.
        auto.
      * auto. (* destruct (is_init own a); auto. *)
        (* eapply move_place_still_not_owned. auto. *)
    (* easy because p' is not in universe *)
    + eapply not_true_iff_false.
      intro. eapply not_true_iff_false in UNI.
      apply UNI.
      erewrite is_prefix_same_local.
      eapply is_init_in_universe. auto. auto.
      (* eapply is_prefix_strict_implies. auto. *)
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
            (* assert (PRES1: is_prefix_strict p a = true). *)
            (* { eapply is_prefix_strict_implies. auto. } *)
            exploit PRES; eauto.
            unfold is_init. intros INIT.
            eapply Paths.mem_1 in IN.
            erewrite is_prefix_same_local in IN; eauto.
            congruence.
        + eapply LPaths.ge_refl. apply LPaths.eq_refl. }
      eapply move_split_places_uncheck_more; eauto.
Qed.



Definition add_paths_in (s: PathsMap.t) (id: ident) (ps: Paths.t) :=
  let l := PathsMap.get id s in
  PathsMap.set id (Paths.union l ps) s.

(* Once for a time to collect the children in the list and add it to
uninit *)
Lemma add_split_places_uncheck_collect_children: forall drops w uninit id
    (LOCAL: forall p, In p (map fst drops) -> local_of_place p = id),
    PathsMap.ge (add_paths_in uninit id (collect_children_in w (map fst drops)))
      (add_split_places_uncheck w uninit drops).
Proof.
  induction drops; simpl; intros.
  - unfold add_paths_in. red. intros.
    red. rewrite !PathsMap.gsspec.
    red. intros.
    destruct peq.
    + subst. eapply Paths.union_2. auto.
    + auto.
  - destruct a; simpl in *.
    unfold add_paths_in.
    red. intros.
    red. rewrite !PathsMap.gsspec.
    red. intros.
    subst. eapply IHdrops in H; eauto.
    unfold add_paths_in in H.
    rewrite !PathsMap.gsspec in H.
    destruct peq in H; try congruence.
    eapply Paths.union_1 in H.
    destruct H.
    * unfold add_place in H.
      rewrite !PathsMap.gsspec in H.
      destruct peq in H.
      -- subst. destruct peq; try congruence.
         eapply Paths.union_1 in H.
         destruct H.
         ++ eapply Paths.union_2. auto.
         ++ eapply Paths.union_3.
            eapply Paths.union_2. auto.
      -- subst. destruct peq; try congruence.
        eapply Paths.union_2. auto.
    * subst. destruct peq; try congruence.
      eapply Paths.union_3.
      eapply Paths.union_3. auto.
    * destruct peq; try congruence.
      unfold add_place in H.
      rewrite !PathsMap.gsspec in H.
      destruct peq in H.      
      -- subst. exfalso. eapply n.
         eapply LOCAL. auto.
      -- auto.            
Qed.      
        
(* add all the children in uninit is still subset of adding the paraent *)
Lemma add_split_places_uncheck_children: forall (drops: list (place * bool)) r w1 w2 uninit
    (PRE: forall p, In p (map fst drops) -> is_prefix r p = true)
    (UNIEQ: PathsMap.eq w1 w2),
    PathsMap.ge (add_place w1 r uninit)
      (add_paths_in uninit (local_of_place r) (collect_children_in w2 (map fst drops))).
Proof.
  induction drops; simpl; intros.
  - unfold add_paths_in, add_place.
    red. intros. red.
    rewrite !PathsMap.gsspec.
    red. intros.
    destruct peq.
    + subst. eapply Paths.union_1 in H.
      destruct H.
      * eapply Paths.union_2. auto.
      * exfalso. eapply Paths.empty_1. eauto.
    + auto.
  - destruct a. simpl in *.
    unfold add_paths_in, add_place.
    red. intros. red.
    rewrite !PathsMap.gsspec.
    red. intros.
    destruct peq.
    + subst. eapply Paths.union_1 in H.
      destruct H.
      * eapply Paths.union_2. auto.
      * eapply Paths.union_1 in H. destruct H.
        -- eapply Paths.union_3.
           exploit PRE. left. eauto. intros PRE1.
           eapply Paths.filter_3.
           red. solve_proper.
           eapply Paths.filter_1 in H.
           erewrite is_prefix_same_local; eauto.
           eapply UNIEQ. auto.
           red. solve_proper.
           eapply Paths.filter_2 in H. eapply is_prefix_trans; eauto.
           red. solve_proper.
        -- exploit IHdrops.
           intros. eapply PRE. eauto.
           eauto.
           instantiate (1 := uninit).
           instantiate (1 := (local_of_place r)).
           instantiate (1 := a).           
           unfold add_paths_in.
           rewrite PathsMap.gsspec. destruct peq; try congruence.
           eapply Paths.union_3; eauto.
           intros IN.
           unfold add_place in IN.
           rewrite PathsMap.gsspec in IN. destruct peq in IN; try congruence.
    + auto.
Qed.

           
(** Soundness of the analysis in drop statement w.r.t. the dynamic
(small-step) update of the ownership environment *)
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
    + eapply PathsMap.ge_trans. 2: eapply UNINITGE.
      eapply PathsMap.ge_trans.
      2: { eapply add_split_places_uncheck_more. eapply sound_own_uninit. eauto. }
      eapply PathsMap.ge_trans.
      eapply add_split_places_uncheck_children.
      2: { eapply sound_own_universe. eauto. }
      instantiate (1 := drops). 
      (* prefix *)
      intros. eapply split_sound; eauto.
      eapply add_split_places_uncheck_collect_children.
      (* local equal *)
      intros. exploit split_sound; eauto. intros (A & B).
      erewrite <- is_prefix_same_local; eauto.
      (* universe equal *)
      + eapply PathsMap.eq_trans; eauto. eapply sound_own_universe; eauto. }
  auto.
Qed.

(** Properties of dominators_is/must_init  *)

Lemma place_dominators_valid_owner_incl: forall p,
    incl (place_dominators (valid_owner p)) (place_dominators p).
Proof.
  induction p; simpl; auto; try apply incl_refl.
  - red. intros. simpl. right. auto.
Qed.

Lemma place_dominators_downcast_incl: forall p fid fty,
    incl (place_dominators p) (place_dominators (Pdowncast p fid fty)).
Proof.
  induction p; simpl; auto; intros; try apply incl_nil_l.
  - red. intros. simpl. right; auto.
  - red. intros. simpl. right; auto.
  - apply incl_refl.
Admitted.
  
(* what if move out a downcast? Use place_dominators_valid_owner_incl
and place_dominators_downcast_incl ! *)
Lemma move_place_dominator_still_init: forall p own,    
    dominators_is_init own p = true ->
    dominators_is_init (move_place own p) p = true.
Proof.
  induction p; intros; unfold dominators_is_init in *; auto.
  - simpl in H. 
    exploit IHp.
    eauto. intros.
    eapply forallb_forall. intros.
    eapply forallb_forall in H0. 2: eauto.
    eapply move_children_still_init. eauto.
    eapply is_prefix_field.
  - simpl in H.
    eapply andb_true_iff in H. destruct H.
    exploit IHp.
    eauto. intros.
    eapply forallb_forall. intros.
    simpl in H2. destruct H2; subst.
    (* case1 *)
    eapply move_irrelavent_place_still_owned. auto.
    eapply is_prefix_antisym. eapply is_prefix_strict_deref.
    (* case2 *)
    eapply forallb_forall in H1. 2: eauto.
    eapply move_children_still_init. eauto.
    eapply is_prefix_deref.
  - exploit IHp. 
    (* H can imply the premise of IHp *)
    eapply forallb_forall. intros.
    eapply forallb_forall in H. eauto. eapply place_dominators_downcast_incl. auto.
    intros A.
    (* valid_owner p is init *)
    simpl in H.  eapply andb_true_iff in H. destruct H.
    simpl. eapply andb_true_iff. split.
    eapply move_irrelavent_place_still_owned. eauto.
    eapply is_prefix_antisym.
    eapply is_prefix_strict_trans_prefix2. eapply is_prefix_valid_owner.
    eapply is_prefix_strict_downcast.
    (* p's dominators are init so the dominators of (valid_owner p) are init *)
    eapply forallb_forall. intros.
    eapply forallb_forall in A. eapply move_children_still_init. eauto.
    eapply is_prefix_downcast.
    eapply place_dominators_valid_owner_incl. auto.
Admitted.


Lemma dominators_must_init_deref1: forall init uninit universe p ty,
    dominators_must_init init uninit universe (Pderef p ty) = true ->
    dominators_must_init init uninit universe p = true.
Proof.
  intros. unfold dominators_must_init in H. simpl in H.
  eapply andb_true_iff in H. destruct H. auto.
Qed.

Lemma dominators_must_init_deref2: forall init uninit universe p ty,
    dominators_must_init init uninit universe (Pderef p ty) = true ->
    must_init init uninit universe p = true.
Proof.
  intros. unfold dominators_must_init in H. simpl in H.
  eapply andb_true_iff in H. destruct H. auto.
Qed.

Lemma dominators_must_init_downcast: forall init uninit universe p fid fty,
    dominators_must_init init uninit universe (Pdowncast p fid fty) = true ->
    dominators_must_init init uninit universe p = true.
Proof.
  intros. unfold dominators_must_init in *.
  eapply forallb_forall. intros.
  erewrite forallb_forall in H. eapply H.
  eapply place_dominators_downcast_incl; auto.
Qed.

Lemma dominators_is_init_field: forall own p fid fty,
    dominators_is_init own (Pfield p fid fty) = true ->
    dominators_is_init own p = true.
Proof.
  intros. unfold dominators_is_init in *. simpl in H. auto.
Qed.

Lemma dominators_is_init_deref1: forall own p ty,
    dominators_is_init own (Pderef p ty) = true ->
    dominators_is_init own p = true.
Proof.
  intros. unfold dominators_is_init in H. simpl in H.
  eapply andb_true_iff in H. destruct H. auto.
Qed.

Lemma dominators_is_init_deref2: forall own p ty,
    dominators_is_init own (Pderef p ty) = true ->
    is_init own p = true.
Proof.
  intros. unfold dominators_is_init in H. simpl in H.
  eapply andb_true_iff in H. destruct H. auto.
Qed.

Lemma dominators_is_init_downcast: forall own p fid fty,
    dominators_is_init own (Pdowncast p fid fty) = true ->
    dominators_is_init own p = true.
Proof.
  intros. unfold dominators_is_init in *.
  eapply forallb_forall. intros.
  erewrite forallb_forall in H. eapply H.
  eapply place_dominators_downcast_incl; auto.
Qed.


Lemma place_dominators_are_prefixes: forall p2 p1,
    In p2 (place_dominators p1) ->
    is_prefix p2 p1 = true.
Proof.
  induction p1; intros; simpl in *; try contradiction.
  - exploit IHp1. eauto. intros PRE.
    eapply is_prefix_trans. eauto.
    eapply is_prefix_field.
  - destruct H; subst.
    + eapply is_prefix_deref.
    + exploit IHp1. eauto. intros PRE.
      eapply is_prefix_trans. eauto.
      eapply is_prefix_deref.
  - destruct H.
    + subst. eapply is_prefix_trans.
      eapply is_prefix_valid_owner.
      eapply is_prefix_downcast.
    + exploit IHp1.
      eapply place_dominators_valid_owner_incl. auto.
      intros PRE.
      eapply is_prefix_trans. eauto.
      eapply is_prefix_downcast.
Admitted.
      
Lemma move_irr_place_dominator_still_init: forall p1 p2 own,
    dominators_is_init own p1 = true ->
    is_init (move_place own p2) p1 = true ->
    dominators_is_init (move_place own p2) p1 = true.
Proof.
  intros p1 p2 own DOM INIT.
  unfold dominators_is_init in *.
  eapply forallb_forall.
  erewrite forallb_forall in DOM. intros.
  eapply DOM in H as A1.
  destruct (is_prefix p2 p1) eqn: PRE.
  exploit (move_prefix_not_init p2 p1 own). eauto. intros INIT1.
  congruence.
  exploit place_dominators_are_prefixes. eapply H. intros PRE1.
  destruct (is_prefix p2 x) eqn: PRE3.
  exploit is_prefix_trans. eapply PRE3. eauto. congruence.
  eapply move_irrelavent_place_still_owned; eauto.
Qed.

Lemma init_place_dominators_still_init: forall p1 p2 own,
    dominators_is_init own p1 = true ->
    dominators_is_init (init_place own p2) p1 = true.
Proof.
  intros p1 p2 own DOM.
  unfold dominators_is_init in *.
  eapply forallb_forall.
  rewrite forallb_forall in DOM. intros.
  eapply init_owned_place_still_owned; eauto.
Qed.

Lemma in_place_dominatros_and_parent_paths: forall p2 p p1
    (IN1: In p (place_dominators p2))
    (IN2: In p1 (parent_paths p2)),
    p1 = p \/ In p1 (parent_paths p) \/ In p (place_dominators p1).
Proof.
  induction p2; intros; simpl in *.
  - contradiction.
  - destruct IN2.
    + subst. auto.
    + eauto.
  - destruct IN1; destruct IN2; subst; eauto.
  - destruct IN1; destruct IN2; subst.
    + destruct p1; simpl; auto.
    + destruct p2; simpl; auto; simpl in *. eauto.
    + destruct p1; simpl in *; auto.
    + destruct p2; simpl; auto. simpl in *. auto.
Admitted.

(* if p in dom(p2) and p1 is prefix (the version with type
   information) of p2, then p is either a children of p1 or p is in
   dom(p1). *)
Lemma in_place_dominatros_prefix_type_rel: forall p2 p p1,
    In p (place_dominators p2) ->
    is_prefix_type p1 p2 = true ->
    is_prefix_type p1 p = true \/ In p (place_dominators p1).
Proof.
  intros. eapply orb_true_iff in H0.
  destruct H0.
  - apply proj_sumbool_true in H0. subst. auto.
  - apply proj_sumbool_true in H0.
    exploit in_place_dominatros_and_parent_paths; eauto.
    intros [A|[B|C]].
    + subst. left. eapply orb_true_iff.
      left. apply proj_sumbool_is_true. auto.
    + left. eapply orb_true_iff. right.
      eapply proj_sumbool_is_true. auto.
    + auto.
Qed.

(* The dominators of p1 are init, so if we initialize p1, all
   the children of p1 (here p2) are dominator initialized. In the
   other word, the ownership chain has no empty hole *)
Lemma init_dominator_init_prefix: forall p1 p2 own
     (* used to ensure that all places in dom(p1) are in the universe *)
    (COMPLETE: forall p,
        In p (place_dominators p2) ->
        in_universe own p = true),
    is_prefix_type p1 p2 = true ->
    dominators_is_init own p1 = true ->
    dominators_is_init (init_place own p1) p2 = true.
Proof.
  intros p1 p2 own COMPLETE PRE DOM.
  unfold dominators_is_init in *.
  eapply forallb_forall.
  rewrite forallb_forall in DOM. intros.      
  exploit in_place_dominatros_prefix_type_rel. eauto. eapply PRE.
  intros [A|B].
  - eapply init_prefix_init.
    eapply COMPLETE in H as INU.
    unfold in_universe in INU.
    erewrite is_prefix_same_local. 
    eapply Paths.mem_2 in INU. eauto.
    eapply is_prefix_type_is_prefix; auto.
    eapply is_prefix_type_is_prefix; auto.
  - eapply init_owned_place_still_owned. eauto.
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

Lemma init_place_list_sound :forall l own init uninit universe
    (OWN: sound_own own init uninit universe),
    sound_own (init_place_list own l) (add_place_list universe l init) (remove_place_list l uninit) universe.
Proof.
  induction l; intros; simpl.
  auto.
  eapply IHl. eapply init_place_sound.
  auto.
Qed.

Lemma dominators_must_init_sound: forall p init uninit universe own,
    sound_own own init uninit universe ->
    dominators_must_init init uninit universe p = true ->
    dominators_is_init own p = true.
Proof.
  intros. unfold dominators_must_init in H0. unfold dominators_is_init.
  eapply forallb_forall. intros.
  eapply forallb_forall in H0. 2: eauto.
  eapply must_init_sound; eauto.
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
    
Lemma sound_own_ge: forall own init init1 uninit uninit1 universe,
    sound_own own init uninit universe ->
    PathsMap.ge init1 init ->
    PathsMap.ge uninit1 uninit ->
    sound_own own init1 uninit1 universe.
Proof.
  intros until universe. intros SOWN GE1 GE2.
  econstructor.
  eapply PathsMap.ge_trans. eauto. eapply sound_own_init; eauto.
  eapply PathsMap.ge_trans. eauto. eapply sound_own_uninit; eauto.
  eapply sound_own_universe. eauto.
Qed.

(* soundness of function entry: use fixpoint_entry to prove it *)
Lemma sound_function_entry: forall f initMap uninitMap universe entry cfg own1 own2
    (AN: analyze ce f cfg entry = OK (initMap, uninitMap, universe))
    (CFG: generate_cfg f.(fn_body) = OK (entry, cfg))
    (FENTRY: init_own_env ce f = OK own1)
    (INITPARAMS: init_place_list own1 (places_of_locals f.(fn_params)) = own2) ,
  exists init uninit,
    get_IM_state initMap!!entry uninitMap!!entry (Some (init, uninit)) /\
      sound_own own2 init uninit universe.
Proof.
  intros until own2. intros AN CFG. unfold analyze in AN.
  unfold init_own_env.  
  Errors.monadInv AN.
  rewrite EQ. simpl.
  set (empty_pathmap := (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)) in *.
  set (uninit1 := (add_place_list x (places_of_locals (fn_params f ++ fn_vars f)) empty_pathmap)) in *.
  set (initParams := (add_place_list x (places_of_locals (fn_params f)) empty_pathmap)) in *.
  set (uninitVars := (remove_place_list (places_of_locals (fn_params f)) uninit1)) in *.
  (* generalize the beq  as Clightgenproof does *)
  (* set (flag := PathsMap.beq x (PathsMap.lub initParams uninitVars) && *)
  (*   PathsMap.beq (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x) *)
  (*     (PathsMap.combine inter_opt initParams uninitVars)). *)
  set (flag := check_own_env_consistency empty_pathmap empty_pathmap uninit1 x).
  generalize (eq_refl flag).
  generalize flag at 1 3.
  intros flag0 E. destruct flag0; try congruence.
  intros FENTRY. inv FENTRY.
  intros.
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
  eapply sound_own_ge with (init := initParams) (uninit:= uninitVars); eauto.
  eapply init_place_list_sound.
  econstructor; simpl; try eapply PathsMap.ge_refl; try eapply PathsMap.eq_refl.
Qed.


(* Some properties of call_cont *)
Lemma sound_call_cont: forall k ck,
    sound_cont k -> call_cont k = Some ck -> sound_cont ck.
Proof.
  intros k ck SOUND A.
  induction k; inv SOUND; inv A; simpl; try econstructor; eauto.  
Qed.

(* Lemma tr_stacks_call_cont: forall k body cfg pc cont brk nret *)
(*     (SOUND: tr_cont body cfg k pc cont brk nret), *)
(*   tr_stacks (call_cont k). *)
(* Proof. *)
(*   induction k; intros; inv SOUND; simpl; try (econstructor; eauto; fail). *)
(*   - eapply IHk. eauto. *)
(*   - eapply IHk. eauto. *)
(*   - inv STK. econstructor; eauto. *)
(*   - eapply IHk. eauto. *)
(*   - eapply IHk. eauto. *)
(* Qed. *)

  
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
  set (params_init := (add_place_list x (places_of_locals (fn_params f))
                  (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x))) in *.
  set (vars_uninit := (remove_place_list (places_of_locals (fn_params f))
                      (add_place_list x (places_of_locals (fn_params f ++ fn_vars f))
                         (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) x)))) in *.

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


End SOUNDNESS.
