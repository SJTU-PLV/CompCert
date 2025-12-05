Require Import Coqlib.
Require Import Maps.
Require Import Lattice Kildall.
Require Import AST.
Require Import Errors.
Require Import FSetWeakList DecidableType.
Require Import Rusttypes Rustlight.

Local Open Scope list_scope.
Local Open Scope error_monad_scope.
Import ListNotations.


Module Place <: DecidableType.DecidableType.
  Definition t := place.
  Definition eq := @eq t.
  Definition eq_dec := place_eq.
  Definition eq_refl: forall x, eq x x := (@eq_refl t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@eq_sym t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@eq_trans t).
End Place.

Module Paths := FSetWeakList.Make(Place).

Module LPaths := LFSet(Paths).

(* why we need this PathsMap, instead of just a set? *)
Module PathsMap := LPMap1(LPaths).

(** Collect places : if [p] is in the collection, do nothing; if [p]'s
ancestor is in the collection, add the siblings and the siblings of
[p]'s parents to the collection until this ancestor; if [p] and all
its parent are not in the collection, just add [p] to the
collection. *)
            
Section COMP_ENV.

Variable ce : composite_env.

Definition field_of_place (p: place) (rels: list origin_rel) (mem: member) :=
  match mem with
  | Member_plain fid fty =>
      (** When we construct a field place, we need to
          subsitute the generic origins of this field with the
          origins in place [p] *)
      (Pfield p fid (replace_origin_in_type fty rels))
  end.

(* get { p.1, p.2 ...}. We need to track the initialized information
of all the locations no matter they are own_type or not *)
Definition places_of_members (p: place) (mems: members) (rels: list origin_rel) :=
  fold_left (fun acc elt =>               
                   (* if own_type ce ty then *)
                     Paths.add (field_of_place p rels elt) acc) mems Paths.empty.

(* siblings of p *)
Definition siblings (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' fid _ =>
      match typeof_place p' with
      | Tstruct orgs1 id =>
          match ce!id with
          | Some co =>
              let siblings := places_of_members p' co.(co_members) (combine (co_generic_origins co) orgs1) in
              let siblings' := Paths.diff siblings (Paths.singleton p) in
              siblings'
          | _ => Paths.empty
          end
      | _ => Paths.empty
      end
  | Pderef p' _ => Paths.empty
  | Pdowncast _ _ _ => Paths.empty
  end.


Fixpoint parents (p: place) : Paths.t :=
  match p with
  | Plocal _ _ => Paths.empty
  | Pfield p' _ _ => Paths.add p' (parents p')
  | Pderef p' _ => Paths.add p' (parents p')
  | Pdowncast p' _ _ => Paths.add p' (parents p')
  end.


(* The whole set [S] and a place [p] s.t. [p] ∈ [S]:

1. If [p] is [Plocal id ty]: if [ty] = [Tstruct], it means that [p]'s
   children are not mentioned in this function and [p] is only moved
   or assigned entirely; if [ty] = [Tbox] and their are no [p]'s
   successors in [S], it means that [p] can be drop with its drop
   glue, otherwise, we should check [*p]'s initialized information to
   determine how to drop the subpath of [p].

 ___________                                                  
|_f_|_g_|_h_|
             
2. If [p] is [Pfield p' fid ty], it means that [p] and its disjoint
   siblings (e.g., [a] and [b]) which construct continious memory are
   in [S]. [p'] must be not in [S] to avoid ambiguity.

   The complicated case is that if [p] is [**a.f] which means that
    [**a.g] and [**a.h] are in [S], but what about [*a]?

3. If [p] is [Pderef p' ty], it means that [p'] is also in [S],
   because we have to consider how to drop [p']. If [p'] is not in
   [S], we don't how the initialized information about it.


Note: if [p] ∉ [S] then [p] must not be mentioned in the function. *)


Fixpoint own_path_box (p: place) (ty: type) :=
  match ty with
  | Tbox ty' =>
      let p' := Pderef p ty' in
      Paths.add p (own_path_box p' ty')
  | _ => Paths.empty
  end.

(* place [p] owns a memory location and we need to check its value is
initialized. If we only consider move checking and the program is
syntactically well-typed , no need to do this check *)
Fixpoint place_owns_loc (p: place) : bool :=
  match p with
  | Plocal _ _ => true
  (* What about x: &mut Box<i32> ? We must check that p is an owned
  chain! *)
  | Pderef p' _ =>
      match typeof_place p' with
      | Tbox _ =>  place_owns_loc p'
      | _ => false
      end
  | Pfield p' _ _ => place_owns_loc p'
  | Pdowncast p' _ _ => place_owns_loc p'
  end.

(* Compute the deepest place of [p] that does not contain reference,
i.e., it represent a memory location that is no accessed via
reference. The return value (is_owner, p) satisfies: if is_owner is
true, than p is the same as the argument place (it is also the deepest
owner), otherwise p is the deepest owner of the argument *)
Fixpoint owner_place' (p: place) : bool * place :=
  match p with
  | Plocal _ _ => (true, p)
  | Pderef p1 ty =>
      let (is_owner, p2) := owner_place' p1 in
      if is_owner then 
        match typeof_place p1 with
        | Tbox _ => (true, p)
        (* p is not owner place, i.e., it is accessed via reference *)
        | _ => (false, p2)
        end
      else (false, p2)
  | Pfield p1 fid fty
  | Pdowncast p1 fid fty =>
      let (is_owner, p2) := owner_place' p1 in
      if is_owner then (true, p)
      else (false, p2)
  end.
        
Definition owner_place (p: place) := snd (owner_place' p).

(** The core function of adding a place [p] to the whole set [l] *)
(* add [p] to the paths [l]: If [p] is [Pderef p' ty], then
recursively add p' and its parents to paths [l]; If [p] is [Pfield p'
fid ty], then add [p']'s siblings and [p']'s parent to paths [l]*)
Fixpoint collect (p: place) (l: Paths.t) : Paths.t :=
  (* if place_owns_loc p then. We do not need this anymore but we
  should ensure that p = owner_place p *)
  (** FIXME: WHY? If there are some children of [p] in [l], do
      nothing. Because [p] may have been split into sub-fields and we
      have collected p (see Pderef and Pfield cases). *)
  if Paths.is_empty (Paths.filter (fun elt => is_prefix p elt) l) then
    match p with
    | Plocal _ _ =>
        Paths.add p l
    | Pfield p' _ _ =>
        (* difficult case: assume p = [**(a.f).g], p' = [**(a.f)], l = ∅ *)
        let l' := collect p' l in (* l' = {**(a.f), *(a.f), a.f, a.h} *)
        (** Adhoc: if p' is not in l, which means that p' may be a
          Pdowncast, we do not collect its subfields *)
        if Paths.mem p' l' then
          let siblings := siblings p in (* sib = {**(a.f).k, **(a.f).l} *)
          (* l'\{p'} ∪ siblings ∪ {p} *)
          (* ret = {*(a.f), a.f, a.h, **(a.f).k, **(a.f).l, **(a.f).f} *)
          (* we can see that each element occupies a memory location *)
          Paths.union (Paths.remove p' l') (Paths.add p siblings)
        else
          l            
    | Pderef p' ty =>
        (* If type of [p] is [Tbox^n<T>] then add its n children to [l] *)
        (* let children := own_path_box p ty in *)
        (* let l' := Paths.union l children in *)
        let l' := collect p' l in
        (** Adhoc: if p' is not in l, which means that p' may be a
          Pdowncast (note that p' must have Tbox type), we do not
          collect its children *)
        if Paths.mem p' l' then
          Paths.add p l'
        else
          l
    (** FIXME: we treat enum as a whole location  *)
    | Pdowncast p' _ _ => collect p' l
    end
  else l.

    
Definition collect_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in
  PathsMap.set id (collect (owner_place p) l) m.

Definition collect_option_place (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with
  | Some p => collect_place p m
  | None => m
  end.

(* General collect functions *)

Fixpoint collect_pexpr (pe: pexpr) (m: PathsMap.t) : PathsMap.t :=
  match pe with
  | Eplace p _
  | Ecktag p _
  | Eref _ _ p _ =>
      collect_place p m
  | Eunop _ pe _ =>
      collect_pexpr pe m
  | Ebinop _ pe1 pe2 _ =>
      collect_pexpr pe2 (collect_pexpr pe1 m)
  (* note that we do not collect global variable *)
  | _ => m
end.          


Definition collect_expr (e: expr) (m: PathsMap.t) : PathsMap.t :=
  match e with
  | Emoveplace p _ =>
      collect_place p m
  | Epure pe =>
      collect_pexpr pe m
  end.

Fixpoint collect_exprlist (l: list expr) (m: PathsMap.t) : PathsMap.t :=
  match l with
  | nil => m
  | e :: l' =>
      collect_exprlist l' (collect_expr e m)
  end.


End COMP_ENV.

(* Kill function *)
Definition remove_place (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in  
  let rm := Paths.filter (fun elt => negb (is_prefix p elt)) l in
  PathsMap.set id rm m.


Definition remove_option (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with 
  | Some p => remove_place p m
  | None => m
  end.

Fixpoint remove_place_list (l: list place) (m: PathsMap.t) : PathsMap.t :=
  match l with
  | nil => m
  | p :: l' =>
      remove_place_list l' (remove_place p m)
  end.

(* Gen function: it add {p' | is_prefix p p' /\ p' ∈ S} to m[id]. Here
[S] is the whole set *)
Definition add_place (S: PathsMap.t) (p: place) (m: PathsMap.t) : PathsMap.t :=
  let id := local_of_place p in
  let l := PathsMap.get id m in
  let whole := PathsMap.get id S in
  let add := Paths.filter (fun elt => is_prefix p elt) whole in
  PathsMap.set id (Paths.union l add) m.

Definition add_option (S: PathsMap.t) (p: option place) (m: PathsMap.t) : PathsMap.t :=
  match p with
  | Some p => add_place S p m
  | None => m
  end.

Fixpoint add_place_list S (l: list place) (m: PathsMap.t) : PathsMap.t :=
  match l with
  | nil => m
  | p :: l' =>
      add_place_list S l' (add_place S p m)
  end.

(** Top-level init domain for analysis which contains bot to represent
impossible cases *)

Module IM <: SEMILATTICE.

  Inductive t' := Bot | State (m: PathsMap.t).
  Definition t := t'.

  Definition eq (x y: t) :=
    match x, y with
    | Bot, Bot => True
    | State m1, State m2 =>
        PathsMap.eq m1 m2
    | _, _ => False
    end.

  Lemma eq_refl: forall x, eq x x.
  Proof.
    destruct x; simpl. auto. eapply PathsMap.eq_refl.
  Qed.
  
  Lemma eq_sym: forall x y, eq x y -> eq y x.
  Proof.
    destruct x, y; simpl; auto.
    intros. eapply PathsMap.eq_sym. auto.
  Qed.
  
  Lemma eq_trans: forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    destruct x, y, z; simpl; try tauto.
    intros. eapply PathsMap.eq_trans; eauto.
  Qed.

  Definition beq (x y: t) : bool :=
    match x, y with
    | Bot, Bot => true
    | State m1, State m2 => PathsMap.beq m1 m2
    | _, _ => false
    end.

  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof.
    destruct x, y; simpl; intros.
    auto.
    congruence.
    congruence.
    eapply PathsMap.beq_correct. auto.
  Qed.

  Definition ge (x y: t) : Prop :=
    match x, y with
    | _, Bot => True
    | Bot, _ => False
    | State m1, State m2 => PathsMap.ge m1 m2
    end.

  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof.
    destruct x, y; simpl; try tauto.
    intros. eapply PathsMap.ge_refl. auto.
  Qed.
  
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof.
    destruct x, y, z; simpl; try tauto.
    intros. eapply PathsMap.ge_trans; eauto.    
  Qed.

  Definition bot : t := Bot.
  Lemma ge_bot: forall x, ge x bot.
  Proof.
    destruct x; simpl; auto.
  Qed.

  Definition lub (x y: t) : t :=
    match x, y with
    | Bot, _ => y
    | _, Bot => x
    | State m1, State m2 => State (PathsMap.lub m1 m2)
    end.

  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    apply ge_refl; apply eq_refl.
    simpl. eapply PathsMap.ge_lub_left.
  Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof.
    destruct x, y.
    apply ge_refl; apply eq_refl.
    apply ge_refl; apply eq_refl.
    simpl. auto.
    simpl. eapply PathsMap.ge_lub_right.
  Qed.

End IM.


(** Comment for [split_drop_places]: When executing a Sdrop(p)
statement, we cannot directly evaluate the address of p and
recursively free its data, because p may partially owns its data. So
we need to split p into list of places that fully own their data. It
is not trivial because we have to ensure the order (specifically,
topological order) of this list of places so that we can free a place
by assuming that all its children are freed. Moreover, some of the
generated split places may have scalar type (which has no effect in
the semantics, see step_dropplace_scalar in RustIRown and
Rustlightown) because we need to generate all the places in the
universe which are children of the [p]. It is necessary to ensure the
soundness of the init-analysis because we need to establish the
relation between dynamic ownership update in step_dropplace and static
ownership update in init-analysis respectively. *)

Section SPLIT.
Variable universe: Paths.t.
  
Variable ce: composite_env.

Variable rec: forall (ce': composite_env), (PTree_Properties.cardinal ce' < PTree_Properties.cardinal ce)%nat -> place -> type -> res (list (place * bool)).

(* Return the list of split places associated with a flag that
indicates whether this place is fully owned or not (if it is init) *)
(** Some property: the output places must be in universe so that we
can check whether this place is initialized or not. So the fully owned
flag is necessary *)
Fixpoint split_drop_place' (p: place) (ty: type) : res (list (place * bool)) :=
  match ty with
  | Tstruct orgs1 id =>
      (** TODO: if we allow collecting overlapped places, we should
      use is_full here. *)
      (* p in universe indicates that p is fully owned/moved (no p's
      children mentioned in this function) *)
      if Paths.mem p universe then
        (** The return true relies on the properties of collect function *)
        OK [(p, true)]
      else
        match get_composite ce id with
        | co_some i co P _ =>
            let children := map (field_of_place p (combine (co_generic_origins co) orgs1)) co.(co_members) in
            let foldf subfld acc :=
              do drops <- acc;
              do drops' <- rec (PTree.remove i ce) (PTree_Properties.cardinal_remove P) subfld (typeof_place subfld);
              OK (drops' ++ drops) in
            fold_right foldf (OK nil) children
        | co_none => Error[CTX id; MSG ": Unfound struct id in composite_env or wrong recursive data: split_drop_place"]
        end
  | Tvariant _ id =>
       if Paths.mem p universe then
        OK [(p, true)]
      else
        (* we must ensure that no p's children in universe? *)
        Error ([MSG "place is "; CTX (local_of_place p); MSG ": enum does not exist in the universe set: split_drop_place"])
  | Tbox ty =>
      if Paths.mem p universe then
        (* p must be not fully owned *)
        if Paths.exists_ (fun p' => is_prefix_strict p p') universe then
          do drops <- split_drop_place' (Pderef p ty) ty;
          OK (drops ++ [(p, false)])
        else
          (* p is fully owned if it is initialized *)
          OK [(p, true)]
      else
        Error ([MSG "place is "; CTX (local_of_place p); MSG ": Box does not exist in the universe set: split_drop_place"])
  (* p has scalar type. In the semantics, we should skip its drop
  statement and in the compilation, Sdrop p would be translated to
  Sskip in ElaborateDrop. Note that scalar place must be fully
  owned *)
  | _ => OK [(p, true)]
   (* Error [MSG ": Normal types do not need drop: split_drop_place"] *)
  end.

End SPLIT.

Require Import Wfsimpl.

(** Specification of split_drop_place  *)

(* similar to sound_split_drop_place in BorrowCheckSafe.v *)
Inductive split_places_ordered : list place -> Prop :=
| split_places_ordered_nil: split_places_ordered []
| split_places_ordered_cons: forall p l,
    (* all remaining places are not children of p *)
    Forall (fun p1 => is_prefix p p1 = false) l ->
    split_places_ordered l ->
    split_places_ordered (p :: l)
.

Lemma split_places_ordered_dec: forall l, {split_places_ordered l} + {~ split_places_ordered l}.
Proof.
  induction l.
  - left. constructor.
  - destruct IHl.
    + destruct (forallb (fun p1 => negb (is_prefix a p1)) l) eqn: A.
      * left. constructor. eapply Forall_forall.
        intros. 
        eapply forallb_forall in A. eapply negb_true_iff. eauto.
        auto. auto.
      * right. intro.
        eapply not_false_iff_true.  2: eauto.
        inv H. eapply forallb_forall. intros.
        eapply Forall_forall in H2.
        eapply negb_true_iff. eauto. auto.
    + right. intro. eapply n. inv H. auto.
Defined.
      
Definition is_full_internal (universe: Paths.t) (p: place) : bool :=
  Paths.for_all (fun p1 => negb (is_prefix_strict p p1)) universe.
  
Definition is_full (universe: PathsMap.t) (p: place) : bool :=
    let w := PathsMap.get (local_of_place p) universe in
    is_full_internal w p.


Lemma is_full_internal_eq_universe: forall u1 u2 p,
    Paths.Equal u1 u2 ->
    is_full_internal u1 p = is_full_internal u2 p.
Proof.
  intros. unfold is_full_internal.
  eapply eq_bool_prop_intro. split.
  - intros. apply Is_true_eq_left.
    apply Paths.for_all_1.
    red. solve_proper.
    red. intros.
    apply Is_true_eq_true in H0.
    apply Paths.for_all_2 in H0.
    red in H0. apply H0. apply H. auto.
    red. solve_proper.
  - intros. apply Is_true_eq_left.
    apply Paths.for_all_1.
    red. solve_proper.
    red. intros.
    apply Is_true_eq_true in H0.
    apply Paths.for_all_2 in H0.
    red in H0. apply H0. apply H. auto.
    red. solve_proper.
Qed.


Lemma is_full_same: forall w1 w2 p,
    PathsMap.eq w1 w2 ->
    is_full w1 p = is_full w2 p.
Proof.
  intros. unfold is_full.
  erewrite is_full_internal_eq_universe.
  eauto. red. intros. split; intros.
  eapply H. auto.
  eapply H. auto.
Qed.

Record split_drop_place_spec (universe: Paths.t) (r: place) (drops: list (place * bool)) : Prop :=
  { split_sound: forall p, In p (map fst drops) -> Paths.In p universe /\ is_prefix r p = true;
    split_complete: forall p, Paths.In p universe -> is_prefix r p = true -> In p (map fst drops);
    split_norepet: list_norepet (map fst drops);
    split_ordered: split_places_ordered (map fst drops);
    (** Adhoc: current implementation does not guarantee this
    property. This property is an invariant of the universe *)
    split_correct_full: forall p full,
      In (p,full) drops ->
      (* no p's children in universe if p is full *)
      is_full_internal universe p = full
  }.


(** Prove split_drop_place satisfies the specification by translation
validation, because it is too compilcated and techenical to fully
verify it. We leave it as future work. *)

Definition check_split_drops_sound (universe: Paths.t) (r: place) (drops: list place) : bool :=
  (* all places in the drops are children of p and are in the universe *)
  forallb (fun p1 => Paths.mem p1 universe && is_prefix r p1) drops.

Definition check_split_drops_complete (universe: Paths.t) (r: place) (drops: list place) : bool :=
  (* all places in the universe which are children of p must in drops *)
  Paths.for_all (fun p1 => in_dec place_eq p1 drops) (Paths.filter (fun p1 => is_prefix r p1) universe).

Definition check_split_correct_full (universe: Paths.t) (drops: list (place * bool)) : bool :=
  (* check that full flag is correct w.r.t is_full_internal *)
  forallb (fun '(p, full) => eqb (is_full_internal universe p) full) drops.

Definition check_split_drop_place_spec (universe: Paths.t) (r: place) (drops: list (place * bool)) : res unit :=
  if check_split_drops_sound universe r (map fst drops) then
    if check_split_drops_complete universe r (map fst drops) then
      if list_norepet_dec place_eq (map fst drops) then
        if split_places_ordered_dec (map fst drops) then
          if check_split_correct_full universe drops then OK tt
          else Error (msg "Error in check_split_drop_place_spec: check_split_correct_full error")
        else Error (msg "Error in check_split_drop_place_spec: split_places_ordered_dec error")
      else Error (msg "Error in check_split_drop_place_spec: list_norepet_dec error in check_split_drop_place_spec")
    else Error (msg "Error in check_split_drop_place_spec: check_split_drops_complete")
  else Error (msg "Error in check_split_drop_place_spec: check_split_drops_sound error").
                                      

(** TODO: implement it in Ocaml  *)
Definition split_drop_place (ce: composite_env) (universe: Paths.t) (p: place) (ty: type) : res (list (place * bool)) :=
  do drops <- if place_owns_loc p then
               Fixm (@PTree_Properties.cardinal composite) (split_drop_place' universe) ce p ty
                    (* We should consider if p is something like *b where b has reference type), we should not split *b *)
             else OK nil;
  (* It checks split_complete property, because the iteration cannot
  ensure that all the childre of p in the universe would be
  collected. *)
  do _ <- check_split_drop_place_spec universe p drops;
  OK drops.

Lemma split_drop_place_meet_spec: forall ce universe p drops,
    split_drop_place ce universe p (typeof_place p) = OK drops ->
    split_drop_place_spec universe p drops.
Proof.
  intros. unfold split_drop_place in H.
  monadInv H.
  unfold check_split_drop_place_spec in EQ1.
  destruct (check_split_drops_sound universe p (map fst drops)) eqn: C1; try congruence.
  destruct (check_split_drops_complete universe p (map fst drops)) eqn: C2; try congruence.
  destruct (list_norepet_dec place_eq (map fst drops)) eqn: C3; try congruence.
  destruct (split_places_ordered_dec (map fst drops)) eqn: C4; try congruence.
  destruct (check_split_correct_full universe drops) eqn: C5; try congruence.
  inv EQ1.
  constructor.
  (* sound *)
  - intros. unfold check_split_drops_sound in C1.
    eapply forallb_forall in C1; eauto.
    eapply andb_true_iff in C1. destruct C1.
    split.
    apply Paths.mem_2; eauto. auto.
  (* complete *)
  - unfold check_split_drops_complete in C2.
    eapply Paths.for_all_2 in C2.
    intros. red in C2.
    exploit C2. eapply Paths.filter_3; eauto.
    red. solve_proper.
    intros. eapply proj_sumbool_true in H1. auto.
    red. solve_proper.
  - auto.
  - auto.
  - unfold check_split_correct_full in C5.
    intros.
    eapply forallb_forall in C5. 2: eauto.
    simpl in C5. eapply eqb_true_iff. auto.
Qed.

(** Properties of split_drop_place *)

Lemma check_split_drops_sound_eq_universe: forall u1 u2 p l,
    Paths.Equal u1 u2 ->
    check_split_drops_sound u1 p l = check_split_drops_sound u2 p l.
Proof.
  intros. unfold check_split_drops_sound.
  eapply eq_bool_prop_intro. split.
  - intros. apply Is_true_eq_left.    
    apply forallb_forall.
    intros.
    apply Is_true_eq_true in H0.
    eapply forallb_forall in H0. 2: eauto.
    eapply andb_true_iff in H0. destruct H0.
    eapply andb_true_iff. split.
    setoid_rewrite H in H0. auto.
    auto.    
  - intros. apply Is_true_eq_left.    
    apply forallb_forall.
    intros.
    apply Is_true_eq_true in H0.
    eapply forallb_forall in H0. 2: eauto.
    eapply andb_true_iff in H0. destruct H0.
    eapply andb_true_iff. split.
    setoid_rewrite H. auto.
    auto.
Qed.    

Lemma check_split_drops_complete_eq_universe: forall u1 u2 p l,
    Paths.Equal u1 u2 ->
    check_split_drops_complete u1 p l = check_split_drops_complete u2 p l.
Proof.
  intros. unfold check_split_drops_complete.
  eapply eq_bool_prop_intro. split.
  - intros. apply Is_true_eq_left.    
    apply Paths.for_all_1.
    red. solve_proper.
    red. intros.
    apply Is_true_eq_true in H0.
    eapply Paths.for_all_2 in H0.
    red in H0. eapply H0.
    setoid_rewrite H. auto.
    red. solve_proper.
  - intros. apply Is_true_eq_left.    
    apply Paths.for_all_1.
    red. solve_proper.
    red. intros.
    apply Is_true_eq_true in H0.
    eapply Paths.for_all_2 in H0.
    red in H0. eapply H0.
    setoid_rewrite H in H1. auto.
    red. solve_proper.
Qed.

  
Lemma check_split_correct_full_eq_universe: forall u1 u2 l,
    Paths.Equal u1 u2 ->
    check_split_correct_full u1 l = check_split_correct_full u2 l.
Proof.
  intros. unfold check_split_correct_full.
  eapply eq_bool_prop_intro. split.
  - intros. apply Is_true_eq_left.    
    apply forallb_forall.
    intros. destruct x.
    apply Is_true_eq_true in H0.
    eapply forallb_forall in H0. 2: eauto.
    simpl in H0.
    erewrite <- is_full_internal_eq_universe; eauto.
  - intros. apply Is_true_eq_left.    
    apply forallb_forall.
    intros. destruct x.
    apply Is_true_eq_true in H0.
    eapply forallb_forall in H0. 2: eauto.
    simpl in H0.
    erewrite is_full_internal_eq_universe; eauto.
Qed.

Lemma check_split_drop_place_spec_eq_universe: forall u1 u2 p drops,
    Paths.Equal u1 u2 ->
    check_split_drop_place_spec u1 p drops = check_split_drop_place_spec u2 p drops.
Proof.
  intros.
  unfold check_split_drop_place_spec.
  erewrite check_split_drops_sound_eq_universe. 2: eauto.
  erewrite check_split_drops_complete_eq_universe. 2: eauto.
  erewrite check_split_correct_full_eq_universe. 2: eauto.
  auto.
Qed.

Lemma split_drop_place_fixm_eq_universe: forall ce u1 u2 p ty,
    Paths.Equal u1 u2 ->
    Fixm (@PTree_Properties.cardinal composite) (split_drop_place' u1) ce p ty = Fixm (@PTree_Properties.cardinal composite) (split_drop_place' u2) ce p ty.
Proof.
  intros ce. pattern ce. apply well_founded_ind with (R := ltof _ (@PTree_Properties.cardinal composite)).
  apply well_founded_ltof.
  intros.  
  erewrite !unroll_Fixm.
  generalize dependent p.
  induction ty; intros p; simpl; auto.
  -  assert (A: Paths.mem p u1 = Paths.mem p u2).
     { setoid_rewrite H0. auto. }
    rewrite A. destruct (Paths.mem p u2) eqn: MEM; auto.
    assert (B: Paths.exists_ (fun p' : Paths.elt => is_prefix_strict p p') u1 =
                 Paths.exists_ (fun p' : Paths.elt => is_prefix_strict p p') u2).
    {  destruct (Paths.exists_ (fun p' : Paths.elt => is_prefix_strict p p') u1) eqn: EX.
      symmetry.
      eapply Paths.exists_1.
      red. solve_proper.
      eapply Paths.exists_2 in EX. red. red in EX.
      destruct EX as (r & B1 & B2). exists r. split; auto.
      eapply H0. auto.
      red. solve_proper.
      symmetry.
      eapply not_true_iff_false. intro.
      eapply not_true_iff_false in EX. eapply EX.
      eapply Paths.exists_1.
      red. solve_proper.
      eapply Paths.exists_2 in H1. red. red in H1.
      destruct H1 as (r & B1 & B2). exists r. split; auto.
      eapply H0. auto.
      red. solve_proper. }
    rewrite B.
    destruct (Paths.exists_ (fun p' : Paths.elt => is_prefix_strict p p') u2); simpl; auto.
    generalize (IHty (Pderef p ty)). intros IHty1.
    destruct (split_drop_place' u1 x
      (fun (y : PTree.t composite)
         (_ : (PTree_Properties.cardinal y < PTree_Properties.cardinal x)%nat) =>
       Fixm (PTree_Properties.cardinal (V:=composite)) (split_drop_place' u1) y)
      (Pderef p ty) ty) eqn: C.    
    rewrite <- IHty1. auto.
    rewrite <- IHty1. auto.
  -  assert (A: Paths.mem p u1 = Paths.mem p u2).
     { setoid_rewrite H0. auto. }
     rewrite A. destruct (Paths.mem p u2) eqn: MEM; auto.
     destruct (get_composite x i); auto.
     (* induction on the list of fields *)
     generalize (OK (@nil (place * bool))).
     generalize ((map (field_of_place p (combine (co_generic_origins co) l)) (co_members co))).
     induction l0.
     + auto.
     + intros. simpl. erewrite IHl0.
       destruct (fold_right
     (fun (subfld : place) (acc : res (list (place * bool))) =>
      do drops <- acc;
      do drops' <-
      Fixm (PTree_Properties.cardinal (V:=composite)) (split_drop_place' u2)
        (PTree.remove id1 x) subfld (typeof_place subfld); OK (drops' ++ drops))) eqn: FOLD.
       * simpl. erewrite H; eauto.
         red. eapply PTree_Properties.cardinal_remove. eauto.
       * simpl. auto.
  - assert (A: Paths.mem p u1 = Paths.mem p u2).
     { setoid_rewrite H0. auto. }
     rewrite A. destruct (Paths.mem p u2) eqn: MEM; auto.
Qed.
      
Lemma split_drop_place_eq_universe: forall ce u1 u2 p ty,
    Paths.Equal u1 u2 ->
    split_drop_place ce u1 p ty = split_drop_place ce u2 p ty.
Proof.
  intros.
  unfold split_drop_place.
  erewrite split_drop_place_fixm_eq_universe; eauto.
  destruct (place_owns_loc p); simpl; auto.
  destruct (Fixm (PTree_Properties.cardinal (V:=composite)) (split_drop_place' u2) ce p ty); eauto.
  simpl.
  erewrite check_split_drop_place_spec_eq_universe; eauto.
  erewrite check_split_drop_place_spec_eq_universe; eauto.
Qed.  
