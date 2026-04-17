Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Ctypes Rusttypes .
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
    match_dropm:
    generate_dropm p = generate_dropm tp;
    match_prog_skel:
    erase_program tp = erase_program p;
  }.

Lemma match_erase_globdef: forall l tl ce,
    transf_globdefs (fun (_ : ident) (f : fundef) => transf_fundef ce f)
      (fun (_ : ident) (v : type) => OK v) l = OK tl ->
    map (fun '(id, g) => (id, erase_globdef g)) l = map (fun '(id, g) => (id, erase_globdef g)) tl.
Proof.
  induction l; simpl; intros tl ce TR.
  inv TR. auto.
  destruct a. destruct g.
  destruct transf_fundef eqn: TF in TR; try congruence.  
  monadInv TR. simpl. f_equal.
  eauto.
  monadInv TR. simpl. f_equal.
  eauto.
Qed.

Lemma match_globdef: forall l tl ce id,
    transf_globdefs (fun (_ : ident) (f : fundef) => transf_fundef ce f)
      (fun (_ : ident) (v : type) => OK v) l = OK tl ->
    Coqlib.option_rel (match_glob ce) ((PTree_Properties.of_list l) ! id) ((PTree_Properties.of_list tl) ! id).
Proof.
  intros l tl ce id TR.
  eapply PTree_Properties.of_list_related.
  generalize dependent tl.
  generalize dependent l.
  induction l; simpl; intros.
  inv TR. econstructor.
  destruct a. destruct g.
  destruct transf_fundef eqn: TF in TR; try congruence.  
  monadInv TR. econstructor.
  split; auto.
  eapply IHl. eauto.
  monadInv TR. econstructor.
  split; auto.
  simpl. destruct v. simpl.
  constructor. auto.
  eauto.
Qed.

Lemma check_drop_glue_match: forall id f f0 ce,
    transf_fundef ce f = OK f0 ->
    check_drop_glue (id, Gfun f) = check_drop_glue (id, Gfun f0).
Proof.
  intros.
  unfold transf_fundef in H. destruct f; auto.
  - monadInv H.
    unfold transf_function in EQ.
    monadInv EQ. destruct x2. destruct p.
    monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
    monadInv EQ3. simpl. auto.
  - inv H. auto.
Qed.

    
Lemma extract_drop_id_match: forall id f f0 ce,
    transf_fundef ce f = OK f0 ->
    extract_drop_id (id, Gfun f) = extract_drop_id (id, Gfun f0).
Proof.
  intros.
  unfold transf_fundef in H. destruct f; auto.
  - monadInv H.
    unfold transf_function in EQ.
    monadInv EQ. destruct x2. destruct p.
    monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
    monadInv EQ3. simpl. auto.
  - inv H. auto.
Qed.
        
Lemma match_generate_dropm: forall l tl ce id,
    transf_globdefs (fun (_ : ident) (f : fundef) => transf_fundef ce f)
      (fun (_ : ident) (v : type) => OK v) l = OK tl ->
    Coqlib.option_rel eq (PTree_Properties.of_list (map extract_drop_id (filter check_drop_glue l))) ! id  (PTree_Properties.of_list (map extract_drop_id (filter check_drop_glue tl))) ! id.
Proof.
  intros l tl ce id TR.
  eapply PTree_Properties.of_list_related.
  generalize dependent tl.
  generalize dependent l.
  induction l; simpl; intros.
  inv TR. econstructor.
  destruct a. destruct g.
  - destruct transf_fundef eqn: TF in TR; try congruence.  
    monadInv TR. 
    erewrite check_drop_glue_match; eauto.
    destruct (check_drop_glue (i, Gfun f0)) eqn: A.
    + replace (map extract_drop_id (filter check_drop_glue ((i, Gfun f0) :: x))) with
        (extract_drop_id (i, Gfun f0) :: (map extract_drop_id (filter check_drop_glue x))).
      2: { unfold filter at 2. rewrite A. auto. }
      rewrite map_cons.
      econstructor; auto.
      erewrite extract_drop_id_match; eauto.
    + unfold filter at 2.
      rewrite A. auto.
  - monadInv TR. simpl. auto.
Qed.

Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  intros. unfold transl_program in H. monadInv H. unfold transform_partial_program in EQ.
  destruct p. simpl in *. unfold transform_partial_program2 in EQ. 
  monadInv EQ. simpl. econstructor; eauto.
  - intros. unfold prog_defmap. simpl in *.
    eapply match_globdef. eauto.
  (* generate_dropm *)
  - unfold generate_dropm. simpl in *.
    eapply PTree.extensionality. intros.
    exploit match_generate_dropm; eauto. instantiate (1 := i).
    intros.
    destruct ((PTree_Properties.of_list (map extract_drop_id (filter check_drop_glue prog_defs))) ! i) eqn: A.
    inv H. auto. inv H. auto.
  - unfold erase_program.
    simpl in *. f_equal.
    erewrite <- match_erase_globdef with (ce:= prog_comp_env); eauto. 
Qed.

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
    (SPLIT: match_split_drop_places flagm (if is_init own p then move_place own p else own) l ts)
    (NOTSCALAR: drop_type (typeof_place p) = true),
    (* how to ensure that p is owned in own_env *)    
    (** FIXME: this drop place has a drop flag does not mean that this
    drop must be conditional. However, if this place require a drop flag and here we do not generate conditional drop, then we also need to update the status of the drop flag. But generate_drop function only uses the flag arguments to decide whether to update the drop flag status *)
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full (Some flag)) ts)
| match_sdp_cons_must_init: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_init own p = true)
    (NOTSCALAR: drop_type (typeof_place p) = true),
    (* how to ensure that p is owned in own_env *)    
    match_split_drop_places flagm own ((p,full)::l) (Ssequence (generate_drop p full None) ts)
| match_sdp_cons_must_uninit: forall p own l ts full
    (FLAG: get_dropflag_temp flagm p = None)
    (SPLIT: match_split_drop_places flagm own l ts)
    (OWN: is_init own p = false),
    (* how to ensure that p is owned in own_env *)
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
| match_sdp_cons_scalar: forall p own l ts full
    (SPLIT: match_split_drop_places flagm (move_place own p) l ts)
    (OWN: is_init own p = true)
    (SCALAR: drop_type (typeof_place p) = false),
    match_split_drop_places flagm own ((p,full)::l) (Ssequence Sskip ts)
.


(* Invariant of generate_drop_flags *)

(* If a place (with non-scalar type) has no drop flag, it must be
either must init or must uninit *)
Record sound_flagm ce (body: statement) (cfg: rustcfg) (flagm: FM) (init uninit: PMap.t IM.t) (universe: PathsMap.t) : Prop :=
  {    
    sound_flagm_none: 
    forall pc next p p1 sel drops mayinit mayuninit,
      cfg ! pc = Some (Isel sel next) ->
      select_stmt body sel = Some (Sdrop p) ->
      split_drop_place ce (PathsMap.get (local_of_place p) universe) p (typeof_place p) = OK drops ->
      In p1 (map fst drops) ->
      (* there is no dropflags for this place *)
      get_dropflag_temp flagm p1 = None ->
      get_IM_state init!!pc uninit!!pc (Some (mayinit, mayuninit)) ->
      drop_type (typeof_place p1) = true ->
      (* So p1 is either must owned *)
      (must_init mayinit mayuninit universe p1 = true \/
         (* or must unowned *)
         may_init mayinit mayuninit universe p1 = false);

    (* If a place has some drop flag, it must has non-scalar type. It
    is used in the simulation of step_dropplace_scalar because we need
    to ensure that moving out a scalar typed place in the own_env does
    not affect match_envs_flagm. *)
    sound_flagm_some: forall p id,
      get_dropflag_temp flagm p = Some id ->
      drop_type (typeof_place p) = true;
  }.
 
Lemma generate_place_map_in_map_not_in_list: forall l p id m,
    ~ In p (map fst l) ->
    get_dropflag_temp m p = Some id ->
    get_dropflag_temp (fold_left generate_place_map_fun l m) p = Some id.
Proof.
  induction l; simpl; intros; auto.
  eapply Decidable.not_or in H. destruct H.
  destruct a. simpl in *.
  eapply IHl. eauto.  
  unfold generate_place_map_fun, get_dropflag_temp. simpl.
  unfold generate_place_map_fun, get_dropflag_temp in H0.
  (* 2 cases: p and p0 have the same local or not *)
  destruct (ident_eq (local_of_place p) (local_of_place p0)).
  - rewrite <- !e.                 (* rewrite! equivalent to repeat rewrite *)
    destruct (m ! (local_of_place p)) eqn: G.
    + rewrite PTree.gss.
      (* p <> p0 so find would skip the first element *)
      simpl. destruct place_eq; try congruence. simpl. auto.
    + congruence.
  - destruct (m ! (local_of_place p)) eqn: G1; try congruence.
    destruct (m ! (local_of_place p0)) eqn: G2.
    + rewrite PTree.gso; eauto. rewrite G1. auto.
    + rewrite PTree.gso; eauto. rewrite G1. auto.
Qed.

Lemma generate_place_map_dom: forall l p,
    In p (map fst l) ->
    exists id, get_dropflag_temp (generate_place_map l) p = Some id.
Proof.
  intros.
  unfold generate_place_map.
  generalize (PTree.empty (list (place * ident))).
  generalize dependent l. induction l; intros; simpl in *.
  - contradiction.
  - destruct a. simpl in H. destruct H.
    (* a is the first element of l *)
    + subst.
      (* case analysis of p in l or not *)
      destruct (in_dec place_eq p (map fst l)).
      * exploit IHl. auto. intros (id & A). erewrite A. eauto.
      (* p is not in l: so whatever in the list does not change the
      mapping of p. Make it a lemma!! *)
      * exploit generate_place_map_in_map_not_in_list; eauto.
        unfold generate_place_map_fun, get_dropflag_temp. simpl.
        destruct (t ! (local_of_place p)); simpl.
        -- rewrite PTree.gss. simpl.
           destruct place_eq; try congruence. simpl. auto.
        -- rewrite PTree.gss. simpl.
           destruct place_eq; try congruence. simpl. auto.
    (* a is in the rest of the list *)
    + eapply IHl; eauto.
Qed.

Lemma generate_place_map_in_list_or_m: forall l p id m,
  get_dropflag_temp (fold_left generate_place_map_fun l m) p = Some id ->
  In (p, id) l \/ get_dropflag_temp m p = Some id.
Proof.
  induction l.
  - intros. simpl in H. right. apply H.
  - intros. simpl in H. apply IHl in H. destruct H.
    + left. simpl. right. apply H.
    + destruct a. destruct (place_eq p p0).
      * unfold generate_place_map_fun in H. simpl in H. subst p0. left.
        destruct (m ! (local_of_place p)). 
        ** unfold get_dropflag_temp in H.
           rewrite PTree.gss in H. simpl in H. 
           destruct (place_eq p p); simpl in H; try congruence; auto.
           inv H. simpl. left. reflexivity.
        ** unfold get_dropflag_temp in H.
           rewrite PTree.gss in H. simpl in H. 
           destruct (place_eq p p); simpl in H; try congruence; auto.
           inv H. simpl. left. reflexivity.
      * right. unfold generate_place_map_fun in H. simpl in H.
        destruct (ident_eq (local_of_place p0) (local_of_place p)).
        ++ rewrite !e in *. unfold get_dropflag_temp.
         destruct (m ! (local_of_place p)).
          ** unfold get_dropflag_temp in H.
            rewrite PTree.gss in H. simpl in H. 
            destruct (place_eq p p0); simpl in H; try congruence; auto.
          ** unfold get_dropflag_temp in H.
            rewrite PTree.gss in H. simpl in H. 
            destruct (place_eq p p0); simpl in H; try congruence; auto.
        ++ destruct (m ! (local_of_place p0)). 
          ** unfold get_dropflag_temp in H.
            rewrite PTree.gso in H by auto. simpl in H. 
            destruct (place_eq p p0); simpl in H; try congruence; auto.
          ** unfold get_dropflag_temp in H.
            rewrite PTree.gso in H by auto. simpl in H. 
            destruct (place_eq p p0); simpl in H; try congruence; auto.
Qed.


Lemma generate_place_map_in_list: forall l p id,
    get_dropflag_temp (generate_place_map l) p = Some id ->
    In (p, id) l.
Proof.
  intros. apply generate_place_map_in_list_or_m in H.
  unfold get_dropflag_temp in H. simpl in H. destruct H.
  apply H. discriminate.
Qed. 

(** Key lemma used in generate_flag_map_sound  *)
Lemma in_drop_flags_for_splits: forall drops p init uninit universe,
    In p drops ->
    must_init init uninit universe p = false ->
    may_init init uninit universe p = true ->
    drop_type (typeof_place p) = true ->
    exists id, In (p, id) (generate_drop_flags_for_splits init uninit universe drops).
Proof.
  induction drops.
  intros. inv H.
  intros. inv H.
  - simpl. rewrite H2. rewrite H0. rewrite H1.
    exists (fresh_atom p). econstructor. auto.
  - exploit IHdrops; eauto.
    intros (id & IN).
    exists id. simpl.
    destruct (drop_type (typeof_place a)); auto.
    destruct (must_init init uninit universe a); auto.
    destruct (may_init init uninit universe a).
    eapply in_cons; auto. auto.
Qed.

(* If the drop flag of a place is genenrated, the place must not have scalar type *)
Lemma in_generated_drop_flags_not_scalar: forall drops p id init uninit universe,
    In (p, id) (generate_drop_flags_for_splits init uninit universe drops) ->
    drop_type (typeof_place p) = true.
Proof.
  induction drops; simpl; intros. contradiction.
  destruct (place_eq p a); subst.
  - destruct (drop_type (typeof_place a)) eqn: A. auto. eapply IHdrops in H. congruence.
  - destruct (drop_type (typeof_place a)) eqn: A. simpl in *.
    destruct (must_init init uninit universe a) eqn: B. eauto.
    destruct (may_init init uninit universe a) eqn: C. 
    inv H. inv H0. eauto. eauto. eauto. simpl in H. eauto. 
Qed.

    
(** generate_drop_flags searches all the Sdrop statement in the CFG
and then generate drop flags for those are maybe initialized. The
conclusion states that the drop flag map generated by the collected
drop flags is sound, which means that any place not in the flags list
is either must-init or must-uninit. *)
Lemma generate_flag_map_sound: forall mayinitMap mayuninitMap universe ce f cfg flags
    (GEN: generate_drop_flags mayinitMap mayuninitMap universe ce f cfg = OK flags),
    sound_flagm ce f.(fn_body) cfg (generate_place_map flags) mayinitMap mayuninitMap universe.
Proof.
  intros. constructor.
  (* sound_flagm_none *)
  - intros until mayuninit.
    intros SEL STMT SPLIT IN G1 G2 NOTSCALAR.
    unfold generate_drop_flags in GEN.
    destruct list_norepet_dec in GEN; try congruence.
    destruct list_norepet_dec in GEN; try congruence.
    inv GEN.
    set (flags := (PTree.elements
                     (PTree.map
                        (generate_drop_flags_at mayinitMap mayuninitMap universe ce f) cfg))) in *.  
    (* use G1 to prove that p1 is not in the flags list *)
    assert (NOTIN: ~ In p1 (map fst (concat (map snd flags)))).
    { intro.
      exploit generate_place_map_dom.  eauto. 
      intros (id & G). rewrite G in G1. congruence. }
    clear G1.                     (* G1 is useless *)
    (* Prove by contradiction *)
    destruct (must_init mayinit mayuninit universe p1) eqn: MUST; auto.
    destruct (may_init mayinit mayuninit universe p1) eqn: MAY; auto.
    exfalso. apply NOTIN. clear NOTIN.
    (* Now to prove p1 is in the flags using MUST and MAY *)
    inv G2.
    eapply in_map_iff.
    exploit in_drop_flags_for_splits; eauto. intros (id & IN1).
    exists (p1,id). split.
    auto.
    eapply in_concat. eexists.
    split.
    eapply in_map_iff.
    eexists. split.
    2: { unfold flags.
         eapply PTree.elements_correct with (i:=pc).
         erewrite PTree.gmap. rewrite SEL.
         simpl. eauto. }
    simpl. eauto.
    unfold generate_drop_flags_at. rewrite <- H0. rewrite <- H.
    rewrite STMT.
    unfold generate_drop_flags_for. rewrite SPLIT.
    auto.
  (* sound_flagm_some  *)
  - intros p id GET.
    unfold generate_drop_flags in GEN.
    destruct list_norepet_dec in GEN; try congruence.
    destruct list_norepet_dec in GEN; try congruence.
    inv GEN.
    set (flags := (PTree.elements
                     (PTree.map
                        (generate_drop_flags_at mayinitMap mayuninitMap universe ce f) cfg))) in *.
    exploit generate_place_map_in_list. eauto.
    intros IN.
    eapply in_concat in IN.
    destruct IN as (fs & A1 & A2).
    eapply in_map_iff in A1.
    destruct A1 as ((pc & fs1) & A3 & A4). simpl in *. subst.
    exploit PTree.elements_complete. eapply A4. intros B.
    rewrite PTree.gmap in B. destruct (cfg ! pc) eqn: PC.
    2: inv B.
    simpl in B. inv B.
    unfold generate_drop_flags_at in A2.
    (* so many inversion *)
    destruct (mayinitMap !! pc); try inv A2.
    destruct (mayuninitMap !! pc); try inv A2.
    destruct i; try inv A2.
    destruct (select_stmt (fn_body f) s); try inv A2.
    destruct s0; try inv A2.
    unfold generate_drop_flags_for in A2.
    destruct split_drop_place in A2; try inv A2.
    eapply in_generated_drop_flags_not_scalar; eauto.
Qed.

Lemma get_place_map_injective: forall (p1 p2 : place) (id1 id2 : ident) l,
    list_norepet (map snd l) ->
    get_dropflag_temp (generate_place_map l) p1 = Some id1 ->
    get_dropflag_temp (generate_place_map l) p2 = Some id2 ->
    p1 <> p2 ->
    id1 <> id2.
Proof.        
  intros p1 p2 id1 id2 l NOREP G1 G2 NEQ.
  exploit generate_place_map_in_list. eapply G1. intros IN1.
  exploit generate_place_map_in_list. eapply G2. intros IN2.
  intro. subst. 
  exploit in_split. eapply IN1.
  intros (l1 & l2 & A). subst.
  exploit in_elt_inv. eapply IN2. intros [A|B]. inv A. auto.
  rewrite map_app in NOREP. simpl in NOREP.
  replace (id2 :: map snd l2) with ((id2::nil) ++ (map snd l2)) in NOREP by auto.
  eapply list_norepet_append_commut2 in NOREP. rewrite app_assoc in NOREP.
  eapply list_norepet_app in NOREP.
  destruct NOREP as (A1 & A2 & A3).
  rewrite <- map_app in A3.
  eapply A3. eapply in_map. eauto. econstructor. eauto.
  auto.
Qed.

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

Let match_stmt (ae: AN) (flagm: FM) := match_stmt get_init_info ae (elaborate_stmt flagm ce) uncheck_expr.


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
  unfold tge, ge. symmetry. eapply  match_dropm; eauto.
Qed.
  
Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef ce fd = OK tfd -> type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. destruct x2. destruct p.  
  monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
  monadInv EQ3.
  simpl; unfold type_of_function; simpl. auto.
Qed.

Lemma good_fundef_preserved: forall fd tfd,
    transf_fundef ce fd = OK tfd ->
    function_not_drop_glue fd ->
    function_not_drop_glue tfd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. destruct x2. destruct p.
  monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
  monadInv EQ3.
  simpl in *. destruct (fn_drop_glue f); auto.
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
    
    (* used in free_list verification *)
    me_initial:
      Mem.sup_include (Mem.support wm1) lo;
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
      ty = type_bool             
      /\ Mem.range_perm tm b 0 (size_chunk Mint8unsigned) Cur Freeable
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
    Mem.sup_include (Mem.support wm1) lo ->
    Mem.sup_include (Mem.support wm2) tlo ->
    match_envs j empty_env m lo hi empty_env tm tlo thi.
Proof.
  intros.
  constructor; intros.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  erewrite PTree.gempty in *. congruence.
  auto. auto.
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
  intros (TYEQ & A & B). inv INJP.  
  split. auto.
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
  
(* establish match_envs after the allocation of the drop flags in the
target programs *)
Lemma alloc_drop_flags_match: forall (flags: list (place * ident)) j1 m1 tm1 e1 lo hi te1 tlo thi Hm1
    (MENV: match_envs j1 e1 m1 lo hi te1 tm1 tlo thi)
    (SINCR: Mem.sup_include thi (Mem.support tm1))
    (DISJOINT: forall id, In id (map snd flags) -> e1 ! id = None)
    (NOREPEAT:list_norepet (map snd flags)),
  exists te2 tm2 Hm2,
    alloc_variables tge te1 tm1 (combine (map snd flags) (repeat type_bool (length flags))) te2 tm2
    /\ injp_acc (injpw j1 m1 tm1 Hm1) (injpw j1 m1 tm2 Hm2)
    (* wf_dropm *)
    /\ (forall id, (In id (map snd flags)) ->
               exists b, te2 ! id = Some (b, type_bool)
                    /\ e1 ! id = None)
    /\ (forall id, ~ In id (map snd flags)  -> te1 ! id = te2 ! id)
    /\ match_envs j1 e1 m1 lo hi te2 tm2 tlo (Mem.support tm2).
Proof. 
  induction flags; intros. 
  - exists te1, tm1, Hm1. 
    split. econstructor. split; auto.
    reflexivity.
    split. intros. contradiction. 
    inv MENV. split. auto. 
    econstructor; eauto. intros. eapply me_trange0 in H. inv H. eauto.   
  - destruct a as [p id]. simpl in DISJOINT. 
    destruct (Mem.alloc tm1 0 1) as (tm1', b) eqn:ALLOC.
    exploit Mem.alloc_right_inject. eauto. eauto. intros A.
    
    exploit IHflags. 
    (* instantiate (1:= Mem.support tm2).  *)
    instantiate (7:= m1).
    instantiate (3:= tm1').
    instantiate (3:= (PTree.set id (b, type_bool) te1)).
    instantiate (5:= e1).
    instantiate (5:= j1).
    instantiate (1:= Mem.support tm1').
    instantiate (1:= tlo).
    instantiate (1:= hi).
    instantiate (1:= lo). 
    inv MENV.
    econstructor.   
    intros. rewrite PTree.gsspec.
    destruct (peq id0 id).
    (* id0 is in flags *)
    inv e. 
    exploit DISJOINT. left. eauto. 
    intro B. intuition. 
    (* id0 not in flags *)
    eapply me_vars0 in H. destruct H as (tb & C & D). 
    exists tb. split; auto.
    (* me_tinj0 *)
    intros. rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
    destruct (peq id2 id); destruct (peq id1 id). 
    congruence. 
    inv e. inv H0. eapply me_trange0 in H. 
    destruct H. unfold Mem.sup_include in SINCR. apply SINCR in H0.
    eapply Mem.valid_not_valid_diff in H0. eauto. eapply Mem.fresh_block_alloc. eauto.
    inv e. inv H. eapply me_trange0 in H0. destruct H0. eapply SINCR in H0.
    eapply Mem.valid_not_valid_diff in H0. eauto. eapply Mem.fresh_block_alloc. eauto.
    eauto.
    (* range0 *)
    eauto.
    (* trange0 *)
    intros. rewrite PTree.gsspec in H. destruct (peq id0 id) eqn:?.    
    (* eq *)
    inv H.
    split. 
    eapply Mem.fresh_block_alloc in ALLOC.
    unfold Mem.valid_block in ALLOC.
    eapply Mem.sup_include_trans in SINCR. instantiate (1:= tlo) in SINCR.
    unfold not. intros.
    unfold not in ALLOC.
    unfold Mem.sup_include in SINCR. eapply SINCR in H.
    eapply ALLOC in H. auto. auto.
    exploit Mem.support_alloc; eauto. intros.
    eapply Mem.alloc_result in ALLOC. inv ALLOC. rewrite H.
    unfold Mem.nextblock. simpl. left. auto. 
    (*not equal*)
    eapply me_trange0 in H. inv H.
    split. auto. 
    unfold Mem.sup_include in SINCR. apply SINCR in H1.
    exploit Mem.support_alloc; eauto. intros. rewrite H. unfold sup_incr. simpl.
    right. auto.
    (* me_tinitial0 and me_initial *)
    auto. auto.
    (*me_incr0*)
    auto.
    (*me_tincr0*)
    eapply Mem.support_alloc in ALLOC. rewrite ALLOC.
    eapply Mem.sup_include_trans. eauto.
    unfold Mem.sup_include. intros. apply SINCR in H. unfold sup_incr.
    simpl. auto. 
    (* me_protect0 *)
    intros. rewrite PTree.gsspec in H0. destruct (peq id0 id). 
    inv H0. split; auto. simpl. split. unfold Mem.range_perm. intros.
    eapply Mem.perm_alloc_2; eauto.
    (* loc_out_of_reach *)
    unfold loc_out_of_reach.
    intros.
    eapply Mem.fresh_block_alloc in ALLOC. 
    eapply Mem.valid_block_inject_2 in H0; eauto. 
    (* not equal*)
    eapply me_protect0 in H; eauto. destruct H as (TYEQ & C & D).
    split. auto.
    split. simpl.
    simpl in C. simpl.
    unfold Mem.range_perm.
    intros. eapply C in H.
    eapply Mem.perm_alloc_1; eauto.
    (*loc_out_of_reach*)
    eauto.
    apply Mem.sup_include_refl.
    eauto.
    (* no repeat *)
    inv NOREPEAT. auto. 
    (*finish IHflags*)
    (* instantiate (1:= Hm1).  *)
    intros (te2 & tm2 & Hm2 & ALLOC' & INJP & WF & NOTIN & MENV2 ). 
    exists te2. exists tm2. exists Hm2. 
    split. simpl.  econstructor. eauto.  eauto.   
    split. instantiate (1:= A) in INJP. 
    transitivity (injpw j1 m1 tm1' A); eauto.
    inv INJP. 
    econstructor; eauto. 
    eapply Mem.ro_unchanged_alloc in ALLOC. auto.  
    red. intros.  
    eapply Mem.perm_alloc_4; eauto. 
    eapply Mem.fresh_block_alloc in ALLOC. 
    eapply Mem.valid_not_valid_diff; eauto.
    eapply Mem.alloc_unchanged_on. eauto.
    eapply inject_separated_refl. 
    split.
    (* wf_dropm *)
    simpl. intros.
    inv NOREPEAT.
    (* eq *)
    pose proof H. inv H. 
    apply DISJOINT in H0.     
    exists b. 
    split; eauto.
    eapply NOTIN in H2. rewrite PTree.gss in H2. auto.  
    (* not eq *)
    generalize (WF id0). intros.
    eapply H in H1. eapply H1.
    split.
    (* NOTIN *)
    simpl. intros. inv NOREPEAT.
    exploit (NOTIN id0). tauto. intros.
    rewrite PTree.gso in H0. 
    auto. apply Decidable.not_or in H. destruct H. auto. 
    (* match_cases *)
    exact MENV2.
Qed. 

Lemma alloc_variables_support:
  forall ge e m vars e' m',
  alloc_variables ge e m vars e' m' -> Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  induction 1.
  apply Mem.sup_include_refl.
  eapply Mem.sup_include_trans; eauto. exploit Mem.support_alloc; eauto.
  intros EQ. unfold sup_incr in EQ.
  apply Mem.sup_include_trans with (Mem.support m1). rewrite EQ.
  apply Mem.sup_include_refl. apply IHalloc_variables.
Qed.

Lemma alloc_variables_range:
  forall ge id b ty e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ ~sup_In b (Mem.support m) /\ sup_In b (Mem.support m').
Proof.
  induction 1; intros.
  auto.
  exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
  destruct (peq id id0). inv A.
  right. exploit Mem.alloc_result; eauto. exploit Mem.support_alloc; eauto.
  generalize (alloc_variables_support _ _ _ _ _ _ H0). intros A B C.
  subst b. split. apply freshness. eapply Mem.sup_include_trans; eauto. apply Mem.sup_include_refl. rewrite B. apply Mem.sup_incr_in1.  auto.
  right. exploit Mem.support_alloc; eauto. intros B. rewrite B in A.
  destruct A.
  split. intro. apply H2. apply Mem.sup_incr_in2.  auto. auto.
Qed.

Lemma alloc_variables_injective:
  forall ge id1 b1 ty1 id2 b2 ty2 e m vars e' m',
  alloc_variables ge e m vars e' m' ->
  (e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2) ->
  (forall id b ty, e!id = Some(b, ty) -> sup_In b (Mem.support m)) ->
  (e'!id1 = Some(b1, ty1) -> e'!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2).
Proof.
  induction 1; intros.
  eauto.
  eapply IHalloc_variables; eauto.
  repeat rewrite PTree.gsspec; intros.
  destruct (peq id1 id); destruct (peq id2 id).
  congruence.
  inv H6. exploit H2; eauto. intros. 
  apply Mem.valid_not_valid_diff with m b2 b1 in H6. auto.
  apply Mem.fresh_block_alloc in H. auto.
  inv H7. exploit H2; eauto. intros.
  apply Mem.valid_not_valid_diff with m b1 b2 in H7. auto.
  apply Mem.fresh_block_alloc in H. auto.
  eauto.
  intros. rewrite PTree.gsspec in H6. destruct (peq id0 id). inv H6.
  apply Mem.valid_new_block in H. auto.
  exploit H2; eauto. eapply Mem.valid_block_alloc; eauto.
Qed. 

Lemma match_env_alloc:  forall vars m1 tm1 e1 te1  e2 m2  j1 
  (ALLOC: alloc_variables ge e1 m1 vars e2 m2)
  (INJ: Mem.inject j1 m1 tm1)
  (* (INJP: injp_acc w (injpw j1 m1 tm1 INJ)) *)
  (MENV: forall (id : positive) (b : block) (ty : type),
  e1 ! id = Some (b, ty) ->
  exists tb : block, te1 ! id = Some (tb, ty) /\ j1 b = Some (tb, 0))

  (PROTECT: forall (id : positive) (b : block) (ty : type),
  e1 ! id = None ->
  te1 ! id = Some (b, ty) ->
  ty = type_bool
  /\ Mem.range_perm tm1 b 0 (size_chunk Mint8unsigned) Cur Freeable
  /\ (forall ofs : Z, loc_out_of_reach j1 m1 b ofs)),
  exists j2 tm2 te2 Hm2, 
  alloc_variables tge te1 tm1 vars te2 tm2 /\
  Mem.inject j2 m2 tm2 /\
  (forall (id : positive) (b : block) (ty : type),
  e2 ! id = Some (b, ty) ->
  exists tb : block, te2 ! id = Some (tb, ty) /\ j2 b = Some (tb, 0)) 
  /\ injp_acc (injpw j1 m1 tm1 INJ) (injpw j2 m2 tm2 Hm2)
  /\ forall (id : positive) (b : block) (ty : type),
  e2 ! id = None ->
  te2 ! id = Some (b, ty) ->
  ty = type_bool /\
  Mem.range_perm tm2 b 0 (size_chunk Mint8unsigned) Cur Freeable /\
  (forall ofs : Z, loc_out_of_reach j2 m2 b ofs).
Proof. 
  induction vars. 
  - intros. inv ALLOC.  exists j1. exists tm1. exists te1. exists INJ. split.  econstructor. 
    split; auto. split. exact MENV. split. reflexivity. eauto.   
  - intros. inv ALLOC. 
    exploit Mem.alloc_parallel_inject. eauto. eauto. eapply Z.le_refl. 
    rewrite <- comp_env_preserved. eapply Z.le_refl. 
    intros (j1' & m1' & b1' & A & B & C & D & E). 
    exploit injp_acc_alloc. eapply H3. 
    rewrite <- comp_env_preserved. eapply A.
    eauto. eauto. eauto. intros. 
    exploit IHvars. eauto. 
    intros. eauto. intros. 
    instantiate (2 := (PTree.set id (b1', ty) te1)).
    instantiate (1 := j1').
    rewrite PTree.gsspec in H0. 
    rewrite PTree.gsspec. 
    destruct (peq id0 id).  
    inv e. inv H0.
    exists b1'. split. auto.  auto. 
    apply MENV in H0. destruct H0. destruct H0. 
    exists x. split.  auto.  auto.
    (* protect  *)
    instantiate (1 := B) in H. 
    instantiate (1 := INJ) in H. 
    instantiate (1:= m1').
    inv H.
    intros until ty0. intros R S.  
    (* destruct (eq_block b b1'). 
    inv e.  *)
    rewrite PTree.gsspec in R. rewrite PTree.gsspec in S. 
    destruct (peq id0 id). 
    (* id0 eq id *)
    inv R. 
    (* id0 not eq id *)
    eapply PROTECT in S; eauto.
    destruct S as (TYEQ& J & K). split. eauto. split.
    inv H13. 
    (* destruct (eq_block b b1'). *)
    unfold Mem.range_perm in *. intros. 
    generalize (K ofs). intros L. eapply unchanged_on_perm in L. 
    eapply L. eauto. eapply Mem.perm_valid_block. eauto. 
    (* unfold injp_max_perm_decrease in H11. generalize (H11 b1' 0 Freeable). intros.
    unfold Mem.range_perm in *. intros. simpl in J. generalize (J 0). intros. 
    eapply Mem.perm_alloc_2. eauto. simpl in H1.  *)
    intros. eapply loc_out_of_reach_incr; eauto. 
    eapply inject_implies_dom_in. eauto. 
    eapply Mem.perm_valid_block. unfold Mem.range_perm in J. 
    generalize (J 0). intros. simpl in H. exploit H. lia. eauto.     
    intros (j2 & tm2 & te2 & INJ' & ALLOC'  & F & G & I & J). 
    eexists. eexists. eexists. eexists. 
    split. econstructor. eapply A. eapply ALLOC'. split; eauto. 
    split; eauto. 
    (* trans *)
    split. 
    transitivity (injpw j1' m0 m1' B); eauto. 
    eauto.  
Qed. 

    
Lemma alloc_variables_match: forall vars m1 tm1  e2 m2  hi  thi j1 
    (ALLOC: alloc_variables ge empty_env m1 vars e2 m2)
    (INCL: Mem.sup_include hi (Mem.support m1))
    (INJ: Mem.inject j1 m1 tm1)
    (INJP: injp_acc w (injpw j1 m1 tm1 INJ))
    (MENV: match_envs j1 empty_env m1 (Mem.support m1) hi empty_env tm1 (Mem.support tm1) thi)
    (TINCL: Mem.sup_include thi (Mem.support tm1)),
  exists j2 tm2 Hm2 te2,
    alloc_variables tge empty_env tm1 vars te2 tm2
    /\ match_envs j2 e2 m2 (Mem.support m1) (Mem.support m2) te2 tm2 (Mem.support tm1) (Mem.support tm2)
    /\ injp_acc (injpw j1 m1 tm1 INJ) (injpw j2 m2 tm2 Hm2).
Proof.  
    intros. 
    exploit match_env_alloc; eauto. 
    intros. inv H.  intros. instantiate (1:= empty_env) in H0. inv H0.
    intros (j2 & tm2 & te2 & Hm2 & ALLOC' & INJ' & ME & INJP' & PROTECT).
    (* instantiate (1 := empty_env). *)
    exists j2. exists tm2. eexists. exists te2.
    split. eauto. 
    split. econstructor.
    (* same_vars *)
    eapply ME.  
    (* tinj *)
    intros. eapply alloc_variables_injective. 
    eapply ALLOC'. intros. inv H2. intros. inv H2. eauto. eauto. eauto. 
    (* range *)
    intros. exploit alloc_variables_range. exact ALLOC. eauto.
    rewrite PTree.gempty. intuition congruence.
    (* trange *)
    intros. exploit alloc_variables_range. exact ALLOC'. eauto.
    rewrite PTree.gempty. intuition congruence.
    unfold wm1.  destruct w. eapply Mem.unchanged_on_support. inv INJP. eauto.  
    unfold wm2.  destruct w. eapply Mem.unchanged_on_support. inv INJP. eauto.  
    inv INJP. 
    eapply alloc_variables_support. eauto. 
    eapply alloc_variables_support. eauto. 
    inv INJP.  
    (* protect *)
    eauto. 
    (* injp_acc *)
    exact INJP'. 
Qed.


Inductive match_cont (j: meminj) : AN -> FM -> statement -> rustcfg -> cont -> RustIRsem.cont -> cfg_kinfo -> mem -> mem -> sup -> sup -> Prop :=
| match_Kseq: forall an flagm body cfg s ts k tk pc next cont brk nret m tm bound tbound
    (MSTMT: match_stmt an flagm body cfg s ts (mk_cfg_info pc next cont brk nret))
    (MCONT: match_cont j an flagm body cfg k tk (mk_cfg_kinfo next cont brk nret) m tm bound tbound),
    match_cont j an flagm body cfg (Kseq s k) (RustIRsem.Kseq ts tk) (mk_cfg_kinfo pc cont brk nret) m tm bound tbound
| match_Kstop: forall an flagm body cfg nret m tm bound tbound
    (RET: cfg ! nret = Some Iend),
    match_cont j an flagm body cfg Kstop RustIRsem.Kstop (mk_cfg_kinfo nret None None nret) m tm bound tbound
| match_Kloop: forall an flagm body cfg s ts k tk body_start loop_jump_node exit_loop nret contn brk m tm bound tbound
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an flagm body cfg s ts (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (MCONT: match_cont j an flagm body cfg k tk (mk_cfg_kinfo exit_loop contn brk nret) m tm bound tbound),
    match_cont j an flagm body cfg (Kloop s k) (RustIRsem.Kloop ts tk) (mk_cfg_kinfo loop_jump_node (Some loop_jump_node) (Some exit_loop) nret) m tm bound tbound
| match_Kcall: forall an flagm body cfg k tk nret f tf le tle own p m tm bound tbound
    (MSTK: match_stacks j (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) m tm bound tbound)
    (RET: cfg ! nret = Some Iend),
    (* in the end of a function. an and body are not important, those
    in match_stacks are important *)
    match_cont j an flagm body cfg (Kcall p f le own k) (RustIRsem.Kcall (Some p) tf tle tk) (mk_cfg_kinfo nret None None nret) m tm bound tbound
| match_Kdropcall: forall an flagm body cfg k tk pc cont brk nret st membs b tb ofs tofs id m tm bound tbound
    (INJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (MCONT: match_cont j an flagm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m tm bound tbound),
    match_cont j an flagm body cfg (Kdropcall id (Vptr b ofs) st membs k) (RustIRsem.Kdropcall id (Vptr tb tofs) st membs tk) (mk_cfg_kinfo pc cont brk nret) m tm bound tbound
| match_Kdropplace: forall f tf st l k tk e te own1 own2 flagm cfg nret cont brk pc ts1 ts2 m tm lo tlo hi thi maybeInit maybeUninit universe entry mayinit mayuninit
    (** Do we need match_stacks here?  *)
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (RETY: f.(fn_return) = tf.(fn_return))
    (MSTK: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk (mk_cfg_kinfo pc cont brk nret) m tm lo tlo)
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
    match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg (Kdropplace f st l e own1 k) (RustIRsem.Kcall None tf te (RustIRsem.Kseq ts1 (RustIRsem.Kseq ts2 tk))) (mk_cfg_kinfo pc cont brk nret) m tm hi thi

with match_stacks (j: meminj) : cont -> RustIRsem.cont -> mem -> mem -> sup -> sup -> Prop :=
| match_stacks_stop: forall m tm bound tbound,
    match_stacks j Kstop (RustIRsem.Kstop) m tm bound tbound
| match_stacks_call: forall flagm f tf nret cfg pc contn brk k tk own1 own2 p le tle m tm lo tlo hi thi maybeInit maybeUninit universe entry stmt mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (RETY: f.(fn_return) = tf.(fn_return))
    (* callee use stacks hi and thi, so caller f uses lo and tlo*)
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk (mk_cfg_kinfo pc contn brk nret) m tm lo tlo)
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
    (MCONT: match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)
    (INJP: injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2))
    (INCL1: Mem.sup_include lo (Mem.support m1))
    (INCL2: Mem.sup_include tlo (Mem.support tm1)),
    match_cont j2 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m2 tm2 lo tlo.
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
    (MCONT: match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)
    (INCL1: Mem.sup_include lo lo')
    (INCL2: Mem.sup_include tlo tlo'),
    match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo' tlo'.
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

(** It is used in the case that tm1 changes to tm2 by modifying the
drop flags. Only support m1 unchanged: because we cannot ensure that
the out_of_reach block becomes mapped in m1 *)
Lemma match_cont_bound_unchanged: forall k tk j an fm body cfg pc cont brk nret m1 tm1 tm2 lo tlo
   (MCONT:match_cont j an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)   
   (UNC: Mem.unchanged_on (fun b _ => Mem.sup_In b tlo) tm1 tm2),
    match_cont j an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm2 lo tlo.
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
    intros (TYEQ & B1 & B2).
    split. auto.
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
    intros (TYEQ & B1 & B2).
    split. auto.
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    eapply Mem.perm_valid_block; eauto.
    (* out_of_reach *)
    auto.
  - econstructor; eauto.
Qed.

(* generalized version of match_cont_bound_unchanged used in
match_cont after free_list. We do not allow memory expansion because
it would cause some out_of_reach block to be reachable by allocating
some blocks in source memory *)
Lemma match_cont_bound_unchanged_gen: forall k tk j an fm body cfg pc cont brk nret m1 m2 tm1 tm2 lo tlo
   (MCONT:match_cont j an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)
   (MINJ: Mem.inject j m1 tm1)
   (UNC1: Mem.unchanged_on (fun b _ => Mem.sup_In b lo) m1 m2)
   (UNC2: Mem.unchanged_on (fun b _ => Mem.sup_In b tlo) tm1 tm2)
   (* prevent assigning permission to freed block so that makes it
   reachable *)
   (DEC: injp_max_perm_decrease m1 m2)
   (* make sure m1 is larger than lo *)
   (INCL: Mem.sup_include lo (Mem.support m1))
   (* make sure m1 cannot expand *)
   (SUP1: Mem.support m1 = Mem.support m2),
   (* (SUP2: Mem.support tm1 = Mem.support tm2), *)
    match_cont j an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m2 tm2 lo tlo.
Proof.
  induction k; intros; inv MCONT.
  - constructor. auto.
  - econstructor; eauto.
  - econstructor; eauto.
  - inv MSTK.
    econstructor; eauto.
    econstructor; eauto.
    eapply IHk; eauto.
    (* m1 -> m2 *)
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply me_incr. eapply me_envs; eauto. auto.
    (* tm1 -> tm2 *)
    eapply Mem.unchanged_on_implies; eauto.        
    intros. simpl. eapply me_tincr. eapply me_envs; eauto. auto.
    (* sup_include *)
    eapply Mem.sup_include_trans. eapply me_incr. eapply me_envs; eauto. auto.
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
    intros (TYEQ & B1 & B2).
    split. auto.
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    eapply Mem.perm_valid_block; eauto.
    (* out_of_reach *)
    intros. red. intros.
    (* b0 is in lo or not*)
    destruct (Sup.sup_dec b0 lo).
    + intro. eapply B2; eauto. eapply Mem.unchanged_on_perm; eauto.
      eapply INCL. auto.
    + intro. eapply B2; eauto. eapply DEC.
      eapply Mem.perm_valid_block in H2. unfold Mem.valid_block.
      rewrite SUP1. auto. eauto.
  - econstructor; eauto.
    eapply IHk. eauto. eauto.
    (* m1 -> m2 *)
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply me_incr. eapply me_envs; eauto. auto.
    (* tm1 -> tm2 *)
    eapply Mem.unchanged_on_implies; eauto.        
    intros. simpl. eapply me_tincr. eapply me_envs; eauto. auto.
    (* max_perm_decrease *)
    auto.
    (* sup_include *)
    eapply Mem.sup_include_trans. eapply me_incr. eapply me_envs; eauto. auto.
    auto. 
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
    intros (TYEQ & B1 & B2).
    split. auto.
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply me_trange.
    eapply me_envs; eauto. eauto.
    eapply Mem.perm_valid_block; eauto.
    (* out_of_reach *)
    intros. red. intros.
    (* b0 is in lo or not*)
    destruct (Sup.sup_dec b0 lo).
    + intro. eapply B2; eauto. eapply Mem.unchanged_on_perm; eauto.
      eapply INCL. auto.
    + intro. eapply B2; eauto. eapply DEC.
      eapply Mem.perm_valid_block in H2. unfold Mem.valid_block.
      rewrite SUP1. auto. eauto.
  - econstructor; eauto.
Qed.


Inductive match_states : state -> RustIRsem.state -> Prop := 
| match_regular_state:
  forall f s k e own m tf ts tk te tm j flagm maybeInit maybeUninit universe cfg nret cont brk next pc Hm lo tlo hi thi entry mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MSTMT: match_stmt (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg s ts (mk_cfg_info pc next cont brk nret))
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk (mk_cfg_kinfo next cont brk nret) m tm lo tlo)
    (RETY: f.(fn_return) = tf.(fn_return))
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
    (RETY: f.(fn_return) = tf.(fn_return))
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm f.(fn_body) cfg k tk (mk_cfg_kinfo next cont brk nret) m tm lo tlo)
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
    (MCONT: match_cont j (maybeInit, maybeUninit, universe) flagm body cfg k tk (mk_cfg_kinfo next cont brk nret) m tm lo tlo)
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

(** It simulates the dynamic ownership update in step_dropplace. This
property says that dynamically updating the own_env does not break the
invariant between the drop flag map and the ownership status of the
drop places. It is correct if the drop places are ordered in
topological order *)
Inductive wf_split_drop_places flagm (init uninit universe: PathsMap.t) : own_env -> list (place * bool) -> Prop :=
| wf_sdp_nil: forall own,
    wf_split_drop_places flagm init uninit universe own nil
| wf_sdp_flag: forall own b id l p
    (* If this drop place has a drop flag, it must not be scalar type *)
    (FLAG: get_dropflag_temp flagm p = Some id)
    (NOTSCALAR: drop_type (typeof_place p) = true)
    (WF: wf_split_drop_places flagm init uninit universe (if is_init own p then (move_place own p) else own) l),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
| wf_sdp_must: forall own b l p
    (FLAG: get_dropflag_temp flagm p = None)
    (OWN: must_init init uninit universe p = is_init own p)
    (WF: wf_split_drop_places flagm init uninit universe (if is_init own p then (move_place own p) else own) l)
    (NOTSCALAR: drop_type (typeof_place p) = true),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
| wf_sdp_scalar: forall own b l p
    (FLAG: get_dropflag_temp flagm p = None)
    (** We do not need to care about the analysis result for place
    with scalar type because drop p must be compiled to Sskip
    regardless of the analysis result *)
    (* (OWN: must_init init uninit universe p = is_init own p) *)
    (WF: wf_split_drop_places flagm init uninit universe (if is_init own p then (move_place own p) else own) l)
    (NOTSCALAR: drop_type (typeof_place p) = false),
    wf_split_drop_places flagm init uninit universe own ((p,b)::l)
.


(** If the drop places are ordered and the flag map satisfies FLAG and
SCALAR properties, then the drop places are well-formed which means
that the relationship between own_env and the static analysis (init,
uninit, universe) tuple is preserved during updating the own_env in
step_dropplace *)
Lemma ordered_split_drop_places_wf:
  forall drops own init uninit universe flagm
    (ORDER: split_places_ordered (map fst drops))
    (OWN: forall p full, In (p, full) drops ->
                    must_init init uninit universe p = true ->
                    is_init own p = true)
    (NOTOWN: forall p, must_init init uninit universe p = false ->
                  may_init init uninit universe p = false ->
                  is_init own p = false)
    (UNI: PathsMap.eq universe (own_universe own))
    (FLAG: forall p full,
        In (p, full) drops ->
        get_dropflag_temp flagm p = None ->
        drop_type (typeof_place p) = true ->
        must_init init uninit universe p = true
        \/ may_init init uninit universe p = false)
    (SCALAR: forall p id,
        get_dropflag_temp flagm p = Some id ->
        drop_type (typeof_place p) = true),
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
      (* show that p1 is still owned after removing p which is not a *)
(*     parent of p1 from the own_env *)
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
    + intros. eapply FLAG; eauto.
    (* scalar *)
    + eauto. }
  
  (* p has drop flag or not *)
  destruct (get_dropflag_temp flagm p) eqn: PFLAG.
  - econstructor; eauto.
  - destruct (drop_type (typeof_place p)) eqn: SCA.
    + exploit FLAG. left; eauto.
      auto. auto. intros MOWN.
      eapply wf_sdp_must. eauto. 2: auto.
      destruct (must_init init uninit universe p) eqn: MUSTOWN.
      * symmetry. eapply OWN; eauto.
      * destruct MOWN. congruence.
        symmetry. eapply NOTOWN.
        auto. auto.
      * auto.
    + eapply wf_sdp_scalar; eauto.      
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
  (* if p has scalar type *)
  destruct (drop_type (typeof_place p)) eqn: SCA.
  - destruct (get_dropflag_temp flagm p) eqn: FLAG.
    + econstructor. auto.
      eapply IHdrops.
      inv WFDROPS; try congruence.
      auto.
    + inv WFDROPS; try congruence.
      destruct (must_init init uninit universe p) eqn: MUST.
      (* must_owned = true *)
      * rewrite <- OWN in WF.
        econstructor; auto.
      (* must_owned = false *)
      * rewrite <- OWN in WF.
        econstructor; auto.
  - inv WFDROPS; try congruence.
    destruct (is_init own p) eqn: INIT.
    + eapply match_sdp_cons_scalar; eauto.
    + eapply match_sdp_cons_must_uninit; eauto.
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
  
Lemma drop_box_rec_injp_acc: forall tyl m1 m2 tm1 j Hm b ofs tb tofs ge tge
        (DROP: drop_box_rec ge b ofs m1 tyl m2)
        (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)),
      exists tj tm2 tHm,
        drop_box_rec tge tb tofs tm1 tyl tm2
        /\ injp_acc (injpw j m1 tm1 Hm) (injpw tj m2 tm2 tHm).
Proof.
  induction tyl. 
  - simpl. intros.  inv DROP. inv VINJ. simpl. exists j. exists tm1. exists Hm.
    split. econstructor. reflexivity. 
  - simpl.
    intros. inv DROP.
    exploit deref_loc_rec_inject; eauto.
    intros (tv & A & B).
    inv B.
    exploit deref_loc_inject; eauto.
    intros (tv & B1 & B2). inv B2.
    exploit extcall_free_injp. eauto. instantiate (2:=j). eauto.
    intros (tm' & Hm' & C & D).
    exploit IHtyl; eauto.
    intros (tj' & tm2' & tHm' & E & F).
    exists tj'. exists tm2'. exists tHm'. split; eauto. econstructor; eauto.
    transitivity  (injpw j m0 tm' Hm'); eauto. 
Qed.


Lemma eval_pexpr_inject:
  forall e le m v tm tle own lo hi flagm tlo thi j
    (EVAL: eval_pexpr ge le m ge e v)
    (MSENV: Genv.match_stbls j se tse)
    (MINJ: Mem.inject j m tm)
    (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
    exists tv, eval_pexpr tge tle tm tge e tv /\ Val.inject j v tv.
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
  - edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB); eauto.
    exploit deref_loc_inject; eauto.
    intros (tv' & TDEF & VINJ).
    rewrite Ptrofs.add_zero_l in TDEF.
    exists tv'. split; eauto.
    econstructor; eauto.        
Qed. 


Lemma eval_expr_inject: forall e le m v tm tle own lo hi flagm tlo thi j
        (EVAL: eval_expr ge le m ge e v)
        (MSENV: Genv.match_stbls j se tse)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tv, eval_expr tge tle tm tge e tv /\ Val.inject j v tv.
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
        (EVAL: eval_exprlist ge le m ge args tyl vl)
        (MSENV: Genv.match_stbls j se tse)
        (MINJ: Mem.inject j m tm)
        (MENV: match_envs_flagm j own le m lo hi tle flagm tm tlo thi),
        exists tvl, eval_exprlist tge tle tm tge args tyl tvl /\ Val.inject_list j vl tvl.
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
Proof.
    induction 1.
    simpl in H0. eapply Mem.support_store; eauto.
    eapply Mem.support_storebytes; eauto.
Qed.
  

Lemma assign_loc_max_perm:
  forall ge ty m loc ofs  v m',
    assign_loc ge ty m loc ofs  v m' ->
    injp_max_perm_decrease m m'.
Proof.
  intros. inv H; red; intros; eauto with mem.
Qed.

Lemma alignof_blockcopy_1248: forall ty ofs,
  access_mode ty = By_copy
  -> sizeof ge ty > 0 -> (alignof_blockcopy ge ty | Ptrofs.unsigned ofs)
  -> (alignof_blockcopy tge  ty | Ptrofs.unsigned ofs). 
Proof. 
  intros. rewrite  comp_env_preserved. eauto. 
Qed. 


Lemma assign_loc_unchanged_on:
  forall ge ty m b ofs v m',
    assign_loc ge ty m b ofs v m' ->
    Mem.unchanged_on (fun b' ofs => b <> b') m m'.
Proof.
  intros. inv H.
  - (*storev*)
    eapply Mem.store_unchanged_on; eauto.
  - eapply Mem.storebytes_unchanged_on; eauto.
Qed.

Lemma assign_loc_ro:
  forall ge ty m b ofs v m',
    assign_loc ge ty m b ofs v m' ->
    Mem.ro_unchanged m m'.
Proof.
  intros. inv H.
  - simpl in H1. eapply Mem.ro_unchanged_store; eauto.
  - eapply Mem.ro_unchanged_storebytes; eauto.
Qed.


  
Lemma assign_loc_injp_acc: forall f ty m loc ofs v m' tm loc' ofs' v' Hm,
  assign_loc ge ty m loc ofs v m' ->
  Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  Val.inject f v v' ->
  exists tm' Hm',
    assign_loc tge ty tm loc' ofs' v' tm'
    /\ injp_acc (injpw f m tm Hm) (injpw f m' tm' Hm').
Proof. 
  induction 1; intros.  
  - exploit Mem.storev_mapped_inject; eauto. intros (tm' & A & B). 
    exploit injp_acc_storev. eapply H0. exact A. exact H1. exact H2. 
    intros. 
    exists tm'. exists B. split. eapply assign_loc_value; eauto. 
    eapply H3.
  - inv H6. inv H7. 
    rename b' into bsrc. rename ofs'0 into osrc. 
    rename loc into bdst. rename ofs into odst.
    rename loc' into bdst'. rename b2 into bsrc'. 
    rewrite <- comp_env_preserved in *.
    destruct (zeq (sizeof tge ty) 0). 
    + assert (bytes = nil).
    { exploit (Mem.loadbytes_empty m bsrc (Ptrofs.unsigned osrc) (sizeof tge ty)).
      lia. congruence. }
    subst.
    destruct (Mem.range_perm_storebytes tm bdst' (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta))) nil)
    as [tm' SB].
    simpl. red; intros; extlia.
    exploit Mem.storebytes_empty_inject; eauto. 
    intro TMINJ. 
    exists tm'. exists TMINJ.
    split. eapply assign_loc_copy; eauto.
    intros. destruct ty; simpl in *; try lia.  
    intros; extlia.  
    intros; extlia. 
    (* rewrite e.  *)
    apply Mem.loadbytes_empty. lia.
    (* injp *)
    econstructor. 
    eapply Mem.ro_unchanged_storebytes; eauto.
    eapply Mem.ro_unchanged_storebytes; eauto.
    red. intros. eauto with mem. 
    red. intros. eauto with mem. 
    eapply Mem.storebytes_unchanged_on. eauto.  intros.
    simpl in *. extlia.  
    eapply Mem.storebytes_unchanged_on. eauto.  intros.
    simpl in *. extlia.  
    eauto. econstructor; rewrite H7 in H6; inv H6. 
    (* inj_incr
    econstructor. eauto. unfold inject_incr_disjoint. intros. 
    rewrite H6 in H7. inv H7. 
    exploit Mem.support_storebytes. eapply H5. congruence.
    exploit Mem.support_storebytes. eapply SB. congruence. *)

  + rewrite  comp_env_preserved in *.
    exploit Mem.loadbytes_length. eauto. intro LEN. 
    assert (SZPOS: sizeof ge ty > 0). 
    {generalize (sizeof_pos ge ty). lia. }
    assert (RPSRC: Mem.range_perm m bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sizeof ge ty) Cur Nonempty).
      eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm. eauto. auto with mem. 
    assert (RPDST: Mem.range_perm m bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sizeof ge ty) Cur Nonempty).
      replace (sizeof ge ty) with (Z.of_nat (List.length bytes)).
      eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm. eauto. eauto with mem.   
      rewrite LEN. apply Z2Nat.id. lia.
    assert (PSRC: Mem.perm m bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
      apply RPSRC. lia. 
    assert (PDST: Mem.perm m bdst (Ptrofs.unsigned odst) Cur Nonempty).
      apply RPDST. lia.
    exploit Mem.address_inject.  eauto. eapply PSRC.  eauto. intros EQ1.
    exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
    exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
    exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
    exists tm'. exists D.
    split. eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto. 
    intros; eapply Mem.aligned_area_inject with (m := m); eauto.
    apply Rusttypes.alignof_blockcopy_1248.
    apply Rusttypes.sizeof_alignof_blockcopy_compat. 
    (* rewrite <- comp_env_preserved.  *)
    intros; eapply Mem.aligned_area_inject with (m := m); eauto.
    apply Rusttypes.alignof_blockcopy_1248.
    apply sizeof_alignof_blockcopy_compat.
    eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
    apply Mem.range_perm_max with Cur; auto.
    apply Mem.range_perm_max with Cur; auto.
    (* injp *)
    econstructor. 
    eapply Mem.ro_unchanged_storebytes; eauto.
    eapply Mem.ro_unchanged_storebytes; eauto.
    red. intros. eauto with mem. 
    red. intros. eauto with mem. 
    eapply Mem.storebytes_unchanged_on; eauto.  intros.
    simpl in *. unfold loc_unmapped. congruence.  
    eapply Mem.storebytes_unchanged_on; eauto.  
    unfold loc_out_of_reach.  
    intros ofs Kofs K.
    eelim K; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.storebytes_range_perm; eauto. 
    apply list_forall2_length in B. extlia. 
    apply inject_incr_refl.
    apply inject_separated_refl.
Qed.


Lemma bind_parameters_injp_acc: forall params vl e te m1 m2  tvl j tm1 Hm1
    (STORE: bind_parameters ge e m1 params vl m2)
    (me_vars0: forall (id : positive) (b : block) (ty : type), e ! id = Some (b, ty) -> exists tb : block, te ! id = Some (tb, ty) /\ j b = Some (tb, 0))
    (VINJS: Val.inject_list j vl tvl),
  exists tm2 Hm2,
    bind_parameters tge te tm1 params tvl tm2
    /\ injp_acc (injpw j m1 tm1 Hm1) (injpw j m2 tm2 Hm2).
Proof. 
  intros. revert me_vars0. revert VINJS. revert tvl. revert Hm1.
  revert j tm1 te.   
  induction STORE; intros.
  - exists tm1. exists Hm1. inv VINJS. split. econstructor. reflexivity. 
  - inv VINJS. 
    eapply me_vars0 in H. destruct H as (tb & C & D). 
    exploit assign_loc_injp_acc; eauto. 
    instantiate (1:= Hm1).
    intros (tm2 & Hm2 & A & B).
    exploit IHSTORE. eauto. intros. eapply me_vars0 in H. eauto. 
    intros (tm3 & Hm3 & E & F). 
    eexists. eexists. split. econstructor; eauto. 
    instantiate (1:= Hm3).
    transitivity (injpw j m1 tm2 Hm2); eauto.
Qed. 


Lemma type_to_drop_member_state_eq: forall id ty,
    type_to_drop_member_state ge id ty = type_to_drop_member_state tge id ty.
Proof.
  intros. unfold type_to_drop_member_state.
  (* erewrite comp_env_preserved; eauto. auto. *)
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
   (STMT: init_drop_flag init uninit universe p id = OK stmt)
   (OWN: sound_own own init uninit universe),
   (* (IN: Paths.In p (PathsMap.get (local_of_place p) universe)), *)
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
  destruct (must_init init uninit universe p) eqn: MUST.
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
  - destruct (may_init init uninit universe p) eqn: MAY; try congruence.
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
  (STMT: init_drop_flags init uninit universe flags = OK init_stmt)
  (OWN: sound_own own init uninit universe)
  (MINJ: Mem.inject j1 m1 tm1)
  (WF: forall p id, In (p, id) flags ->
               exists tb, te ! id = Some (tb, type_bool)
                       /\ e ! id = None)
  (MENV: match_envs j1 e m1 lo hi te tm1 tlo thi)
  (* we require that te is injective *)
  (INJ: forall id1 b1 ty1 id2 b2 ty2, te!id1 = Some(b1, ty1) -> te!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2)
  (* idents in flags are norepet *)
  (NOREPET: list_norepet (map snd flags)),
  (* (INUNI: forall p, In p (map fst flags) -> Paths.In p (PathsMap.get (local_of_place p) universe)), *)
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
    intros (TYEQ& PERM & REACH). 
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
    intros (TYEQ1 & PERM1 & REACH1). split; auto. split; auto.
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


(* Evaluate the statements of setting the drop flags for the split
places (the split places are generated for the re-assignment). The
important point here is that we need to ensure that the drop flags not
related the drops are unchanged. *)
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
              (* proved by split_complete. If this place is not in the
              drops which means that it has been updated or it is
              unrelated to drops. *)
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
        intros (TYEQ & D1 & D2).
        split; auto. split; auto.
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


(** important: it performs the evaluation of the statement generated
by add_dropflag whichs sets the drop flag for the place. The
conclusion includes some helpful result of the evaluation, such as
unchanged_on and ro_acc *)
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
    (* p0 not in drops (two cases: 1. p0 is not generated by
    split_drop_place (but think about p0 has drop flag!!!) or 2. p is
    just unrealted to p) so modify the ownership of drops does not
    change the ownership of p0 *)
    intros. rewrite A4. symmetry.
    destruct (is_init own1 p0) eqn: INIT.
    - destruct flag.
      + eapply init_owned_place_still_owned. auto.
      + eapply move_irrelavent_place_still_owned.
        auto.
        (* prove is_prefix p p0 by split_complete (is it correct?), we
        can prove p0 is own_type (added property for
        get_dropflag_temp) and then weaken the split_complete to make
        it only be satisfied when the place has own_type *)
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
  (ORDERED:  forall p', is_prefix p p' = true -> p <> p' -> is_init own p' = false)
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
    destruct (is_prefix p p0) eqn: PRE.
    -- eapply ORDERED in PRE. rewrite C4. rewrite PRE.
       symmetry. eapply move_place_still_not_owned. auto. auto.
    -- destruct (is_init own p0) eqn: OWNP.
       ++ rewrite C4. symmetry.
          eapply move_irrelavent_place_still_owned. auto.
          (** IMPORTANT TODO: is_prefix_strict false and neq imply is_prefix false *)
          eapply not_true_iff_false. intro.
          eapply not_true_iff_false in PRE. apply PRE.
          eapply is_prefix_strict_implies; auto.
       ++ rewrite C4. symmetry.
          eapply move_place_still_not_owned. auto.
  * eapply me_flagm_inj. eauto.
  * inv MENV. inv me_envs0.
    econstructor; eauto.
    intros. exploit me_protect0; eauto.
    intros (TYEQ & A & B). split; auto. split; auto.
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
(ORDERED:  forall p', is_prefix p p' = true -> p <> p' -> is_init own p' = false),
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
    destruct (is_prefix p p0) eqn: PRE.
    -- eapply ORDERED in PRE. rewrite C4. rewrite PRE.
       symmetry. eapply move_place_still_not_owned. auto. auto.
    -- destruct (is_init own p0) eqn: OWNP.
       ++ rewrite C4. symmetry.
          eapply move_irrelavent_place_still_owned. auto.
          (** IMPORTANT TODO: is_prefix_strict false and neq imply is_prefix false *)
          eapply not_true_iff_false. intro.
          eapply not_true_iff_false in PRE. apply PRE.
          eapply is_prefix_strict_implies; auto.
       ++ rewrite C4. symmetry.
          eapply move_place_still_not_owned. auto.
  * eapply me_flagm_inj. eauto.
  * inv MENV. inv me_envs0.
    econstructor; eauto.
Qed.


Lemma pair_snd_in: forall (A B: Type) (a: A) (b: B) (l: list (A * B)),
    In (a, b) l -> In b (map snd l).
Proof.
  induction l; simpl; intros.
  - inv H.
  - destruct a0. simpl in H. destruct H.
    + inv H. simpl. auto.
    + simpl. right. eapply IHl. eauto.
Qed.


Lemma blocks_of_env_translated:
forall e, blocks_of_env tge e = blocks_of_env ge e.
Proof.
intros. unfold blocks_of_env, block_of_binding.
rewrite comp_env_preserved; auto.
Qed.


(** [match_cont] and freeing of environment blocks *)

Fixpoint freelist_no_overlap (l: list (block * Z * Z)) : Prop :=
match l with
| nil => True
| (b, lo, hi) :: l' =>
    freelist_no_overlap l' /\
    (forall b' lo' hi', In (b', lo', hi') l' ->
     b' <> b \/ hi' <= lo \/ hi <= lo')
end.


Lemma can_free_list:
  forall l m,
    (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
    freelist_no_overlap l ->
    exists m', Mem.free_list m l = Some m'.
Proof.
  induction l; simpl; intros.
  - exists m; auto.
  - destruct a as [[b lo] hi]. destruct H0.
    destruct (Mem.range_perm_free m b lo hi) as [m1 A]; auto.
    rewrite A. apply IHl; auto.
    intros. red. intros. eapply Mem.perm_free_1; eauto.
    exploit H1; eauto. intros [B|B]. auto. right; lia.
    eapply H; eauto.
Qed.

Lemma free_list_freeable:
  forall l m m',
    Mem.free_list m l = Some m' ->
    forall b lo hi,
      In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H.
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.


Lemma free_list_perm':
  forall b lo hi l m m',
    Mem.free_list m l = Some m' ->
    In (b, lo, hi) l ->
    Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a as [[b1 lo1] hi1].
  destruct (Mem.free m b1 lo1 hi1) as [m1|] eqn:?; try discriminate.
  destruct H0. inv H0. eapply Mem.free_range_perm; eauto.
  red; intros. eapply Mem.perm_free_3; eauto. eapply IHl; eauto.
Qed.

Lemma free_blocks_of_env_perm_1:
  forall ce m e m' id b ty ofs k p,
  Mem.free_list m (blocks_of_env ce e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.perm m' b ofs k p ->
  0 <= ofs < sizeof ce ty ->
  False.
Proof.
  intros. exploit Mem.perm_free_list; eauto. intros [A B].
  apply B with 0 (sizeof ce0 ty); auto.
  unfold blocks_of_env. change (b, 0, sizeof ce0 ty) with (block_of_binding ce0 (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma free_blocks_of_env_perm_2:
  forall m e m' id b ty,
    Mem.free_list m (blocks_of_env ce e) = Some m' ->
    e!id = Some(b, ty) ->
    Mem.range_perm m b 0 (sizeof ce ty) Cur Freeable.
Proof.
  intros. eapply free_list_perm'; eauto.
  unfold blocks_of_env. change (b, 0, sizeof ce ty) with (block_of_binding ce (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma blocks_of_env_in_list: forall b lo hi e ce,
    In (b, lo, hi) (blocks_of_env ce e) ->
    exists id ty, e ! id = Some (b, ty)
             /\ sizeof ce ty = hi - lo.
Proof.
  intros. unfold blocks_of_env in *.
  eapply in_map_iff in H. destruct H as ((id & (b1 & ty)) & A1 & A2).
  simpl in A1. inv A1.
  exists id, ty. split.
  eapply PTree.elements_complete. auto.
  symmetry. apply Z.sub_0_r.
Qed.

(* also prove lo is zero *)
Lemma blocks_of_env_in_list1: forall b lo hi e ce,
    In (b, lo, hi) (blocks_of_env ce e) ->
    exists id ty, e ! id = Some (b, ty)
             /\ lo = 0
             /\ sizeof ce ty = hi.
Proof.
  intros. unfold blocks_of_env in *.
  eapply in_map_iff in H. destruct H as ((id & (b1 & ty)) & A1 & A2).
  simpl in A1. inv A1.
  exists id, ty. split.
  eapply PTree.elements_complete. auto.
  auto.
Qed.


Lemma blocks_of_env_no_overlap:
  forall (ge: genv) j m e lo hi te tlo thi m' tm,
    match_envs j e m lo hi te m' tlo thi ->
    Mem.inject j m tm ->
    (* (forall id b ty,
 e!id = Some(b, ty) -> Mem.range_perm m b 0 (sizeof ge ty) Cur Freeable) -> *)
    forall l,
      list_norepet (List.map fst l) ->
      (forall id bty, In (id, bty) l -> te!id = Some bty) ->
      freelist_no_overlap (map (block_of_binding ge) l).
Proof.
  intros until tm; intros ME MINJ. induction l; simpl; intros.
- auto.
- destruct a as [id [b ty]]. simpl in *. inv H. split.
  + apply IHl; auto.
  + intros. exploit list_in_map_inv; eauto. intros [[id' [b'' ty']] [A B]].
    simpl in A. inv A. rename b'' into b'.
    assert (IDNEQ: id <> id').
    { intro. subst. eapply H3. eapply in_map_iff.
      exists (id', (b',ty')). auto. }    
    assert (TE: te!id = Some(b, ty)). eauto. 
    assert (TE': te!id' = Some(b', ty')) by eauto.
    left.
    eapply me_tinj; eauto.  
Qed.

Lemma blocks_of_env_dom: forall e id b ty ge,
    e ! id = Some (b, ty) ->
    In (b, 0, sizeof ge ty) (blocks_of_env ge e).
Proof.
  intros. unfold blocks_of_env.
  eapply PTree.elements_correct in H.
  eapply in_map_iff.
  exists (id, (b, ty)). simpl. auto.
Qed.

(* match_envs j e m lo hi te tm tlo thi *)
Theorem match_envs_free_blocks:
  forall j e m lo hi te tlo thi m' tm,
    match_envs j e m lo hi te tm tlo thi ->
    Mem.inject j m tm ->
    Mem.free_list m (blocks_of_env ge e) = Some m' ->
    exists tm',
      Mem.free_list tm (blocks_of_env tge te) = Some tm'
      /\ Mem.inject j m' tm'.
Proof.
  intros until tm. 
  intros ME INJ FREE. 
  assert (X: exists tm', Mem.free_list tm (blocks_of_env tge te) = Some tm'). 
  {
    rewrite blocks_of_env_translated. eapply can_free_list. 
    (* prove every block in the free list is freeable *)
    - intros. exploit blocks_of_env_in_list1. eauto.
      intros (id & ty & A1 & A2 & A3). subst.
      (* two cases *)
      destruct (e ! id) as [(b1 & ty1)| ] eqn: F.
      + exploit me_vars; eauto.
        intros (tb & A3 & A4). rewrite A1 in A3. inv A3.
        replace 0 with (0 + 0) by lia.
        replace (sizeof ge ty1) with ((sizeof ge ty1)+ 0) by lia.
        eapply Mem.range_perm_inject; eauto.
        eapply free_blocks_of_env_perm_2; eauto.
      (* e!id = None *)
      + exploit me_protect; eauto.
        intros (TYEQ & B1 & B2). subst. simpl in *.
        auto.
    (* prove the free list is no overlap *)
    - eapply blocks_of_env_no_overlap; eauto.
      eapply PTree.elements_keys_norepet.
      intros. eapply PTree.elements_complete. auto.
  }  
  destruct X as [tm' TFREE].
  exists tm'; split; auto.
  eapply SimplLocalsproof.free_list_right_inject; eauto.
  eapply Mem.free_list_left_inject; eauto.
  (* The condition of free_list_left_inject: free block has no
  permission, which is not easy *)
  intros. exploit blocks_of_env_in_list1; eauto.
  intros (id & ty & A1 & A2 & A3). subst.
  destruct (e!id) as [(b & ty1)| ] eqn: F.
  + exploit me_vars; eauto. intros (tb2 & C1 & C2).
    rewrite A1 in C1. inv C1.
    (* b is equal to b1 or not *)
    destruct (eq_block b b1).
    * subst. rewrite H in C2. inv C2.
      eapply free_blocks_of_env_perm_1 with (m:=m); eauto.
      erewrite <- comp_env_preserved. lia.
    (* b <> b1 which is impossible *)
    * exploit Mem.inject_no_overlap. eauto.
      eapply n. eauto. eauto.
      instantiate (1 := ofs + delta).
      (* prove permission of freed block *)
      exploit blocks_of_env_dom; eauto. instantiate (1 := ge).
      intros IN.    
      exploit free_list_perm'. eapply FREE. eauto.
      rewrite <- comp_env_preserved. eauto.
      intros. eapply Mem.perm_cur_max.
      eapply Mem.perm_implies. eauto. econstructor.
      (* b1 in m has permission *)
      instantiate (1 := ofs).
      eapply Mem.perm_max. eapply Mem.perm_free_list. eauto.
      eapply Mem.perm_implies. eauto. eapply perm_any_N.
      (* contradiction *)
      intros. rewrite Z.add_0_r in H3. destruct H3; congruence.
  (* e!id = None. b1 is out_of_reach *)
  + exploit me_protect; eauto.
    intros (B1 & B2 & B3). eapply B3; eauto.
    instantiate (1 := ofs + delta).
    replace (ofs + delta - delta) with ofs by lia.
    eapply SimplLocalsproof.free_list_max_perm. eauto.
    (* prove b1 is valid block *)
    eapply Mem.perm_valid_block in H1. red.
    erewrite <- SimplLocalsproof.free_list_support. eauto. eauto.
    (* perm *)
    eapply Mem.perm_max. eapply Mem.perm_implies; eauto.
    eapply perm_any_N.
Qed.

Lemma injp_acc_free_list: forall m1 m2 le tle tm1 tm2 j Hm1 Hm2 lo hi tlo thi
  (FREE1: Mem.free_list m1 (blocks_of_env ge le) = Some m2)
  (FREE2: Mem.free_list tm1 (blocks_of_env tge tle) = Some tm2)
  (INJP: injp_acc w (injpw j m1 tm1 Hm1))
  (MENV: match_envs j le m1 lo hi tle tm1 tlo thi),
    injp_acc w (injpw j m2 tm2 Hm2).
Proof.
  intros. destruct w eqn: Hw. 
  eapply SimplLocalsproof.injp_acc_local; eauto.
  - eapply Mem.ro_unchanged_free_list; eauto.
  - eapply Mem.ro_unchanged_free_list; eauto.
  - eapply SimplLocalsproof.free_list_max_perm; eauto.
  - eapply SimplLocalsproof.free_list_max_perm; eauto.
  - inv INJP. auto.
  - eapply Mem.unchanged_on_implies.
    eapply SimplLocalsproof.free_list_unchanged_on; eauto.
    instantiate (1 := fun b => Mem.valid_block m0 b).
    simpl. intros.
    exploit blocks_of_env_in_list; eauto.
    intros (id & ty & A1 & A2).
    (* b in le so b must not valid in m0 *)
    intro. 
    eapply me_range; eauto. eapply me_initial. eauto.
    unfold wm1. rewrite Hw. auto.
    intuition.
  - eapply Mem.unchanged_on_implies.
    eapply SimplLocalsproof.free_list_unchanged_on; eauto.
    instantiate (1 := fun b => Mem.valid_block m3 b).
    simpl. intros.
    exploit blocks_of_env_in_list; eauto.
    intros (id & ty & A1 & A2).
    (* b in le so b must not valid in m3 *)
    intro. 
    eapply me_trange; eauto. eapply me_tinitial. eauto.
    unfold wm2. rewrite Hw. auto.
    intuition.
Qed.

(* free_list preserves match_cont *)
Lemma match_cont_free_env: forall k tk j1 own le tle m1 m2 lo hi flagm tm1 tm2 tlo thi an fm body cfg pc cont brk nret
    (MENV: match_envs_flagm j1 own le m1 lo hi tle flagm tm1 tlo thi)
    (MCONT: match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)
    (INCL1: Mem.sup_include hi (Mem.support m1))
    (* (INCL2: Mem.sup_include thi (Mem.support tm1)) *)
    (MINJ: Mem.inject j1 m1 tm1)
    (FREE1: Mem.free_list m1 (blocks_of_env ge le) = Some m2)
    (FREE2: Mem.free_list tm1 (blocks_of_env tge tle) = Some tm2),
    match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m2 tm2 lo tlo
.
Proof.
  intros.
  eapply match_cont_bound_unchanged_gen. eauto. eauto.
  (* prove lo and tlo unchanged *)
  (* m1 -> m2 *)
  eapply Mem.unchanged_on_implies.
  eapply SimplLocalsproof.free_list_unchanged_on; eauto.
  instantiate (1 := fun b => Mem.sup_In b lo). intros.
  exploit blocks_of_env_in_list; eauto. intros (id & ty & A1 & A2).
  simpl. eapply me_range; eauto. eapply me_envs; eauto.
  simpl. auto.
  (* tm1 -> tm2 *)
  eapply Mem.unchanged_on_implies.
  eapply SimplLocalsproof.free_list_unchanged_on; eauto.
  instantiate (1 := fun b => Mem.sup_In b tlo). intros.
  exploit blocks_of_env_in_list; eauto. intros (id & ty & A1 & A2).
  simpl. eapply me_trange; eauto. eapply me_envs; eauto.
  simpl. auto.
  (* max_perm_decrease *)
  eapply SimplLocalsproof.free_list_max_perm. eauto.
  eapply Mem.sup_include_trans. eapply me_incr. eapply me_envs; eauto.
  auto.
  symmetry. eapply SimplLocalsproof.free_list_support. eauto.
Qed.

(* used in return step *)
Lemma match_cont_call_cont: forall k ck tk j1 an fm body cfg pc cont brk nret m1 tm1 lo tlo
    (MCONT: match_cont j1 an fm body cfg k tk (mk_cfg_kinfo pc cont brk nret) m1 tm1 lo tlo)
    (CCONT: call_cont k = Some ck),
  exists tck,
    RustIRsem.call_cont tk = Some tck /\
      match_stacks j1 ck tck m1 tm1 lo tlo.
Proof.
  induction k; intros; simpl; inv CCONT; inv MCONT; simpl.
  - eexists. split; eauto. econstructor.
  - exploit IHk; eauto.
  - exploit IHk; eauto.
  - inv MSTK. eexists. split; eauto.
    econstructor; eauto.
Qed.

(* gen_drop_place_state in simulation and drop_fully_own in compilation match *)
Lemma gen_drop_place_state_match: forall p,
    match_drop_place_state (Some (gen_drop_place_state p)) (drop_fully_own p).
Proof.
  intros.
  unfold gen_drop_place_state, drop_fully_own.
  destruct (split_fully_own_place p (typeof_place p)) eqn: SPLIT.
  econstructor.
  destruct (typeof_place p0) eqn: TYP; try econstructor.
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
    (**  cases of skipping this drop: one is must uninit and the
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
    + congruence.
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
      eauto. eauto. intros (TYEQ & PERM & REACH).
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
      econstructor. eauto. auto.
      (* match_cont *)
      eapply match_cont_bound_unchanged. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. intro. subst.
      eapply me_trange. eapply me_envs; eauto. eauto. auto.
      (** TODO: match_drop_place_state and gen_drop_place_state *)
      destruct full.
      eapply gen_drop_place_state_match.
      econstructor.
      (* match_split_drop_places *)
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
      simpl. destruct full.
      eapply gen_drop_place_state_match.
      econstructor.
      (** move out a place which does not have drop flag has no
      effect on match_envs_flagm *)
      eapply match_envs_flagm_move_no_flag_place; eauto.
      (* sound_own *)
      simpl in OWN0.
      rewrite OWN in OWN0. auto.
    + congruence.
    + congruence.
  (* step_dropplace_scalar *)
  - inv MDPS. inv ORDERED.
    inv MSPLIT; try congruence.
    eexists. split.
    econstructor. eapply RustIRsem.step_skip_seq.
    eapply star_step. econstructor.
    eapply star_refl. 1-2: eauto.
    econstructor; eauto. econstructor.
    rewrite OWN1 in MORD. auto.
    eapply match_envs_flagm_move_no_flag_place; eauto.
    (* prove by sound_flagm_some *)
    destruct (get_dropflag_temp flagm p) eqn: A; auto.
    eapply sound_flagm_some in A; eauto. congruence.
    (* sound_own *)
    simpl in OWN0.
    rewrite OWN in OWN0. auto.    
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
Qed.


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
  - inv VINJ.
    exploit deref_loc_rec_inject; eauto.
    intros (tv & DEREF1 & VINJ1). inv VINJ1.
    exploit Mem.loadv_inject; eauto.
    intros (v2 & TAG2 & VINJ2). inv VINJ2.
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
    erewrite <- type_to_drop_member_state_eq.
    econstructor. econstructor.
    econstructor; eauto.
    eauto. eauto.
    econstructor; eauto.
    auto. auto.    
  (* step_dropstate_box *)
  - inv VINJ.
    exploit (drop_box_rec_injp_acc tys m m' tm); eauto.
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
Qed.


Lemma map_split_l {A B: Type} : forall (l: list (A*B)),
    map fst l = fst (split l).
Proof.
  induction l; simpl; intros; auto.
  destruct a. destruct (split l) eqn: S.
  simpl in *. f_equal. auto.
Qed.  


Lemma injp_acc_globalenv:
  forall f m tm Hm,
  injp_acc w (injpw f m tm Hm)->
  Genv.match_stbls f se tse.
Proof.
  intros.
  simpl in GE.
  destruct w. inv GE.
  inv H.
  eapply Genv.match_stbls_incr; eauto.
  intros. exploit H16; eauto. 
  intros (A & B). split; eauto.
  intro. eapply A. eapply H6. auto.
  intro. eapply B. eapply H7. auto.
Qed.

Hint Resolve injp_acc_globalenv: matsym.

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
    exploit eval_expr_inject; eauto with matsym.
    intros (tv & EXPR & VINJ).
    exploit eval_place_inject; eauto.
    intros (tb & tofs & EVALP & VINJ1).
    exploit sem_cast_inject; eauto.
    intros (tv1 & CAST1 & VINJ2).
    exploit assign_loc_injp_acc; eauto.
    instantiate (1 := MINJ2).
    intros (tm4 & MINJ3 & ASSIGN & INJP2).
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
  - inv MSTMT. simpl in TR. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    monadInv TR.
    set (own2:=(move_place_option own1 (moved_place e))).
    set (own3:=(own_transfer_assign own2 p)).
    (* evaluate x: the statement updating drop flags for the rhs (the expression) *)
    exploit eval_dropflag_option_match; eauto.
    eapply PathsMap.eq_sym. eapply sound_own_universe. eauto.
    instantiate (1 := (RustIRsem.Kseq (Ssequence x0 (Sassign_variant p enum_id fid e)) tk)).
    instantiate (1 := tf).
    intros (tm2 & STEP1 & MINJ1 & MENV1 & UNC1 & RO1).
    (* evaluate x0: the statement upadting drop flags for the lhs (the place) *)    
    exploit eval_dropflag_match; eauto.
    eapply PathsMap.eq_sym. eapply PathsMap.eq_trans.
    eapply sound_own_universe. eauto.
    eapply move_place_option_eq_universe.
    instantiate (1 := (RustIRsem.Kseq (Sassign_variant p enum_id fid e) tk)).
    instantiate (1 := tf).
    intros (tm3 & STEP2 & MINJ2 & MENV2 & UNC2 & RO2).
    (* evaluate assign_variant *)
    exploit eval_expr_inject; eauto with matsym.
    intros (tv & TEXPR & VINJ).
    exploit eval_place_inject. eapply PADDR1. eauto. eauto.
    intros (tb & tofs & EVALP & VINJ1).
    exploit sem_cast_inject; eauto.
    intros (tv1 & CAST1 & VINJ2).
    inv VINJ1.
    exploit assign_loc_injp_acc; eauto.
    instantiate (1 := MINJ2).
    intros (tm4 & MINJ3 & ASSIGN & INJP2).
    assert (OFSEQ: (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr fofs)) (Ptrofs.repr delta)) =
                     (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta)) (Ptrofs.repr fofs))).
    { rewrite !Ptrofs.add_assoc. f_equal. apply Ptrofs.add_commut. }
    rewrite OFSEQ in ASSIGN.
    (* match_envs_flagm *)
    assert (SUP1: Mem.sup_include thi (Mem.support tm3)).
    { eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. eauto.
      eapply Mem.unchanged_on_support. eauto. }    
    exploit match_envs_flagm_injp_acc. eapply MENV2. eauto.
    auto. auto.    
    intros MENV3.
    (* evaluate the address of the place again and then set the tag *)
    exploit eval_place_inject. eapply PADDR2. eauto. eauto.
    intros (tb1 & tofs1 & EVALP1 & VINJ4).
    exploit Mem.storev_mapped_inject. eapply MINJ3. eauto. eauto. econstructor.
    intros (tm5 & STORETAG & MINJ4).
    exploit injp_acc_storev. eapply STAG. eauto. eauto. econstructor.
    instantiate (1 := MINJ4). instantiate (1 := MINJ3).
    intros INJP3.
    assert (SUPm2: Mem.sup_include hi (Mem.support m2)).
    { erewrite assign_loc_support. eauto. eauto. }
    assert (SUPtm4: Mem.sup_include thi (Mem.support tm4)).
    { erewrite assign_loc_support. eauto. eauto. }    
    exploit match_envs_flagm_injp_acc. eapply MENV3. eauto.
    auto. auto.
    intros MENV4.
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
    exploit match_cont_injp_acc. eauto.
    etransitivity. eauto. eauto.
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
      intros. simpl. destruct H3.
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
    1-2: rewrite comp_env_preserved; eauto.    
    eapply star_refl. 1-8: eauto.
    (* match_states *)
    assert (SUP2: Mem.sup_include hi (Mem.support m3)).
    { eapply Mem.sup_include_trans. eauto. 
      erewrite Mem.support_storev; eauto. }
    assert (SUP3: Mem.sup_include thi (Mem.support tm5)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite Mem.support_storev; eauto. }
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
    etransitivity. eauto.
    etransitivity. eauto. eauto.
  (* step_box *)
  - inv MSTMT. simpl in TR. inv IM.
    rewrite <- H8 in TR. rewrite <- H9 in TR.
    rename H8 into GETINIT. rename H9 into GETUNINIT.
    monadInv TR.
    set (own2:=(move_place_option own1 (moved_place e))).
    set (own3:=(own_transfer_assign own2 p)).
    (* evaluate x: the statement updating drop flags for the rhs (the expression) *)
    exploit eval_dropflag_option_match; eauto.
    eapply PathsMap.eq_sym. eapply sound_own_universe. eauto.
    instantiate (1 := (RustIRsem.Kseq (Ssequence x0 (Sbox p e)) tk)).
    instantiate (1 := tf).
    intros (tm2 & STEP1 & MINJ1 & MENV1 & UNC1 & RO1).
    (* evaluate x0: the statement upadting drop flags for the lhs (the place) *)    
    exploit eval_dropflag_match; eauto.
    eapply PathsMap.eq_sym. eapply PathsMap.eq_trans.
    eapply sound_own_universe. eauto.
    eapply move_place_option_eq_universe.
    instantiate (1 := (RustIRsem.Kseq (Sbox p e) tk)).
    instantiate (1 := tf).
    intros (tm3 & STEP2 & MINJ2 & MENV2 & UNC2 & RO2).
    (* evaluate Sbox *)
    exploit Mem.alloc_parallel_inject. eauto. eauto.
    eapply Z.le_refl. rewrite <- comp_env_preserved.
    eapply Z.le_refl.
    intros (j1 & tm4 & tb & TALLOC & MINJ3 & INCR1 & A1 & A2).
    exploit injp_acc_alloc. eapply H0. rewrite <- comp_env_preserved. eauto.
    eauto. auto. auto.
    instantiate (1 := MINJ3). instantiate (1 := MINJ2).
    intros INJP1.
    (* store size to the allocated block *)
    exploit Mem.store_mapped_inject. eapply MINJ3. eauto. eauto.
    eapply Vptrofs_inject. rewrite <- comp_env_preserved.
    intros (tm5 & STORE1 & MINJ4).
    exploit injp_acc_store. eapply H1. eauto. rewrite comp_env_preserved.
    eapply Vptrofs_inject. eauto.
    instantiate (1 := MINJ4). instantiate (1 := MINJ3).
    intros INJP2.
    assert (SUPtm3: Mem.sup_include thi (Mem.support tm3)).
    { eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. eauto.
      eapply Mem.unchanged_on_support. eauto. }    
    (* prove match_env in (m3, tm5) *)
    exploit match_envs_flagm_injp_acc. eauto.
    etransitivity. eauto. eauto. auto. auto.
    intros MENV3.
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
        assert (RO3: ValueAnalysis.ro_acc tm tm3).
    { eapply ValueAnalysis.ro_acc_trans. eauto.
      auto. }
    assert (INJP0: injp_acc w (injpw j m1 tm3 MINJ2)).
    { generalize me_tinitial. intros TINIT.
      unfold wm2 in TINIT.
      destruct w. inv RO3.
      eapply injp_acc_local_simple. eauto.
      auto. auto.
      eapply Mem.unchanged_on_implies. eauto.
      intros. simpl. destruct H10.
      eapply TINIT. eapply me_envs; eauto. auto. }
    exploit eval_expr_inject; eauto.
    eapply injp_acc_globalenv. etransitivity. eauto. eauto.
    intros (tv & TEXPR & VINJ).
    exploit sem_cast_inject; eauto. intros (tv1 & TCAST & VINJ1).
    (* assign the value to the allocated block *)
    exploit assign_loc_injp_acc. eapply H4. econstructor. eauto.
    rewrite Ptrofs.add_zero_l. eauto. eauto.
    instantiate (1 := MINJ4).
    intros (tm6 & MINJ5 & TAS1 & INJP3).
    assert (SUPm3: Mem.sup_include hi (Mem.support m3)).
    { eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. inv INJP1. eauto.
      eapply Mem.unchanged_on_support. inv INJP2. eauto. }
    assert (SUPtm5: Mem.sup_include thi (Mem.support tm5)).
    { eapply Mem.sup_include_trans. eauto.
      eapply Mem.sup_include_trans.
      eapply Mem.unchanged_on_support. inv INJP1. eauto.
      eapply Mem.unchanged_on_support. inv INJP2. eauto. }    
    exploit match_envs_flagm_injp_acc. eauto.
    eauto. auto. auto.
    intros MENV4.    
    exploit eval_place_inject; eauto. 
    intros (tb1 & tofs1 & EVALP & VINJ2).
    exploit assign_loc_injp_acc. eapply H6. eauto. eauto.
    instantiate (1 := MINJ5).
    intros (tm7 & MINJ6 & ASSIGN & INJP4).
    (* match_envs_flagm *)
    assert (SUPm4: Mem.sup_include hi (Mem.support m4)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eauto. eauto. }
    assert (SUPtm6: Mem.sup_include thi (Mem.support tm6)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eauto. eauto. }    
    exploit match_envs_flagm_injp_acc. eapply MENV4. eauto.
    auto. auto.
    intros MENV5.
    (* match_cont *)
    assert (INJP15: injp_acc (injpw j m1 tm3 MINJ2) (injpw j1 m5 tm7 MINJ6)).
    { etransitivity. eauto.
      etransitivity. eauto.
      etransitivity. eauto. eauto. }
    exploit match_cont_bound_unchanged;eauto.
    intros MCONT1.
    exploit match_cont_injp_acc. eauto. eauto.
    eapply Mem.sup_include_trans.
    eapply me_incr. eapply me_envs. eauto. auto.
    eapply Mem.sup_include_trans.
    eapply me_tincr. eapply me_envs. eauto. auto.
    intros MCONT2.        
    (* injp_acc *)
    assert (INJP05: injp_acc w (injpw j1 m5 tm7 MINJ6)).
    { etransitivity; eauto. }
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
    assert (SUPm5: Mem.sup_include hi (Mem.support m5)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eauto. eauto. }
    assert (SUPtm7: Mem.sup_include thi (Mem.support tm7)).
    { eapply Mem.sup_include_trans. eauto.
      erewrite <- assign_loc_support. eauto. eauto. }    
    (** *** How to make it a lemma? construct get_IM and sound_own *)
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
    (** *** end of construct *)
    econstructor; eauto. econstructor.
  (* step_to_dropplace *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    unfold elaborate_drop_for in TR.
    (** sound_own property *)
    erewrite split_drop_place_eq_universe in TR.
    unfold ce in TR. erewrite SPLIT in TR.
    2: { eapply sound_own_universe. eauto. }
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
    (** wf_split_drop_places *)
    erewrite <- split_drop_place_eq_universe in SPLIT.
    2: { eapply sound_own_universe. eauto. }
    exploit split_drop_place_meet_spec; eauto.
    intros SPEC.
    eapply ordered_split_drop_places_wf.
    eapply split_ordered. eauto.
    (* use sound_own properties, prove p0 is in the universe *)
    intros. eapply must_init_sound; eauto.
    (* The following comment code is used to prove in_universe but it
    is useless now *)
    (* exploit split_sound; eauto. *)
    (* eapply (in_map fst)in H. eauto. *)
    (* intros (C & D). *)
    (* erewrite <- is_prefix_same_local; eauto. *)
    intros. eapply must_not_init_sound; eauto.
    eapply sound_own_universe; eauto.
    intros. eapply SFLAGM; eauto.
    eapply in_map_iff. exists (p0, full). auto.
    (* sound_flagm_some *)
    eapply sound_flagm_some; eauto.
  (* step_in_dropplace *)
  - eapply step_dropplace_simulation. eauto.
    econstructor; eauto.
  (* step_dropstate *)
  - eapply step_dropstate_simulation. eauto.
    econstructor; eauto.
  (* step_storagelive *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    monadInv TR.
    eexists. split.
    eapply plus_one. econstructor.
    (* construct sound_own and get_IM *)
    exploit analyze_succ. 1-3: eauto. simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT. eauto.
    eauto.
    intros (mayinit3 & mayuninit3 & A & B).
    econstructor; eauto.
    econstructor.
  (* step_storagedead *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    monadInv TR.
    eexists. split.
    eapply plus_one. econstructor.
    (* construct sound_own and get_IM *)
    exploit analyze_succ. 1-3: eauto. simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT. eauto.
    eauto.
    intros (mayinit3 & mayuninit3 & A & B).
    econstructor; eauto.
    econstructor.
  (* step_call *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H5 in TR. rewrite <- H6 in TR.
    rename H5 into GETINIT. rename H6 into GETUNINIT.
    monadInv TR.
    (* evaluate drop flag list of arguments *)
    exploit eval_dropflag_list_match; eauto.
    eapply PathsMap.eq_sym. eapply sound_own_universe; eauto.
    instantiate (2 := tf).
    intros (tm1 & A1 & A2 & A3 & A4 & A5).
    exploit eval_expr_inject; eauto with matsym.
    intros (tv & TEXPR & VINJ1).
    exploit eval_exprlist_inject; eauto with matsym.
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
      intros. simpl. destruct H7. intros.
      intro. subst.
      (* tb is not valid in m2 *)
      eapply me_trange. eapply me_envs; eauto.
      eauto. eapply SUP. eapply me_envs; eauto.
      eapply H7. }
      
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
    (** function_not_drop_glue in RustIRown *)
    eapply good_fundef_preserved; eauto.
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
    monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
    monadInv EQ3.
    (* use transl_on_cfg_meet_spec to get match_stmt in fuction entry *)
    exploit (@transl_on_cfg_meet_spec AN); eauto. 
    intros (nret & MSTMT & RET).
    (* own_env in function entry is sound *)
    exploit sound_function_entry. simpl. eauto.
    eauto. eauto. eauto. intros (einit & euninit & GIM & OWNENTRY).
    (** TODO: construct function entry in target program *)
    inv ENTRY.
    
    (* alloc the same variables and parameters in source and target *)
    exploit alloc_variables_match; eauto. 
    eapply match_empty_envs.
    eapply Mem.sup_include_refl.
    eapply Mem.sup_include_refl. 
    unfold wm1. destruct w.
    inv MINJ. eapply Mem.unchanged_on_support. eauto.
    unfold wm2. destruct w.
    inv MINJ. eapply Mem.unchanged_on_support. eauto.    
    intros (j1 & tm1 & Hm1 & te1 & ALLOC1 & MENV1 & INJP1).
    (* alloc drop flag in the target program *)
    rename x2 into drop_flags.
    set (flags := combine (map snd drop_flags) (repeat type_bool (Datatypes.length drop_flags))) in *.
    (* norepet of drop flags *)
    assert (NOREP_FLAGS: list_norepet (map snd drop_flags)).
    { unfold generate_drop_flags in EQ1.
      destruct list_norepet_dec in EQ1; try congruence.
      destruct list_norepet_dec in EQ1; try congruence. inv EQ1. auto. }    
    exploit alloc_drop_flags_match; eauto.
    (* A disjoint check between the drop flags and the local variables *)
    intros. destruct (e!id) eqn: A; auto. destruct p.
    exploit alloc_variables_in. eapply H0. eauto.
    intros [B1|B2]. erewrite PTree.gempty in B1. inv B1.
    exfalso. eapply l. eauto. eapply in_map_iff. eauto. simpl. auto.
    intros (te2 & tm2 & Hm2 & ALLOC2 & INJP2 & WFFLAG & NOTIN & MENV2 ).
    (* bind_parameters in target program *)
    exploit bind_parameters_injp_acc. eauto. inv MENV2. eauto.  
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
    intros. exploit WFFLAG. instantiate (1:= id). eapply pair_snd_in. eauto. eauto.  
    eapply me_tinj; eauto.
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
    assert (A: map fst flags = map snd drop_flags).
    { unfold flags.
      rewrite map_split_l. 
      rewrite combine_split. simpl. auto.
      rewrite repeat_length. rewrite map_length. auto. }      
    unfold var_names.
    erewrite map_app. rewrite A. rewrite app_assoc.
    unfold var_names in H.
    eapply list_norepet_append; eauto.
    eapply list_disjoint_sym. rewrite <- map_app. auto.
    (* alloc_variables *)
    simpl. rewrite app_assoc.
    eapply alloc_variables_app; eauto.
    (* bind_parameters *)
    eauto.
    (** evaluate init statement *)
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
    (** sup_include lo (Mem.support m) by match_envs_flagm *)
    eapply me_incr. eapply me_envs. eauto.
    eapply me_tincr. eapply me_envs. eauto.
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
    eapply generate_place_map_in_list. auto.
    (** injective of get_dropflag_temp of the generated flagm. Prove
    by norepet of drop_flags *)
    intros.
    eapply get_place_map_injective; eauto.
    (** sound_flagm *)
    eapply generate_flag_map_sound; eauto.
  (* step_external_function *)
  - simpl in FIND.
    assert (GE1: Genv.match_stbls j se tse).
    { replace j with (mi injp (injpw j m tm Hm)) by auto.
      eapply match_stbls_proj.
      eapply match_stbls_acc; eauto. }
    exploit find_funct_match; eauto.
    intros (tf & TFIND & TRFUN).
    (* destruct tf *)
    unfold transf_fundef in TRFUN.
    monadInv TRFUN.
    (* injp_acc *)
    exploit external_call_mem_inject; eauto.
    intros (j1 & tv1 & tm1 & TEXT & VINJ1 & MINJ1 & UNC1 & TUNC1 & INCR1 & SEP1).
    eexists. split.
    econstructor. eapply RustIRsem.step_external_function; eauto.
    eapply star_refl.
    eapply app_nil_end.
    (* match_state *)
    assert (INJP: injp_acc (injpw j m tm Hm) (injpw j1 m' tm1 MINJ1)).
    { econstructor; eauto.
      red. eauto using external_call_readonly.
      red. eauto using external_call_readonly.
      red. eauto using external_call_max_perm; eauto.
      red. eauto using external_call_max_perm; eauto. }    
    econstructor; eauto.
    etransitivity; eauto.
    (* match_stacks *)
    eapply match_stacks_incr_bounds.
    eapply match_stacks_injp_acc. eauto. eauto.
    eapply Mem.sup_include_refl. eapply Mem.sup_include_refl.
    eapply Mem.unchanged_on_support. eauto.
    eapply Mem.unchanged_on_support. eauto.
  (* step_return_1 *)
  - inv MSTMT. simpl in TR.
    generalize IM as IM1. intros. inv IM.
    rewrite <- H0 in TR. rewrite <- H in TR.
    rename H0 into GETINIT. rename H into GETUNINIT.
    monadInv TR.
    (* evaluate the return place value *)
    exploit eval_expr_inject; eauto with matsym. intros (tv & TEVAL & VINJ).
    (* sem_cast *)
    exploit sem_cast_inject; eauto. intros (tv1 & TCAST & VINJ1).
    (* free_list in target *)
    exploit match_envs_free_blocks. eapply me_envs; eauto.
    eauto. eauto.
    intros (tm2 & TFREE & MINJ2).
    (* injp_acc for free_list, may be lift to a lemma *)
    exploit injp_acc_free_list; eauto.
    eapply me_envs; eauto. instantiate (1 := MINJ2).
    intros INJP2.
    (* match_cont *)
    exploit match_cont_free_env; eauto.
    intros MCONT1.
    exploit match_cont_incr_bounds. eauto.
    eapply Mem.sup_include_trans. eapply me_incr. eapply me_envs; eauto. eauto.
    eapply Mem.sup_include_trans. eapply me_tincr. eapply me_envs; eauto. eauto.
    intros MCONT2.
    (* call_cont *)
    exploit match_cont_call_cont; eauto.
    intros (tck & CCONT & MSTK).    
    (* step *)    
    eexists. split.
    econstructor. econstructor. eauto. eauto.
    rewrite <- RETY. eauto.
    eauto. eauto.
    eapply star_refl. auto.
    econstructor; eauto. 
    erewrite SimplLocalsproof.free_list_support. 2: eapply FREE.
    erewrite (SimplLocalsproof.free_list_support _ _ _ TFREE). eauto.     
  (* step_returnstate *)
  - inv MCONT.
    generalize IM as IM1. intros. inv IM.
    rename H3 into GETINIT. rename H4 into GETUNINIT.
    exploit eval_place_inject; eauto.
    intros (tb1 & tofs1 & EVALP & VINJ1). inv VINJ1.
    exploit assign_loc_injp_acc; eauto.
    instantiate (1 := Hm).
    intros (tm2 & Hm2 & AS2 & INJP2).
    (* evaluate the add_dropflag statement *)
    exploit match_envs_flagm_injp_acc. eauto. eauto.
    eapply Mem.sup_include_refl. eapply Mem.sup_include_refl.
    intros MENV2.
    exploit eval_dropflag_match; eauto.
    unfold init_place in OWN. inv OWN. simpl in *.
    eapply PathsMap.eq_sym. eauto.
    instantiate (1 := tk0).
    instantiate (1 := tf).
    intros (tm3 & STEP2 & MINJ2 & MENV3 & UNC2 & RO2).
    (* step *)
    eexists. split.
    econstructor. econstructor; eauto.
    eapply val_casted_inject; eauto.
    eapply star_step. eapply RustIRsem.step_skip_seq.
    eauto. 1-2: eauto.
    (* match_state *)
    assert (INJP3: injp_acc w (injpw j m2 tm3 MINJ2)).
    { inv RO2.
      generalize me_tinitial. intros SUP.
      unfold wm2 in SUP.
      destruct w. 
      eapply injp_acc_local_simple.
      etransitivity. eauto. eauto. eauto. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      intros. simpl. destruct H6. intros.
      intro. subst.
      (* tb is not valid in m2 *)
      eapply me_trange. eapply me_envs; eauto.
      eauto. eapply SUP. eapply me_envs; eauto.
      eapply H6. }
    econstructor. eauto. econstructor.    
    (* match_cont *)    
    eapply match_cont_bound_unchanged.
    eapply match_cont_injp_acc. eauto. eauto.
    eapply me_incr. eapply me_envs. eauto.
    eapply me_tincr. eapply me_envs. eauto.
    (* unchanged on the blocks in tlo from tm2 to tm3 *)
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. intros. intro. subst.
    eapply me_trange. eapply me_envs; eauto. eauto. auto.
    auto.
    (* injp_acc w ~-> (j, m2, tm3) *)
    eauto.
    eauto. eauto. eauto.
    (* sound_own *)
    eauto.
    (* sup_include *)
    inv INJP2. eapply Mem.unchanged_on_support; eauto.
    inv RO2. eapply Mem.sup_include_trans. 2: eauto.
    inv INJP2. eapply Mem.unchanged_on_support; eauto.
  (* step_seq *)
  - inv MSTMT.
    eexists. split.
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_seq *)
  - inv MSTMT. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRsem.step_skip_seq.
    eapply star_refl. auto.
    econstructor; eauto.
  (* step_continue_seq *)
  - inv MSTMT. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRsem.step_continue_seq.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor.
  (* step_break_seq *)
  - inv MSTMT. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRsem.step_break_seq.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor.
  (* step_ifthenelse *)
  - inv MSTMT.
    generalize IM as IM1. intros. inv IM.
    rename H2 into GETINIT. rename H3 into GETUNINIT.
    exploit eval_expr_inject; eauto with matsym.
    intros (tv & EVAL & VINJ).
    eexists. split.
    econstructor. econstructor; eauto.
    eapply Cop.bool_val_inject; eauto.
    eapply star_refl. auto.
    destruct b.
    + exploit analyze_succ; eauto.
      simpl. left. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite MCOND. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite MCOND. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      (* match_state *)
      econstructor; eauto.
    + exploit analyze_succ; eauto.
      simpl. right. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite MCOND. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite MCOND. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      (* match_state *)
      econstructor; eauto.
  (* step_loop *)
  - inv MSTMT.
    generalize IM as IM1. intros. inv IM.
    rename H0 into GETINIT. rename H into GETUNINIT.
    eexists. split.
    econstructor. econstructor.
    eapply star_refl. auto.
    (* sound_own *)
    exploit analyze_succ; eauto.
    simpl. left. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite START. auto.
    unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
    intros (mayinit3 & mayuninit3 & GIM & SO).
    econstructor; eauto.
    econstructor; eauto.    
  (* step_skip_or_continue_loop *)
  - inv MCONT.
    generalize IM as IM1. intros. inv IM.
    rename H1 into GETINIT. rename H2 into GETUNINIT.
    destruct H; subst; inv MSTMT.
    + eexists. split.
      econstructor. eapply RustIRsem.step_skip_or_continue_loop; auto.
      eapply star_refl. auto.
      (* sound_own *)
      exploit analyze_succ; eauto.
      simpl. left. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite START. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
      econstructor; eauto.
    + eexists. split.
      econstructor. eapply RustIRsem.step_skip_or_continue_loop; auto.
      eapply star_refl. auto.
      (* sound_own *)
      exploit analyze_succ; eauto.
      simpl. left. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite START. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
      econstructor; eauto.
  (* step_break_loop *)
  - inv MSTMT. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRsem.step_break_loop; auto.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor.
Qed.

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
      monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
      monadInv EQ3.
      unfold type_of_function in H5. inv H5.
      f_equal. }
    (* fn_drop_glue *)
    { unfold type_of_function.
      unfold transf_function in EQ.
      monadInv EQ. destruct x2 as [[i1 i2] i3].
      monadInv EQ2. destruct list_disjoint_dec in EQ3; try congruence.
      monadInv EQ3.
      simpl. auto. }
    eapply val_casted_inject_list;eauto.
    (* sup_include *)
    (* simpl. inv Hm. inv GE. simpl in *. auto. *)
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
