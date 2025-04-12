Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Rusttypes.
Require Import Errors.
Require Import LanguageInterface CKLR Inject InjectFootprint.
Require Import RustIR Rustlight RustOp RustIRgen.
Require Import SmallstepSafe RustIRown.
Require Import InitDomain Rustlightown.    

Import ListNotations.
Local Open Scope list_scope.
Local Open Scope error_monad_scope.

(** Semantics preservation of the generation of RustIR programs from
Rustlight programs. The key part of the proof is to relate the
semantics drops expressed in the continuation to the drop statements
explicitly inserted in the program *)


Definition match_glob (ctx: composite_env) (gd: globdef Rustlight.fundef type) (tgd: globdef RustIR.fundef type) : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar eq v1 v2
  | Gfun fd1, Gfun fd2 =>
      transl_fundef ctx fd1 = fd2
  | _, _ => False
  end.

Record match_prog (p : Rustlight.program) (tp : RustIR.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_types:
    tp.(prog_types) = p.(prog_types);
    match_prog_defs:
    list_forall2 (fun g1 g2 => fst g1 = fst g2 /\ match_glob p.(prog_comp_env) (snd g1) (snd g2)) p.(prog_defs) tp.(prog_defs);
    match_prog_skel:
    erase_program tp = erase_program p;
  }.

Lemma match_globdefs: forall (l: list (ident * globdef fundef type)) ce,
    list_forall2
      (fun (g1 : ident * globdef fundef type) (g2 : ident * globdef RustIR.fundef type) =>
         fst g1 = fst g2 /\ match_glob ce (snd g1) (snd g2))
      l
      (map (transform_program_globdef (transl_fundef ce)) l).
Proof.
  induction l; intros; simpl.
  - constructor.
  - constructor.
    + destruct a. simpl. destruct g; simpl; auto.
      split; auto. destruct v. constructor. auto.
    + auto.
Qed.
   
Lemma match_erase_program: forall ce (l: list (ident * globdef fundef type)),
    map (fun '(id, g) => (id, erase_globdef g))
      (map (transform_program_globdef (transl_fundef ce)) l) =
      map (fun '(id, g) => (id, erase_globdef g)) l.
Proof.
  induction l; intros; simpl.
  auto.
  f_equal. destruct a. simpl. destruct g; simpl; auto.
  auto.
Qed.

Lemma match_transf_program: forall p tp,
    transl_program p = tp ->
    match_prog p tp.
Proof.
  intros p tp TR. unfold transl_program in TR. subst.
  constructor; simpl; auto.
  - eapply match_globdefs.    
  - unfold erase_program; simpl.
    f_equal.
    eapply match_erase_program.
Qed.
    
(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: program.
Variable tp: RustIR.program.
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
    intros.
    eapply PTree_Properties.of_list_related.
    apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob ce)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Rusttypes.fundef RustIR.function) type)) None ))).
  (* adhoc generalize because types are the same *)
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None).
    generalize (NMap.init (option (globdef (Rusttypes.fundef RustIR.function) type)) None).
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
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ transl_fundef ce f = tf.
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
  Genv.find_funct (RustIR.globalenv tse tp) tv = None.
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
  (forall f tf, transl_fundef ce f = tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (RustIR.globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold fundef.
    simpl. setoid_rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.


Section PRESERVATION.


Variable prog: program.
Variable tprog: RustIR.program.

Hypothesis TRANSL: match_prog prog tprog.

Variable se: Genv.symtbl.

(* Variable dropflags: PTree.t (list (place * ident)). *)

Let ge := globalenv se prog.
Let tge := RustIR.globalenv se tprog.

(* Some lemmas about function definitions in identical symtbls *)

Corollary find_funct_match_id:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef ge f = tf.
Proof.
  intros. eapply find_funct_match; eauto using Genv.match_stbls_id.
    apply val_inject_id. auto.
Qed.

Corollary find_funct_match_id_inv:
  forall v tf,
  Genv.find_funct tge v = Some tf ->
  exists f,
  Genv.find_funct ge v = Some f /\ transl_fundef ge f = tf.
Proof.  
  intros. destruct (Genv.find_funct ge v) eqn: FIND.
  - simpl in FIND. exploit find_funct_match; eauto using Genv.match_stbls_id.    
    apply val_inject_id. eauto.
    intros (tf1 & FIND1 & TR). simpl in H.
    setoid_rewrite H in FIND1. inv FIND1.
    exists f. split; eauto.
  - simpl in FIND.
    exploit Genv.find_funct_inv; eauto. intros (b & VEQ). subst.
    exploit find_funct_none. eauto.
    2: eapply FIND. 2: eapply val_inject_id.
    eauto using Genv.match_stbls_id. econstructor. congruence.
    intros FN. simpl in H. setoid_rewrite H in FN. congruence.
Qed.


Theorem is_internal_match_id :
  (forall f tf, transl_fundef ge f = tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v ,    
    Genv.is_internal tge v = Genv.is_internal ge v.
Proof.
  intros. destruct v; auto.
  eapply is_internal_match; eauto using Genv.match_stbls_id.
  apply val_inject_id; auto.
  congruence.
Qed.


Lemma comp_env_preserved:
  RustIR.genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. inv TRANSL. simpl in *.
  congruence.
Qed.


Lemma type_of_fundef_preserved:
  forall fd tfd,
  transl_fundef ge fd = tfd -> RustIR.type_of_fundef tfd = type_of_fundef fd.
Proof.
  intros. destruct fd; simpl in H; subst.
  simpl; unfold type_of_function; simpl. auto.
  simpl; unfold type_of_function; simpl. auto.
Qed.

Lemma function_not_drop_glue_preserved: forall fd tfd,
    transl_fundef ge fd = tfd ->
    function_not_drop_glue fd ->
    RustIR.function_not_drop_glue tfd.
Proof.
  intros. destruct fd.
  - simpl in *. destruct (fn_drop_glue f) eqn: A; try contradiction.
    subst. simpl. rewrite A. auto.
  - subst. simpl in *. auto.
Qed.

Lemma function_not_drop_glue_preserved_inv: forall fd tfd,
    transl_fundef ge fd = tfd ->
    RustIR.function_not_drop_glue tfd ->
    function_not_drop_glue fd.
Proof.
  intros. destruct fd.
  - simpl in *. destruct (fn_drop_glue f) eqn: A; try contradiction.
    subst. simpl in H0. rewrite A in H0. contradiction. auto.
  - subst. simpl in *. auto.
Qed.


Lemma dropm_preserved:
  RustIR.genv_dropm tge = genv_dropm ge.
Proof.
  simpl. unfold RustIR.generate_dropm, generate_dropm.
  f_equal. exploit match_prog_defs; eauto.
  simpl.
  generalize (Rusttypes.prog_defs tprog).
  generalize (Rusttypes.prog_defs prog).
  induction l; intros.
  - inv H. auto.
  - inv H. destruct H2. simpl.
    destruct a. destruct b1. simpl in *. subst.
    destruct g.
    + simpl in H0. destruct g0; try contradiction. subst.
      destruct f; simpl; auto.
      destruct (fn_drop_glue f) eqn: A; auto.
      simpl.  rewrite A. f_equal. auto.
    + destruct g0; simpl in *; try contradiction.
      auto.
Qed.

  
Lemma type_to_drop_member_state_eq: forall id ty,
    RustIR.type_to_drop_member_state tge id ty = type_to_drop_member_state ge id ty.
Proof.
  intros. unfold RustIR.type_to_drop_member_state, type_to_drop_member_state.
  erewrite comp_env_preserved; eauto. auto.
  erewrite dropm_preserved; eauto.
Qed.

Lemma pair_eq_dec {A B: Type} (H1: forall x y : A, {x = y} + {x <> y})
  (H2: forall x y : B, {x = y} + {x <> y})
  : forall (x y: A*B),
    {x = y} + {x <> y}.
Proof.
  intros. destruct x; destruct y.
  destruct (H1 a a0); subst.
  - destruct (H2 b b0); subst. auto.
    right. congruence.
  - right. congruence.
Qed.

    
Lemma drop_insert_kind_eq: forall (k1 k2: drop_insert_kind),
    {k1 = k2} + {k1 <> k2}.
Proof.
  intros. destruct k1.
  - destruct k2; try (right; congruence).
    destruct (place_eq p p0); subst. auto.
    right. congruence.
  - destruct k2; try (right; congruence).
    generalize ident_eq, type_eq. intros.
    destruct (list_eq_dec (pair_eq_dec ident_eq type_eq) l l0); subst.
    auto.
    right. congruence.
  - destruct k2; try (right; congruence).
    generalize ident_eq, type_eq. intros.
    destruct (list_eq_dec (pair_eq_dec ident_eq type_eq) l l0); subst.
    destruct (ident_eq i i0); subst; auto.
    right. congruence.
    right. congruence.
  - destruct k2; try (right; congruence).
    generalize ident_eq, type_eq. intros.
    destruct (list_eq_dec (pair_eq_dec ident_eq type_eq) l l0); subst.
    auto.
    right. congruence.
  - destruct k2; try (right; congruence).
    auto.
Qed.

  
Inductive match_drop_insert_kind: drop_insert_kind -> RustIR.statement -> Prop :=
| match_drop_reassign: forall p,
    match_drop_insert_kind (drop_reassign p) (gen_drop ge p)
| match_drop_escape_before: forall l,
    match_drop_insert_kind (drop_escape_before l) (gen_drops_for_escape_vars ge l)
| match_drop_escape_after: forall id l,
    match_drop_insert_kind (drop_escape_after id l) (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l))
| match_drop_return: forall l,
    match_drop_insert_kind (drop_return l) (gen_drops_for_vars ge l)
| match_drop_end:
  match_drop_insert_kind drop_end RustIR.Sskip
.


(* We distinguish the dropcont from reassign purpose and out-of-scope
purpose *)

Inductive match_dropcont : dropcont -> RustIR.statement -> Prop :=
| match_Dassign: forall p e,
    match_dropcont (Dassign p e) (RustIR.Sassign p e)
| match_Dassign_variant: forall p e eid fid,
    match_dropcont (Dassign_variant p eid fid e) (RustIR.Sassign_variant p eid fid e)
| match_Dbox: forall p e,
    match_dropcont (Dbox p e) (RustIR.Sbox p e)
| match_Dcall: forall p a al,
    match_dropcont (Dcall p a al) (RustIR.Scall p a al)
| match_Dbreak:
  match_dropcont Dbreak RustIR.Sbreak
| match_Dcontinue:
  match_dropcont Dcontinue RustIR.Scontinue
| match_Dreturn: forall p,
    match_dropcont (Dreturn p) (RustIR.Sreturn p)
| match_Dendlet:
  (* may be we should generate sskip in the end of the let *)
  match_dropcont Dendlet RustIR.Sskip
.

(* Sometimes the statement for dropcont depends on the
drop_insert_kind (e.g., return statment because after we drop the
escaped variables, we also need to drop the parameters *)
Inductive match_drop_insert_kind_dropcont (params: list (ident * type)): drop_insert_kind -> dropcont -> RustIR.statement -> Prop :=
| match_drop_insert_kind_dropcont_normal: forall st dk s2
    (MDCONT: match_dropcont dk s2)
    (NOTRET: (forall p, dk <> Dreturn p) /\ dk <> Dendlet)
    (NOTDRET: forall l, st <> drop_return l),
    match_drop_insert_kind_dropcont params st dk s2
| match_drop_insert_kind_dropcont_Dendlet1: forall l,
    match_drop_insert_kind_dropcont params (drop_escape_before l) Dendlet RustIR.Sskip
| match_drop_insert_kind_dropcont_Dendlet2: forall id l,
    match_drop_insert_kind_dropcont params (drop_escape_after id l) Dendlet RustIR.Sskip
| match_drop_insert_kind_dropcont_return1: forall s2 p drop l
    (* The parameters are not ready to be dropped *)
    (MRET: match_dropcont (Dreturn p) s2)
    (PARAMS: drop = gen_drops_for_vars ge params),
    match_drop_insert_kind_dropcont params (drop_escape_before l) (Dreturn p) (RustIR.Ssequence drop s2)
| match_drop_insert_kind_dropcont_return2: forall s2 p drop l id
    (* The parameters are not ready to be dropped *)
    (MRET: match_dropcont (Dreturn p) s2)
    (PARAMS: drop = gen_drops_for_vars ge params),
    match_drop_insert_kind_dropcont params (drop_escape_after id l) (Dreturn p) (RustIR.Ssequence drop s2)                                    
| match_drop_insert_kind_dropcont_return3: forall s2 p l
    (* The parameters are not ready to be dropped *)
    (MRET: match_dropcont (Dreturn p) s2),
    match_drop_insert_kind_dropcont params (drop_return l) (Dreturn p) s2.


Inductive match_cont (params: list (ident * type)) : cont -> RustIRown.cont -> Prop :=
| match_Klet: forall k tk drop id ty
    (MCONT: match_cont params k tk)
    (DROP: drop = gen_drops_for_escape_vars ge [(id, ty)]),
    (* when executing Klet, Rustlight would enter Dropinsert state
    where drop_escape contains the out-of-scope variable which is
    related to (drop;storagedead id) *)
    (* skip is used to simulate the Dendlet step  *)
    match_cont params (Klet id ty k) (RustIRown.Kseq drop (RustIRown.Kseq RustIR.Sskip tk))
(* The drops are inserted for the reassignment. The translated
statement does not contain storagedead *)
(* | match_Kdropinsert: forall k tk dk s1 s2 st *)
(*     (MCONT: match_cont params k tk) *)
(*     (* (MDCONT: match_dropcont dk s2) *) *)
(*     (MDINS: match_drop_insert_kind st s1) *)
(*     (MST: match_drop_insert_kind_dropcont params st dk s2), *)
(*     (** TODO: before running st, we may need to execute the *)
(*     storagedead in the target *) *)
(*     match_cont params (Kdropinsert st dk k) *)
(*       (* s1 should contain the storagedead of the first element of st *) *)
(*       (RustIRown.Kseq s1 (RustIRown.Kseq s2 tk)) *)
(* move dropcont related statement to front *)
(* | match_Kdropinsert_end: forall k tk dk s1 *)
(*     (MCONT: match_cont params k tk) *)
(*     (MDCONT: match_dropcont dk s1), *)
(*     (** TODO: before running st, we may need to execute the *)
(*     storagedead in the target *) *)
(*     match_cont params (Kdropinsert drop_end dk k) tk *)
| match_Kstop:
    match_cont params Kstop RustIRown.Kstop
| match_Kseq: forall k s tk ts
    (TRSTMT: transl_stmt ge params s (cont_vars k) = ts)
    (MCONT: match_cont params k tk),
    match_cont params (Kseq s k) (RustIRown.Kseq ts tk)
| match_Kloop: forall k tk s ts
    (MCONT: match_cont params k tk)
    (TRSTMT: transl_stmt ge params s (cont_vars (Kloop s k)) = ts),
    match_cont params (Kloop s k) (RustIRown.Kloop ts tk)
| match_Kcall: forall k tk p f tf le own
    (TRFUN: transl_function ge f = tf)
    (MCONT: match_cont f.(fn_params) k tk),
    match_cont params (Kcall p f le own k) (RustIRown.Kcall p tf le own tk)
| match_Kdropplace: forall k tk f tf st drops le own l dk
    (MCONT: match_cont_Kdropinsert f.(fn_params) (Kdropinsert l dk k) tk)
    (TRFUN: transl_function ge f = tf),
    match_cont params (Kdropplace f st drops le own (Kdropinsert l dk k)) (RustIRown.Kdropplace tf st drops le own tk)
| match_Kdropcall: forall k tk id v st membs
    (MCONT: match_cont params k tk),
    match_cont params (Kdropcall id v st membs k) (RustIRown.Kdropcall id v st membs tk)

with match_cont_Kdropinsert (params: list (ident * type)) : cont -> RustIRown.cont -> Prop :=
| match_Kdropinsert: forall k tk dk s1 s2 st
    (MCONT: match_cont params k tk)
    (* (MDCONT: match_dropcont dk s2) *)
    (MDINS: match_drop_insert_kind st s1)
    (MST: match_drop_insert_kind_dropcont params st dk s2)
    (WF: st <> drop_end),
    match_cont_Kdropinsert params (Kdropinsert st dk k)
      (* s1 should contain the storagedead of the first element of st *)
      (RustIRown.Kseq s1 (RustIRown.Kseq s2 tk))
| match_Kdropinsert_end: forall k tk dk  s2
    (MCONT: match_cont params k tk)
    (STMT2: match_dropcont dk s2)
    (WF: (forall p, dk <> Dreturn p) /\ dk <> Dendlet),
    match_cont_Kdropinsert params (Kdropinsert drop_end dk k)
      (* s1 should contain the storagedead of the first element of st *)
      (RustIRown.Kseq RustIR.Sskip (RustIRown.Kseq s2 tk))
.

Inductive match_states: Rustlightown.state -> RustIRown.state -> Prop := 
| match_regular_state: forall f s k e own m tf ts tk vars
    (TRFUN: transl_function ge f = tf)
    (TRSTMT: transl_stmt ge f.(fn_params) s vars = ts)
    (* The in-scope variables collected in transl_stmt are the same as
    those collected in the continuation *)
    (CONTVARS: cont_vars k = vars)
    (MCONT: match_cont f.(fn_params) k tk),
    match_states (State f s k e own m) (RustIRown.State tf ts tk e own m)
| match_dropinsert: forall f tf st dk k tk le own m ts1 ts2
    (TRFUN: transl_function ge f = tf)
    (STMT1: match_drop_insert_kind st ts1)
    (* (STMT2: match_dropcont dk ts2) *)
    (MST: match_drop_insert_kind_dropcont f.(fn_params) st dk ts2)
    (MCONT: match_cont f.(fn_params) k tk)
    (WF: st <> drop_end),
    match_states (Dropinsert f st dk k le own m) (RustIRown.State tf ts1 (RustIRown.Kseq ts2 tk) le own m)
(* move dropcont related statement to front *)
| match_dropinsert_end: forall f tf dk k tk le own m ts2 
    (TRFUN: transl_function ge f = tf)
    (STMT2: match_dropcont dk ts2)
    (MCONT: match_cont f.(fn_params) k tk)    
    (WF: (forall p, dk <> Dreturn p) /\ dk <> Dendlet),
    match_states (Dropinsert f drop_end dk k le own m) (RustIRown.State tf ts2 tk le own m)
| match_dropplace: forall f tf k tk st drops le m own dk l
    (TRFUN: transl_function ge f = tf)
    (MCONT: match_cont_Kdropinsert f.(fn_params) (Kdropinsert l dk k) tk),
    (* all dropplace comes from dropinsert *)
    match_states (Dropplace f st drops (Kdropinsert l dk k) le own m) (RustIRown.Dropplace tf st drops tk le own m)
| match_dropstate: forall id v st membs k tk m
    (* We does not care the parameters in drop glue state *)
    (MCONT: forall l, match_cont l k tk),
    match_states (Dropstate id v st membs k m) (RustIRown.Dropstate id v st membs tk m)
| match_callstate: forall v al k tk m
    (MCONT: forall l, match_cont l k tk)
    (ISCALL: is_call_cont k),
    match_states (Callstate v al k m) (RustIRown.Callstate v al tk m)
| match_returnstate: forall v k tk m
    (MCONT: forall l, match_cont l k tk),
    match_states (Returnstate v k m) (RustIRown.Returnstate v tk m)
.

Lemma gen_drops_for_escape_vars_nil:
    gen_drops_for_escape_vars ge nil = RustIR.Sskip.
Proof.
  auto.
Qed.

Lemma gen_drops_for_vars_nil:
    gen_drops_for_vars ge nil = RustIR.Sskip.
Proof.
  auto.
Qed.

  
Lemma gen_drops_for_escape_vars_cons1: forall id ty l ge,
    own_type ge ty = true ->
    gen_drops_for_escape_vars ge ((id, ty) :: l) =
      RustIR.Ssequence (Sdrop (Plocal id ty)) (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l)).
Proof.
  unfold gen_drops_for_escape_vars.
  intros. simpl in *. rewrite H. auto.
Qed.


Lemma gen_drops_for_escape_vars_cons2: forall id ty l ge,
    own_type ge ty = false ->
    gen_drops_for_escape_vars ge ((id, ty) :: l) =
      RustIR.Ssequence RustIR.Sskip (RustIR.Ssequence (Sstoragedead id) (gen_drops_for_escape_vars ge l)).
Proof.
  unfold gen_drops_for_escape_vars.
  intros. simpl in *. rewrite H.
 auto.
Qed.

Lemma gen_drops_for_vars_cons1: forall id ty l ge,
    own_type ge ty = true ->
    gen_drops_for_vars ge ((id, ty) :: l) =
      RustIR.Ssequence (Sdrop (Plocal id ty)) (gen_drops_for_vars ge l).
Proof.
  unfold gen_drops_for_vars.
  intros. simpl in *.
  unfold  vars_to_drops. simpl.
  rewrite H. 
  auto.
Qed.


Lemma gen_drops_for_vars_cons2: forall id ty l ge,
    own_type ge ty = false ->
    gen_drops_for_vars ge ((id, ty) :: l) =
      RustIR.Ssequence RustIR.Sskip (gen_drops_for_vars ge l).
Proof.
  unfold gen_drops_for_vars.
  intros. simpl in *.
  unfold  vars_to_drops. simpl.
  rewrite H.  
  auto.
Qed.

Ltac solve_eval :=
  try erewrite comp_env_preserved; eauto.

Lemma match_cont_call_cont: forall k ck tk l,
    call_cont k = Some ck ->
    match_cont l k tk ->
    exists tck,  RustIRown.call_cont tk = Some tck
              /\ (forall l', match_cont l' ck tck).
Proof.
  induction k; try (intros until l; intros A1 A2; simpl in *; inv A1; inv A2; simpl; eauto).
  - exists RustIRown.Kstop. split; auto.
    intros. constructor.
  - eexists.
    split; eauto.
    intros.
    econstructor; auto.
  - intros. simpl in *. inv H.
Qed.

Lemma drop_box_rec_eq: forall l b ofs m1 m2,
    drop_box_rec ge b ofs m1 l m2 ->
    RustIR.drop_box_rec tge b ofs m1 l m2.
Proof.
  induction l; intros.
  - inv H. constructor.
  - inv H. econstructor. eauto.
    eauto.
    inv H5. econstructor; eauto.
    eauto.
Qed.

Lemma drop_box_rec_eq_inv: forall l b ofs m1 m2,
    RustIR.drop_box_rec tge b ofs m1 l m2 ->
    drop_box_rec ge b ofs m1 l m2.
Proof.
  induction l; intros.
  - inv H. constructor.
  - inv H. econstructor. eauto.
    eauto.
    inv H5. econstructor; eauto.
    eauto.
Qed.


(* collect_func returns the same result in source and target *)

Lemma collect_stmt_drops_empty1: forall l w ce,
    RustIR.collect_stmt ce (gen_drops_for_escape_vars ce l) w = w.
Proof.
  induction l; intros; simpl; auto.
  - destruct a.
    destruct (own_type ce t) eqn: T.
    + rewrite gen_drops_for_escape_vars_cons1; auto. simpl.
      auto. 
    + rewrite gen_drops_for_escape_vars_cons2; auto. simpl.
      auto.
Qed.


Lemma collect_stmt_drops_empty2: forall l w ce,
    RustIR.collect_stmt ce (gen_drops_for_vars ce l) w = w.
Proof.
  induction l; intros; auto.
  - destruct a.
    destruct (own_type ce t) eqn: T.
    + rewrite gen_drops_for_vars_cons1; auto. simpl.
      auto. 
    + rewrite gen_drops_for_vars_cons2; auto. simpl.
      auto.
Qed.

Lemma collect_stmt_drops_empty3: forall p w ce,
    RustIR.collect_stmt ce (gen_drop ce p) w = w.
Proof.
  intros. unfold gen_drop.
  destruct own_type; auto.
Qed.

      
Lemma collect_stmt_eq: forall s w params vars ce,
    collect_stmt ce s w =
      RustIR.collect_stmt ce (transl_stmt ce params s vars) w.
Proof.
  induction s; intros; simpl; auto; try (rewrite collect_stmt_drops_empty3; auto).
  - rewrite collect_stmt_drops_empty1. auto.
  - erewrite IHs2. eauto.
  - erewrite IHs2. eauto.
  - rewrite collect_stmt_drops_empty1. auto.
  - rewrite collect_stmt_drops_empty1. auto.
  - rewrite collect_stmt_drops_empty2.
    rewrite collect_stmt_drops_empty1. auto.
Qed.

    
Lemma collect_func_eq: forall f tf ce,
    transl_function ce f = tf ->
    collect_func ce f = RustIR.collect_func ce tf.
Proof.
  unfold transl_function, collect_func, RustIR.collect_func.
  intros. subst. simpl in *.
  (* destruct list_norepet_dec; try congruence. *)
  f_equal.
  erewrite <- collect_stmt_eq. auto.
Qed.


Lemma init_own_env_eq: forall f tf ce,
    transl_function ce f = tf ->
    init_own_env ce f = RustIRown.init_own_env ce tf.
Proof.
  unfold transl_function. intros. subst.
  unfold init_own_env, RustIRown.init_own_env.
  destruct (collect_func ce f) eqn: A.
  - erewrite <- collect_func_eq. erewrite A.
    simpl.
    (* copy what we do in sound_function_entry (InitAnalysis) and
    match_transf_program (Clightgenproof) *)
    set (empty_pathmap := (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) t)) in *.
    (* set (initParams := (add_place_list t *)
    (*           (map (fun elt : ident * type => Plocal (fst elt) (snd elt)) (fn_params f)) *)
    (*           empty_pathmap)) in *. *)
    set (uninitVars := (add_place_list t (places_of_locals (fn_params f ++ fn_vars f)) empty_pathmap)) in *.
  set (flag := check_own_env_consistency empty_pathmap empty_pathmap  uninitVars t).
  generalize (eq_refl flag).
  (* so adhoc generalization... *)
  generalize flag at 1 3 7.
  intros flag0 E. destruct flag0; try congruence.
  repeat f_equal.
  auto.
  - erewrite <- collect_func_eq. erewrite A. simpl. auto.
    auto.
Qed.

Lemma function_entry_eq: forall f vl m1 e m2,
    function_entry ge f vl m1 e m2 ->
    RustIR.function_entry tge (transl_function tge f) vl m1 e m2.
Proof.
  intros. inv H. econstructor; solve_eval.
Qed.


Lemma step_dropstate_simulation:
  forall S1 t S2, step_drop ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  - eexists. split.
    econstructor. econstructor; eauto. econstructor; eauto.
    eapply star_refl. auto.
    rewrite type_to_drop_member_state_eq.
    econstructor; auto.
  - eexists. split.
    econstructor. econstructor; eauto.
    eapply RustIRown.step_dropstate_struct; solve_eval.
    eapply star_refl. auto.
    econstructor; auto.
    intros. econstructor. auto.
  - eexists. split.
    econstructor. econstructor; eauto.
    eapply RustIRown.step_dropstate_enum; solve_eval.
    eapply star_refl. auto.
    rewrite type_to_drop_member_state_eq.
    econstructor; auto.
    intros. econstructor. auto.
  - eexists. split.
    econstructor. econstructor; eauto.
    eapply RustIRown.step_dropstate_box; solve_eval.
    eapply drop_box_rec_eq; eauto.
    eapply star_refl. auto.
    econstructor; auto.
  - generalize (MCONT f.(fn_params)).
    intros MCONT1. inv MCONT1.
    eexists. split.
    econstructor. econstructor; eauto.
    eapply RustIRown.step_dropstate_return1; solve_eval.
    eapply star_refl. auto.
    econstructor; auto.
  - generalize (MCONT nil).
    intros MCONT1. inv MCONT1.    
    eexists. split.
    econstructor. econstructor; eauto.
    eapply RustIRown.step_dropstate_return2; solve_eval.
    eapply star_refl. auto.
    econstructor; auto.
    intros. generalize (MCONT l). intros MCONT2. inv MCONT2. auto.
Qed.

    
Lemma step_dropplace_simulation:
  forall S1 t S2, step_dropplace ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_dropplace_init1 *)
  - eexists. split.
    econstructor. econstructor; eauto. econstructor; eauto.
    eapply star_refl. auto.
    econstructor; auto.
  - eexists. split.
    econstructor. econstructor. eapply RustIRown.step_dropplace_init2; eauto.
    eapply star_refl. auto.
    econstructor; auto.
  (* step_dropplace_scalar *)
  - eexists. split.
    econstructor. econstructor. eapply RustIRown.step_dropplace_scalar; eauto.
    eapply star_refl. auto.
    econstructor; auto.
  - eexists. split.
    econstructor. econstructor. econstructor; solve_eval.
    eapply star_refl. auto.
    econstructor; auto.
  - eexists. split.
    econstructor. econstructor. econstructor; solve_eval.
    eapply star_refl. auto.
    econstructor; auto.
    intros. econstructor; auto.
  - eexists. split.
    econstructor. econstructor. eapply RustIRown.step_dropplace_enum; solve_eval.
    eapply star_refl. auto.
    rewrite type_to_drop_member_state_eq.
    econstructor.
    intros. econstructor; auto.
  - eexists. split.
    econstructor. econstructor. econstructor; eauto.
    eapply star_refl. auto.
    econstructor; auto.
  - inv MCONT.
    + (* destruct (drop_insert_kind_eq l drop_end); subst. *)
      (* * inv MST. inv MDINS. *)
      (*   eexists. split. *)
      (*   econstructor. econstructor; eauto. *)
      (*   econstructor. *)
      (*   eapply star_step. eapply RustIRown.step_skip_seq. *)
      (*   eapply star_step. eapply RustIRown.step_skip_seq. *)
      (*   eapply star_refl. 1-3: eauto. *)
      (*   eapply match_dropinsert_end; auto. *)
      eexists. split.
      econstructor. econstructor; eauto.
      econstructor.
      eapply star_step. eapply RustIRown.step_skip_seq.
      eapply star_refl. 1-2: eauto.
      econstructor; auto.
    + (* inv MST. inv MDINS. *)
      eexists. split.
      econstructor. econstructor; eauto.
      econstructor.
      eapply star_step. eapply RustIRown.step_skip_seq.
      eapply star_step. eapply RustIRown.step_skip_seq.
      eapply star_refl. 1-3: eauto.
      eapply match_dropinsert_end; auto.
Qed.

    
Lemma step_in_dropinsert_simulation:
  forall S1 t S2, step_dropinsert ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS; try congruence.
  (* step_dropinsert_to_dropplace_escape *)
  - inv STMT1.
    erewrite gen_drops_for_escape_vars_cons1; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto. rewrite comp_env_preserved. eauto. 
    eapply star_refl. 1-2 : eauto.
      (* match_states *)
    econstructor; auto.
    econstructor; auto.
    econstructor; auto.
    2: congruence.
    inv MST.
    + econstructor; auto. congruence.
    + eapply match_drop_insert_kind_dropcont_Dendlet2.
    + eapply match_drop_insert_kind_dropcont_return2; auto.
  (* step_dropinsert_to_dropplace_reassign *)
  - inv MST. inv STMT1. unfold gen_drop. rewrite OWNTY. simpl.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto. rewrite comp_env_preserved. eauto.
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    eapply match_Kdropinsert_end; eauto.
    (* econstructor; auto. *)
    (* constructor; auto. congruence. *)
  (* step_dropinsert_skip_escape *)
  - inv STMT1.
    erewrite gen_drops_for_escape_vars_cons2; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor.
    eapply star_step. eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-2: eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    2: congruence.
    inv MST.
    + econstructor; auto. congruence.
    + eapply match_drop_insert_kind_dropcont_Dendlet2.
    + eapply match_drop_insert_kind_dropcont_return2; auto.
    (* congruence. *)
  (* step_dropinsert_skip_reassign *)
  - inv MST. inv STMT1. unfold gen_drop. rewrite OWNTY. simpl.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto.
    eapply star_step. eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-3 : eauto.
    (* match_states *)
    eapply match_dropinsert_end ; auto.
  (* step_dropinsert_to_dropplace_return *)
  - inv STMT1. erewrite gen_drops_for_vars_cons1; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor; eauto.
    rewrite comp_env_preserved. eauto.
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    econstructor; auto.
    inv MST.
    econstructor; auto. congruence.
    eapply match_drop_insert_kind_dropcont_return3; auto.
    congruence.
  (* step_dropinsert_skip_return *)
  - inv STMT1. erewrite gen_drops_for_vars_cons2; eauto.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-2 : eauto.
    (* match_states *)
    econstructor; auto.
    econstructor; auto.
    inv MST.
    econstructor; auto. congruence.
    eapply match_drop_insert_kind_dropcont_return3; auto.
    congruence.
  (* step_dropinsert_escape_to_after *)
  - inv STMT1.
    eexists. split.
    (* step *)
    econstructor.
    econstructor. eapply star_step.
    econstructor. eapply star_step.
    eapply RustIRown.step_skip_seq.
    eapply star_refl. 1-3 : eauto.
    (* match_state *)
    econstructor; auto.
    constructor.
    2: congruence.
    inv MST. 
    + econstructor; auto. congruence.
    + eapply match_drop_insert_kind_dropcont_Dendlet1.
    + eapply match_drop_insert_kind_dropcont_return1; auto.
    (* congruence.       *)
  (* step_dropinsert_to_drop_end *)
  - inv STMT1. rewrite gen_drops_for_escape_vars_nil.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_refl. auto.
    econstructor; auto.
    inv MST; auto. econstructor.
    destruct NOTRETURN as (N1 & N2).
    generalize (N1 p). congruence.
    (* intros. eapply NOTRETURN. *)
  (* step_dropinsert_assign *)
  - inv STMT2.
    eexists. split.
    econstructor.
    econstructor; solve_eval.
    eapply star_refl. eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinsert_assign_variant *)
  - inv STMT2.
    eexists. split.
    econstructor.
    econstructor; solve_eval.
    eapply star_refl. eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinsert_box *)
  - inv STMT2.
    eexists. split.
    econstructor.  econstructor; solve_eval.
    eapply star_refl.  eauto.
    (* match_states *)
    econstructor; eauto.
  (* step_dropinset_call *)
  - inv STMT2.
    exploit find_funct_match_id; eauto.
    intros (tf & FIND & TRF).
    eexists. split.
    econstructor. econstructor; solve_eval.
    eapply function_not_drop_glue_preserved; eauto.
    erewrite type_of_fundef_preserved; eauto.
    eapply star_refl. eauto.
    (* match_states *)
    econstructor; eauto.
    intros. econstructor; auto.
    simpl. auto.
  (* step_dropinsert_break_seq *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. econstructor.
    eapply star_refl. eauto.
    (* match_state *)
    econstructor; auto.
    constructor.
  (* step_dropinsert_break_let *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. econstructor.
    eapply star_step. econstructor.
    eapply star_refl.  1-2: eauto.
    (* match_state *)
    eapply match_dropinsert_end ; auto.
    constructor.
  (* step_dropinsert_break_loop *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_break_loop.
    eapply star_refl. eauto.
    (* match_state *)
    econstructor; auto.
  (* step_dropinsert_continue_seq *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_continue_seq.
    eapply star_refl. eauto.
    (* match_state *)
    econstructor; auto.
    constructor.
  (* step_dropinsert_continue_let *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_continue_seq.
    eapply star_step. econstructor.
    eapply star_refl.  1-2: eauto.
    (* match_state *)
    econstructor; auto.
    constructor.
  (* step_dropinsert_continue_loop *)
  - inv STMT2. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_or_continue_loop. auto.
    eapply star_refl. eauto.
    (* match_state *)
    econstructor; auto. simpl.
    constructor; auto.
  (* step_dropinsert_return_before (to drop the parameters) *)
  - inv STMT1. inv MST.
    + destruct NOTRET as (N1 & N2). generalize (N1 p). congruence.
    + eexists. split. rewrite gen_drops_for_escape_vars_nil.
      econstructor. eapply RustIRown.step_skip_seq.
      eapply star_step. econstructor.
      eapply star_refl. 1-2: auto.
      econstructor; eauto.
      econstructor.
      eapply match_drop_insert_kind_dropcont_return3. auto.
      congruence.
  (* step_dropinsert_return_after *)
  - inv STMT1. inv MST.
    destruct NOTRET as (N1 & N2).
    generalize (N1 p). congruence.
    inv MRET.
    exploit match_cont_call_cont; eauto.
    intros (tck & CK & MK).
    eexists. split. rewrite gen_drops_for_vars_nil.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_step. econstructor; solve_eval.
    eapply star_refl. 1-2: eauto.
    econstructor. auto.
  (* step_dropinsert_endlet *)
  - inv STMT1. 
    rewrite gen_drops_for_escape_vars_nil.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_refl. auto.
    inv MST. destruct NOTRET. congruence.
    econstructor; auto.
Qed.

   
Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus RustIRown.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros; inv MS.
  (* step_assign *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
    econstructor.
    split.
    all: congruence. 
  (* step_assign_variant *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
    econstructor. 
    split.
    all: congruence. 
  (* step_box *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor. econstructor.
    split.
    all: congruence. 
  (* step_let *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_step. econstructor.
    eapply star_step. eapply RustIRown.step_skip_seq.
    eapply star_step. econstructor.
    eapply star_step. econstructor.
    eapply star_refl. 1-5: eauto.
    econstructor; auto.
    econstructor; auto.
  (* step_end_let *)
  - simpl. inv MCONT.
    eexists. split.
    econstructor. eapply RustIRown.step_skip_seq.
    eapply star_refl. auto.
    econstructor; auto.
    constructor. eapply match_drop_insert_kind_dropcont_Dendlet1. 
    congruence. 
  (* step_in_dropinsert (not drop_end) *)
  - eapply step_in_dropinsert_simulation; eauto.
    econstructor; eauto.
  (* step_in_dropinsert *)
  - eapply step_in_dropinsert_simulation; eauto.
    econstructor; eauto.
  (* step_in_dropplace *)
  - eapply step_dropplace_simulation; eauto.
    econstructor; eauto.
  (* step_dropstate *)
  - eapply step_dropstate_simulation; eauto.
    econstructor; eauto.
  (* step_call *)
  - simpl.
    eexists. split.
    (* step *)
    econstructor. econstructor.
    eapply star_refl. auto.
    econstructor; auto.
    econstructor. econstructor.
    constructor.
    split. 
    all: congruence. 
  (* step_internal_function *)
  - exploit find_funct_match_id; eauto.
    intros (tf & A1 & A2). simpl in A2. subst.
    eexists. split.
    econstructor. eapply RustIRown.step_internal_function.
    5: { eapply function_entry_eq. eauto. }
    1-3: solve_eval.
    erewrite <- init_own_env_eq; eauto. eauto.
    eapply star_refl. auto.
    econstructor; eauto.
    solve_eval.
    unfold transl_function. simpl.
    replace (prog_comp_env prog) with (genv_cenv ge); auto.
    erewrite <- comp_env_preserved.
    destruct k; simpl in *; try contradiction; auto.        
  (* step_external_function *)
  - exploit find_funct_match_id; eauto.
    intros (tf & A1 & A2). simpl in A2. subst.
    simpl in H.
    eexists. split.
    econstructor. eapply RustIRown.step_external_function; eauto.
    eapply star_refl. eapply app_nil_end.
    econstructor. auto.    
  (* step_return_1 *)
  - eexists. split.
    econstructor. simpl.
    econstructor. eapply star_refl. auto.
    econstructor; auto.
    econstructor.
    eapply match_drop_insert_kind_dropcont_return1.
    econstructor. econstructor.
    congruence.    
  (* step_returnstate *)
  - generalize (MCONT nil). intros MCONT1. inv MCONT1.
    eexists. split.
    econstructor.
    econstructor; solve_eval.
    eapply star_refl. auto.
    econstructor; eauto.    
  (* step_seq *)
  - eexists. split.
    econstructor. simpl. econstructor.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_seq *)
  - inv MCONT.
    eexists. split.
    econstructor. simpl. eapply RustIRown.step_skip_seq.
    eapply star_refl. auto.
    econstructor; eauto.
  (* step_continue_insert_drops *)    
  - eexists. split.
    econstructor. simpl. econstructor.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor. econstructor.
    split.
    all: congruence. 
  (* step_break_insert_drops *)    
  - eexists. split.
    econstructor. simpl. econstructor.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor; eauto.
    econstructor. econstructor.
    split.
    all: congruence. 
  (* step_ifthenelse *)
  - eexists. split.
    econstructor. simpl. econstructor; solve_eval.
    eapply star_refl. auto.
    econstructor; eauto.
    destruct b;
    econstructor; eauto.
  (* step_loop *)
  - eexists. split.
    econstructor. simpl. econstructor.
    eapply star_refl. auto.
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_loop *)
  - inv MCONT.
    destruct H; subst.
    + eexists. split.
      econstructor. simpl.    
      eapply RustIRown.step_skip_or_continue_loop. auto.
      eapply star_refl. auto.
      econstructor; eauto.
      econstructor; eauto.
    + eexists. split.
      econstructor. simpl.
      setoid_rewrite gen_drops_for_escape_vars_nil.
      econstructor. eapply star_step.
      eapply RustIRown.step_skip_seq.
      eapply star_step.
      eapply RustIRown.step_skip_or_continue_loop. auto.
      eapply star_refl. 1-3: eauto.
      econstructor; eauto.
      econstructor; eauto.
Qed.

Lemma initial_states_simulation:
  forall q S, initial_state ge q S ->
  exists R, RustIRown.initial_state tge q R /\ match_states S R.
Proof.
  intros. inv H.
  exploit find_funct_match_id; eauto.
  intros (tf & A1 & A2). simpl in A2. subst.
  eexists. split.
  rewrite <- comp_env_preserved. 
  econstructor; eauto.
  econstructor; simpl; auto.
  intros. constructor.
Qed.

Lemma external_states_simulation: forall S R q,
    match_states S R -> at_external ge S q ->
    RustIRown.at_external tge R q /\
      forall r S', after_external S r S' ->
              exists R', RustIRown.after_external R r R' /\ match_states S' R'.
Proof.
  intros S R q HSR Hq. destruct Hq. inv HSR.
  exploit find_funct_match_id; eauto.
  intros (tf & A1 & A2). simpl in A2. subst.
  split.
  (* at_external *)
  rewrite <- comp_env_preserved. econstructor; eauto.
  (* after_external *)
  intros r S' AF. inv AF.
  eexists. split.
  econstructor.
  econstructor. auto.
Qed.

Lemma final_states_simulation: forall S R r,
  match_states S R -> final_state S r -> RustIRown.final_state R r.
Proof.
  intros. inv H0. inv H. generalize (MCONT nil).
  intros. inv H. constructor.
Qed.

(** The progress property used to prove the safety of Rustlight *)

Let L1 := Rustlightown.semantics prog se.
Let L2 := RustIRown.semantics tprog se.


Lemma match_drop_insert_kind_inv: forall st s,
    match_drop_insert_kind st s ->
    (match s with
     | RustIR.Ssequence _ _
     | RustIR.Sskip => True
     | _ => False         
     end).
Proof.
  intros st s M.
  inv M; auto.
  - unfold gen_drop. destruct own_type; simpl; auto.
  - unfold gen_drops_for_escape_vars. destruct l; simpl; auto.
    destruct p. destruct own_type; simpl; auto.
  - unfold gen_drops_for_vars. destruct l; simpl; auto.
Qed.    

  
Ltac solve_eval1 :=
  try erewrite <- !comp_env_preserved; eauto.


Lemma function_entry_eq_inv: forall f vl m1 e m2,
    RustIR.function_entry tge (transl_function tge f) vl m1 e m2 ->
    function_entry ge f vl m1 e m2.
Proof.
  intros. inv H. econstructor; solve_eval1.
Qed.

Lemma match_cont_call_cont_inv: forall k tck tk l,
    RustIRown.call_cont tk = Some tck ->
    match_cont l k tk ->
    exists ck, call_cont k = Some ck
          /\ (forall l', match_cont l' ck tck).
Proof.
  induction k; try (intros until l; intros A1 A2; inv A2; simpl in *; inv A1; simpl; eauto).
  - exists Kstop. split; auto.
    intros. constructor.
  - eexists.
    split; eauto.
    intros.
    econstructor; auto.
  - intros. simpl in *. inv H0. simpl in H. congruence.
Qed.


Lemma match_progress: forall s1 s2,
    match_states s1 s2 ->
    safe L2 s2 ->
    (exists r, final_state s1 r)
    \/ (exists q, at_external ge s1 q)
    \/ (exists t, exists s1', step ge s1 t s1').
Proof.
  intros s1 s2 MATCH SAFE.
  exploit SAFE. eapply star_refl.
  (* target takes one step *)
  intros [(r2 & FINAL2)|[(q2 & ATEXT2)|(t2 & s2' & STEP2)]].
  - simpl in FINAL2.
    inv MATCH; inv FINAL2; try congruence.
    left. exists (rsr v m).
    generalize (MCONT nil). intros. inv H. econstructor.
  - simpl in ATEXT2. inv MATCH; inv ATEXT2.
    right. left.
    exploit find_funct_match_id_inv; eauto. intros (f & FIND & TR).
    destruct f; simpl in TR; try congruence. inv TR.
    eexists. econstructor; eauto.
  - right. right.
    generalize STEP2 as STEP2'. intros.
    simpl in STEP2. inv STEP2.
    (* step_assign *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      (* match_dropinsert: prove that STMT1 is impossible *)
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
        do 2 eexists. econstructor.
        econstructor; eauto; solve_eval1.
    (* step_assign_variant *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      (* match_dropinsert: prove that STMT1 is impossible *)
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
        do 2 eexists. econstructor.
        econstructor; eauto; solve_eval1.        
    (* step_box *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      (* match_dropinsert: prove that STMT1 is impossible *)
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
        do 2 eexists. econstructor.
        econstructor; eauto; solve_eval1.
    (* step_to_dropplace *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction. 
      * inv STMT2.
    (* step_in_dropplace *)
    + inv MATCH. inv SDROP.
      * do 2 eexists; econstructor; econstructor; eauto.
      * do 2 eexists. econstructor. eapply step_dropplace_init2; eauto.
      * do 2 eexists. econstructor. eapply step_dropplace_scalar; eauto.
      * do 2 eexists. econstructor. econstructor; eauto. solve_eval1.
      * do 2 eexists. econstructor. econstructor; eauto; solve_eval1.
      * do 2 eexists. econstructor. eapply step_dropplace_enum; eauto; solve_eval1.
      * do 2 eexists. econstructor. econstructor; eauto; solve_eval1.
      * do 2 eexists. econstructor. econstructor.
    (* step_in_dropstate *)
    + inv MATCH. inv SDROP.
      * do 2 eexists. econstructor. econstructor.
      * do 2 eexists. econstructor. econstructor; solve_eval1.
      * do 2 eexists. econstructor. econstructor; solve_eval1.
      * do 2 eexists. econstructor. econstructor; solve_eval1.
        eapply drop_box_rec_eq_inv; eauto.
      * generalize (MCONT nil). intros MCONT1. inv MCONT1.        
        do 2 eexists. econstructor.
        econstructor; solve_eval1.
      * generalize (MCONT nil). intros MCONT1. inv MCONT1.        
        do 2 eexists. econstructor.
        econstructor; solve_eval1.
    (* Sstoragelive *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction. 
      * inv STMT2.
    (* Sstoragedead *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction. 
      * inv STMT2.
    (* step_call *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
        exploit find_funct_match_id_inv; eauto. intros (f1 & FIND & TR).
        do 2 eexists.
        econstructor. econstructor; solve_eval1.
        erewrite <- type_of_fundef_preserved; eauto.
        intros. subst.
        eapply function_not_drop_glue_preserved_inv; eauto.
    (* step_internal_function *)
    + inv MATCH.
      exploit find_funct_match_id_inv; eauto. intros (f1 & FIND1 & TR).
      destruct f1; simpl in TR; inv TR.
      do 2 eexists.
      econstructor; solve_eval1.
      replace (prog_comp_env prog) with (RustIR.genv_cenv tge) in ENTRY.
      eapply function_entry_eq_inv in ENTRY. solve_eval.
      solve_eval.
      erewrite init_own_env_eq; eauto.
      (* solve_eval. *)
    (* step_external_function *)
    + inv MATCH.
      exploit find_funct_match_id_inv; eauto. intros (f1 & FIND1 & TR).
      destruct f1; simpl in TR; inv TR.
      do 2 eexists.
      eapply step_external_function; solve_eval1.
    (* step_return_1 *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2. destruct WF as (N1 & N2). generalize (N1 p). intros. congruence.
    (* step_returnstate *)
    + inv MATCH. generalize (MCONT nil). intros MCONT1.
      inv MCONT1.
      do 2 eexists. econstructor; eauto; solve_eval1.
    (* step_seq *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
        all: do 2 eexists; econstructor; eauto.
      * inv STMT1.
        -- eapply star_safe in SAFE.
           (* show that L1 can take one more step *)
           2: { eapply star_step; eauto. eapply star_refl. eauto. }
           unfold gen_drop in H1.    
           destruct own_type eqn: OWNTY in H1; simpl in H1; inv H1.
           ++ (* own_type is true, to show source can take
              step_dropinsert_to_dropplace_reassign, we need to show
              split_drop_place return OK *)
              exploit SAFE. eapply star_refl.
              (* final and at_external is impossible *)
              intros [(r2 & CON)|[(q2 & CON)|(t2 & s2' & STEP2)]]; try inv CON.
              inv STEP2.
              do 2 eexists.
              econstructor. econstructor; eauto. simpl in SPLIT.
              solve_eval1.
           ++ do 2 eexists.
              econstructor. eapply step_dropinsert_skip_reassign; eauto.
        -- eapply star_safe in SAFE.
           (* show that L1 can take one more step *)
           2: { eapply star_step; eauto. eapply star_refl. eauto. }
           unfold gen_drops_for_escape_vars in H1. destruct l; simpl in H1. inv H1.
           destruct p; simpl in H1.
           destruct own_type eqn: OWNTY in H1; simpl in H1; inv H1.
           (* similar to the above case *)
           ++ exploit SAFE. eapply star_refl.
              (* final and at_external is impossible *)
              intros [(r2 & CON)|[(q2 & CON)|(t2 & s2' & STEP2)]]; try inv CON.
              inv STEP2. simpl in SPLIT.
              do 2 eexists.
              econstructor. econstructor; eauto. 
              solve_eval1.
           ++ do 2 eexists.
              econstructor. eapply step_dropinsert_skip_escape; eauto.
        -- do 2 eexists. econstructor. econstructor.
        -- eapply star_safe in SAFE.
           (* show that L1 can take one more step *)
           2: { eapply star_step; eauto. eapply star_refl. eauto. }
           unfold gen_drops_for_vars in H1. destruct l; simpl in H1. inv H1.
           destruct p; simpl in H1.
           destruct own_type eqn: OWNTY in H1; simpl in H1; inv H1.
           ++ exploit SAFE. eapply star_refl.
              (* final and at_external is impossible *)
              intros [(r2 & CON)|[(q2 & CON)|(t2 & s2' & STEP2)]]; try inv CON.
              inv STEP2. simpl in SPLIT.
              do 2 eexists.
              econstructor. econstructor; eauto.
              solve_eval1.
           ++ do 2 eexists.
              econstructor. eapply step_dropinsert_skip_return; eauto.
      * inv STMT2.
    (* step_skip_seq *)
    + inv MATCH.
      * destruct s0; simpl in TRSTMT; try congruence.
        inv MCONT.
        -- do 2 eexists. econstructor.
        -- do 2 eexists. econstructor.
      * inv STMT1.
        -- unfold gen_drop in H1.
           destruct own_type eqn: OWNTY in H1; inv H1.
        -- unfold gen_drops_for_escape_vars in H1. destruct l; simpl in H1.
           2: { destruct p; destruct own_type; inv H1. }
           inv MST.
           ++ inv MDCONT; try (do 2 eexists; econstructor; econstructor; intros; split; congruence; fail).
           ++ do 2 eexists. econstructor. eapply step_dropinsert_endlet.
           ++ inv MRET.
              do 2 eexists. econstructor. eapply step_dropinsert_return_before.
        -- unfold gen_drops_for_vars in H1. destruct l; simpl in H1.
           2: { destruct p; destruct own_type; inv H1. }
           inv MST.
           ++ congruence. 
           ++ inv MRET.
              eapply star_safe in SAFE.
              (* show that L1 can take one more step *)
              2: { eapply star_step; eauto. eapply star_refl. eauto. }
              exploit SAFE. eapply star_refl.
              intros [(r2 & CON)|[(q2 & CON)|(t2 & s2' & STEP2)]]; try inv CON.
              inv STEP2.
              2: { destruct H8; congruence. }
                exploit match_cont_call_cont_inv; eauto.
              intros (ck1 & A1 & A2).
              do 2 eexists. econstructor. eapply step_dropinsert_return_after; solve_eval1.
        -- congruence.
      * inv STMT2. destruct WF. congruence.
    (* step_continue_seq *)
    + inv MATCH.
      * destruct s0; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2. inv MCONT.
        -- do 2 eexists. econstructor. econstructor.
        -- do 2 eexists. econstructor. econstructor.
    (* step_break_seq *)
    + inv MATCH.
      * destruct s0; simpl in TRSTMT; try congruence.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2. inv MCONT.
        -- do 2 eexists. econstructor. econstructor.
        -- do 2 eexists. econstructor. econstructor.
    (* step_ifthenelse *)
    + inv MATCH.
      * destruct s; simpl in TRSTMT; try congruence.
        inv TRSTMT.
        do 2 eexists.
        econstructor; solve_eval1.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
    (* step_loop *)
     + inv MATCH.
      * destruct s0; simpl in TRSTMT; try congruence.
        inv TRSTMT.
        do 2 eexists.
        econstructor; solve_eval1.
      * exploit match_drop_insert_kind_inv; eauto. simpl. contradiction.
      * inv STMT2.
     (* step_skip_or_continue_loop *)
     + inv MATCH.
       * destruct H; inv MCONT.
         -- destruct s0; simpl in H; try congruence.
            do 2 eexists. econstructor; solve_eval1.
         -- destruct s0; simpl in H; try congruence.
       * inv MCONT.  destruct H; subst; inv STMT2.
         -- destruct WF. congruence.
         -- do 2 eexists. econstructor; econstructor; solve_eval1.
     (* step_break_loop *)
     + inv MATCH.
      * destruct s0; simpl in TRSTMT; try congruence.
      * inv STMT2. inv MCONT.
        do 2 eexists. econstructor; econstructor; solve_eval1.
Qed.        

Lemma initial_progress: forall q s2,      
      RustIRown.initial_state tge q s2 ->
      exists s1, initial_state ge q s1.
Proof.
  intros q s2 INIT. inv INIT.
  exploit find_funct_match_id_inv; eauto. intros (f1 & FIND1 & TR).
  destruct f1; simpl in TR; inv TR.
  erewrite comp_env_preserved.
  eexists. econstructor; solve_eval1.
Qed.

Lemma external_progress: forall s2 s2' s1 r,
    match_states s1 s2 ->
    RustIRown.after_external s2 r s2' ->
    exists s1', after_external s1 r s1'.
Proof.
  intros. inv H0. inv H.  
  eexists. econstructor.
Qed.

(** Proof of the preservation of memory error *)

Lemma drop_box_rec_mem_error_implies: forall b ofs m tys,
    drop_box_rec_mem_error ge b ofs m tys ->
    RustIR.drop_box_rec_mem_error tge b ofs m tys.
Proof.
  intros. induction H.
  - econstructor; eauto.
  - eapply RustIR.drop_box_rec_error2; eauto.
  - eapply RustIR.drop_box_rec_error3; eauto.
  - eapply RustIR.drop_box_rec_error4; eauto.
Qed.
    
Lemma mem_error_preservation: forall s1 s2,
    step_mem_error ge s1 ->
    match_states s1 s2 ->
    exists s2', star RustIRown.step tge s2 E0 s2'
           /\ RustIRown.step_mem_error tge s2'.
Proof.
  intros s1 s2 Err MATCH.
  inv MATCH; inv Err.
  (* step_ifthenelse_error *)
  - eexists. split.
    eapply star_refl.
    econstructor. solve_eval.
  - inv H0; try congruence.
    (* step_dropinsert_return_error1 *)
    + inv STMT1. rewrite gen_drops_for_vars_nil.
      inv MST.
      * inv MDCONT. eexists. split.
        eapply star_step.
        eapply RustIRown.step_skip_seq. eapply star_refl. eauto.
        eapply RustIRown.step_return_error1; solve_eval.
      * inv MRET. eexists. split.
        eapply star_step.
        eapply RustIRown.step_skip_seq. eapply star_refl. eauto.
        eapply RustIRown.step_return_error1; solve_eval.
    (* step_dropinsert_return_error2 *)
    + inv STMT1. inv MST.
      * inv MDCONT. eexists. split.
        eapply star_step.
        eapply RustIRown.step_skip_seq. eapply star_refl. eauto.
        eapply RustIRown.step_return_error2; solve_eval.
      * inv MRET. eexists. split.
        eapply star_step.
        eapply RustIRown.step_skip_seq. eapply star_refl. eauto.
        eapply RustIRown.step_return_error2; solve_eval.
  - inv H0; try congruence.
    all: inv STMT2; eexists; split; [eapply star_refl|].
    (* step_assign_error *)
    eapply step_assign_error1; solve_eval.
    eapply step_assign_error2; solve_eval.
    eapply step_assign_error3; solve_eval.
    eapply step_assign_error4; solve_eval.
    (* step_assign_variant_error *)
    eapply step_assign_variant_error1; solve_eval.
    eapply step_assign_variant_error2; solve_eval.
    eapply step_assign_variant_error3; solve_eval.
    eapply step_assign_variant_error4; solve_eval.
    eapply step_assign_variant_error5; solve_eval.
    (* step_box_error *)
    eapply step_box_error1; solve_eval.
    eapply step_box_error2; solve_eval.
    eapply step_box_error3; solve_eval.
    eapply step_box_error4; solve_eval.
    eapply step_box_error5; solve_eval.
    (* step_call_error *)
    eapply step_call_error1; solve_eval.
    eapply step_call_error2; solve_eval.
  - inv MCONT.
    + inv H0.      
      all: eexists; split; [eapply star_refl| econstructor].
      (* step_dropplace_box_error *)
      eapply RustIRown.step_dropplace_box_error1; solve_eval.
      eapply RustIRown.step_dropplace_box_error2; solve_eval.
      eapply RustIRown.step_dropplace_box_error3; solve_eval.
      eapply RustIRown.step_dropplace_struct_error; solve_eval.
      eapply RustIRown.step_dropplace_enum_error1; solve_eval.
      eapply RustIRown.step_dropplace_enum_error2; solve_eval.
    + inv H0.
      all: eexists; split; [eapply star_refl| econstructor].
      (* step_dropplace_box_error *)
      eapply RustIRown.step_dropplace_box_error1; solve_eval.
      eapply RustIRown.step_dropplace_box_error2; solve_eval.
      eapply RustIRown.step_dropplace_box_error3; solve_eval.
      eapply RustIRown.step_dropplace_struct_error; solve_eval.
      eapply RustIRown.step_dropplace_enum_error1; solve_eval.
      eapply RustIRown.step_dropplace_enum_error2; solve_eval.
  - inv H0.    
    all: eexists; split; [eapply star_refl| econstructor].
    eapply RustIRown.step_dropstate_struct_error; solve_eval.
    eapply RustIRown.step_dropstate_enum_error1; solve_eval.
    eapply RustIRown.step_dropstate_enum_error2; solve_eval.
    eapply RustIRown.step_dropstate_box_error; solve_eval.
    eapply drop_box_rec_mem_error_implies. eauto.
  - eexists. split.
    eapply star_refl.
    exploit find_funct_match_id; eauto. intros (tf & A1 & A2).
    destruct tf; simpl in A2; inv A2.    
    econstructor; solve_eval.
    erewrite <- init_own_env_eq; eauto.
    inv H0.
    econstructor; solve_eval.
  - eexists. split.
    eapply star_refl.
    specialize (MCONT nil). inv MCONT.
    econstructor; solve_eval.
  - eexists. split.
    eapply star_refl.
    specialize (MCONT nil). inv MCONT.
    eapply RustIRown.step_returnstate_error2 ; solve_eval.
Qed.  

End PRESERVATION.

(* forward simulation with the progress property *)
Theorem transl_program_correct1 prog tprog:
   match_prog prog tprog ->
   forward_simulation_progress_ubpreserve cc_id cc_id (semantics prog) (RustIRown.semantics tprog) (mem_error prog) (RustIRown.mem_error tprog).
Proof.
  fsimp eapply forward_simulation_plus; simpl in *. 
  - symmetry. eapply match_prog_skel. auto.
  - intros q _ [ ]. subst. eapply is_internal_match_id. eauto.
    intros. destruct f; simpl in H. subst. auto. subst. auto.
  - intros. subst. eapply initial_states_simulation; eauto.
  - intros. exists r1. split. eapply final_states_simulation; eauto. auto.
  - intros. subst. edestruct external_states_simulation; eauto. exists tt, q1. intuition subst; eauto.
  - intros. eapply step_simulation; eauto. subst. auto.
  - intros. subst. eapply initial_progress; eauto.
  - intros. destruct H. subst. eapply external_progress; eauto.
  - intros. destruct H. subst. eapply match_progress; eauto.
  - intros. destruct H. subst.
    eapply mem_error_preservation; eauto.    
Qed.

Theorem transl_program_correct prog tprog:
   match_prog prog tprog ->
   forward_simulation cc_id cc_id (semantics prog) (RustIRown.semantics tprog).
Proof.
  intros.
  eapply fsim_progress_ubpreserve_implies; eauto.
  eapply transl_program_correct1; eauto.
Qed.
