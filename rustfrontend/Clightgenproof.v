Require Import Coqlib.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import AST Linking.
Require Import Ctypes Rusttypes.
Require Import Cop.
Require Import Clight.
Require Import RustlightBase RustIR RustIRsem RustOp.
Require Import Errors.
Require Import Clightgen Clightgenspec.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Import ListNotations.

Local Open Scope error_monad_scope.
Local Open Scope gensym_monad_scope.

(** Correctness proof for the generation of Clight *)

Definition match_glob (ctx: clgen_env) gd tgd : Prop :=
  match gd, tgd with
  | Gvar v1, Gvar v2 =>
      match_globvar (fun ty ty' => to_ctype ty = ty') v1 v2
  | Gfun fd1, Gfun fd2 =>
      tr_fundef ctx fd1 fd2
  | _, _ => False
  end.

Record match_prog (p: RustIR.program) (tp: Clight.program) : Prop := {
    match_prog_main:
    tp.(prog_main) = p.(prog_main);
    match_prog_public:
    tp.(prog_public) = p.(prog_public);
    match_prog_comp_env:
    tr_composite_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env);
    match_prog_def:
    (* match_program_gen tr_fundef (fun ty ty' => to_ctype ty = ty') p p tp; *)
    forall id, Coqlib.option_rel (match_glob (build_clgen_env p tp)) ((prog_defmap p)!id) ((prog_defmap tp)!id);
    match_prog_skel:
    erase_program tp = erase_program p;
    match_prog_malloc:
    exists orgs rels tyl rety cc, (prog_defmap p) ! malloc_id = Some (Gfun (Rusttypes.External orgs rels EF_malloc tyl rety cc));
    match_prog_free:
    exists orgs rels tyl rety cc, (prog_defmap p) ! free_id = Some (Gfun (Rusttypes.External orgs rels EF_free tyl rety cc));
    match_prog_wf_param_id:
    list_disjoint [param_id] (malloc_id :: free_id :: (map snd (PTree.elements (clgen_dropm (build_clgen_env p tp)))))
  }.

Lemma match_globdef: forall l tl ctx id,
    transf_globdefs (transl_fundef (clgen_src_cenv ctx) (clgen_tgt_cenv ctx) (clgen_dropm ctx) (clgen_glues ctx)) transl_globvar l = OK tl ->
    Coqlib.option_rel (match_glob ctx) ((PTree_Properties.of_list l) ! id) ((PTree_Properties.of_list tl) ! id).
Proof.
  intros l tl ctx id TR.
  eapply PTree_Properties.of_list_related.
  generalize dependent tl.
  generalize dependent l.
  induction l; simpl; intros.
  inv TR. econstructor.
  destruct a. destruct g.
  destruct transl_fundef eqn: TF in TR; try congruence.  
  monadInv TR. econstructor.
  split; auto.
  simpl. eapply transl_fundef_meet_spec; eauto.
  eauto.
  monadInv TR. econstructor.
  split; auto.
  simpl. destruct v. simpl.
  constructor. auto.
  eauto.
Qed.

Lemma match_erase_globdef: forall l tl ce tce dropm drops,
    transf_globdefs (transl_fundef ce tce dropm drops) transl_globvar l = OK tl ->
    map (fun '(id, g) => (id, erase_globdef g)) l = map (fun '(id, g) => (id, erase_globdef g)) tl.
Proof.
  induction l; simpl; intros tl ce tce dropm drops TR.
  inv TR. auto.
  destruct a. destruct g.
  destruct transl_fundef eqn: TF in TR; try congruence.  
  monadInv TR. simpl. f_equal.
  eauto.
  monadInv TR. simpl. f_equal.
  eauto.
Qed.

  
Lemma match_transf_program: forall p tp,
    transl_program p = OK tp ->
    match_prog p tp.
Proof.
  unfold transl_program. intros p tp.
  destruct list_disjoint_dec; try congruence.
  destruct check_malloc_free_existence eqn: EXT; try congruence.
  destruct transl_composites as [tdefs| ]eqn: TRCOMP; try congruence.
  (** solution comes from https://coq.discourse.group/t/destructing-term-when-match-generates-equality-involving-that-term/2209/3 *)
  generalize (eq_refl (Ctypes.build_composite_env tdefs)).
  generalize (Ctypes.build_composite_env tdefs) at 2 3.
  intros [tce|] E; try congruence.
  intros TR. monadInv TR.
  unfold transform_partial_program2 in EQ.
  monadInv EQ.
  simpl.
  constructor;auto.
  - simpl. eapply transl_composites_meet_spec; eauto.
    eapply prog_comp_env_eq.
  - intros. eapply match_globdef. simpl. auto.
  (* erase_program *)
  - unfold erase_program.
    simpl in *. f_equal.
    erewrite match_erase_globdef. eauto. eauto.
  - unfold check_malloc_free_existence in EXT.
    destruct ((prog_defmap p) ! malloc_id); try congruence.
    destruct g; try destruct f; try congruence; try destruct e; try congruence; eauto.
    repeat eexists.
  - unfold check_malloc_free_existence in EXT.
    destruct ((prog_defmap p) ! malloc_id) eqn: MALLOC; try congruence.
    destruct g; try destruct f; try congruence; try destruct e; try congruence; eauto.
    destruct ((prog_defmap p) ! free_id) eqn: FREE; try congruence.
    destruct g; try destruct f; try congruence; try destruct e; try congruence; eauto.
    repeat eexists.
Qed.

(* Prove match_genv for this specific match_prog *)

Section MATCH_PROGRAMS.

Variable p: RustIR.program.
Variable tp: Clight.program.
Let build_ctx := build_clgen_env p tp.
Hypothesis TRANSL: match_prog p tp.

Section INJECT.

Variable j: meminj.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Hypothesis sematch: Genv.match_stbls j se tse.

Lemma globalenvs_match:
  Genv.match_genvs j (match_glob build_ctx) (Genv.globalenv se p) (Genv.globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn [Genv.globalenv Genv.genv_defs NMap.get].
  assert (Hd:forall i, Coqlib.option_rel (match_glob build_ctx) (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. apply TRANSL.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
  (*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (Coqlib.option_rel (match_glob build_ctx)
         (NMap.get _ b1 (NMap.init (option (globdef (Rusttypes.fundef function) type)) None))
         (NMap.get _ b2 (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None ))).
  - generalize (NMap.init (option (globdef (Rusttypes.fundef function) type)) None),
      (NMap.init (option (globdef (Ctypes.fundef Clight.function) Ctypes.type)) None).
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
  match_glob (build_ctx) g tg /\
  delta = 0.
Proof.
  apply Genv.find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  Genv.find_funct (Genv.globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists tf,
  Genv.find_funct (Genv.globalenv tse tp) tv = Some tf /\ tr_fundef build_ctx f tf.
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
  Genv.find_funct (Clight.globalenv tse tp) tv = None.
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
  (forall c f tf, tr_fundef c f tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    Genv.is_internal (Clight.globalenv tse tp) tv = Genv.is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold Genv.is_internal.
  destruct (Genv.find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (tf & Htf & ?); try eassumption.
    unfold Clight.fundef.
    simpl. rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.


End INJECT.

End MATCH_PROGRAMS.

Section PRESERVATION.

Variable prog: RustIR.program.
Variable tprog: Clight.program.
Let ctx := build_clgen_env prog tprog.
Let ce := ctx.(clgen_src_cenv).
Let tce := ctx.(clgen_tgt_cenv).
Let dropm := ctx.(clgen_dropm).
Let glues := ctx.(clgen_glues).

Hypothesis TRANSL: match_prog prog tprog.
Variable w: inj_world.

Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
(* injp or inj ? *)
Hypothesis SEVALID: Genv.valid_for (erase_program prog) se.

Let ge := RustIR.globalenv se prog.
Let tge := Clight.globalenv tse tprog.

Hypothesis GE: inj_stbls w se tse.

(* Simulation relation *)

(* Let ce := prog.(prog_comp_env). *)
(* Let tce := tprog.(Ctypes.prog_comp_env). *)
(* Let dropm := generate_dropm prog. *)
(* Let glues := generate_drops ce tce prog.(prog_types) dropm. *)

Definition var_block_rel (f: meminj) (s: block * type) (t: block * Ctypes.type) : Prop :=
  let (b, ty) := s in
  let (tb, cty) := t in
  f b = Some (tb, 0) /\ cty = to_ctype ty.

Definition match_env (f: meminj) (e: env) (te: Clight.env) : Prop :=
  (* me_mapped in Simpllocalproof.v *)
  forall id, Coqlib.option_rel (var_block_rel f) e!id te!id.
  
Lemma match_env_incr: forall e te j1 j2,
    match_env j1 e te ->
    inject_incr j1 j2 ->
    match_env j2 e te.
Proof.
  unfold match_env.
  intros. generalize (H id). intros REL.
  inv REL. constructor. constructor.
  destruct x. destruct y.
  red. red in H3. destruct H3.
  split; eauto.
Qed.


(* We need to maintain the well-formedness of local environment in the
simulation *)
Definition well_formed_env (f: function) (e: env) : Prop :=
  forall id, ~ In id (var_names (f.(fn_params) ++ f.(fn_vars))) -> e!id = None.

Lemma var_names_app: forall a b, 
  var_names (a ++ b) = var_names a ++ var_names b. 
Proof. 
  induction a; intros. 
  - simpl. auto. 
  - simpl. f_equal. apply IHa.
Qed.


Lemma wf_env_target_none: forall j e te l id f,
    match_env j e te ->
    well_formed_env f e ->
    list_disjoint (var_names (f.(fn_params) ++ f.(fn_vars))) l ->
    In id l ->
    te!id = None.
Proof.
  intros j e te l id f MENV WF DISJ IN. red in MENV. specialize (MENV id). 
  eapply list_disjoint_sym in DISJ. 
  eapply list_disjoint_notin in DISJ; eauto. 
  apply WF in DISJ.   
  rewrite DISJ in MENV. inv MENV. auto.  
Qed. 

Lemma alloc_variables_wf_env: forall ce l id e1 e2 m1 m2,
    alloc_variables ce e1 m1 l e2 m2 ->
    (* constraint for e1 *)
    e1 ! id = None ->
    ~ In id (var_names l) ->
    e2 ! id = None.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destruct a. simpl in *.
  inv H.
  eapply IHl; eauto.
  rewrite PTree.gsspec.
  destruct (peq id i). subst.
  exfalso. apply H1. auto.
  auto.
Qed.

Lemma function_entry_wf_env: forall ge f vargs e m1 m2,
    function_entry ge f vargs m1 e m2 ->
    well_formed_env f e.
Proof.
  intros until m2.
  intros FENTRY. inv FENTRY.
  red. intros.
  eapply alloc_variables_wf_env; eauto.
Qed.

(* Can be proved by tr_composite *)
Definition enum_consistent (eid fid uid ufid: ident) : Prop :=
  forall co,
    ce ! eid = Some co ->
    co.(co_sv) = TaggedUnion ->
    exists tco utco, tce ! eid = Some tco
                /\ tce ! uid = Some utco
                /\ forall fofs bf, variant_field_offset ce fid co.(co_members) = OK (fofs, bf) ->
                  exists cfofs1 cfofs2,
                    Ctypes.field_offset tce ufid tco.(Ctypes.co_members) = OK (cfofs1, Full)
                    /\ Ctypes.union_field_offset tce fid utco.(Ctypes.co_members) = OK (cfofs2, Full)
                    /\ fofs = cfofs1 + cfofs2.
    
Inductive match_dropmemb_stmt (co_id: ident) (arg: Clight.expr) : struct_or_variant -> option drop_member_state -> Clight.statement -> Prop :=
| match_drop_in_struct_comp: forall id fid fty tys drop_id ts call_arg orgs co_ty,
    let field_param := Efield arg fid (to_ctype fty) in
    forall (GLUE: dropm ! id = Some drop_id)
      (COTY: co_ty = Tstruct orgs id \/ co_ty = Tvariant orgs id)
      (MSTMT: makeseq (drop_glue_for_box_rec field_param tys) = ts)
      (CHILDTY: drop_glue_children_types fty = co_ty :: tys)
      (CALLARG: call_arg = (deref_arg_rec co_ty field_param tys)),
    match_dropmemb_stmt co_id arg Struct (Some (drop_member_comp fid fty co_ty tys))
      (Clight.Ssequence (call_composite_drop_glue call_arg (Clight.typeof call_arg) drop_id) ts)
| match_drop_in_enum_comp: forall id fid fty tys drop_id ts uid ufid call_arg orgs co_ty,
    let field_param := Efield (Efield arg ufid (Tunion uid noattr)) fid (to_ctype fty) in
    forall (ECONSIST: enum_consistent co_id fid uid ufid)
    (GLUE: dropm ! id = Some drop_id)
    (COTY: co_ty = Tstruct orgs id \/ co_ty = Tvariant orgs id)
    (MSTMT: makeseq (drop_glue_for_box_rec field_param tys) = ts)
    (CHILDTY: drop_glue_children_types fty = co_ty :: tys)
    (CALLARG: call_arg = (deref_arg_rec co_ty field_param tys)),
    match_dropmemb_stmt co_id arg TaggedUnion (Some (drop_member_comp fid fty co_ty tys))
    (Clight.Ssequence (call_composite_drop_glue call_arg (Clight.typeof call_arg) drop_id) ts)
| match_drop_box_struct: forall fid fty tys,
    let field_param := Efield arg fid (to_ctype fty) in
    forall (FTYLAST: fty = last tys fty),
    match_dropmemb_stmt co_id arg Struct (Some (drop_member_box fid fty tys))
      (makeseq (drop_glue_for_box_rec field_param tys))
| match_drop_box_enum: forall fid fty tys uid ufid,
    let field_param := Efield (Efield arg ufid (Tunion uid noattr)) fid (to_ctype fty) in
    forall (ECONSIST: enum_consistent co_id fid uid ufid)
    (FTYLAST: fty = last tys fty),
    match_dropmemb_stmt co_id arg TaggedUnion (Some (drop_member_box fid fty tys))
    (makeseq (drop_glue_for_box_rec field_param tys))
| match_drop_none: forall sv,
    match_dropmemb_stmt co_id arg sv None Clight.Sskip
.

(* We need to record the list of stack block for the parameter of the
drop glue *)
Inductive match_cont (j: meminj) : cont -> Clight.cont -> mem -> mem -> list block -> Prop :=
| match_Kstop: forall m tm bs,
    match_cont j Kstop Clight.Kstop m tm bs
| match_Kseq: forall s ts k tk m tm bs
    (* To avoid generator, we need to build the spec *)
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs),
    match_cont j (Kseq s k) (Clight.Kseq ts tk) m tm bs
| match_Kloop: forall s ts k tk m tm bs
    (MSTMT: tr_stmt ce tce dropm s ts)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs),
    match_cont j (Kloop s k) (Clight.Kloop1 ts Clight.Sskip tk) m tm bs
| match_Kcall1: forall p f tf e te le k tk cty temp pe m tm bs
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None)
    (* we need to consider temp is set to a Clight expr which is
    translated from p *)
    (TRFUN: tr_function ce tce dropm glues f tf)
    (CTY: cty = to_ctype (typeof_place p))
    (PE: place_to_cexpr ce tce p = OK pe)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MENV: match_env j e te),
    match_cont j (Kcall (Some p) f e k) (Clight.Kcall (Some temp) tf te le (Clight.Kseq (Clight.Sassign pe (Etempvar temp cty)) tk)) m tm bs
| match_Kcall2: forall f tf e te le k tk m tm bs
    (WFENV: well_formed_env f e)
    (NORMALF: f.(fn_drop_glue) = None)
    (* how to relate le? *)
    (TRFUN: tr_function ce tce dropm glues f tf)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MENV: match_env j e te),
    match_cont j (Kcall None f e k) (Clight.Kcall None tf te le tk) m tm bs
| match_Kdropcall_composite: forall id te le k tk tf b ofs b' ofs' pb m tm co membs ts1 kts fid fty tys bs,
    (* invariant that needed to be preserved *)
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    (* let field_param := Efield deref_param fid (to_ctype fty) in *)
    forall (CO: ce ! id = Some co)
      (MSTMT:
        match_dropmemb_stmt id deref_param co.(co_sv) (Some (drop_member_box fid fty tys)) ts1 /\
        match co.(co_sv) with
        | Struct =>
            exists ts2,            
              drop_glue_for_members ce dropm deref_param membs = ts2 /\
              kts = (Clight.Kseq ts2 tk)
        | TaggedUnion =>
            exists uts,
              kts = (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Clight.Kswitch tk))) /\
              membs = nil
        end)
    (* (STRUCT: co.(co_sv) = Struct) *)
    (* (MSTMT1: match_dropmemb_stmt id deref_param Struct (Some (drop_member_box fid fty tys)) ts1) *)
    (* (MSTMT2: drop_glue_for_members ce dropm deref_param membs = ts2) *)
    (MCONT: match_cont j k tk m tm bs)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env ))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (* Free pb does not affect bs *)
    (NOTIN: ~ In pb bs)
    (GLUE: glues ! id = Some tf),
      match_cont j
        (Kdropcall id (Vptr b ofs) (Some (drop_member_box fid fty tys)) membs k)
        (Clight.Kcall None tf te le (Clight.Kseq ts1 kts)) m tm (pb :: bs)
.

(* | match_Kdropcall_enum: forall id te le k tk tf b ofs b' ofs' pb m tm co tys ts fid fty uts, *)
(*     (* invariant that needed to be preserved *) *)
(*     let co_ty := (Ctypes.Tstruct id co.(co_attr)) in *)
(*     let pty := Tpointer co_ty noattr in *)
(*     let deref_param := Ederef (Evar param_id pty) co_ty in *)
(*     (* we do not know the union_id and union_type *) *)
(*     (* let field_param := Efield (Efield deref_param ufid (Tunion uid noattr)) fid (to_ctype fty) in *) *)
(*     forall (CO: ce ! id = Some co) *)
(*     (ENUM: co.(co_sv) = TaggedUnion)       *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MSTMT: match_dropmemb_stmt id deref_param TaggedUnion (Some (drop_member_box fid fty tys)) ts) *)
(*     (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env )) *)
(*     (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs')) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs')) *)
(*     (UNREACH: forall ofs, loc_out_of_reach j m pb ofs) *)
(*     (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable) *)
(*     (GLUE: glues ! id = Some tf) *)
(*     (MINJ: Mem.inject j m tm), *)
(*       match_cont j *)
(*         (RustIR.Kdropcall id (Vptr b ofs) (Some (drop_member_box fid fty tys)) nil k) *)
(*         (Clight.Kcall None tf te le (Clight.Kseq ts (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Clight.Kswitch tk))))) m tm *)
(* . *)


Inductive match_states: state -> Clight.state -> Prop :=
| match_regular_state: forall f tf s ts k tk m tm e te le j
    (WFENV: well_formed_env f e)
    (* maintain that this function is a normal function *)
    (NORMALF: f.(fn_drop_glue) = None)
    (MFUN: tr_function ce tce dropm glues f tf)
    (MSTMT: tr_stmt ce tce dropm s ts)    
    (* match continuation: we do not care about m and tm because they
    must be unused in the continuation of normal state *)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (MINJ: Mem.inject j m tm)   
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (MENV: match_env j e te),
    match_states (State f s k e m) (Clight.State tf ts tk te le tm)
| match_call_state: forall vf vargs k m tvf tvargs tk tm j
    (* match_kcall is independent of ce and dropm  *)
    (MCONT: forall m tm bs, match_cont j k tk m tm bs)
    (VINJ: Val.inject j vf tvf)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (AINJ: Val.inject_list j vargs tvargs),
    (* (VFIND: Genv.find_funct ge vf = Some fd) *)
    (* (FUNTY: type_of_fundef fd = Tfunction orgs rels targs tres cconv), *)
    match_states (Callstate vf vargs k m) (Clight.Callstate tvf tvargs tk tm)
| match_return_state: forall v k m tv tk tm j
   (MCONT: forall m tm bs, match_cont j k tk m tm bs)
   (MINJ: Mem.inject j m tm)
   (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
   (RINJ: Val.inject j v tv),
    match_states (Returnstate v k m) (Clight.Returnstate tv tk tm)
(* | match_calldrop_box: forall k m b ofs tk tm ty j fb tb tofs *)
(*     (* we can store the address of p in calldrop and build a local env *)
(*        in Drop state according to this address *) *)
(*     (VFIND: Genv.find_def tge fb = Some (Gfun free_decl)) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)) *)
(*     (* Because k may contain Kdropcall, we must consider the specific *)
(*     m and tm *) *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MINJ: Mem.inject j m tm) *)
(*     (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))), *)
(*     match_states (RustIR.Calldrop (Vptr b ofs) (Tbox ty) k m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr tb tofs)] tk tm) *)
(* | match_calldrop_composite: forall k m b ofs tb tofs tk tm j fb id fid drop_glue orgs ty *)
(*     (GLUE: glues ! id = Some drop_glue) *)
(*     (DROPM: dropm ! id = Some fid) *)
(*     (VFIND: Genv.find_funct tge (Vptr fb Ptrofs.zero) = Some (Ctypes.Internal drop_glue)) *)
(*     (SYMB: Genv.find_symbol tge fid = Some fb) *)
(*     (TY: ty = Tstruct orgs id \/ ty = Tvariant orgs id) *)
(*     (MCONT: match_cont j k tk m tm) *)
(*     (MINJ: Mem.inject j m tm) *)
(*     (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs)) *)
(*     (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm))), *)
(*     match_states (RustIR.Calldrop (Vptr b ofs) ty k m) (Clight.Callstate (Vptr fb Ptrofs.zero) [(Vptr tb tofs)] tk tm) *)
| match_dropstate_struct: forall id k m tf ts1 ts2 tk te le tm j co membs pb b' ofs' b ofs s bs,
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    forall (CO: ce ! id = Some co)
    (STRUCT: co.(co_sv) = Struct)
    (MSTMT1: match_dropmemb_stmt id deref_param Struct s ts1)
    (MSTMT2: drop_glue_for_members ce dropm deref_param membs = ts2)
    (MCONT: match_cont j k tk m tm bs)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (GLUE: glues ! id = Some tf)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (VALIDBS: forall b, In b bs -> Mem.valid_block tm b)
    (NOTIN: ~ In pb bs),
      match_states (Dropstate id (Vptr b ofs) s membs k m) (Clight.State tf ts1 (Clight.Kseq ts2 tk) te le tm)
| match_dropstate_enum: forall id k m tf tk te le tm j co pb b' ofs' b ofs s ts uts bs,
    let co_ty := (Ctypes.Tstruct id noattr) in
    let pty := Tpointer co_ty noattr in
    let deref_param := Ederef (Evar param_id pty) co_ty in
    (* we do not know the union_id and union_type *)
    (* let field_param := Efield (Efield deref_param ufid (Tunion uid noattr)) fid (to_ctype fty) in *)
    forall (CO: ce ! id = Some co)
    (ENUM: co.(co_sv) = TaggedUnion)
    (MCONT: match_cont j k tk m tm bs)
    (MSTMT: match_dropmemb_stmt id deref_param TaggedUnion s ts)
    (MINJ: Mem.inject j m tm)
    (INCR: inj_incr w (injw j (Mem.support m) (Mem.support tm)))
    (GLUE: glues ! id = Some tf)
    (TE: te = (PTree.set param_id (pb, pty) Clight.empty_env))
    (LOAD: Mem.loadv Mptr tm (Vptr pb Ptrofs.zero) = Some (Vptr b' ofs'))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr b' ofs'))
    (FREE: Mem.range_perm tm pb 0 (Ctypes.sizeof tce pty) Cur Freeable)
    (* It is used to preserve pb during (m,tm) injected move *)
    (UNREACH: forall ofs, loc_out_of_reach j m pb ofs)
    (* Use VALIDBS to prove NOTIN in Dropstate tansitions *)
    (VALIDBS: forall b, In b bs -> Mem.valid_block tm b)
    (NOTIN: ~ In pb bs),
      match_states (Dropstate id (Vptr b ofs) s nil k m) (Clight.State tf ts (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Kswitch tk))) te le tm)
.


(* Type preservation in translation *)
Lemma type_eq_except_origins_to_ctype: forall ty1 ty2,
    type_eq_except_origins ty1 ty2 = true ->
    to_ctype ty1 = to_ctype ty2.
Proof.
  induction ty1; destruct ty2;simpl; try congruence;
    intros TYEQ; try eapply proj_sumbool_true in TYEQ; try congruence.
    erewrite IHty1. eauto.
    destruct m; destruct m0; auto.
    congruence. congruence.
Qed.

Lemma place_to_cexpr_type: forall p e,
    place_to_cexpr ce tce p = OK e ->
    to_ctype (typeof_place p) = Clight.typeof e.
    Proof.
    induction p; simpl; intros; simpl in *.
  -  monadInv H. auto.
  - destruct (typeof_place _); inversion H. 
    destruct (ce ! i0);  inversion H. 
    destruct (co_sv c); inv H. 
    monadInv H3.  destruct t; auto. 
  - monadInv H. auto.
  - destruct (typeof_place _); inversion H.
    destruct (ce ! i0);  inversion H.
    destruct (tce ! i0);  inversion H.
    destruct (co_sv c);  inversion H.
    destruct (Ctypes.co_members c0 );  inversion H.
    destruct m;
    destruct m0; inversion H;
    try destruct m; try destruct m0;
    monadInv H4; try monadInv H; auto.  
  Qed.

Lemma expr_to_cexpr_type: forall e e',
    expr_to_cexpr ce tce e = OK e' ->
    to_ctype (typeof e) = Clight.typeof e'.
Proof.
    destruct e eqn: E. 
    - simpl. 
      destruct (type_eq_except_origins) eqn:Horg.
      intros.
      assert ((to_ctype t) = to_ctype (typeof_place p)) as EQtp.
      { 
        eapply type_eq_except_origins_to_ctype.
        auto.
      }
      rewrite EQtp. apply place_to_cexpr_type. auto.
      intros. monadInv H.
    - simpl; destruct p;  intros ; simpl in *; try (monadInv H); auto.
      destruct (type_eq_except_origins t (typeof_place p)) eqn : Htype_eq_org; simpl in *.
      apply type_eq_except_origins_to_ctype in Htype_eq_org.
      rewrite Htype_eq_org. apply place_to_cexpr_type. auto.
      inversion H.
      destruct (typeof_place p); try (inversion H).
      destruct (ce ! i0); try (inversion H).
      destruct (field_tag i (co_members c)); try inversion H.
      destruct (get_variant_tag tce i0); try inversion H.
      monadInv H4. auto.
Qed.

Lemma pexpr_to_cexpr_types : forall p x,
    pexpr_to_cexpr ce tce p = OK x ->
    to_ctype (typeof_pexpr p) = Clight.typeof x. 
Proof.
  induction p. 
  - simpl. intros. monadInv H. auto.
  - simpl. intros. monadInv H. auto.
  - simpl. intros. monadInv H. auto.
  - simpl. intros. monadInv H. auto.
  - simpl. intros. monadInv H. auto.
  - simpl. intros. destruct (type_eq_except_origins t (typeof_place p) ) eqn : Horg.

    eapply type_eq_except_origins_to_ctype in Horg. 
    rewrite Horg. 
    eapply place_to_cexpr_type. eauto.
    inv H. 
  - simpl. intros. destruct (typeof_place p ) eqn: Htp; inv H. 
    destruct (ce ! i0) eqn: Hce; inv H1.
    destruct (field_tag i (co_members c)) eqn: Hcosv; inv H0.
    destruct (get_variant_tag tce i0) eqn: Htag; inv H1.
    monadInv H0.
    simpl.  auto. 
  - intros. simpl in H. monadInv H. 
    simpl.  auto. 
  - intros. inv H. monadInv H1. simpl. auto.
  - intros. inv H. monadInv H1. simpl. auto.
Qed. 


(* Injection is preserved during evaluation *)

Lemma deref_loc_inject: forall ty m tm b ofs b' ofs' v j,
    deref_loc ty m b ofs v ->
    Mem.inject j m tm ->
    Val.inject j (Vptr b ofs) (Vptr b' ofs') ->
    exists v', Clight.deref_loc (to_ctype ty) tm b' ofs' Full v' /\ Val.inject j v v'.
Proof.
  intros.
  inv H.
  - (*by value*)
    exploit Mem.loadv_inject; eauto. intros [tv [A B]].
    exists tv. split. econstructor. 
    instantiate (1:= chunk). 
    destruct ty; simpl in *; congruence.
    auto. auto.
  - (* by ref*)
    exists ((Vptr b' ofs')). split. 
    eapply Clight.deref_loc_reference. 
    destruct ty; simpl in *; congruence.
    auto. 
  - (*by copy*)
    exists (Vptr b' ofs'). split. eapply Clight.deref_loc_copy.
    destruct ty; simpl in *; congruence.
    auto.
Qed.



Lemma eval_place_inject: forall p lv e te j m tm le b ofs,
    place_to_cexpr ce tce p = OK lv ->
    eval_place ce e m p b ofs ->
    match_env j e te ->
    Mem.inject j m tm ->
    (** Why eval_lvalue requires tge ? Because eval_Evar_global ! We
    want to just use ctce. But I think we can prove that ctce!id =
    tge.(cenv)!id because we have ce!id and tr_composte ce tge.(cenv)
    and tr_composite ce ctce *)
    exists b' ofs', Clight.eval_lvalue tge te le tm lv b' ofs' Full /\ Val.inject j (Vptr b ofs) (Vptr b' ofs').
Proof. 
  intros p;
  intros lv e te j m tm le b ofs.
  intros Hplaceok Hevalp. 
  generalize dependent lv.
  induction Hevalp; intros lv Hplaceok Hmatch Hmem_inj; intros.   
  - (* p = Plocal i t *)
    monadInv Hplaceok.
    generalize (Hmatch id). intros REL. inv REL.
    + rewrite <- H1 in H. inv H.
    + destruct x. destruct y. simpl in H2. destruct H2. 
      subst. 
      rewrite <- H0 in H. inv H.
      esplit. esplit. 
      split. econstructor. eauto. 
      econstructor. eauto. eauto.
  - (* p = Pfield p i t *)  
    simpl in Hplaceok. 
    inv Hplaceok. simpl in *.  
    inv TRANSL. 
    pose (H0_cp := H0). 
    apply match_prog_comp_env0 in H0_cp. 
    rewrite H in H3. 
    rewrite H0 in H3. 
    destruct (co_sv co) eqn : Hcosv.  
    monadInv H3. 
    exploit IHHevalp; eauto. 
    intros[b' [ofs' [A B]]].
    inv B. 
    exists b'.
    exists (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr delta0)) (Ptrofs.repr delta)). 
    split. 
    + exploit struct_field_offset_match; eauto. 
      intros [tco' [E F]].
      exploit place_to_cexpr_type; eauto. intro Htpx. 
      rewrite H in Htpx.  simpl in Htpx. 
      eapply eval_Efield_struct. eapply Clight.eval_Elvalue. 
      apply A.   apply Clight.deref_loc_copy.   
      rewrite <- Htpx. auto. eauto. eauto. eauto.
    + econstructor. eauto. repeat rewrite Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. 
    + inv H3. 
  - rename Hplaceok into PEXPR.
    rename Hevalp into EVALP.
    rename Hmatch into MENV.
    rename Hmem_inj into MINJ.
    simpl in PEXPR. 
    rewrite H in PEXPR. rewrite H0 in PEXPR. 
    assert (ENUM: co_sv co = TaggedUnion).
    destruct (co_sv co). 
    destruct tce!id; inv PEXPR. auto.
    exploit variant_field_offset_match.
    eapply match_prog_comp_env; eauto.
    eauto.
    auto.
    intros (tco & union_id & tag_fid & union_fid & union & A & B & C & D & E).
    generalize (E _ _ H3). intros (ofs1 & ofs2 & UNIONFOFS & MEMBFOFS & FEQ). subst.
    unfold tce in PEXPR. simpl in PEXPR.
    rewrite A in PEXPR.
    rewrite ENUM in PEXPR.
    rewrite C in PEXPR.
    monadInv PEXPR.
    exploit IHHevalp; eauto.
    intros (pb & pofs & EVAL1 & VINJ1).
    do 2 eexists.
    split.
    assert (TYX: Clight.typeof x = Ctypes.Tstruct id noattr).
    erewrite <- place_to_cexpr_type; eauto.
    rewrite H. auto.
       
    eapply eval_Efield_union. eapply eval_Elvalue.
    eapply eval_Efield_struct. eapply eval_Elvalue.
    eauto. rewrite TYX.
    simpl. eapply Clight.deref_loc_copy.
    auto. eauto.
    simpl. eauto. eauto.

    simpl. eapply Clight.deref_loc_copy.
    auto. simpl. eauto.
    simpl. eauto. eauto.
    inv VINJ1.
    econstructor; eauto.
    rewrite add_repr.
    rewrite <- (Ptrofs.add_assoc ofs _ _).
    rewrite (Ptrofs.add_assoc (Ptrofs.add ofs (Ptrofs.repr ofs1)) _ _).
    rewrite (Ptrofs.add_commut (Ptrofs.repr ofs2) (Ptrofs.repr delta)).
    rewrite <- (Ptrofs.add_assoc (Ptrofs.add ofs (Ptrofs.repr ofs1)) _ _).
    f_equal. do 2 rewrite Ptrofs.add_assoc.
    f_equal. eapply Ptrofs.add_commut.
    
  - monadInv Hplaceok.
    exploit IHHevalp; eauto.
    intros [b' [ofs'' [A B]]]. 
    exploit deref_loc_inject; eauto. intros [tv [C D]].
    inv D. 
    esplit. esplit. 
    split. eapply Clight.eval_Ederef. 
    eapply eval_Elvalue. apply A. 
    + exploit place_to_cexpr_type. eauto. intro Hctypex. rewrite <- Hctypex.
      eauto.
    + eauto.
Qed. 

Lemma eval_expr_inject: forall e te j a a' m tm v le,
    eval_expr ce e m a v ->
    expr_to_cexpr ce tce a = OK a' ->
    match_env j e te ->
    Mem.inject j m tm ->
    exists v', Clight.eval_expr tge te le tm a' v' /\ Val.inject j v v'.  
(* To prove this lemma, we need to support type checking in the
   evaluation of expression in RustIR *)
Proof. 
  destruct a.
  - simpl. 
    destruct (type_eq_except_origins t (typeof_place p)) eqn :Horg; try congruence. 
    exploit type_eq_except_origins_to_ctype; eauto. 
    intros TTYP.
    intros a' m tm v le.
    intros EVAL PEXPR MATJ MINJ.
    inv EVAL. 
    inv H2. 
    exploit eval_place_inject; eauto. 
    intros (b' & ofs' & A & B).
    exploit deref_loc_inject; eauto.
    intros [v' [C D]].
    eexists. split. eapply Clight.eval_Elvalue. eauto.
    exploit place_to_cexpr_type; eauto. 
    intros Htpx. rewrite <- TTYP in Htpx. rewrite <- Htpx. 
    eauto. eauto.
  - simpl. 
    intros a' m tm v le. 
    intros EVAL PEXPR MATJ MINJ. 
    generalize dependent v. 
    generalize dependent a'. 
    induction p; intros.
    + simpl. intros. simpl in *. inv EVAL. monadInv PEXPR.   
      esplit. split. econstructor. inv H0. eauto. 
    + intros. simpl in *. inv EVAL. monadInv PEXPR. exists (Vint i). 
      split. inv H0. constructor. inv H0. eauto. 
    + intros. simpl in *. inv EVAL. monadInv PEXPR. exists (Vfloat f).
      split. inv H0. constructor. inv H0. eauto. 
    + intros. simpl in *. inv EVAL. monadInv PEXPR. exists (Vsingle f).
      split. inv H0. constructor. inv H0. eauto. 
    + intros. simpl in *. inv EVAL. monadInv PEXPR. exists (Vlong i).
      split. inv H0. constructor. inv H0. eauto. 
    + (* Eplace p0 t *)
      inv PEXPR. destruct (type_eq_except_origins t (typeof_place p) ) eqn:Horg; inv H0. 
      inv EVAL. inv H0.   
      exploit eval_place_inject; eauto.
      intros (b' & ofs' & A & B).
      exploit deref_loc_inject; eauto. intros [v' [C D]].
      eexists.  split. eapply Clight.eval_Elvalue. eauto. 
      assert (EQTYPETA: to_ctype t = Clight.typeof a'). 
      {
        exploit place_to_cexpr_type; eauto. 
        intros. exploit type_eq_except_origins_to_ctype; eauto. 
        intro K. congruence. 
      }
      rewrite <-  EQTYPETA. eauto. eauto. 
    + inv EVAL. inv H0.   
      inversion PEXPR. 
      rewrite H4 in H0. 
      rewrite H5 in H0. 
      rewrite H7 in H0. 
      destruct (get_variant_tag tce id) eqn:VTAG; inv H0.
      unfold get_variant_tag in VTAG. 
      destruct (tce ! id) eqn:TCID; inv VTAG. 
      destruct (co_su c) eqn: COSUC; inv H0. 
      destruct (Ctypes.co_members c) eqn: COMEM; inv H6. 
      destruct (m0) eqn: MEMB; inv H0. 
      destruct (m1) eqn: MEMB1; inv H6. 
      destruct (m0) eqn: MEMB0; inv H0.
      destruct (t0) eqn: T0; inv H6. 
      destruct l eqn: L; inv H0.  
      monadInv H1. 
      exploit place_to_cexpr_type; eauto. 
      intros Htpx. rewrite H4 in Htpx. simpl in Htpx. 
      exploit eval_place_inject; eauto. 
      instantiate (1:=le).  
      intros (b' & ofs' & A & B). 
      pose (CEID := H5).  
      eexists. split. 
      * eapply Clight.eval_Ebinop. 
         
        **eapply eval_Elvalue. 
          eapply eval_Efield_struct.  
          eapply eval_Elvalue. eauto. 
          rewrite <- Htpx. eapply Clight.deref_loc_copy; eauto.  rewrite Htpx.  auto.
          simpl. eauto. 
          rewrite COMEM.
          unfold Ctypes.field_offset.    
          unfold Ctypes.field_offset_rec. simpl. 
          destruct (ident_eq i0 i0). auto. congruence. 
          simpl. 
          eapply Clight.deref_loc_value. 
          simpl. eauto.  
          exploit Mem.loadv_inject; eauto.    
          intros (v2 & LOAD & VINJ).
          inv VINJ.    
          assert ( L : (align 0 (Ctypes.bitalignof (Ctypes.prog_comp_env tprog) t) / 8)= 0). 
          exploit align_same. 
          instantiate ( 1:= Ctypes.bitalignof (Ctypes.prog_comp_env tprog) t). 
          unfold Ctypes.bitalignof. 
          exploit Ctypes.alignof_pos.  
          instantiate (1:= t).
          instantiate (1 := Ctypes.prog_comp_env tprog).
          lia. 
          instantiate (1:=0).
          apply Z.divide_0_r. 
          intros ALIGNZERO. 
          rewrite ALIGNZERO. auto. 
          rewrite  L.   rewrite   Ptrofs.add_zero.  eauto. 
        ** eapply Clight.eval_Econst_int. 
        ** simpl. 
          unfold sem_cmp. simpl. 
          unfold sem_binarith. simpl. 
          unfold Cop.sem_cast. simpl. 
          destruct Archi.ptr64 eqn:ARCHI. 
          simpl. eauto. 
          destruct (intsize_eq I32 I32); try congruence. 
      * destruct (Int.eq tag (Int.repr tagz)); econstructor.  
    + inv EVAL. inv H0.  monadInv PEXPR. 
      exploit place_to_cexpr_type; eauto. 
      intros Htpx. 
      exploit eval_place_inject; eauto.
      instantiate (1:=le).
      intros (b' & ofs' & A & B). 
      eexists.  
      split. 
      * eapply Clight.eval_Eaddrof. eauto. 
      * eauto.
    + simpl in PEXPR. monadInv PEXPR.
      inv EVAL. 
      inv H0. 
      exploit IHp. eauto. econstructor. eauto. 
      intros [v' [A B]]. 
      exploit sem_unary_operation_inject; eauto.
      intros [v2 [C D]].
      eexists. 
      split.
      econstructor. eauto. 
      exploit pexpr_to_cexpr_types; eauto. 
      intros Htpx. rewrite <- Htpx. eauto. eauto.
    + simpl in PEXPR. monadInv PEXPR.
      inv EVAL.
      inv H0. 
      exploit IHp1; eauto.  econstructor.  eauto. 
      intros [v1' [A B]].
      exploit IHp2; eauto. econstructor. eauto.
      intros [v2' [C D]].
      exploit sem_binary_operation_rust_inject; eauto.
      intros [v3 [E F]]. eauto.

      esplit. split. econstructor. eapply A. eapply C. 
      exploit  pexpr_to_cexpr_types.  eapply EQ. 
      intros Htpx. rewrite <- Htpx.
      exploit pexpr_to_cexpr_types. eapply EQ1. 
      intros Htpx0. rewrite <- Htpx0. 
      eauto. eauto.
Qed. 

Lemma alignof_blockcopy_1248: forall ty ofs,
  access_mode ty = By_copy
  -> sizeof ge ty > 0 -> (alignof_blockcopy ge ty | Ptrofs.unsigned ofs)
  -> (Ctypes.alignof_blockcopy tge (to_ctype ty) | Ptrofs.unsigned ofs). 
Proof. 
  intros. 
  induction ty; inv H; simpl in *; eauto.
  - destruct ((prog_comp_env prog) ! i) eqn: A; inv H0.
    inv TRANSL. 
    apply match_prog_comp_env0 in A. 
    destruct (co_sv c). 
    destruct A as (tco & B & C & D & E & F). 
    rewrite B. rewrite <- F.
    eauto. 
    destruct A as ( tco & uid & tfid & ufid & un & B & C & D & E & F & I & J & K).
    rewrite B. rewrite J. eauto. 
  - destruct ((prog_comp_env prog) ! i) eqn: A; inv H0. 
    inv TRANSL. 
    apply match_prog_comp_env0 in A. 
    destruct (co_sv c). 
    destruct A as (tco & B & C & D & E & F). 
    rewrite B. rewrite <- F.
    eauto. 
    destruct A as ( tco & uid & tfid & ufid & un & B & C & D & E & F & I & J & K).
    rewrite B. rewrite J. eauto. 
Qed. 
  
(* cited from SimplLocalsproof.v assign_loc_inject *)
Lemma assign_loc_inject: forall f ty m loc ofs v m' tm loc' ofs' v',
    assign_loc ge ty m loc ofs v m' ->
    Val.inject f (Vptr loc ofs) (Vptr loc' ofs') ->
    Val.inject f v v' ->
    Mem.inject f m tm ->
    exists tm',
      Clight.assign_loc tge (to_ctype ty) tm loc' ofs' Full v' tm'
      /\ Mem.inject f m' tm'
      /\ inj_incr (injw f (Mem.support m) (Mem.support tm)) (injw f (Mem.support m') (Mem.support tm')).
Proof. 
  intros f ty m loc ofs v m' tm loc' ofs' v' Hassign Hloc Hval Hmem. 
  inv Hassign.
  - exploit Mem.storev_mapped_inject; eauto.  
    intros. destruct H1 as [m2 [MSTOREV MINJM2]].      
    eexists.
    esplit. 
    + econstructor; eauto. 
      destruct ty; eauto. 
    + split. eauto. 
    inv Hmem.
    
    econstructor. eauto. unfold inject_incr_disjoint. intros. 
    rewrite H1 in H2. inv H2. 
    inv GE. unfold  Mem.sup_include. unfold sup_In.
    apply Mem.support_storev in H0. congruence.  
    apply Mem.support_storev in MSTOREV. congruence. 
  - (* by copy *)
    inv Hloc. inv Hval.
    rename b' into bsrc. rename ofs'0 into osrc. 
    rename loc into bdst. rename ofs into odst.
    rename loc' into bdst'. rename b2 into bsrc'.
    exploit sizeof_match; eauto. inv TRANSL.  
    assert (Ctypes.prog_comp_env tprog = tge) by auto. 
    rewrite H6 in match_prog_comp_env0. eauto. 
    intros EQSIZE. 
    destruct (zeq (sizeof ge ty) 0). 
    + assert (bytes = nil).
      { exploit (Mem.loadbytes_empty m bsrc (Ptrofs.unsigned osrc) (sizeof ge ty)).
        lia. congruence. }
      subst.
      destruct (Mem.range_perm_storebytes tm bdst' (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta))) nil)
      as [tm' SB].
      simpl. red; intros; extlia.
       exists tm'.
      split. eapply Clight.assign_loc_copy; eauto.
      destruct ty; simpl in *; congruence.  
      intros; extlia.  
      intros; extlia.
      rewrite EQSIZE. 
      rewrite e; right; lia.
      apply Mem.loadbytes_empty. lia.
      exploit Mem.storebytes_empty_inject; eauto. 
      intro TMINJ. 
      split. eauto.
      (* inj_incr *)
      econstructor. eauto. unfold inject_incr_disjoint. intros. 
      rewrite H6 in H7. inv H7. 
      exploit Mem.support_storebytes. eapply H5. congruence.
      exploit Mem.support_storebytes. eapply SB. congruence.
    + exploit Mem.loadbytes_length. eauto. intro LEN. 
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
      exists tm'. 
      split. eapply Clight.assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto. 
      destruct ty; simpl in *; eauto. 
      intros; eapply Mem.aligned_area_inject with (m := m); eauto. 
      apply Ctypes.alignof_blockcopy_1248. 
      apply sizeof_alignof_blockcopy_compat.
      rewrite EQSIZE. auto.  
      exploit alignof_blockcopy_1248. eauto. eauto. eapply H1. eauto. eauto. 
      intros; eapply Mem.aligned_area_inject with (m := m); eauto. 
      apply Ctypes.alignof_blockcopy_1248. 
      apply sizeof_alignof_blockcopy_compat.
      rewrite EQSIZE. auto.    
      exploit alignof_blockcopy_1248. eauto. eauto. eapply H2. eauto. eauto. 
      rewrite EQSIZE.   
      eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
      apply Mem.range_perm_max with Cur; auto. 
      apply Mem.range_perm_max with Cur; auto.
      rewrite EQSIZE. auto. 
      split. auto. 
      (* inj_incr *)
      econstructor. eauto. unfold inject_incr_disjoint. intros. 
      rewrite H6 in H7. inv H7. 
      exploit Mem.support_storebytes. eapply H5. congruence.
      exploit Mem.support_storebytes. eapply C. congruence.
Qed. 

Ltac TrivialInject :=
  match goal with
  | [ H: None = Some _ |- _ ] => discriminate
  | [ H: Some _ = Some _ |- _ ] => inv H; TrivialInject
  | [ H: match ?x with Some _ => _ | None => _ end = Some _ |- _ ] => destruct x; TrivialInject
  | [ H: match ?x with true => _ | false => _ end = Some _ |- _ ] => destruct x eqn:?; TrivialInject
  | [ |- exists v2', Some ?v = Some v2' /\ _ ] => exists v; split; auto
  (* | [ H:  match match ?i0 with IBool  => _ | _ => _ end with ?v4 => ?v5 | _ => _ end = _ |- Some _ ] => destruct i0; simpl in *; TrivialInject *)
  | _ => idtac
  end.

Lemma sem_cast_to_ctype_inject: forall f v1 v1' v2 t1 t2 m,
    sem_cast v1 t1 t2 = Some v2 ->
    Val.inject f v1 v1' ->
    exists v2', Cop.sem_cast v1' (to_ctype t1) (to_ctype t2) m = Some v2' /\ Val.inject f v2 v2'.
Proof. 
  unfold sem_cast; unfold Cop.sem_cast; intros; destruct t1; simpl in *; TrivialInject.
  - destruct t2; inv H0; simpl in *;
     try (destruct i; simpl in *);
    try (destruct f0; simpl in *); TrivialInject.  
  -  destruct t2; inv H0; simpl in *; TrivialInject; try(destruct i0; destruct (Archi.ptr64); simpl in *; TrivialInject; simpl in *);
    try (destruct (intsize_eq I8 I32); TrivialInject; inv e);
    try (destruct (intsize_eq I16 I32); TrivialInject; inv e);
    try (destruct f0; simpl in *; TrivialInject).  
    destruct (intsize_eq I32 I32).  esplit.  eauto. exfalso. apply n. auto.        
  - destruct t2; inv H0; simpl in *; 
    try(destruct i);  
    try(destruct Archi.ptr64 );
    try (destruct f0; simpl in *);
    TrivialInject. 
    econstructor. eauto. auto.    
  - destruct t2; inv H0; simpl in *;
    try (destruct f0);
    try (destruct i); 
    try (destruct f1); TrivialInject. 
  - destruct t2; inv H0; simpl in *; 
    try(destruct i; destruct (Archi.ptr64)); 
    try (destruct f0); TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64));
    try (destruct f0); TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64));
    try (destruct f0); TrivialInject. 
    econstructor; eauto; TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i; destruct (Archi.ptr64));
    try (destruct f0); TrivialInject. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i0; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
  - destruct t2; inv H0; simpl in *;
    try(destruct i0; destruct (Archi.ptr64)); 
    try (destruct f0); 
    try (destruct (ident_eq i i0~1); TrivialInject); 
    try (destruct (ident_eq i i0~0); TrivialInject); 
    try (inv H);
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
    try (eapply Val.inject_ptr; eauto). 
    exists (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta))).
    destruct (ident_eq i 1). split. auto.  
    TrivialInject. eapply Val.inject_ptr; eauto. inv H2. 
  Qed. 

Lemma extcall_free_injp: forall se tse v tv m m' tm t j Hm,
    extcall_free_sem se [v] m t Vundef m' ->
    Val.inject j v tv ->
    exists tm' Hm',
      extcall_free_sem tse [tv] tm t Vundef tm'
      /\ injp_acc (injpw j m tm Hm) (injpw j m' tm' Hm').
Proof.
  intros until Hm.
  intros FREE VINJ.
  inv FREE. inv VINJ.
  exploit Mem.load_inject; eauto.
  intros (v2 & LOAD & VINJ).
  exploit Mem.free_parallel_inject; eauto.
  intros (m2' & TFREE & MINJ).
  assert (P: Mem.range_perm m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  (* refer the proof of extcall_free in Event: use address_inject *)  
  exploit Mem.address_inject. eapply Hm.
  apply Mem.perm_implies with Freeable; auto with mem.
  apply P. instantiate (1 := lo).
  generalize (size_chunk_pos Mptr); lia. eauto.
  intros EQ.
  assert (injp_acc (injpw j m tm Hm) (injpw j m' m2' MINJ)).
  replace (Ptrofs.unsigned lo + Ptrofs.unsigned sz) with ((Ptrofs.unsigned lo - size_chunk Mptr) + (size_chunk Mptr + Ptrofs.unsigned sz)) in * by lia.
  exploit injp_acc_free; eauto. 
  assert (v2 = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv VINJ; auto. }
  subst.
  exists m2', MINJ. split; auto.  
  econstructor. erewrite <- LOAD. f_equal. lia.
  auto. 
  rewrite ! EQ. rewrite <- TFREE. f_equal; lia.
  auto.
  (* case 2 *)
  exists tm, Hm. split.
  replace tv with Vnullptr.
  econstructor.
  unfold Vnullptr in *.
  destruct (Archi.ptr64); inv VINJ; auto.
  reflexivity.
Qed.  
  
(* use injp_acc to prove inj_incr *)
Lemma injp_acc_inj_incr: forall f f' m1 m2 m1' m2' Hm Hm',
          injp_acc (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm') ->
          inj_incr (injw f (Mem.support m1) (Mem.support m2)) (injw f' (Mem.support m1') (Mem.support m2')).
Proof.
  intros. inv H.
  econstructor. eauto.
  red. red in H13. unfold Mem.valid_block in H13. eauto.
  eapply (Mem.unchanged_on_support _ _ _ H10).
  eapply (Mem.unchanged_on_support _ _ _ H11).
Qed.


Lemma typ_of_type_to_ctype: forall ty,
    typ_of_type ty = Ctypes.typ_of_type (to_ctype ty).
Proof.
  destruct ty; simpl; auto.
Qed.

Lemma rettype_of_type_to_ctype: forall ty,
    rettype_of_type ty = Ctypes.rettype_of_type (to_ctype ty).
Proof.
  destruct ty; simpl; auto.
Qed.


Lemma typlist_of_typelist_to_ctype: forall tyl,
    typlist_of_typelist tyl = Ctypes.typlist_of_typelist (to_ctypelist tyl).
  induction tyl; simpl; auto.
  rewrite IHtyl.
  rewrite typ_of_type_to_ctype. auto.
Qed.

Lemma type_of_params_to_ctype: forall l,
    Ctypes.type_of_params (map (fun elt : ident * type => (fst elt, to_ctype (snd elt))) l) = to_ctypelist (type_of_params l).
Proof.
  induction l; simpl; auto.
  rewrite IHl. destruct a. simpl. auto.
Qed.

Remark list_cons_neq: forall A (a: A) l, a :: l <> l.
Proof.
  intros. induction l. intro. congruence.
  intro. inv H.  congruence.
Qed.

(* move to RustOp *)
Lemma val_casted_to_ctype: forall ty v,
    val_casted v ty ->
    Cop.val_casted v (to_ctype ty).
Proof.
  destruct ty; intros v CAST; simpl in *; inv CAST; econstructor.
  unfold cast_int_int. auto.
  auto.
Qed.

Lemma val_casted_list_to_ctype: forall tyl vl,
    val_casted_list vl tyl ->
    Cop.val_casted_list vl (to_ctypelist tyl).
Proof.
  induction tyl; simpl; intros vl CAST; inv CAST; econstructor; eauto.
  eapply val_casted_to_ctype. auto.  
Qed.

Lemma val_casted_inject: forall ty v1 v2 j,
    val_casted v1 ty ->
    Val.inject j v1 v2 ->
    val_casted v2 ty.
Proof.
  destruct ty; intros v1 v2 j CAST INJ; inv CAST; inv INJ; econstructor; auto.
Qed.

Lemma val_casted_inject_list: forall tyl vl1 vl2 j,
    val_casted_list vl1 tyl ->
    Val.inject_list j vl1 vl2 ->
    val_casted_list vl2 tyl.
Proof.
  induction tyl; intros vl1 vl2 j CAST INJ; inv CAST; inv INJ; econstructor; eauto.
  eapply val_casted_inject; eauto.
Qed.


Lemma initial_states_simulation:
  forall q1 q2 S, match_query (cc_c inj) w q1 q2 -> initial_state ge q1 S ->
             exists R, Clight.initial_state tge q2 R /\ match_states S R.
Proof.
  intros ? ? ? Hq HS.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq.
  subst. 
  inversion HS. clear HS. subst vf sg vargs m.
  exploit find_funct_match;eauto. eapply inj_stbls_match. eauto. eauto.
  intros (tf & FIND & TRF).
  (* inversion TRF to get tf *)
  inv TRF.
  eexists. split.
  - assert (SIG: signature_of_type targs tres tcc = Ctypes.signature_of_type (to_ctypelist targs) (to_ctype tres) tcc).
    { unfold signature_of_type, Ctypes.signature_of_type. f_equal.
      eapply typlist_of_typelist_to_ctype.
      eapply rettype_of_type_to_ctype. }      
    rewrite SIG. econstructor. eauto.
    (* type of function *)
    { unfold Clight.type_of_function. 
      inv H0; try congruence.
      unfold type_of_function in H4. inv H4.
      f_equal.
      rewrite H9.
      eapply type_of_params_to_ctype.
      rewrite H2. auto.
      auto. }        
    (* val_casted_list *)
    eapply val_casted_list_to_ctype.
    eapply val_casted_inject_list;eauto.
    (* sup include *)
    simpl. inv Hm. inv GE. simpl in *. auto.
  - econstructor; eauto. econstructor.
    inv Hm. simpl. reflexivity.
Qed.

Lemma Clight_list_norepet: forall f, 
  list_norepet (var_names (fn_params f) ++ var_names (fn_vars f))
  -> list_norepet
  (Clight.var_names
     (map
        (fun elt : ident * type =>
         (fst elt, to_ctype (snd elt)))
        (fn_params f)) ++
   Clight.var_names
     (map
        (fun elt : ident * type =>
         (fst elt, to_ctype (snd elt)))
        (fn_vars f))). 
Proof. 
  intros. 
  assert (var_names (fn_params f) = Clight.var_names
  (map (fun elt : ident * type => (fst elt, to_ctype (snd elt))) (fn_params f))). 
  {
    induction (fn_params f).
    simpl in *. auto. 
    simpl in *. f_equal. 
    eapply IHl. 
    inv H. eauto. 
  } 
  assert (var_names (fn_vars f) = Clight.var_names
  (map (fun elt : ident * type => (fst elt, to_ctype (snd elt))) (fn_vars f))). 
  { apply list_norepet_append_commut in H. 
    induction (fn_vars f).
    simpl in *. auto. 
    simpl in *. f_equal. 
    eapply IHl. 
    inv H. eauto. 
  } 
  congruence. 
Qed. 

Lemma sizeof_ge_tge_relation: forall ty,
sizeof ge ty <= Ctypes.sizeof tge (to_ctype ty). 
Proof. 
  intros. 
  induction ty; simpl in *; try (lia). 
  zify. 
  destruct H0. destruct H. subst. 
  eapply Zmult_lt_0_le_compat_r. auto. 
  auto. 
  destruct H. lia. 
  - inv TRANSL. 
    inv match_prog_comp_env0. 
    destruct ((prog_comp_env prog) ! i) eqn : Q.
    apply tr_composite_some in Q. 
    destruct (co_sv c). 
    destruct Q as (tco & B & C & D & E & F). 
    rewrite B. lia. 
    destruct Q as ( tco & uid & tfid & ufid & un & B & C & D & E & F & I & J & K).
    rewrite B. lia. 
    destruct ((Ctypes.prog_comp_env tprog) ! i). 
    generalize (Ctypes.co_sizeof_pos c). lia. 
    lia. 
    - inv TRANSL. 
    inv match_prog_comp_env0. 
    destruct ((prog_comp_env prog) ! i) eqn : Q.
    apply tr_composite_some in Q. 
    destruct (co_sv c). 
    destruct Q as (tco & B & C & D & E & F). 
    rewrite B. lia. 
    destruct Q as ( tco & uid & tfid & ufid & un & B & C & D & E & F & I & J & K).
    rewrite B. lia. 
    destruct ((Ctypes.prog_comp_env tprog) ! i). 
    generalize (Ctypes.co_sizeof_pos c). lia. 
    lia. 
Qed. 

Lemma map_nil : forall (A B: Type) (f: A -> B) l, 
nil = map f l -> l = nil.
Proof. 
  induction l. 
  - auto. 
  - simpl. intros. congruence. Qed. 

Lemma bind_parameters_trans: forall vargs l e m m' te' tm tvargs j1,
Val.inject_list j1 vargs tvargs ->
Mem.inject j1 m tm ->
(* Mem.inject j1 m0 m1' -> *)
bind_parameters ge e m l vargs m' ->
match_env j1 e te' ->
exists tm', Clight.bind_parameters tge te' tm (map (fun elt => (fst elt, to_ctype (snd elt))) l) tvargs tm'
/\ Mem.inject j1 m' tm' 
/\ inj_incr (injw j1 (Mem.support m) (Mem.support tm)) (injw j1 (Mem.support m') (Mem.support tm')).
Proof. 
  intros vargs l e m m' te' tm tvargs j1 VINJL MINJ BIND MATCH. 
  revert BIND MINJ MATCH. 
  revert  l e m m' te' tm. 
  induction VINJL. 
  - intros. inv BIND. simpl. eexists. split; eauto. econstructor. 
    split. auto. econstructor; eauto. 
    econstructor; rewrite H in H0; inv H0.
  - intros. destruct l. inv BIND. 
    inv BIND. 
    generalize (MATCH id). intros REL. 
    rewrite H5 in REL. inv REL. destruct y as (b' & ty').  
    inv H2. 
    exploit assign_loc_inject; eauto.
    intros (tm' & A & B & C).
    exploit IHVINJL; eauto. 
    intros D. destruct D as (tm'' & E & F & G).
    eexists. split; eauto. 
    econstructor; eauto. split; eauto. 
    inv G. inv C. econstructor; try (eapply Mem.sup_include_trans); eauto. 
Qed. 


Lemma alloc_variables_inject_match: forall tm e m l j1 m' e0 e0',
alloc_variables ge e0 m l e m'
-> Mem.inject j1 m tm
-> match_env j1 e0 e0'
-> exists te' tm' j2,  Clight.alloc_variables tge e0' tm
(map (fun elt => (fst elt, to_ctype (snd elt))) l) te' tm'
/\ Mem.inject j2 m' tm' 
/\ match_env j2 e te' 
/\ inj_incr (injw j1 (Mem.support m) (Mem.support tm)) (injw j2 (Mem.support m') (Mem.support tm')).
Proof.
  intros tm e m l j1 m' e0 e0' ALLOC INJ MATCH. 
  revert ALLOC INJ MATCH. 
  revert tm e m j1 m' e0 e0'. 
  induction l. 
  - intros. 
    inv ALLOC. 
    simpl. eexists. eexists. eexists. split. econstructor. split; eauto. split. auto. split; auto. 
    econstructor; auto;
    rewrite H in H0; inv H0.
  - intros. inv ALLOC. 
    exploit Mem.alloc_parallel_inject; eauto. 
    instantiate (1:=0). lia. instantiate (1 := (Ctypes.sizeof tge (to_ctype ty))).
    eapply sizeof_ge_tge_relation. 
    intros K. destruct K as (f' & m2' & b2 & ALLOCINJ & INJ2 & P & Q & R).
    exploit IHl. eauto. eapply INJ2. 
    (* prove IH match_env *)
    instantiate (1:= (PTree.set id (b2, to_ctype ty) e0')).
    red. intros. repeat rewrite PTree.gsspec. 
    generalize (MATCH id0). intros MATCH'.
    destruct (peq id0 id). econstructor. econstructor; eauto.
    exploit match_env_incr; eauto.
    simpl.
    intro A. destruct A as (te' & tm' & j2 & TALLOC & MATCH2 & K & J ). 
    exploit Mem.support_alloc. eapply ALLOCINJ.
    exploit Mem.support_alloc. eapply H3. intros SUP1 SUP2. 
    rewrite SUP1 in J.  rewrite SUP2 in J. inv J.
    assert (INJ12: inject_incr j1 j2). 
    {
      eapply inject_incr_trans; eauto. 
    }
    exists te'. exists tm'. exists j2.  
    split; econstructor; eauto. 
    split; eauto.   
    econstructor; eauto.
    unfold inject_incr_disjoint in *.
    intros.   
    destruct (peq b b1). subst.  
    + exploit H5; eauto. intros. rewrite H0 in H1. inv H1. 
    exploit Mem.alloc_result. eapply H3. intros FM. 
    exploit Mem.alloc_result. eapply ALLOCINJ. intros FTM. 
    subst.  
    unfold Mem.nextblock. 
    split; apply Mem.freshness. 
    + apply R in n. rewrite H in n.
      generalize (H8 b b' delta). intros.
      apply H1 in n; auto.
      unfold not in *. split. intros. 
      destruct n. apply H4. apply Mem.sup_incr_in. right; auto. 
      destruct n. intros. apply H4. apply Mem.sup_incr_in. right; auto.  
Qed.

Lemma function_entry_inject:
forall f tf m1 m2 tm1 j1 vargs tvargs e
  (VARS:  Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars))
  (PARAMS: Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params)),
  function_entry ge f vargs m1 e m2 ->
  Mem.inject j1 m1 tm1 ->
  Val.inject_list j1 vargs tvargs ->
  exists j2 te tm2,
    Clight.function_entry1 tge tf tvargs tm1 te (create_undef_temps (fn_temps tf)) tm2
    /\ match_env j2 e te
    /\ Mem.inject j2 m2 tm2
    /\ inj_incr (injw j1 (Mem.support m1) (Mem.support tm1)) (injw j2 (Mem.support m2) (Mem.support tm2)).
 Proof. 
  intros f tf m1 m2 tm1 j1 vargs tvargs e. 
  intro. intro. intros FUNCENT MEMINJ VALINJ.
  inv FUNCENT.   
  exploit alloc_variables_inject_match; eauto. 
  instantiate (1:= Clight.empty_env). econstructor. 
  intros. destruct H2 as (te' & m1' & j2 & ALLOC' & MEMINJ2 & MATCH & INJ_INCR).
  inv INJ_INCR. 
  exploit val_inject_list_incr; eauto. 
  intros VALINJL2. 
  exploit bind_parameters_trans; eauto. eauto. eauto.  
  intros W. destruct W as (tm'  & BIND & MINJ2 & INJINCRB).  
  eexists. eexists. eexists. split.
  - econstructor; eauto.
    + exploit Clight_list_norepet; eauto. intros. congruence. 
    + rewrite VARS. rewrite PARAMS. 
      erewrite <- map_app. eauto. 
    + rewrite PARAMS. eauto.
  - split; eauto. 
    split. eauto.  
    inv INJINCRB.
    econstructor; try (eapply  Mem.sup_include_trans); eauto. 
Qed.  

(* transition of match_cont *)
Lemma unchanged_on_blocks_match_cont: forall m tm tm' bs j k tk,
    Mem.unchanged_on (fun b ofs => In b bs) tm tm' ->
    match_cont j k tk m tm bs ->
    match_cont j k tk m tm' bs.
Proof.
  induction 2; try econstructor; eauto.
  eapply IHmatch_cont. eapply Mem.unchanged_on_implies; eauto.
  simpl. intros. auto.
  eapply Mem.load_unchanged_on; eauto. simpl. auto.
  red. intros. eapply Mem.perm_unchanged_on; eauto. simpl. auto.
Qed.

Lemma match_cont_inj_incr: forall j j' k tk,
    (* m tm bs are unrealated to this match_cont *)
    (forall m tm bs, match_cont j k tk m tm bs) ->
    inject_incr j j' ->
    forall m tm bs, match_cont j' k tk m tm bs.
Proof.
  induction k; intros until tk; intros MCONT INCR; intros m1 tm1 bs1.
  1-4:
    generalize (MCONT m1 tm1 bs1); intros MCONT1;
    inv MCONT1; econstructor; eauto.
  1-2: eapply match_env_incr; eauto.
  destruct tk.
  1-5: generalize (MCONT m1 tm1 bs1); intros MCONT1; inv MCONT1.
  (* premise is impossible *)
  generalize (MCONT m1 tm1 nil).
  intros MCONT1. inv MCONT1.
Qed.


(* This lemma is too strong, but it is easy to use *)
Lemma injp_acc_match_cont: forall j1 j2 m1 m2 tm1 tm2 Hm1 Hm2 k tk bs,
    match_cont j1 k tk m1 tm1 bs ->
    injp_acc (injpw j1 m1 tm1 Hm1) (injpw j2 m2 tm2 Hm2) ->
    match_cont j2 k tk m2 tm2 bs.
Proof.
  induction 1.
  - intros INJP; econstructor; eauto.
  - intros INJP; econstructor; eauto.
    inv INJP; eapply match_cont_inj_incr; eauto.
  - intros INJP; econstructor; eauto.
    inv INJP; eapply match_cont_inj_incr; eauto.
  - intros INJP; inv INJP. econstructor; eauto.
    eapply match_cont_inj_incr; eauto.
    eapply match_env_incr; eauto.
  - intros INJP; inv INJP. econstructor; eauto.
    eapply match_cont_inj_incr; eauto.
    eapply match_env_incr; eauto.
  - intros INJP. (* inv INJP. *) econstructor; eauto.
    inv INJP.
    eapply Mem.load_unchanged_on; eauto.
    inv INJP. inv VINJ. econstructor. eapply H12. eauto.
    auto.
    intros. inv INJP.
    eapply loc_out_of_reach_incr; eauto.
    eapply inject_implies_dom_in; eauto.
    eapply Mem.perm_valid_block. eapply FREE. instantiate (1 := 0).
    simpl. destruct Archi.ptr64; lia.
    (* perm unchanged *)
    inv INJP.
    red. intros. eapply Mem.perm_unchanged_on; eauto.
Qed.


Lemma PTree_elements_one (A: Type) : forall id (elt: A),
    PTree.elements (PTree.set id elt (PTree.empty A)) = (id, elt) :: nil.
Proof.
  intros.
  generalize (PTree.elements_correct (PTree.set id elt (PTree.empty A)) id (PTree.gss _ _ _)).
  intros IN.
  generalize (PTree.elements_keys_norepet (PTree.set id elt (PTree.empty A))).
  intros NOREPEAT.
  destruct (PTree.elements (PTree.set id elt (PTree.empty A))) eqn: LIST.
  inv IN.
  destruct p. 
  inv IN.
  - inv H.
    destruct l. auto. destruct p.
    assert (IN1: In (p,a) ((id,elt)::(p,a)::l)).
    eapply in_cons. econstructor. auto.
    simpl in NOREPEAT. inv NOREPEAT. 
    generalize (PTree.elements_complete (PTree.set id elt (PTree.empty A)) p a).
    rewrite LIST. intros B. apply B in IN1.
    erewrite PTree.gsspec in IN1.
    destruct (peq p id) eqn: PEQ. inv IN1.
    exfalso. eapply H1. econstructor. auto.
    rewrite PTree.gempty in IN1. congruence.
  - simpl in NOREPEAT. inv NOREPEAT.
    assert (GP: (PTree.set id elt (PTree.empty A))! p = Some a).
    eapply PTree.elements_complete. rewrite LIST.
    econstructor. auto.
    erewrite PTree.gsspec in GP.
    destruct (peq p id) eqn: PEQ. inv GP.
    exfalso. eapply H2. replace id with (fst (id, a)). eapply in_map.
    auto. auto.
    rewrite PTree.gempty in GP. congruence.
Qed.

Lemma drop_glue_children_types_last: forall tys ty hty,
    drop_glue_children_types ty = hty :: tys ->
    ty = last tys hty.
Proof.
  destruct tys.
  simpl. intros.
  destruct ty; simpl in H; inv H; auto.
  destruct (drop_glue_children_types ty). simpl in *. inv H1. auto.
  simpl in H1. inv H1. exfalso.
  eapply app_cons_not_nil. eauto.
  intros.
  intros. destruct ty; simpl in H; inv H.
  assert (last (hty::t::tys) hty = Tbox ty).
  rewrite <- H1. eapply last_last.
  simpl in *. auto.
Qed.


Lemma match_dropmemb_stmt_struct_member: forall id arg fid fty,
    match_dropmemb_stmt id arg Struct (type_to_drop_member_state ge fid fty) (drop_glue_for_member ce dropm arg (Member_plain fid fty)).
Proof.
  intros.
  unfold type_to_drop_member_state. simpl.
  unfold ce. simpl.
  destruct (own_type (prog_comp_env prog) fty); try econstructor.
  unfold drop_glue_for_type.
  destruct (drop_glue_children_types fty) eqn: CHILDTYS.
  econstructor.
  destruct t; try econstructor; eauto.
  1-8 :
    erewrite last_default_unrelate; simpl;
    eapply drop_glue_children_types_last in CHILDTYS; subst;
    destruct l; simpl; eauto.
  unfold dropm. simpl.
  destruct ((generate_dropm prog) ! i) eqn: DM.
  econstructor; eauto. econstructor.
  unfold dropm. simpl.
  destruct ((generate_dropm prog) ! i) eqn: DM.
  econstructor; eauto. econstructor.
Qed.

Lemma match_dropmemb_stmt_enum_member:
  forall id fid uid ufid arg fty,
    enum_consistent id fid uid ufid ->
    match_dropmemb_stmt id arg TaggedUnion (type_to_drop_member_state ge fid fty)
      (drop_glue_for_member ce dropm (Efield arg ufid (Tunion uid noattr)) (Member_plain fid fty)).
Proof.
  intros.
  unfold type_to_drop_member_state. simpl.
  unfold ce. simpl.
  destruct (own_type (prog_comp_env prog) fty); try econstructor.
  unfold drop_glue_for_type.
  destruct (drop_glue_children_types fty) eqn: CHILDTYS.
  econstructor.
destruct t; try econstructor; eauto.
  1-8 :
    erewrite last_default_unrelate; simpl;
    eapply drop_glue_children_types_last in CHILDTYS; subst;
  destruct l; simpl; eauto.
  unfold dropm. simpl.
  destruct ((generate_dropm prog) ! i) eqn: DM.
  econstructor; eauto. econstructor.
  unfold dropm. simpl.
  destruct ((generate_dropm prog) ! i) eqn: DM.
  econstructor; eauto. econstructor.
Qed.


(* The relation between dropm and glues *)
Lemma find_dropm_sound: forall id drop_id,
    dropm ! id = Some drop_id ->
    exists tmb tf,
      Genv.find_symbol tse drop_id = Some tmb
      /\ Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some (Ctypes.Internal tf)
      /\ glues ! id = Some tf.
Proof.
  intros id drop_id DROPM. unfold dropm, ctx in *. simpl in DROPM.
  (* Four steps to get the target drop glue for composite id *)
  (* 1. use generate_dropm_inv to get the source empty drop glue *)
  exploit generate_dropm_inv;eauto.
  intros (src_drop & PROGM & GLUEID).
  (* 2. use Genv.find_def_symbol to get the block of this drop glue
    and prove that target can also find an injected block *)
  exploit Genv.find_def_symbol. eauto. intros A.
  eapply A in PROGM as (mb & FINDSYMB & FINDGLUE). clear A.
  edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
  eapply inj_stbls_match. eauto. eauto.
  (* 3. use find_funct_match to prove that taget can find a
    drop_glue and tr_fundef src_drop tgt_drop *)
  exploit find_funct_match. eauto.
  eapply inj_stbls_match. eauto.
  instantiate (2 := Vptr mb Ptrofs.zero). simpl.
  destruct Ptrofs.eq_dec; try congruence.
  eapply Genv.find_funct_ptr_iff. eauto.
  econstructor. eauto.
  erewrite Ptrofs.add_zero_l. reflexivity.
  intros (tgt_drop & TFINDFUNC & TRFUN).
  (* 4. use generate_drops_inv to prove tgt_drop is the same as the
    result of drop_glue_for_composite *)
  inv TRFUN. inv H0. congruence.
  rewrite GLUEID in H. inv H.
  simpl in H1.
  exists tmb,tf. split; auto. 
Qed.

(* The execution of function entry for drop glue *)
Lemma drop_glue_function_entry_step: forall m tm j chunk v,
    Mem.inject j m tm ->
    exists psb tm1 tm2,
      Mem.alloc tm 0 (size_chunk chunk) = (tm1, psb)
      /\ Mem.store chunk tm1 psb 0 v = Some tm2
      /\ Mem.range_perm tm2 psb 0 (size_chunk chunk) Cur Freeable
      /\ (forall ofs, loc_out_of_reach j m psb ofs)
      /\ Mem.inject j m tm2.
Proof.
  intros until v.
  intros MINJ.
  (* alloc stack block in function entry *)
  destruct (Mem.alloc tm 0 (size_chunk chunk)) as [tm1 psb] eqn: ALLOC.
  (* permission of psb *)
  assert (PERMFREE1: Mem.range_perm tm1 psb 0 (size_chunk chunk) Cur Freeable).
  { red. intros.
    eapply Mem.perm_alloc_2; eauto. }
  (* Mem.inject j m tm1 *)
  exploit Mem.alloc_right_inject; eauto. intros MINJ1.
  (* forall ofs, loc_out_of_reach j m psb ofs *)
  generalize (Mem.fresh_block_alloc _ _ _ _ _ ALLOC). intros NVALID.
  assert (OUTREACH1: forall ofs, loc_out_of_reach j m psb ofs).
  { red. intros. intro. eapply NVALID.
    eapply Mem.valid_block_inject_2; eauto. }
  (* store the function argument to (psb,0) *)
  assert (STORETM1: {tm2: mem | Mem.store chunk tm1 psb 0 v = Some tm2}).
  { eapply Mem.valid_access_store. eapply Mem.valid_access_implies.
    eapply Mem.valid_access_alloc_same;eauto. lia. lia.
    eapply Z.divide_0_r. econstructor. }
  destruct STORETM1 as (tm2 & STORETM1).
  (* Mem.inject j m tm2 *)
  exploit Mem.store_outside_inject. eapply MINJ1.
  2: eapply STORETM1. intros.
  eapply Mem.fresh_block_alloc;eauto.
  eapply Mem.valid_block_inject_2;eauto.
  intros MINJ2.       
  (* store does not change permission *)
  assert (PERMFREE2: Mem.range_perm tm2 psb 0 (size_chunk chunk) Cur Freeable).
  red. intros. eapply Mem.perm_store_1; eauto.
  exists psb, tm1, tm2. auto.
Qed.

                                       
Lemma length_S_inv : forall A n (l: list A),
    length l = S n ->
    exists l' a, l = l' ++ [a] /\ length l' = n.
Proof.
  induction n.
  - intros. destruct l. cbn in *.
    congruence.
    cbn in H. inv H.
    rewrite length_zero_iff_nil in H1.
    subst. exists nil. cbn. eauto.
  - intros. simpl in *. 
    destruct l. cbn in H. congruence.
    cbn in H. inv H.
    generalize (IHn _ H1).
    destruct 1 as (l' & a0 & eq & LEN). subst.
    exists (a :: l'). cbn. eexists; split; eauto.
Qed.

Lemma deref_loc_rec_app: forall tys1 tys2 m b ofs b' ofs',
    deref_loc_rec m b ofs (tys1 ++ tys2) (Vptr b' ofs') <->
      exists b1 ofs1, deref_loc_rec m b ofs tys2 (Vptr b1 ofs1)
                 /\ deref_loc_rec m b1 ofs1 tys1 (Vptr b' ofs').
Proof.
  induction tys1.
  -  simpl. intros.     
     split.
     + intros DER.
       exists b', ofs'.
       split. auto. econstructor.
     + intros (b1 & ofs1 & DER1 & DER2).
       inv DER2. auto.
  - simpl. split.
    + intros DER.
      inv DER. eapply IHtys1 in H1.
      destruct H1 as (b2 & ofs2 & DER1 & DER2).
      exists b2, ofs2. split. auto.
      econstructor. eauto. auto.
    + intros (b1 & ofs1 & DER1 & DER2).
      inv DER2.
      econstructor. eapply IHtys1.
      exists b1, ofs1. split. auto. eauto.
      auto.
Qed.


Lemma deref_loc_rec_inject: forall j m tm tys hty b ofs b1 ofs1 tb tofs e e' te le,
    deref_loc_rec m b ofs tys (Vptr b1 ofs1) ->
    Mem.inject j m tm ->
    deref_arg_rec hty e tys = e' ->
    (Clight.typeof e = to_ctype (last tys hty)) ->
    (* evaluate the address of e *)
    Clight.eval_lvalue tge te le tm e tb tofs Full ->
    Val.inject j (Vptr b ofs) (Vptr tb tofs) ->
    (* the address of e' injects v *)
    exists tb1 tofs1, Clight.eval_lvalue tge te le tm e' tb1 tofs1 Full
                 /\ Val.inject j (Vptr b1 ofs1) (Vptr tb1 tofs1)
.
(* Hard!  *)
Proof.
  intros until tys.
  cut (exists n, length tys = n); eauto. intros (n & LEN).
  generalize dependent tys.
  induction n.
  intros until le; intros DER MINJ DARG HTY EVAL VINJ; subst.  
  eapply length_zero_iff_nil in LEN. subst.
  simpl.  
  exists tb, tofs. inv DER. auto.
  intros until le; intros DER MINJ DARG HTY EVAL VINJ; subst.  
  exploit length_S_inv; eauto.
  intros (tys' & ty & TYS & LEN1). subst.
  rewrite deref_arg_rec_app. eapply deref_loc_rec_app in DER.
  destruct DER as (b2 & ofs2 & DER1 & DER2).
  (* deref_loc ty *)
  inv DER1. inv H1.
  exploit deref_loc_inject; eauto.
  intros (v2 & DER3 & VINJ2). inv VINJ2.
  
  exploit IHn. eauto. eauto. auto.
  instantiate (3:= hty).
  instantiate (2:= (deref_arg_rec (last tys' hty) e [ty])).
  eauto.
  simpl. auto.
  simpl. eapply eval_Ederef. eapply eval_Elvalue.
  eauto. rewrite HTY. rewrite last_last.
  (* deref_loc *)
  eauto.
  econstructor; eauto.
  eauto.
Qed.


Lemma drop_box_rec_injp_acc: forall tys m m' tm j Hm te le b ofs tb tofs arg tk tf hty
    (WFENV: te ! free_id = None)
    (DROPBOX: drop_box_rec ge b ofs m tys m')
    (EVALARG: eval_lvalue tge te le tm arg tb tofs Full)
    (HTY: Clight.typeof arg = to_ctype (last tys hty))
    (VINJ: Val.inject j (Vptr b ofs) (Vptr tb tofs))
    (UNREACH: forall tm1, Mem.unchanged_on (loc_out_of_reach j m) tm tm1 ->
                     eval_lvalue tge te le tm1 arg tb tofs Full),
  exists j' tm' Hm', 
    plus step1 tge
      (Clight.State tf (makeseq (drop_glue_for_box_rec arg tys)) tk te le tm) E0
      (Clight.State tf Clight.Sskip tk te le tm') 
    /\ injp_acc (injpw j m tm Hm) (injpw j' m' tm' Hm')
.
Proof.
  induction tys; simpl; intros.
  inv DROPBOX. exists j, tm, Hm.
  unfold makeseq. simpl. split.
  econstructor. econstructor.
  eapply star_step. econstructor. econstructor.
  1-2: eauto. reflexivity.
  inv DROPBOX.
  (* eval_lvalue (deref_arg_rec a arg tys) *)
  exploit deref_loc_rec_inject; eauto.
  instantiate (1 := a).
  rewrite HTY. f_equal. destruct tys; auto.
  eapply last_default_unrelate.
  intros (tb1 & tofs1 & EVALARG1 & VINJ1).
  (* extcall_free *)  
  exploit extcall_free_injp; eauto.
  instantiate (1 := Hm). instantiate (1 := tge).
  intros (tm1 & Hm1 & FREE1 & INJP1).
  (* use I.H. *)
  exploit IHtys. eauto. eapply H5.
  eapply UNREACH. inv INJP1. eapply H13.
  instantiate (1 := a).
  rewrite HTY. f_equal. destruct tys; auto.
  eapply last_default_unrelate.
  eauto.
  intros. eapply UNREACH.  
  eapply Mem.unchanged_on_trans. inv INJP1. eauto.
  (* prove loc_out_of_reach j m1 implies loc_out_of_reach j m *)
  eapply Mem.unchanged_on_implies. eauto.
  intros. red. intros.
  generalize (H0 b2 delta H4).
  intros BPERM. inv H3.
  intro. eapply BPERM.
  eapply Mem.perm_free_3. eauto. auto.

  instantiate (1:= Hm1). instantiate (1 := tk).
  instantiate (1 := tf).
  intros (j2 & tm2 & Hm2 & STEP & INJP2).

  (* find_symbol free = Some b *)
  destruct (match_prog_free _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MFREE).    
  exploit Genv.find_def_symbol. eauto. intros A.
  eapply A in MFREE as (mb & FINDSYMB & FINDFREE). clear A.
  edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
  eapply inj_stbls_match. eauto. eauto.
  (* find_funct tge tb = Some free_decl *)
  assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some free_decl).
  { edestruct find_funct_match as (free & TFINDFUN & TRFREE).
    eauto. 
    eapply inj_stbls_match. eauto.
    instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
    destruct Ptrofs.eq_dec; try congruence.
    eapply Genv.find_funct_ptr_iff. eauto.
    econstructor. eauto. eauto.
    erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
    inv TRFREE. eauto. intuition. }
    
  do 3 eexists. split.
  (* step *)
  + econstructor.
     econstructor. eapply star_step.     
    (* step to call drop *)
    { econstructor. simpl. eauto.
      econstructor. eapply eval_Evar_global.
      (* We have to ensure that e!free_id = None *)
      auto.
      eauto. simpl. eapply Clight.deref_loc_reference. auto.
      econstructor. econstructor. eauto.
      (* sem_cast *)
      simpl. instantiate (1:= (Vptr tb1 tofs1)).
      unfold Cop.sem_cast. simpl. auto.
      (* eval_exprlist *)
      econstructor.
      eauto. simpl.
      auto. }
    (* step to external call *)
    eapply star_step.
    { eapply Clight.step_external_function. eauto.
      eauto. }
    eapply star_step.    
    econstructor.
    eapply star_step.    
    econstructor.
    eapply plus_star. eauto.
    1-5: eauto.
  + etransitivity. eauto.
    eauto.
Qed.


Lemma step_drop_simulation:
  forall S1 t S2, step_drop ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  unfold build_clgen_env in *. unfold ctx in *. simpl in *.
  induction 1; intros; inv MS.

  (* step_dropstate_init *)
  - inv MSTMT1. cbn [drop_glue_for_members].

    eexists. split.
    (* step *)
    + eapply plus_left.
      econstructor. eapply star_step.
      econstructor. eapply star_refl.
      1-2 : eauto.
    (* match_states *)
    + econstructor; eauto.
      unfold deref_param, pty, co_ty.
      eapply match_dropmemb_stmt_struct_member.

  (** *** There are lots of redundant code in the following four cases *)
      
  (* step_dropstate_composite (from struct to struct) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite STRUCT0 in FOFS.
    inv MSTMT1. destruct COTY; try congruence. inv H.
    (* the field offset *)
    exploit struct_field_offset_match; eauto. eapply (match_prog_comp_env _ _ TRANSL).
    intros (tco1 & TCO1 & TFOFS).
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add ofs' (Ptrofs.repr fofs)) Full).
    { eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. auto.
    }
                        
    (* evaluate (deref_arg_rec field_param tys)  *)
    exploit deref_loc_rec_inject; eauto. instantiate (1:= Tstruct orgs0 id).
    simpl. f_equal. eapply drop_glue_children_types_last;eauto.
    inv VINJ.
    econstructor; eauto. do 2 rewrite Ptrofs.add_assoc. f_equal.
    eapply Ptrofs.add_commut.
    intros (tcb & tcofs & TEVAL & VINJ2).
    
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound. eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eapply CO2. eauto. rewrite STRUCT. simpl.
    intros  DGLUE. inv DGLUE.
    (* alloc stack block in function entry *)
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr tcb tcofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).

    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { erewrite PTree.gso.
          eapply PTree.gempty.
          intro. subst. eapply match_prog_wf_param_id; eauto.
          econstructor. reflexivity.
          eapply in_cons. eapply in_cons.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, param_id). split;auto.
          eapply PTree.elements_correct. auto. }
        eauto.        
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. eauto.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        unfold Clight.type_of_fundef, Clight.type_of_function. simpl.
        repeat f_equal.
        destruct tys. simpl. exploit drop_glue_children_types_last.
        eauto. simpl. intros. subst. auto.
        auto. }                
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl.
      eapply star_one.
      econstructor.
      1-3: eauto.

    (* match_states *)
    +  assert (VALIDPB: Mem.valid_block tm pb).
      { eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access; eauto. econstructor. }
      assert (NOTIN2: ~ In psb (pb :: bs)).
      { intro. inv H. eapply Mem.fresh_block_alloc. eapply ALLOC. auto.
        eapply Mem.fresh_block_alloc. eapply ALLOC. auto. }      
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => In b (pb :: bs)) tm tm2).
      { eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.store_unchanged_on; eauto. }
      eapply match_dropstate_struct with (bs := pb :: bs);eauto.
      econstructor.      
      (* match_cont *)
      { econstructor; eauto.
        rewrite STRUCT0. instantiate (1 := tk).
        split.
        econstructor.
        (* prove fty = last tys fty to preserve this invariant to step_drop_box_rec *)
        exploit  drop_glue_children_types_last; eauto.
        intros. subst. destruct tys; auto.
        eapply last_default_unrelate.        
        eexists. split.
        reflexivity. f_equal.
        (* unchanged_on *)
        eapply  unchanged_on_blocks_match_cont.
        eapply Mem.unchanged_on_implies; eauto.
        simpl. intros. auto.
        auto.
        eapply Mem.load_unchanged_on; eauto. simpl. auto.
        red.  intros. eapply Mem.perm_unchanged_on; eauto.
        simpl. auto. }
      
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr tcb tcofs)). eauto. eauto.
      intros. eapply Mem.valid_block_unchanged_on; eauto.
      inv H; auto.
          
  (* step_dropstate_composite (from enum to struct) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite ENUM in FOFS.
    inv MSTMT. destruct COTY; try congruence. inv H.
    (* the field offset *)
    generalize (ECONSIST _ CO ENUM).
    intros (tco1 & utco & TCO1 & UTCO & TFOFS).
    generalize (TFOFS _ _ FOFS).
    intros (cfofs1 & cfofs2 & TUFOFS & TFFOFS & OFSEQ).
    subst.
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add (Ptrofs.add ofs' (Ptrofs.repr cfofs1)) (Ptrofs.repr cfofs2)) Full).
    { eapply eval_Efield_union. eapply eval_Elvalue.
      eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. eauto.
      simpl. eapply Clight.deref_loc_copy. auto.
      simpl. eauto. eauto.
      auto.
    }
    
    (* evaluate (deref_arg_rec field_param tys)  *)
    exploit deref_loc_rec_inject; eauto. instantiate (1:= Tstruct orgs0 id).
    simpl. f_equal. eapply drop_glue_children_types_last;eauto.
    inv VINJ.
    econstructor; eauto.
    rewrite add_repr.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.add_permut. f_equal.
    apply Ptrofs.add_commut.
    intros (tcb & tcofs & TEVAL & VINJ2).
    
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound. eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eapply CO2. eauto. rewrite STRUCT. simpl.
    intros DGLUE. inv DGLUE.
    (* alloc stack block in function entry *)
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr tcb tcofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).

    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { erewrite PTree.gso.
          eapply PTree.gempty.
          intro. subst. eapply match_prog_wf_param_id; eauto.
          econstructor. reflexivity.
          eapply in_cons. eapply in_cons.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, param_id). split;auto.
          eapply PTree.elements_correct. auto. }        
        simpl. eauto. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. eauto.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        unfold Clight.type_of_fundef, Clight.type_of_function. simpl.
        repeat f_equal.
        destruct tys. simpl. exploit drop_glue_children_types_last.
        eauto. simpl. intros. subst. auto.
        auto. }                
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl.
      eapply star_one.
      econstructor.
      1-3: eauto.

    (* match_states *)
    +  assert (VALIDPB: Mem.valid_block tm pb).
      { eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access; eauto. econstructor. }
      assert (NOTIN2: ~ In psb (pb :: bs)).
      { intro. inv H. eapply Mem.fresh_block_alloc. eapply ALLOC. auto.
        eapply Mem.fresh_block_alloc. eapply ALLOC. auto. }      
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => In b (pb :: bs)) tm tm2).
      { eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.store_unchanged_on; eauto. }
      eapply match_dropstate_struct with (bs := pb :: bs);eauto.
      econstructor.      
      (* match_cont *)
      { econstructor; eauto.
        rewrite ENUM. instantiate (1 := tk).
        split.
        econstructor. eauto.
        (* prove fty = last tys fty to preserve this invariant to step_drop_box_rec *)
        exploit  drop_glue_children_types_last; eauto.
        intros. subst. destruct tys; auto.
        eapply last_default_unrelate.        
        eexists. split.
        reflexivity. f_equal.
        (* unchanged_on *)
        eapply  unchanged_on_blocks_match_cont.
        eapply Mem.unchanged_on_implies; eauto.
        simpl. intros. auto.
        auto.
        eapply Mem.load_unchanged_on; eauto. simpl. auto.
        red.  intros. eapply Mem.perm_unchanged_on; eauto.
        simpl. auto. }
      
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr tcb tcofs)). eauto. eauto.
      intros. eapply Mem.valid_block_unchanged_on; eauto.
      inv H; auto.
    
  (* step_dropstate_composite (from struct to enum) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite STRUCT in FOFS.
    inv MSTMT1. destruct COTY; try congruence. inv H.
    (* the field offset *)
    exploit struct_field_offset_match; eauto. eapply (match_prog_comp_env _ _ TRANSL).
    intros (tco1 & TCO1 & TFOFS).
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add ofs' (Ptrofs.repr fofs)) Full).
    { eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. auto.
    }
                        
    (* evaluate (deref_arg_rec field_param tys)  *)
    exploit deref_loc_rec_inject; eauto. instantiate (1:= Tvariant orgs0 id).
    simpl. f_equal. eapply drop_glue_children_types_last;eauto.
    inv VINJ.
    econstructor; eauto. do 2 rewrite Ptrofs.add_assoc. f_equal.
    eapply Ptrofs.add_commut.
    intros (tcb & tcofs & TEVAL & VINJ2).
    
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound. eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eapply CO2. eauto. rewrite ENUM. simpl.
    intros (union_id & tag_fid & union_fid & tco & uco & DGLUE & TCO & TUCO & TAGOFS & UFOFS).
    inv DGLUE.
    (* alloc stack block in function entry *)
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr tcb tcofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).
    
    exploit select_switch_sem_match; eauto.
    instantiate (1 := (Efield  (Ederef (Evar param_id (Tpointer (Ctypes.Tstruct id noattr) noattr)) (Ctypes.Tstruct id noattr)) union_fid (Tunion union_id noattr))).
    instantiate (1 := (generate_dropm prog)).
    instantiate (1 := (prog_comp_env prog)).
    intros (unused_ts & SEL). 
        
    eexists. split.
    (* step *)
    + econstructor.
      econstructor. eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { erewrite PTree.gso.
          eapply PTree.gempty.
          intro. subst. eapply match_prog_wf_param_id; eauto.
          econstructor. reflexivity.
          eapply in_cons. eapply in_cons.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, param_id). split;auto.
          eapply PTree.elements_correct. auto. } 
        eauto.
        simpl. eauto. eapply Clight.deref_loc_reference. auto.        
        econstructor. econstructor. eauto.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        unfold Clight.type_of_fundef, Clight.type_of_function. simpl.
        repeat f_equal.
        destruct tys. simpl. exploit drop_glue_children_types_last.
        eauto. simpl. intros. subst. auto.
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl. eapply star_step.
      (** Start to evaluate the swtich statement *)
      { econstructor.
        (* evaluate switch tag *)
        { instantiate (1 := Vint tag).
          econstructor. econstructor. econstructor.
          econstructor. econstructor. econstructor.
          eapply PTree.gss. eapply Clight.deref_loc_value.
          simpl. eauto.
          instantiate (1 := tcofs). instantiate (1 := tcb).
          simpl. erewrite Mem.load_store_same with (v:= Vptr tcb tcofs).
          auto. eauto.
          simpl. eapply Clight.deref_loc_copy. auto.
          simpl. eauto. simpl. eauto.
          eauto. rewrite Ptrofs.add_zero.
          simpl. eapply Clight.deref_loc_value.
          simpl. eauto.
          exploit Mem.loadv_inject. eapply MINJ2. eauto. eauto.
          intros (v2 & TLOAD & VINJ3). inv VINJ3.
          auto. }
        simpl. unfold Ctypes.type_int32s, sem_switch_arg. simpl. eauto. }
      eapply star_step.
      (* evaluate switch *)
      rewrite SEL.
      econstructor. eapply star_step.
      econstructor. eapply star_refl.
      1-6 : eauto.

    +  assert (VALIDPB: Mem.valid_block tm pb).
      { eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access; eauto. econstructor. }
      assert (NOTIN2: ~ In psb (pb :: bs)).
      { intro. inv H. eapply Mem.fresh_block_alloc. eapply ALLOC. auto.
        eapply Mem.fresh_block_alloc. eapply ALLOC. auto. }      
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => In b (pb :: bs)) tm tm2).
      { eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.store_unchanged_on; eauto. }
      eapply match_dropstate_enum with (bs := pb::bs); eauto.
      (* match_cont *)
      { econstructor; eauto.
        rewrite STRUCT. instantiate (1 := tk).
        split.
        econstructor. eauto.
        (* prove fty = last tys fty to preserve this invariant to step_drop_box_rec *)
        exploit  drop_glue_children_types_last; eauto.
        intros. subst. destruct tys; auto.
        eapply last_default_unrelate.
        (* unchanged_on *)
        eauto.
        eapply  unchanged_on_blocks_match_cont.
        eapply Mem.unchanged_on_implies; eauto.
        simpl. intros. auto.
        auto.
        eapply Mem.load_unchanged_on; eauto. simpl. auto.
        red.  intros. eapply Mem.perm_unchanged_on; eauto.
        simpl. auto. }
      (* match_dropmemb_stmt idmatch_dropmemb_stmt id *)
      (* prove match_dropmemb_stmt *)
      assert (ENUMCON: enum_consistent id fid2 union_id union_fid).
      { unfold enum_consistent. simpl in CO2. unfold ce. rewrite CO2.
          intros. inv H. exists tco, uco.
          split. unfold tce. auto. split. unfold tce. auto.
          intros. eapply UFOFS. eauto. }
      eapply match_dropmemb_stmt_enum_member; eauto.
      (* inj_incr *)
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr tcb tcofs)). eauto. eauto.
      intros. eapply Mem.valid_block_unchanged_on; eauto.
      inv H; auto.
            
  (* step_dropstate_composite (from enum to enum) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite ENUM0 in FOFS.
    inv MSTMT. destruct COTY; try congruence. inv H.
    (* the field offset *)
    generalize (ECONSIST _ CO ENUM0).
    intros (tco1 & utco & TCO1 & UTCO & TFOFS).
    generalize (TFOFS _ _ FOFS).
    intros (cfofs1 & cfofs2 & TUFOFS & TFFOFS & OFSEQ).
    subst.
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add (Ptrofs.add ofs' (Ptrofs.repr cfofs1)) (Ptrofs.repr cfofs2)) Full).
    { eapply eval_Efield_union. eapply eval_Elvalue.
      eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. eauto.
      simpl. eapply Clight.deref_loc_copy. auto.
      simpl. eauto. eauto.
      auto.
    }
    
    (* evaluate (deref_arg_rec field_param tys)  *)
    exploit deref_loc_rec_inject; eauto. instantiate (1:= Tvariant orgs0 id).
    simpl. f_equal. eapply drop_glue_children_types_last;eauto. 
    inv VINJ.
    econstructor; eauto.
    rewrite add_repr.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.add_permut. f_equal.
    apply Ptrofs.add_commut.
    intros (tcb & tcofs & TEVAL & VINJ2).
    
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound. eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eapply CO2. eauto. rewrite ENUM. simpl.
    intros (union_id & tag_fid & union_fid & tco & uco & DGLUE & TCO & TUCO & TAGOFS & UFOFS).
    inv DGLUE.
    (* alloc stack block in function entry *)
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr tcb tcofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).

    (* evaluate switch *)
    exploit select_switch_sem_match; eauto.
    instantiate (1 := (Efield (Ederef (Evar param_id (Tpointer (Ctypes.Tstruct id noattr) noattr)) (Ctypes.Tstruct id noattr)) union_fid (Tunion union_id noattr))).
    instantiate (1 := (generate_dropm prog)).
    instantiate (1 := (prog_comp_env prog)).
    intros (unused_ts & SEL). 
        
    eexists. split.
    (* step *)
    + econstructor.
      econstructor. eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { erewrite PTree.gso.
          eapply PTree.gempty.
          intro. subst. eapply match_prog_wf_param_id; eauto.
          econstructor. reflexivity.
          eapply in_cons. eapply in_cons.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, param_id). split;auto.
          eapply PTree.elements_correct. auto. } 
        eauto.
        simpl. eauto. eapply Clight.deref_loc_reference. auto.        
        econstructor. econstructor. eauto.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        unfold Clight.type_of_fundef, Clight.type_of_function. simpl.
        repeat f_equal.
        destruct tys. simpl. exploit drop_glue_children_types_last.
        eauto. simpl. intros. subst. auto.
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl. eapply star_step.
      (** Start to evaluate the swtich statement *)
      { econstructor.
        (* evaluate switch tag *)
        { instantiate (1 := Vint tag).
          econstructor. econstructor. econstructor.
          econstructor. econstructor. econstructor.
          eapply PTree.gss. eapply Clight.deref_loc_value.
          simpl. eauto.
          instantiate (1 := tcofs). instantiate (1 := tcb).
          simpl. erewrite Mem.load_store_same with (v:= Vptr tcb tcofs).
          auto. eauto.
          simpl. eapply Clight.deref_loc_copy. auto.
          simpl. eauto. simpl. eauto.
          eauto. rewrite Ptrofs.add_zero.
          simpl. eapply Clight.deref_loc_value.
          simpl. eauto.
          exploit Mem.loadv_inject. eapply MINJ2. eauto. eauto.
          intros (v2 & TLOAD & VINJ3). inv VINJ3.
          auto. }
        simpl. unfold Ctypes.type_int32s, sem_switch_arg. simpl. eauto. }
      eapply star_step.
      (* evaluate switch *)
      rewrite SEL.
      econstructor. eapply star_step.
      econstructor. eapply star_refl.
      1-6 : eauto.

    +  assert (VALIDPB: Mem.valid_block tm pb).
      { eapply Mem.valid_access_valid_block.
        eapply Mem.valid_access_implies.
        eapply Mem.load_valid_access; eauto. econstructor. }
      assert (NOTIN2: ~ In psb (pb :: bs)).
      { intro. inv H. eapply Mem.fresh_block_alloc. eapply ALLOC. auto.
        eapply Mem.fresh_block_alloc. eapply ALLOC. auto. }      
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => In b (pb :: bs)) tm tm2).
      { eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on; eauto.
        eapply Mem.store_unchanged_on; eauto. }
      eapply match_dropstate_enum with (bs := pb::bs); eauto.
      (* match_cont *)
      { econstructor; eauto.
        rewrite ENUM0. instantiate (1 := tk).
        split.
        econstructor. eauto.
        (* prove fty = last tys fty to preserve this invariant to step_drop_box_rec *)
        exploit  drop_glue_children_types_last; eauto.
        intros. subst. destruct tys; auto.
        eapply last_default_unrelate.
        eauto.        
        (* unchanged_on *)
        eapply  unchanged_on_blocks_match_cont.
        eapply Mem.unchanged_on_implies; eauto.
        simpl. intros. auto.
        auto.
        eapply Mem.load_unchanged_on; eauto. simpl. auto.
        red.  intros. eapply Mem.perm_unchanged_on; eauto.
        simpl. auto. }
      (* match_dropmemb_stmt idmatch_dropmemb_stmt id *)     
      (* prove match_dropmemb_stmt *)
      assert (ENUMCON: enum_consistent id fid2 union_id union_fid).
      { unfold enum_consistent. simpl in CO2. unfold ce. rewrite CO2.
          intros. inv H. exists tco, uco.
          split. unfold tce. auto. split. unfold tce. auto.
          intros. eapply UFOFS. eauto. }
      eapply match_dropmemb_stmt_enum_member; eauto.

      
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr tcb tcofs)). eauto. eauto.
      intros. eapply Mem.valid_block_unchanged_on; eauto.
      inv H; auto.
    
  (* step_dropstate_box (in struct) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite STRUCT in FOFS.
    inv MSTMT1.
    (* the field offset *)
    exploit struct_field_offset_match; eauto. eapply (match_prog_comp_env _ _ TRANSL).
    intros (tco1 & TCO1 & TFOFS).
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add ofs' (Ptrofs.repr fofs)) Full).
    { eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. auto.
    }

    exploit drop_box_rec_injp_acc; eauto.
    assert (param_id <> free_id).
    { exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
      eapply CO. eauto. rewrite STRUCT. simpl.
      intros DGLUE. eapply match_prog_wf_param_id; eauto.
      intuition.
      intuition. }
    rewrite PTree.gso. eapply PTree.gempty. intuition.
    simpl. f_equal. eauto.
    inv VINJ.
    econstructor; eauto. repeat rewrite Ptrofs.add_assoc.
    f_equal. eapply Ptrofs.add_commut.
    (* unchanged_on out_of_reach  *)
    intros. econstructor. econstructor. econstructor.
    econstructor. econstructor.
    eapply PTree.gss. eapply Clight.deref_loc_value.
    simpl. eauto.
    eapply Mem.load_unchanged_on; eauto.
    eapply Clight.deref_loc_copy. auto.
    simpl. unfold co_ty. eauto.
    eauto. auto.
    (* evaluation get *)
    instantiate (1 := MINJ). instantiate (1 := (Clight.Kseq (drop_glue_for_members ce dropm deref_param membs) tk)).
    instantiate (1 := tf).
    intros (j' & tm' & MINJ' & STEP & INJP).
    eexists. split. eauto.
    (* match_state *)
    exploit injp_acc_inj_incr; eauto. intros INCR2.
    exploit injp_acc_match_cont; eauto. intros MCONT2.
    inv INJP.
    eapply match_dropstate_struct with (bs:= bs);eauto.
    econstructor.
    etransitivity. eauto. auto.
    (* load pb in tm' unchanged *)
    eapply Mem.load_unchanged_on; eauto.
    (* perm unchanged *)
    red. intros. eapply Mem.perm_unchanged_on; eauto.
    (* loc_out_of_reach unchanged *)
    intros. eapply loc_out_of_reach_incr; eauto.
    eapply inject_implies_dom_in; eauto.
    eapply Mem.perm_valid_block. eapply FREE. instantiate (1 := 0).
    simpl. destruct Archi.ptr64; lia.
    (* valid_block unchanged *)    
    intros. eapply Mem.valid_block_unchanged_on; eauto.
       
  (* step_dropstate_box (in enum) *)
  - simpl in CO1. unfold ce in CO. rewrite CO in CO1. inv CO1.
    rewrite ENUM in FOFS.
    inv MSTMT.
    (* the field offset *)
    generalize (ECONSIST _ CO ENUM).
    intros (tco1 & utco & TCO1 & UTCO & TFOFS).
    generalize (TFOFS _ _ FOFS).
    intros (cfofs1 & cfofs2 & TUFOFS & TFFOFS & OFSEQ).
    subst.
    (* evaluate field_param *)
    assert (EVALFP: Clight.eval_lvalue tge (PTree.set param_id (pb, pty) Clight.empty_env) le tm field_param b' (Ptrofs.add (Ptrofs.add ofs' (Ptrofs.repr cfofs1)) (Ptrofs.repr cfofs2)) Full).
    { eapply eval_Efield_union. eapply eval_Elvalue.
      eapply eval_Efield_struct. eapply eval_Elvalue.
      eapply eval_Ederef. econstructor. econstructor.
      eapply PTree.gss. simpl. econstructor. simpl. auto.
      eauto.  simpl. eapply Clight.deref_loc_copy. auto.
      simpl. unfold co_ty. auto.
      eauto. eauto.
      simpl. eapply Clight.deref_loc_copy. auto.
      simpl. eauto. eauto.
      auto.
    }    

    exploit drop_box_rec_injp_acc; eauto.
    assert (param_id <> free_id).
    { exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
      eapply CO. eauto. rewrite ENUM. simpl.
      intros (union_id & tag_fid & union_fid & tco & uco & DGLUE & TCO & TUCO & TAGOFS & UFOFS).
      eapply match_prog_wf_param_id; eauto.
      intuition.
      intuition. }
    rewrite PTree.gso. eapply PTree.gempty. intuition.
    simpl. f_equal. eauto.
    inv VINJ.
    econstructor; eauto.
    rewrite add_repr.
    repeat rewrite Ptrofs.add_assoc. f_equal.
    rewrite Ptrofs.add_permut. f_equal.
    apply Ptrofs.add_commut.
    (* unchanged_on out_of_reach  *)
    intros. eapply eval_Efield_union. econstructor. eapply eval_Efield_struct.
    econstructor. econstructor. econstructor. econstructor.
    eapply PTree.gss. eapply Clight.deref_loc_value.
    simpl. eauto.
    eapply Mem.load_unchanged_on; eauto.
    eapply Clight.deref_loc_copy. auto.
    simpl. unfold co_ty. eauto.
    eauto. auto.
    eauto. eapply Clight.deref_loc_copy. auto.
    simpl. eauto. eauto. auto.
    (* evaluation get *)
    instantiate (1 := MINJ). instantiate (1 := (Clight.Kseq Clight.Sbreak (Clight.Kseq uts (Kswitch tk)))).
    instantiate (1 := tf).
    intros (j' & tm' & MINJ' & STEP & INJP).
    eexists. split. eauto.
    (* match_state *)
    exploit injp_acc_inj_incr; eauto. intros INCR2.
    exploit injp_acc_match_cont; eauto. intros MCONT2.
    inv INJP.
    eapply match_dropstate_enum with (bs:= bs);eauto.
    econstructor.
    etransitivity. eauto. auto.
    (* load pb in tm' unchanged *)
    eapply Mem.load_unchanged_on; eauto.
    (* perm unchanged *)
    red. intros. eapply Mem.perm_unchanged_on; eauto.
    (* loc_out_of_reach unchanged *)
    intros. eapply loc_out_of_reach_incr; eauto.
    eapply inject_implies_dom_in; eauto.
    eapply Mem.perm_valid_block. eapply FREE. instantiate (1 := 0).
    simpl. destruct Archi.ptr64; lia.
    (* valid_block unchanged *)    
    intros. eapply Mem.valid_block_unchanged_on; eauto.
    
  (* step_drop_return1 *)
  - inv MSTMT1. simpl.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_refl.
      1-3: eauto.
    (* match_states *)
    + econstructor; auto. econstructor.
      instantiate (1 := initial_generator). auto.
      
      (* Mem.inject *)
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs0 + delta).
      replace (ofs0 + delta - delta) with ofs0 by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      (* inj_incr *)
      erewrite Mem.support_free with (m2:= tm1); eauto.
            
  (* step_drop_return1 (in enum) *)
  - inv MSTMT.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      (* evaluate Sbreak *)
      econstructor. eapply star_step.
      econstructor. auto.
      (* evaluate Kcall *)
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_refl.
      1-5: eauto.
    (* match_states *)
    + econstructor; auto. econstructor.
      instantiate (1 := initial_generator). auto.
      (* Mem.inject *)
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs0 + delta).
      replace (ofs0 + delta - delta) with ofs0 by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      (* inj_incr *)
      erewrite Mem.support_free with (m2:= tm1); eauto.
      
  (* step_drop_return2 (in struct) *)
  - inv MSTMT1. simpl.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    inv MCONT.
    
    eexists. split.
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_step.
      econstructor.
      eapply star_refl.
      1-4: eauto.
    (* match_states *)
    + assert (MINJ3: Mem.inject j m tm1).
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs + delta).
      replace (ofs + delta - delta) with ofs by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      assert (INCR3: inj_incr w (injw j (Mem.support m) (Mem.support tm1))).
      erewrite Mem.support_free with (m2:= tm1); eauto.
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => pb <> b) tm tm1).
      { eapply Mem.free_unchanged_on; eauto. }        
      assert (MCONT3: match_cont j k tk0 m tm1 bs0).
      { eapply unchanged_on_blocks_match_cont. instantiate (1 := tm).
        eapply Mem.unchanged_on_implies. eauto. simpl. intros.
        intro. eapply NOTIN. subst. intuition.
        eauto. }                
      assert (LOADV3: Mem.loadv Mptr tm1 (Vptr pb0 Ptrofs.zero) = Some (Vptr b'0 ofs'0)).
      { eapply Mem.load_unchanged_on; eauto.
        rewrite Ptrofs.unsigned_zero. intros.         
        eapply not_in_cons. eauto. }
      assert (PERM3: Mem.range_perm tm1 pb0 0 (Ctypes.sizeof tce (Tpointer (Ctypes.Tstruct id2 noattr) noattr)) Cur Freeable).
      { red. intros.
        (* range_perm *)
        erewrite <- Mem.unchanged_on_perm; eauto. simpl. eapply not_in_cons.
        eauto. eapply VALIDBS. constructor; auto. }
      assert (VALIDBS3: forall b : block, In b bs0 -> Mem.valid_block tm1 b).
      { (* validbs *)
        intros.
        eapply Mem.valid_block_unchanged_on; eauto.
        eapply VALIDBS. eapply in_cons. auto. }
      
      (* case 1: co_sv co0 = Struct. Return to a struct drop glue*)      
      destruct (co_sv co0) eqn: SV.
      * destruct MSTMT as (MEMBST & ts2 & TS2 & KTS). subst.
        eapply match_dropstate_struct; eauto.
        
      (* case 2: co_sv co0 = Taggedunion. Return to a enum drop glue*)      
      * destruct MSTMT as (MEMBST & uts & KTS & MEMBS). subst.
        eapply match_dropstate_enum; eauto.
        
  (* step_drop_return2 (in enum) *)
  - inv MSTMT.
    inv MCONT.
    (* free function arguments success *)   
    assert (MFREE: {tm1 | Mem.free tm pb 0 (Ctypes.sizeof tce pty) = Some tm1}).
    eapply Mem.range_perm_free. auto.
    destruct MFREE as (tm1 & MFREE).
    
    eexists. split.    
    (* step *)
    + eapply plus_left.
      econstructor.
      eapply star_step.
      (* evaluate Sbreak *)
      econstructor. eapply star_step.
      econstructor. auto.
      (* evaluate Kcall *)
      eapply star_step.
      econstructor. simpl. auto.
      unfold Clight.blocks_of_env.
      erewrite PTree_elements_one.
      simpl. unfold pty in *.
      simpl in MFREE. rewrite MFREE.
      eauto.
      eapply star_step.
      econstructor. simpl.
      eapply star_step.
      econstructor.      
      eapply star_refl.
      1-6: eauto.
    (* match_states *)
    + assert (MINJ3: Mem.inject j m tm1).
      eapply Mem.free_right_inject; eauto.
      intros. eapply UNREACH. eauto. instantiate (1 := ofs + delta).
      replace (ofs + delta - delta) with ofs by lia.
      eapply Mem.perm_max. eapply Mem.perm_implies.
      eauto. econstructor.
      assert (INCR3: inj_incr w (injw j (Mem.support m) (Mem.support tm1))).
      erewrite Mem.support_free with (m2:= tm1); eauto.
      assert (UNCHANGE: Mem.unchanged_on (fun b ofs => pb <> b) tm tm1).
      { eapply Mem.free_unchanged_on; eauto. }        
      assert (MCONT3: match_cont j k tk0 m tm1 bs0).
      { eapply unchanged_on_blocks_match_cont. instantiate (1 := tm).
        eapply Mem.unchanged_on_implies. eauto. simpl. intros.
        intro. eapply NOTIN. subst. intuition.
        eauto. }                
      assert (LOADV3: Mem.loadv Mptr tm1 (Vptr pb0 Ptrofs.zero) = Some (Vptr b'0 ofs'0)).
      { eapply Mem.load_unchanged_on; eauto.
        rewrite Ptrofs.unsigned_zero. intros.         
        eapply not_in_cons. eauto. }
      assert (PERM3: Mem.range_perm tm1 pb0 0 (Ctypes.sizeof tce (Tpointer (Ctypes.Tstruct id2 noattr) noattr)) Cur Freeable).
      { red. intros.
        (* range_perm *)
        erewrite <- Mem.unchanged_on_perm; eauto. simpl. eapply not_in_cons.
        eauto. eapply VALIDBS. constructor; auto. }
      assert (VALIDBS3: forall b : block, In b bs0 -> Mem.valid_block tm1 b).
      { (* validbs *)
        intros.
        eapply Mem.valid_block_unchanged_on; eauto.
        eapply VALIDBS. eapply in_cons. auto. }
      
      (* case 1: co_sv co0 = Struct. Return to a struct drop glue*)      
      destruct (co_sv co0) eqn: SV.
      * destruct MSTMT as (MEMBST & ts2 & TS2 & KTS). subst.
        eapply match_dropstate_struct; eauto.
        
      (* case 2: co_sv co0 = Taggedunion. Return to a enum drop glue*)      
      * destruct MSTMT as (MEMBST & uts1 & KTS & MEMBS). subst.
        eapply match_dropstate_enum; eauto.
        
Qed.

  
Lemma step_simulation:
  forall S1 t S2, step ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  unfold build_clgen_env in *. unfold ctx in *. simpl in *.
  induction 1; intros; inv MS.
          
  (* assign *)
  - inv MSTMT. simpl in H3.
    monadInv_comb H3.
    (* eval place and expr *)       
    exploit eval_place_inject;eauto. instantiate (1:= le0).
    intros (b' & ofs' & EL & INJL).
    exploit eval_expr_inject; eauto. instantiate (1:= le0).
    intros (v' & ER & INJV1).
    exploit sem_cast_to_ctype_inject; eauto. instantiate (1 := tm).
    intros (v1' & CASTINJ & INJV2).  
    exploit assign_loc_inject. eauto. eauto. eapply INJV2. eauto.
    intros (tm2 & TASS & INJA & INCR2).
    erewrite place_to_cexpr_type in *;eauto.
    erewrite expr_to_cexpr_type in *;eauto.
    eexists. split.
    (* step *)
    + eapply plus_one.
      eapply Clight.step_assign;eauto.
      (* Other proof strategy for sem_cast:
         1. type equal between lhs and rhs
         2. evaluation of well typed expression produces casted value (val_casted)
         3. use cast_val_casted *)
    (* match state *)
    + assert (INCR3: inj_incr w (injw j (Mem.support m2) (Mem.support tm2))).
      etransitivity. eauto. eauto.      
      eapply match_regular_state. eauto. eauto. eauto.
      econstructor. simpl. instantiate (1 := g). eauto.
      instantiate (1 := j).
      (* inject_incr and match_cont *)
      { eapply match_cont_inj_incr; auto. }
      eauto. eauto.
      eapply match_env_incr;eauto. 
      
  (* assign_variant *)
  - inv MSTMT. simpl in H9.
    monadInv_comb H9.
    unfold transl_assign_variant in EQ0.
    rename H3 into SENUM.
    unfold ge in SENUM. simpl in SENUM. fold ce in SENUM.
    rewrite SENUM in EQ0.
    destruct (co_sv co) eqn: SCV; [inv EQ0|].
    (* variant_field_offset *)
    exploit variant_field_offset_match.
    eapply match_prog_comp_env; eauto.
    eauto.
    auto.
    intros (tco & union_id & tag_fid & union_fid & union & A & B & C & D & E).
    clear E.
    (* rewrite to_cstmt *)
    rename H4 into TAG. rewrite TAG in EQ0.
    unfold tce in EQ0. rewrite A in EQ0. rewrite C in EQ0.
    rewrite H0 in EQ0.
    inv EQ0.
    (* eval_lvalue (Efield x0 tag_fid Ctypes.type_int32s) *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (tb & tofs & TEVALP & VINJ1).
    assert (TYTP: Clight.typeof x0 = Ctypes.Tstruct enum_id noattr).
    exploit place_to_cexpr_type; eauto. intros CTYP.
    rewrite <- CTYP. rewrite TYP. simpl. auto.    
    assert (EVALTAG: eval_lvalue tge te le0 tm (Efield x0 tag_fid Ctypes.type_int32s) tb (Ptrofs.add tofs (Ptrofs.zero)) Full).
    { eapply eval_Efield_struct. eapply eval_Elvalue; eauto.
      rewrite TYTP. eapply Clight.deref_loc_copy; eauto.
      eauto. eauto.
      (* tag field offset *)
      rewrite C. unfold Ctypes.field_offset. simpl.
      destruct ident_eq; try congruence.
      f_equal. }
    (* store tag to tm *)
    inv VINJ1.
    exploit Mem.store_mapped_inject; eauto.
    intros (tm2 & TSTORETAG & VINJ2).
    (* eval_lvalue (Efield (Efield x0 union_fid (Tunion union_id noattr)) fid
       (to_ctype (typeof e))) in tm2 *)    
    exploit eval_place_inject. 2: eapply H7. simpl.
    rewrite TYP. simpl in H. unfold ce. rewrite H.
    unfold tce. rewrite A.  rewrite SCV. rewrite C.
    unfold ce, tce in EQ1. rewrite EQ1. simpl. eauto.
    eauto. eauto.
    instantiate (1 := le0).
    intros (tb1 & tofs1 & TEVALP1 & VINJ3).
    (* eval_expr_inject  *)
    exploit eval_expr_inject; eauto. instantiate (1 := le0).
    intros (tv & TEVAL & VINJ4).
    (* sem_cast inject *)
    exploit sem_cast_to_ctype_inject; eauto. instantiate (1 := tm2).
    intros (tv1 & SEMCAST & VINJ5).
    (* assign_loc inject *)
    exploit assign_loc_inject; eauto.
    intros (tm3 & TASSLOC & MINJ3 & INCR3).
    
    (* step in target *)
    eexists. split.
    + eapply plus_left.
      eapply Clight.step_seq.
      (* assign tag *)
      eapply star_step. eapply Clight.step_assign.
      eauto. econstructor.
      simpl. eapply cast_val_casted. econstructor.
      auto.
      econstructor. simpl. eauto.
      rewrite Ptrofs.add_zero. simpl.
      erewrite Mem.address_inject. eauto.
      eapply MINJ.
      exploit Mem.store_valid_access_3. eapply H5.
      intros. eapply Mem.valid_access_perm. eauto.
      eauto.
      (* assign body *)
      eapply star_step. econstructor.
      eapply star_step. econstructor.
      instantiate (1 := Full). instantiate (1 := tofs1).
      instantiate (1 := tb1).
      inv TEVALP1. simpl in H12.  inv H12.
      eapply eval_Efield_union;eauto.
      eauto. simpl. erewrite expr_to_cexpr_type in *; eauto.
      simpl. eauto.
      econstructor.
      1-4 : eauto.

    + eapply match_regular_state with (j := j);eauto.
      econstructor. instantiate (1 := initial_generator).
      auto. 
      (* inject_incr and match_cont *)
      (* inj_incr *)
      etransitivity. eauto.
      replace (Mem.support m1) with (Mem.support m2).
      replace (Mem.support tm) with (Mem.support tm2). auto.
      eapply Mem.support_store; eauto.
      eapply Mem.support_store; eauto.
      
  (* box *)
  - inv MSTMT. simpl in H7.
    monadInv_sym H7. unfold gensym in EQ. inv EQ.    
    monadInv_comb EQ0.
    destruct g. simpl in H9. inv H9. eapply list_cons_neq in H8.
    contradiction.
    unfold transl_Sbox in H11.
    destruct (complete_type ce (typeof e)) eqn: COMPLETE; try congruence.
    monadInv H11.
    destruct andb eqn: ANDB in EQ0;try congruence.
    eapply andb_true_iff in ANDB. destruct ANDB as (SZGT & SZLT).
    eapply Z.leb_le in SZGT. eapply Z.leb_le in SZLT.
    inv EQ0.
    (* find_symbol malloc = Some b *)
    destruct (match_prog_malloc _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MALLOC).    
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in MALLOC as (mb & FINDSYMB & FINDMALLOC). clear A.    
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* find_funct tge tb = Some malloc_decl *)
    assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some malloc_decl).
    { edestruct find_funct_match as (malloc & TFINDFUN & TRMALLOC).
      eauto. 
      eapply inj_stbls_match. eauto.
      instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
      destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff. eauto.
      econstructor. eauto. eauto.
      erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
      inv TRMALLOC. eauto. intuition. }
    (* mem alloc in target *)
    exploit Mem.alloc_parallel_inject. eapply MINJ.
    eauto. eapply Z.le_refl. eapply Z.le_refl. 
    intros (j2 & tm2 & tb & TALLOC & INJ2 & INCR2 & A & B).
    cut (match_env j2 le te).
    2: { eapply match_env_incr;eauto. }
    intros MENV2.
    (* store in malloc *)
    exploit Mem.store_mapped_inject. eapply INJ2. eauto.
    eapply A. instantiate (1:= (Vptrofs (Ptrofs.repr (sizeof ge (typeof e))))).
    econstructor. rewrite Z.add_0_r.
    intros (tm3 & STORE & INJ3).
    (* evaluate the expression which is stored in the malloc pointer *)
    exploit eval_expr_inject. eauto. eauto.
    eapply match_env_incr. eapply match_env_incr.
    eauto. eauto. eauto. eauto.
    instantiate (1:= (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tv & EXPR & VINJ). 
    (* sem_cast *)
    exploit sem_cast_to_ctype_inject. eauto. eauto. instantiate (1 := tm3).
    intros (tv1 & CAST1 & INJCAST).
    (* assign_loc for *temp *)
    exploit assign_loc_inject. eapply H4. instantiate (3 := j2).
    econstructor;eauto. eauto. eauto.
    rewrite Ptrofs.add_zero_l.
    intros (tm4 & ASSIGNLOC1 & INJ4 & INCR3).
    cut (match_env j2 le te).
    2: { eapply match_env_incr;eauto. }
    intros MENV3.
    (* eval_lvalue lhs *)
    exploit eval_place_inject. eauto. eauto.
    eauto. eauto.
    instantiate (1 := (set_opttemp (Some temp) (Vptr tb Ptrofs.zero) le0)).
    intros (tpb & tpofs & ELHS & VINJ3).
    (* assign_loc for lhs *)
    exploit assign_loc_inject. eapply H6. instantiate (3 := j2).
    eauto. 
    econstructor. inv INCR3. eapply H12. eauto. eauto.
    eauto. rewrite Ptrofs.add_zero_l.
    intros (tm5 & ASSIGNLOC2 & INJ5 & INCR4).
    cut (match_env j2 le te).
    2: { eapply match_env_incr;eauto. }
    intros MENV4.
    
    eexists. split.
    + econstructor. econstructor. eapply star_step.
      econstructor. eapply star_left.
      (* step_call to malloc *)
      { eapply Clight.step_call.
        * simpl. eauto.
        * eapply eval_Elvalue. eapply eval_Evar_global.
          (* We have to ensure that e!malloc_id = None *)
          eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. eauto.
          eauto.
          simpl. eapply Clight.deref_loc_reference. auto.
        * repeat econstructor.
        * eauto.          
        * auto. }
      eapply star_step.
      (* evaluate malloc *)
      { eapply Clight.step_external_function.
        eauto.
        econstructor. erewrite Ptrofs.unsigned_repr; try lia.
        (* alloc *)
        instantiate (1 := tb).
        erewrite <- TALLOC. f_equal. 
        erewrite <- sizeof_match. f_equal.
        symmetry.
        eapply expr_to_cexpr_type;eauto.
        eapply TRANSL. auto.
        (* store sz *)        
        erewrite <- STORE. repeat f_equal.
        erewrite <- sizeof_match. f_equal.
        symmetry.
        eapply expr_to_cexpr_type;eauto.
        eapply TRANSL. auto. }
      eapply star_step.
      (* returnstate to regular state *)
      eapply Clight.step_returnstate.
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_step.
      (* assign to the malloc pointer *)
      { eapply Clight.step_assign.
        eapply eval_Ederef. eapply eval_Etempvar.
        simpl. eapply PTree.gss.
        eauto.
        (* sem_cast in C side *)
        erewrite <- CAST1. rewrite H. f_equal. symmetry.
        eapply expr_to_cexpr_type;eauto.
        rewrite H. eauto. }
      eapply star_step.
      eapply Clight.step_skip_seq.
      eapply star_one.
      (* assign temp to p *)
      { eapply Clight.step_assign.
        eauto.
        econstructor. eapply PTree.gss.
        instantiate (1 := (Vptr tb Ptrofs.zero)).
        erewrite <- (place_to_cexpr_type p lhs). rewrite H. simpl.
        eapply cast_val_casted. econstructor.
        eauto.
        erewrite <- (place_to_cexpr_type p lhs). eauto.
        auto. }
      1-8: eauto.
    (* match_states *)
    + econstructor. 1-3 : eauto.      
      econstructor. simpl. instantiate (1 := initial_generator). eauto.
      instantiate (1 := j2).
      (* inject_incr and match_cont *)
      assert (inject_incr j j2).
      { inv INCR3. inv INCR4. eapply inject_incr_trans. eauto.
        eapply inject_incr_trans. eauto. auto. }
      { eapply match_cont_inj_incr; auto. }
      apply INJ5.
      exploit Mem.support_alloc. eapply H0. intros SUPM2.
      exploit Mem.support_alloc. eapply TALLOC. intros SUPTM2.      
      etransitivity. eauto.
      etransitivity. instantiate (1 := injw j2 (Mem.support m2) (Mem.support tm2)).
      eapply injp_acc_inj_incr.
      instantiate (1 := INJ2). instantiate (1 := MINJ).
      eapply injp_acc_alloc;eauto.
      exploit Mem.support_store. eapply H1.
      exploit Mem.support_store. eapply STORE. intros S1 S2.
      rewrite <- S1. rewrite <- S2.
      etransitivity. eauto. eauto.
      apply MENV4.
      
  (* step_drop_box *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2. inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* find_symbol free = Some b *)
    destruct (match_prog_free _ _ TRANSL) as (orgs & rels & tyl & rety & cc & MFREE).    
    exploit Genv.find_def_symbol. eauto. intros A.
    eapply A in MFREE as (mb & FINDSYMB & FINDFREE). clear A.
    edestruct @Genv.find_symbol_match as (tmb & Htb & TFINDSYMB).
    eapply inj_stbls_match. eauto. eauto.
    (* find_funct tge tb = Some free_decl *)
    assert (TFINDFUN: Genv.find_funct tge (Vptr tmb Ptrofs.zero) = Some free_decl).
    { edestruct find_funct_match as (free & TFINDFUN & TRFREE).
      eauto. 
      eapply inj_stbls_match. eauto.
      instantiate (2 := (Vptr mb Ptrofs.zero)). simpl.
      destruct Ptrofs.eq_dec; try congruence.
      eapply Genv.find_funct_ptr_iff. eauto.
      econstructor. eauto. eauto.
      erewrite Ptrofs.add_zero_l in TFINDFUN. unfold tge.
      inv TRFREE. eauto. intuition. }
    (* deref_loc inject *)
    exploit deref_loc_inject;eauto. intros (tv' & TDEREF & VINJ2).    
    (* extcall_free_sem inject *)
    exploit extcall_free_injp; eauto.
    instantiate (1:= MINJ). instantiate (1 := tge).
    intros (tm' & MINJ1 & TFREE & INJP).
    eapply injp_acc_inj_incr in INJP as INCR1.
    
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* step to call drop *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* We have to ensure that e!free_id = None *)
        eapply wf_env_target_none; eauto.
        inv MFUN; try congruence.
        eauto. simpl. eauto.
        eauto.
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. econstructor. econstructor.                   
        eapply PTree.gss. simpl.
        (* deref_loc inject *)
        eauto. 
        (* sem_cast *)
        simpl. instantiate (1:= tv'). inv VINJ2.
        unfold Cop.sem_cast. simpl. auto.
        (* eval_exprlist *)
        econstructor.
        eauto. simpl.
        auto. }
      (* step to external call *)
      eapply star_step.
      { eapply Clight.step_external_function. eauto.
        eauto. }
      eapply star_one.
      econstructor.
      1-5: eauto.
      
    (* match_states  *)
    + econstructor; eauto.
      econstructor. instantiate (1 := initial_generator). eauto.
      etransitivity. eauto. eauto.

  (* step_drop_struct *)
  - inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2.
    destruct (own_type ce (Tstruct orgs id)) eqn: OWNTY; try congruence.
    destruct (dropm!id) as [glue_id|]eqn: DROPM; try congruence.
    inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound; eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).    
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eauto. eauto. rewrite COSTRUCT. simpl.
    intros DGLUE. inv DGLUE.
        
    (* alloc stack block in function entry *)
    set (pty := Tpointer (Ctypes.Tstruct id noattr) noattr) in *.
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr pb pofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).
    
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. right. right.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, glue_id). split;auto.
          eapply PTree.elements_correct. auto. }
        eauto.        
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. 
        eapply PTree.gss. simpl.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl.
      eapply star_one.
      econstructor.
      1-5: eauto.

    (* match_states *)
    + eapply match_dropstate_struct with (bs := nil);eauto.
      econstructor.
      econstructor; eauto.
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr pb pofs)). eauto. eauto.
      intros. inv H.
      
  (* step_drop_enum *)
  - (** The following code is mostly the same as that in step_drop_struct *)
    inv MSTMT. simpl in H.
    monadInv_sym H. unfold gensym in EQ. inv EQ.
    monadInv_comb EQ0. destruct expand_drop in EQ1;[|inv EQ1].
    inv EQ1. destruct g. simpl in H1. inv H1. apply list_cons_neq in H0.
    contradiction.
    unfold expand_drop in H2. rewrite PTY in H2.
    destruct (own_type ce (Tvariant orgs id)) eqn: OWNTY; try congruence.
    destruct (dropm!id) as [glue_id|]eqn: DROPM; try congruence.
    inv H2.
    (* eval_place inject *)
    exploit eval_place_inject; eauto. instantiate (1 := le0).
    intros (pb & pofs & EVALPE & VINJ1).
    (* use find_dropm_sound to get the drop glue *)
    exploit find_dropm_sound; eauto.
    intros (tmb & tf0 & TFINDSYMB & TFINDFUNC & GETGLUE).
    exploit (generate_drops_inv). eapply match_prog_comp_env. eauto.
    eauto. eauto. rewrite COENUM.
    simpl. intros (union_id & tag_fid & union_fid & tco & uco & DGLUE & TCO & TUCO & TAGOFS & UFOFS).
    inv DGLUE.
    
    (* alloc stack block in function entry *)
    set (pty := Tpointer (Ctypes.Tstruct id noattr) noattr) in *.
    exploit drop_glue_function_entry_step; eauto.
    instantiate (1:= Mptr). instantiate (1 := Vptr pb pofs).
    intros (psb & tm1 & tm2 & ALLOC & STORETM1 & PERMFREE2 & OUTREACH1 & MINJ2).

    (* evaluate switch *)
    exploit select_switch_sem_match; eauto.
    instantiate (1 := (Efield  (Ederef (Evar param_id pty) (Ctypes.Tstruct id noattr)) union_fid (Tunion union_id noattr))).
    instantiate (1 := (generate_dropm prog)).
    instantiate (1 := (prog_comp_env prog)).
    intros (unused_ts & SEL). 
        
    eexists. split.
    (* step *)
    + econstructor.
      econstructor.
      (* set *)
      eapply star_step. econstructor.
      econstructor. eauto.
      eapply star_step. econstructor.
      eapply star_step.
      (* to callstate *)
      { econstructor. simpl. eauto.
        econstructor. eapply eval_Evar_global.
        (* prove te!glue_id = None *)
        { eapply wf_env_target_none; eauto.
          inv MFUN; try congruence.
          eauto. simpl. right. right.
          (* prove glue_id in dropm's codomain *)
          eapply in_map_iff. exists (id, glue_id). split;auto.
          eapply PTree.elements_correct. auto. }
        eauto.
        simpl. eapply Clight.deref_loc_reference. auto.
        econstructor. econstructor. 
        eapply PTree.gss. simpl.
        (* sem_cast *)
        eapply cast_val_casted. econstructor.
        econstructor.
        eauto.
        (* type of drop glue *)
        auto. }
      eapply star_step. econstructor.
      (* call internal function *)
      eauto. econstructor;simpl.
      econstructor. intuition. econstructor.
      econstructor. eauto. econstructor.
      econstructor. eapply PTree.gss.
      econstructor. unfold pty. simpl. eauto.
      eauto. econstructor.
      reflexivity.
      simpl. eapply star_step.
      (** Start to evaluate the swtich statement *)
      { econstructor.
        (* evaluate switch tag *)
        { instantiate (1 := Vint tag).
          econstructor. econstructor. econstructor.
          econstructor. econstructor. econstructor.
          eapply PTree.gss. eapply Clight.deref_loc_value.
          unfold pty. simpl. eauto.
          instantiate (1 := pofs). instantiate (1 := pb).
          simpl. erewrite Mem.load_store_same with (v:= Vptr pb pofs).
          auto. eauto.
          simpl. eapply Clight.deref_loc_copy. auto.
          simpl. eauto. simpl. eauto.
          eauto. rewrite Ptrofs.add_zero.
          simpl. eapply Clight.deref_loc_value.
          simpl. eauto.
          inv VINJ1.
          exploit Mem.loadv_inject. eapply MINJ2. eauto. eauto.
          intros (v2 & TLOAD & VINJ2). inv VINJ2.
          auto. }
        simpl. unfold Ctypes.type_int32s, sem_switch_arg. simpl. eauto. }
      eapply star_step.
      (* evaluate switch *)
      rewrite SEL.
      econstructor. eapply star_step.
      econstructor. eapply star_refl.
      1-8 : eauto.

    + eapply match_dropstate_enum with (bs := nil); eauto.
      econstructor; eauto.
      unfold pty.
      set (param := (Ederef (Evar param_id (Tpointer (Ctypes.Tstruct id noattr) noattr))
                       (Ctypes.Tstruct id noattr))).
      (** FIXME (adhoc): prove match_dropmemb_stmt *)
      assert (ENUMCON: enum_consistent id fid union_id union_fid).
        { unfold enum_consistent. simpl in SCO. unfold ce. rewrite SCO.
          intros. inv H. exists tco, uco.
          split. unfold tce. auto. split. unfold tce. auto.
          auto. intros. eapply UFOFS. eauto. }
     eapply match_dropmemb_stmt_enum_member; eauto.
      (* prove inj_incr *)
      exploit Mem.support_store. eapply STORETM1.
      intros SUP. rewrite SUP.
      inv INCR. econstructor. auto. auto.
      auto. erewrite Mem.support_alloc. eapply Mem.sup_include_trans.
      eauto. eapply Mem.sup_include_incr.
      eauto.
      (* prove loadv in match_cont *)
      simpl. erewrite Mem.load_store_same.
      instantiate (1 := (Vptr pb pofs)). eauto. eauto.
      intros. inv H.
            
  (* step_dropstate (in struct) *)
  - eapply step_drop_simulation. eauto.
    eapply match_dropstate_struct; eauto.
  (* step_dropstate (in enum) *)
  - eapply step_drop_simulation. eauto.
    eapply match_dropstate_enum; eauto.

  (* step_storagelive *)
  - admit.
  (* step_storagedead *)
  - admit.

  (* step_call *)
  - inv MSTMT. simpl in H4.
    monadInv_comb H4. monadInv_sym EQ3. unfold gensym in EQ2. inv EQ2.
    destruct g. simpl in H6. inv H6. eapply list_cons_neq in H5.
    contradiction.
    admit.

  (* step_internal_function *)
  - (* how to prove tr_function f tf because we should guarantee that
    f is not a drop glue *)
    assert (MSTBL: Genv.match_stbls j se tse). {   
      destruct w. inv GE. simpl in *. inv INCR. 
      eapply Genv.match_stbls_incr; eauto. 
      (* disjoint *)
      intros. exploit H7; eauto. intros (A & B). split; eauto. }
    
    edestruct find_funct_match as (tfd & FINDT & TF); eauto.
    inv TF. inv H1;try congruence.

    (* function entry inject *)
    exploit function_entry_inject; eauto. 
    intros (j' & te & tm' & TENTRY & MENV1 & MINJ1 & INCR1).
    exists (Clight.State tf tf.(Clight.fn_body) tk te (create_undef_temps (fn_temps tf)) tm').
    (* step and match states *)
    split.
    + eapply plus_one. econstructor;eauto.
    + econstructor.
      (* initial env is well_formed *)
      eapply function_entry_wf_env. eauto. eauto.
      eapply tr_function_normal;eauto.
      eauto.
      instantiate (1 := j').
      (* inject_incr and match_cont *)
      { eapply match_cont_inj_incr. auto. inv INCR1. auto. }
      eauto.
      etransitivity;eauto. auto.
      
  (* step_external_function *)
  - admit.

  (* step_return_0 *)
  - admit.
  (* step_return_1 *)
  - admit.
  (* step_skip_call *)
  - admit.
  (* step_returnstate *)
  - admit.
  (* step_seq *)
  - admit.
  (* step_skip_seq *)
  - admit.
  (* step_continue_seq *)
  - admit.
  (* step_break_seq *)
  - admit.
  (* step_ifthenelse *)
  - admit.
  (* step_loop *)
  - admit.
  (* step_skip_or_continue_loop *)
  - admit.
  (* step_break_loop *)
  - admit.
        
Admitted.

    
Lemma final_states_simulation:
  forall S R r1, match_states S R -> final_state S r1 ->
  exists r2, Clight.final_state R r2 /\ match_reply (cc_c inj) w r1 r2.
Proof.
  intros. inv H0. inv H.
  generalize (MCONT m tm nil). intros MCONT1.
  inv MCONT1.
  eexists. split. econstructor; split; eauto.
  simpl.
  econstructor. split.
  eauto. econstructor. eauto.
  constructor; eauto.
Qed.


Lemma external_states_simulation:
  forall S R q1, match_states S R -> at_external ge S q1 ->
  exists wx q2, Clight.at_external tge R q2 /\ cc_c_query inj wx q1 q2 /\ match_stbls inj wx se tse /\
  forall r1 r2 S', match_reply (cc_c inj) wx r1 r2 -> after_external S r1 S' ->
  exists R', Clight.after_external R r2 R' /\ match_states S' R'.
Proof.
  intros S R q1 HSR Hq1.
  destruct Hq1; inv HSR.
  exploit (match_stbls_acc inj). eauto. eauto. intros GE1.
  (* target find external function *)  
  simpl in H. exploit find_funct_match; eauto.
  inv GE1. simpl in *. eauto.
  intros (tf & TFINDF & TRFUN). inv TRFUN. 
  (* vf <> Vundef *)
  assert (Hvf: vf <> Vundef) by (destruct vf; try discriminate).
  eexists (injw j (Mem.support m) (Mem.support tm)), _. intuition idtac.
  - econstructor; eauto.
  - econstructor; eauto. constructor. auto.
  - inv H3. destruct H2 as (wx' & ACC & REP). inv ACC. inv REP. inv H10. eexists. split.
    + econstructor; eauto.
    + econstructor. instantiate (1 := f').
      eapply match_cont_inj_incr; eauto.
      auto. etransitivity; eauto.
      auto.
Qed.

End PRESERVATION.

Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  forward_simulation (cc_c inj) (cc_c inj) (RustIRsem.semantics prog) (Clight.semantics1 tprog).
Proof.
  fsim eapply forward_simulation_plus. 
  - inv MATCH. auto.
  - intros. destruct Hse, H. simpl.
    eapply is_internal_match. eapply MATCH.
    eauto.
    (* tr_fundef relates internal function to internal function *)
    intros. inv H3;auto.
    auto. auto.
  (* initial state *)
  - eapply initial_states_simulation; eauto. 
  (* final state *)
  - eapply final_states_simulation; eauto.
  (* external state *)
  - eapply external_states_simulation; eauto.
  (* step *)
  - eapply step_simulation;eauto.
Qed.
