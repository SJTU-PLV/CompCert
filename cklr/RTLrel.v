Require Import Coqlib Mapsrel.
Require Import AST Integers Valuesrel Eventsrel CKLR LanguageInterface Smallstep.
Require Import Op Registersrel.
Require Export RTL.

Notation regset_inject f := (RegmapRel.r (Val.inject f)).

Global Instance init_regs_inject f:
  Monotonic (@init_regs) (Val.inject_list f ++> - ==> regset_inject f).
Proof.
  intros vl1 vl2 Hvl rl. revert vl1 vl2 Hvl.
  induction rl; simpl; intros.
  - rauto.
  - repeat rstep. eauto.
Qed.

(** RTL relies on hardcoded offsets for stack blocks, so we need to
  make sure that the stack pointer can only inject with a zero delta.
  To this end we introduce the following restricted injection relation
  on values. *)

Inductive sp_inject f: relation val :=
  | sp_inject_ptr:
      Monotonic (@Vptr) (block_inject_sameofs f ++> - ==> sp_inject f).

Global Existing Instance sp_inject_ptr | 5.

Global Instance sp_inject_incr:
  Monotonic (@sp_inject) (inject_incr ++> subrel).
Proof.
  intros f g Hfg x y Hxy.
  destruct Hxy; constructor; eauto.
Qed.

Global Instance sp_val_inject_subrel:
  Related (@sp_inject) (@Val.inject) (inject_incr ++> subrel).
Proof.
  intros f g Hfg x y Hxy.
  destruct Hxy; econstructor; eauto.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Inductive stackframe_inject f: relation stackframe :=
  Stackframe_inject:
    Monotonic
      (@Stackframe)
      (-==> -==> sp_inject f ++> -==> regset_inject f ++> stackframe_inject f).

Global Existing Instance Stackframe_inject.

Global Instance stackframe_inject_incr:
  Monotonic (@stackframe_inject) (inject_incr ++> subrel).
Proof.
  intros f1 f2 Hf sf1 sf2 Hsf.
  destruct Hsf. rauto.
Qed.

Inductive state_rel R w: relation state :=
  | State_rel:
      Monotonic
        (@State)
        (list_rel (stackframe_inject (mi R w)) ++>
         - ==> sp_inject (mi R w) ++> - ==> regset_inject (mi R w) ++>
         match_mem R w ++> state_rel R w)
  | Callstate_rel:
      Monotonic
        (@Callstate)
        (list_rel (stackframe_inject (mi R w)) ++>
         Val.inject (mi R w) ==> Val.inject_list (mi R w) ++>
         match_mem R w ++> - ==> state_rel R w)
  | Returnstate_rel:
      Monotonic
        (@Returnstate)
        (list_rel (stackframe_inject (mi R w)) ++>
         Val.inject (mi R w) ++>
         match_mem R w ++> state_rel R w).

Global Existing Instance State_rel.
Global Existing Instance Callstate_rel.
Global Existing Instance Returnstate_rel.

Global Instance eval_addressing32_rel R w:
  Monotonic
    (@eval_addressing32)
    (Genv.match_stbls (mi R w) ++>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing32. rauto.
Qed.

Global Instance eval_addressing64_rel R w:
  Monotonic
    (@eval_addressing64)
    (Genv.match_stbls (mi R w) ++>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing64. rauto.
Qed.

Global Instance eval_addressing_rel R w:
  Monotonic
    (@eval_addressing)
    (Genv.match_stbls (mi R w) ++>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++>
     option_le (Val.inject (mi R w))).
Proof.
  unfold eval_addressing. rauto.
Qed.

Global Instance eval_condition_rel R w:
  Monotonic
    (@eval_condition)
    (- ==> Val.inject_list (mi R w) ++> match_mem R w ++> option_le eq).
Proof.
  unfold eval_condition.
  repeat rstep; congruence.
Qed.

Global Instance maxf_rel f:
  Monotonic (@maxf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold maxf.
  rauto.
Qed.

Global Instance minf_rel f:
  Monotonic (@minf) (Val.inject f ++> Val.inject f ++> Val.inject f).
Proof.
  unfold minf.
  rauto.
Qed.

Global Instance eval_operation_rel R w:
  Monotonic
    (@eval_operation)
    (Genv.match_stbls (mi R w) ++>
     Val.inject (mi R w) ++> - ==>
     Val.inject_list (mi R w) ++> match_mem R w ++>
     option_le (Val.inject (mi R w))).
Proof.
  intros ge1 ge2 Hge sp1 sp2 Hsp op vl1 vl2 Hvl m1 m2 Hm.
  unfold eval_operation. destruct op; try rauto.
Qed.

Global Instance map_inject_list {A} R f:
  Monotonic (@map A val) ((R ++> Val.inject f) ++> list_rel R ++> Val.inject_list f).
Proof.
  intros f1 f2 Hf x y Hxy.
  induction Hxy; simpl; constructor; rauto.
Qed.

Global Instance map_inject_list_params:
  Params (@map) 2 := {}.


(** The [option] equivalent of [R ++> impl]. *)

Definition option_impl {A B} (R: rel A B) x y :=
  forall a b, R a b -> x = Some a -> y = Some b.

Global Instance option_impl_subrel A B:
  Monotonic (@option_impl A B) (subrel --> subrel).
Proof.
  firstorder.
Qed.

Global Instance option_impl_subrel_params:
  Params (@option_impl) 3 := {}.

Global Instance option_impl_bot {A B} (R: rel A B) y:
  Related None y (option_impl R).
Proof.
  discriminate.
Qed.

Global Instance option_impl_transport {A B} (R: rel A B) x y a b:
  Transport (option_impl R * R) (x, a) (y, b) (x = Some a) (y = Some b) | 5.
Proof.
  firstorder.
Qed.

Global Instance ros_address_inject f:
  Monotonic
    (@ros_address)
    (Genv.match_stbls f ++> - ==> regset_inject f ++> Val.inject f).
Proof.
  unfold ros_address. rauto.
Qed.

Section PROG.

Context (p: program).

Definition genv_match R w : relation genv :=
  (match_stbls R w) !! (fun se => Genv.globalenv se p).

Lemma match_prog {C} `{!Linking.Linker C} (c: C):
  Linking.match_program_gen (fun _ => eq) eq c p p.
Proof.
  repeat apply conj; auto.
  induction (prog_defs p) as [ | [id [f|v]] defs IHdefs];
  repeat (econstructor; eauto).
  - apply Linking.linkorder_refl.
  - destruct v; constructor; auto.
Qed.

Global Instance find_funct_inject R w ge1 v1 ge2 v2 f:
  Transport (genv_match R w * Val.inject (mi R w)) (ge1, v1) (ge2, v2)
    (Genv.find_funct ge1 v1 = Some f)
    (Genv.find_funct ge2 v2 = Some f).
Proof.
  intros [Hge Hv] Hf. cbn in *.
  destruct Hge. apply match_stbls_proj in H. cbn in Hf.
  edestruct @Genv.find_funct_match as (?&?&?&?&?); eauto using (match_prog tt).
  cbn in *. congruence.
Qed.

(*
Lemma block_inject_glob R w m1 m2 id b2:
  match_mem R w m1 m2 ->
  block_inject (mi R w) (Block.glob id) b2 ->
  b2 = Block.glob id.
Proof.
  intros Hm [delta Hb].
  apply cklr_wf in Hm as [INCR _].
  specialize (INCR (Block.glob id)). unfold Mem.flat_inj in INCR.
  destruct Block.lt_dec.
  - specialize (INCR _ _ eq_refl). congruence.
  - elim n. apply Block.lt_glob_init.
Qed.
 *)

Global Instance step_rel R:
  Monotonic
    (@step)
    (|= - ==> genv_match R ++> state_rel R ++> - ==>
     k1 set_le (<> state_rel R)).
Proof.
  intros w fsr ge tge Hge s1 s2 Hs t s1' H1.
  assert (Hse: match_stbls R w ge tge) by (destruct Hge; eauto).
  assert (Hse': Genv.match_stbls (mi R w) ge tge) by (apply match_stbls_proj; eauto).
  deconstruct H1 ltac:(fun x => pose (c := x)); inv Hs.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps. eexists. split; [ eapply c; eauto; fail | ].
    exists w'. split; rauto.
  - subst vf.
    transport_hyps. eexists; split.
    eapply c; eauto. red in r. red. destruct ros; eauto.
    admit. (* f Global *)
    eexists. split. reflexivity. admit.
  - subst vf. inv H8.
    transport_hyps; eexists; split. eapply c; eauto. admit. admit.
    exists w'; split; [rauto | ].
    repeat rstep. eapply match_stbls_proj. rauto.
  - transport_hyps; eexists; split. eapply c; eauto.
    admit. (*push_stage*)
    admit.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | rauto ].
  - transport_hyps; eexists; split; [ eapply c; eauto | rauto ].
    + specialize (H9 arg). destruct H9; congruence.
  - inv H8.
    transport_hyps; eexists; split. eapply c; eauto. admit.
    exists w'; split; rauto.
  - edestruct cklr_alloc as (w' & Hw' & Halloc); eauto.
    transport e. clear Halloc. transport FIND.
    (* todo: transport e0. *)
    eexists; split. eapply c; eauto. admit.
    exists w'; split. rauto.
    repeat rstep.
    clear - H8 Hw'.
    induction H8; constructor; rauto. admit.
  - transport_hyps; eexists; split; [ eapply c; eauto; fail | ].
    exists w'; split; rauto.
  - inv H3. inv H2.
    transport_hyps; eexists; split.
    eapply c; eauto. admit. (*pop_stage*)
    admit.
Admitted.

(*
Lemma block_inject_glob R w m1 m2 id b2:
  match_mem R w m1 m2 ->
  block_inject (mi R w) (Block.glob id) b2 ->
  b2 = Block.glob id.
Proof.
  intros Hm [delta Hb].
  apply cklr_wf in Hm as [INCR _].
  specialize (INCR (Block.glob id)). unfold Mem.flat_inj in INCR.
  destruct Block.lt_dec.
  - specialize (INCR _ _ eq_refl). congruence.
  - elim n. apply Block.lt_glob_init.
Qed.
*)

End PROG.

Hint Extern 1 (Transport _ _ _ _ _) =>
  set_le_transport @step : typeclass_instances.

Global Instance semantics_rel fsr R:
  Monotonic (@RTL.semantics fsr) (- ==> forward_simulation (cc_c R) (cc_c R)).
Proof.
  intros p. constructor. econstructor; auto.
  intros se1 se2 w Hse1 Hse. cbn -[semantics] in *.
  eapply forward_simulation_step with (match_states := klr_diam tt (state_rel R) w).
  - cbn. intros q1 q2 Hq. eapply (Genv.is_internal_match (ctx := p)).
    + eapply (match_prog p).
    + eapply match_stbls_proj; eauto.
    + cbn. congruence.
    + destruct Hq. cbn. auto.
    + destruct Hq. cbn. auto.
  - intros q1 q2 s1 Hq. destruct 1. inv Hq. cbn.
    eassert (Hge: genv_match p R w _ _) by (red; rauto).
    transport H.
    eexists; split.
    + econstructor; eauto. admit.
    + eexists. split. reflexivity.  econstructor; eauto. constructor.
      admit. (*push_stage*)
  - intros s1 s2 r1 (w' & Hw' & Hs) Hr1. inv Hr1. inv Hs. inv H3.
    (*cklr_pop_stage*)
    admit.
   (* eexists. simpl. split.
    + constructor. admit.
    + exists w'. split; [rauto | ]. constructor; auto. eauto. *)
  - intros s1 s2 qx1 (w' & Hw' & Hs) Hqx1.
    eassert (Hge: genv_match p R w' _ _) by (red; rauto).
    destruct Hqx1. inv Hs.
    (* assert (vf <> Vundef) by (destruct vf; discriminate). *)
    transport H.
    eexists w', (LanguageInterface.cq _ _ y1 _). split.
    + econstructor; simpl; eauto. admit.
    + split.
      * econstructor; auto. congruence.
      * split. cbn; rauto.
        intros r1 [vres2 m2'] s1' (w'' & Hw'' & Hr) HAE. inv HAE. inv Hr.
        eexists. split.
        -- constructor. admit.
        -- exists w''. split; rauto.
  - intros s1 t s1' Hstep1 s2 (w' & Hw' & Hs).
    eassert (Hge: genv_match p R w' _ _) by (red; rauto).
    simpl in Hstep1.
    transport Hstep1.
    eexists. split; eauto. rauto.
  - auto using well_founded_ltof.
Admitted.
