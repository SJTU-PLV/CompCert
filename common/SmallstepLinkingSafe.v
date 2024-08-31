Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

(** Module safety : similar to the preservation of invariant in LTS *)

Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').

(* Definition partial_safe {liA liB st} mem_error (L: lts liA liB st) (s: st) : Prop := *)
(*   (exists r, final_state L s r) *)
(*   \/ (exists q, at_external L s q) *)
(*   \/ (exists t, exists s', Step L s t s') *)
(*   \/ (mem_error liA liB st L s). *)


(** TODO: generalize safe/partial_safe to module linking and show that
the original safe/partial_safe is identical to the composed
safe/partial_safe *)

Record lts_safe {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: _ -> S -> Prop) wI :=
  {
    step_safe s t s' (REACH: reachable L s):
      (* SI L s -> *)
      Step L s t s' ->
      SI L s';
    initial_safe q:
      valid_query L q = true ->
      query_inv IB wI q ->
      (* initial_progress *)
      (exists s, initial_state L q s)
      (* initial_safe *)
      /\ (forall s, initial_state L q s -> SI L s);
    external_safe s q (REACH: reachable L s):
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s')
                   (* after external safe *)
                   /\ (forall s', after_external L s r s' -> SI L s');
    final_safe s r (REACH: reachable L s):
      final_state L s r ->
      reply_inv IB wI r;
  }.


(* se as an oracle, is it correct? *)
Definition module_safe {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI se :=
  forall w,
    Genv.valid_for (skel L) se ->
    symtbl_inv IB w se ->
    lts_safe se (L se) IA IB SI w.


Lemma safe_internal {li} (I: invariant li) L1 L2: forall i sk se s k w,
    let L := fun (i:bool) => if i then L1 else L2 in
    forall (Hsk: link (skel L1) (skel L2) = Some sk)
      (VALID: Genv.valid_for (skel (SmallstepLinking.semantics L sk)) se)
      (INV : symtbl_inv I w se)
      (VALIDSE: forall i, Genv.valid_for (skel (L i)) se)
      (SAFE: forall i, module_safe (L i) I I safe se)
      (STSAFE: safe (L i se) s)
      (WFSTATE: wf_state L se (st L i s :: k)),
      safe (SmallstepLinking.semantics L sk se) (st L i s :: k).
Proof.
  intros.
  destruct STSAFE as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
  * destruct k.
    -- left. exists r.
       econstructor. auto.
    -- destruct f.
       right. right.
       (* s0 in in at_external state *)
       inv WFSTATE. subst_dep. inv H3. inv H2. subst_dep.
       generalize (external_safe _ _ _ _ _ _ (SAFE i0 _ (VALIDSE i0) INV) s0 q H5 H3).
       intros (wA & SYMBINV & QINV & AFTER).
       generalize (final_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) SYMBINV) _ _ H1 FINAL).
       intros WR.
       generalize (AFTER _ WR).
       intros ((s0' & AFTER1) & SAFTER).
       do 2 eexists.
       eapply step_pop; eauto.
  * inv WFSTATE. subst_dep.
    generalize (external_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) INV) s q H1 EXT).
    intros (wA & SYMBINV & QINV & AFTER).
    destruct (valid_query (L i se) q) eqn: VQ1.
    -- right. right.
       generalize (initial_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) SYMBINV) _ VQ1 QINV).
       intros ((initS & INIT) & INITSAFE).
       do 2 eexists.
       eapply step_push; eauto.
    -- destruct i; simpl in *.
       ++ destruct (valid_query (L2 se) q) eqn: VQ2.
          ** right. right.
             generalize (initial_safe _ _ _ _ _ _ (SAFE false _ (VALIDSE false) SYMBINV) _ VQ2 QINV).
             intros ((initS & INIT) & INITSAFE).
             do 2 eexists.
             eapply step_push. eauto.
             instantiate (1 := false). auto.
             simpl. eauto.
          ** right. left.
             eexists. econstructor.
             simpl. eauto.
             intros. destruct j; simpl; auto.
       ++  destruct (valid_query (L1 se) q) eqn: VQ2.
           ** right. right.
              generalize (initial_safe _ _ _ _ _ _ (SAFE true _ (VALIDSE true) SYMBINV) _ VQ2 QINV).
              intros ((initS & INIT) & INITSAFE).
              do 2 eexists.
              eapply step_push. eauto.
              instantiate (1 := true). auto.
              simpl. eauto.
           ** right. left.
              eexists. econstructor.
              simpl. eauto.
              intros. destruct j; simpl; auto.
  * right. right. do 2 eexists.
    eapply step_internal. simpl. eauto.
Qed.


Lemma compose_safety {li} (I: invariant li) L1 L2 L se:
  module_safe L1 I I safe se ->
  module_safe L2 I I safe se ->
  compose L1 L2 = Some L ->
  module_safe L I I safe se.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  red. intros w VALID INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  destruct i.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (SAFE: forall i, module_safe (L i) I I safe se).
  destruct i; simpl; auto.
  constructor.
  - intros s t s' REACH STEP.
    eapply reachable_wf_state in REACH.
    inv STEP.
    + (* destruct i; simpl in H. *)
      assert (A: safe (L i se) s0). right. right. eauto.
      assert (B: safe (L i se) s'0). {
        eapply step_safe; eauto. eapply SAFE; eauto.
        inv REACH. subst_dep. auto. }
      eapply safe_internal; eauto.
      inv REACH. subst_dep. econstructor;eauto. eapply step_reachable; eauto.
    (* step_push *)
    + assert (A: safe (L i se) s0). right. left. eauto.
      assert (B: safe (L j se) s'0).
      { inv REACH. subst_dep.
        generalize (external_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) INV) s0 q H4 H).
        intros (wA & SYMBINV & QINV & AFTER).
        eapply initial_safe. eapply SAFE; eauto. eauto. auto. auto. }
      eapply safe_internal;eauto.
      constructor; eauto. econstructor; eauto.
      eapply star_refl.
      inv REACH. subst_dep. econstructor;eauto.
      econstructor;eauto.
    (* step_pop *)
    + inv REACH. inv H5. subst_dep.
      inv H6. subst_dep.
      assert (ATEXT: exists q, at_external (L j se) sk0 q).
      eauto.
      destruct ATEXT as (q1 & ATEXT).
      generalize (external_safe _ _ _ _ _ _ (SAFE j _ (VALIDSE j) INV) sk0 q1 H5 ATEXT).
      intros (wA & SYMBINV & QINV & AFTER).
      generalize (final_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) SYMBINV) _ _ H3 H).
      intros VR.
      generalize (AFTER r VR).
      intros ((s' & AFTER1) & C).
      assert (B: safe (L j se) s'0). eapply C. eauto.
      eapply safe_internal; eauto.
      econstructor;eauto. eapply external_reach. eapply H5. eapply H0.
      eapply star_refl.
  (* initial_safe *)
  - intros q VQ SQ. simpl in *.
    unfold SmallstepLinking.valid_query in VQ.
    simpl in *. split.
    + (* progress *)
      destruct (valid_query (L1 se) q) eqn: VQ1.
      * generalize (initial_safe _ _ _ _ _ _ (SAFE true _ (VALIDSE true) INV) _ VQ1 SQ).
        intros ((s & INIT) & INITSAFE).
        exists (st L true s :: nil). econstructor; eauto.
      * rewrite orb_false_l in VQ.
        generalize (initial_safe _ _ _ _ _ _ (SAFE false _ (VALIDSE false) INV) _ VQ SQ).
        intros ((s & INIT) & INITSAFE).
        exists (st L false s :: nil). econstructor; eauto.
    + (* safe *)
      intros s INIT.
      inv INIT.
      generalize (initial_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) INV) _ H SQ).
      intros ((s & INIT) & INITSAFE).
      (* repeated work *)
      clear INIT.
      eapply safe_internal; eauto.
      econstructor. eapply initial_reach; eauto.
      eapply star_refl. constructor.  
  - intros s q REACH EXT. inv EXT.
    eapply reachable_wf_state in REACH. inv REACH. subst_dep.
    generalize (external_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) INV) s0 q H3 H).
    intros (wA & SYMBINV & QINV & AFTER).
    exists wA. split; auto. split; auto.
    intros r SR.
    generalize (AFTER r SR).
    intros ((s' & AFTER1) & C).
    split. exists (st L i s' :: k). econstructor; eauto.
    intros s1' AFTER2. simpl in *. inv AFTER2. 
    subst_dep.
    generalize (C s'0 H8). intros D.
    (* repeated work *)
    eapply safe_internal; eauto.
    econstructor; eauto. eapply external_reach; eauto.
    eapply star_refl.    
  - intros s r REACH FINAL.
    inv FINAL.
    apply reachable_wf_state in REACH. inv REACH. subst_dep.
    generalize (final_safe _ _ _ _ _ _ (SAFE i _ (VALIDSE i) INV) _ _ H2 H).
    auto.
Qed.


(* Similar to ccref *)
Record bsim_invariant {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) : Type :=
  { inv_incoming:
    forall w2 se1 se2 ccw q2,
      symtbl_inv I2 w2 se2 ->
      match_senv cc ccw se1 se2 ->
      query_inv I2 w2 q2 ->
      exists w1 q1, symtbl_inv I1 w1 se1 /\
                 query_inv I1 w1 q1 /\
                 match_query cc ccw q1 q2 /\
                 forall r1,
                   reply_inv I1 w1 r1 ->
                   exists r2, reply_inv I2 w2 r2;

    inv_outgoing:
    forall w1 se1 se2 ccw q1,
      symtbl_inv I1 w1 se1 ->
      match_senv cc ccw se1 se2 ->
      query_inv I1 w1 q1 ->
      exists w2 q2, symtbl_inv I2 w2 se2 /\
                 query_inv I2 w2 q2 /\
                 match_query cc ccw q1 q2 /\
                 forall r2,
                   reply_inv I2 w2 r2 ->
                   exists r1, reply_inv I1 w1 r1;
   
    }.


(* Relation between two semantics invariants *)
(* Record bsim_invariant {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) : Type := *)
(*   { inv_match_world: ccworld cc -> inv_world I1 -> inv_world I2 -> Prop; *)

(*     (** TODO: how to get inv_match_world? *) *)
(*     inv_match_symtbl: forall w2 se1 se2 ccw, *)
(*       symtbl_inv I2 w2 se2 -> *)
(*       match_senv cc ccw se1 se2 -> *)
(*       exists w1, inv_match_world ccw w1 w2 *)
(*             /\ symtbl_inv I1 w1 se1; *)

(*     inv_match_query: forall w1 w2 q2 ccw, *)
(*       query_inv I2 w2 q2 -> *)
(*       inv_match_world ccw w1 w2 -> *)
(*       exists q1, match_query cc ccw q1 q2 *)
(*             /\ query_inv I1 w1 q1; *)

(*     inv_match_reply: forall w1 w2 r2 ccw, *)
(*       reply_inv I2 w2 r2 -> *)
(*       inv_match_world ccw w1 w2 -> *)
(*       exists r1, match_reply cc ccw r1 r2 *)
(*             /\ reply_inv I1 w1 r1 *)

(*   }. *)

(* Section LTS_SAFETY_PRESERVATION. *)

(* Context {li1 li2} (cc: callconv li1 li2). *)
(* Context {state1 state2: Type}. *)
(* Context (L1: lts li1 li1 state1) (L2: lts li2 li2 state2). *)
(* Context (I1: invariant li1) (I2: invariant li2). *)
(* Context (se1 se2: Genv.symtbl). *)
(* Context (ccw: ccworld cc) (w1: inv_world I1) (w2: inv_world I2). *)
(* Context {index: Type} (order: index -> index -> Prop). *)
(* Context (match_states: index -> state1 -> state2 -> Prop). *)

(* Hypothesis BSIM_INV: bsim_invariant cc I1 I2. *)
(* Hypothesis MATCHWORLD: inv_match_world cc I1 I2 BSIM_INV ccw w1 w2. *)

(* Lemma lts_safety_preservation: *)
(*   lts_safe se1 L1 I1 I1 safe w1 -> *)
(*   bsim_properties cc cc se1 se2 ccw L1 L2 index order match_states -> *)
(*   lts_safe se2 L2 I2 I2 safe w2. *)
(* Proof. *)
(*   intros SAFE1 BSIM. *)
(*   inv BSIM. inv SAFE1. *)
(*   econstructor. *)
(*   (* prove lts safety preservation *) *)
(*   econstructor. *)
(*   (* step_safe *) *)
(*   - admit. *)
(*   (* initial_safe *) *)
(*   - intros q2 QV2 QINV2. *)
(*     generalize (inv_match_query _ _ _ BSIM_INV w1 w2 q2 ccw QINV2 MATCHWORLD). *)
(*     intros (q1 & MQ & QINV1). *)
(*     exploit initial_safe0. *)
(*     erewrite <- bsim_match_valid_query; eauto. *)
(*     auto. admit. *)
    
(*   (* external_safe *) *)
(*   - admit. *)
(*   (* final_safe *) *)
(*   - admit. *)
(* Admitted. *)


(* End LTS_SAFETY_PRESERVATION. *)


(** Safety Preservation Under Backward Simulation *)

Section SAFETY_PRESERVATION.

Context {li1 li2} (cc: callconv li1 li2).
Context (L1: semantics li1 li1) (L2: semantics li2 li2).
Context (I1: invariant li1) (I2: invariant li2).
Context (se1 se2: Genv.symtbl) (ccw: ccworld cc).

Hypothesis BSIM_INV: bsim_invariant cc I1 I2.

Lemma module_safety_preservation:
  match_senv cc ccw se1 se2 ->
  module_safe L1 I1 I1 safe se1 ->
  backward_simulation cc cc L1 L2 ->
  module_safe L2 I2 I2 safe se2.
Proof.
  (** Test2  *)
  intros MSENV SAFE [BSIM].
  destruct BSIM as [index order match_states SKEL PROP WF].
  red. intros w2 VSE2 SINV2.
  set (safe' (l: lts li2 li2 (state L2)) s :=
         exists w1: inv_world I1,
           safe l s /\
           symtbl_inv I1 w1 se1 /\
           forall r1,
             reply_inv I1 w1 r1 ->
             exists r2, reply_inv I2 w2 r2).

  cut (lts_safe se2 (L2 se2) I2 I2 safe' w2).
  (** TODO: safe' implies safe *)
  admit.
  split.
  - admit.
  - intros q2 VQ2 QINV2.
    destruct (inv_incoming _ _ _ BSIM_INV w2 se1 se2 ccw q2 SINV2 MSENV QINV2) as (w1 & q1 & SINV1 & QINV1 & MQ & Hr).
    assert (VSE1: Genv.valid_for (skel L1) se1).
    (** TODO: we need the inevert of match_senv_valid_for  *)
    admit.
    assert (VQ1: valid_query (L1 se1) q1 = true).
    { erewrite <- bsim_match_valid_query. eauto.
      eapply PROP. eauto.
      auto. auto. }
    edestruct (initial_safe _ _ _ _ _ _ (SAFE w1 VSE1 SINV1) q1 VQ1 QINV1) as ((s1 & INIT1) & INIT1'). 
    edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
    split.
    + eapply EXIST. eauto.
    + intros s2 INIT2.
      red. exists w1.
      split; auto.
      (** use bsim_progress *)
      exploit MATCH; eauto.
      intros (s1' & INIT1'' & (idx & MST)).
      (* show s1' is safe *)
      exploit INIT1'. eapply INIT1''. intros SAFES1'.
      (** TODO: how to prove safe s1 implies safe s2?  *)
      (* eapply bsim_progress; eauto. red.  *)
      admit.

  - intros s2 q2 REACH2 EXTERN2.
    (** TODO: how to prove there is a reachable state s1 and s1 simulates s2*)
    assert (A: exists s1 idx, reachable (L1 se1) s1 /\ match_states se1 se2 ccw idx s1 s2).
    admit.
    destruct A as (s1 & idx & REACH1 & MST).
    
    
  (** Test1  *)
  (* intros MSENV SAFE BSIM. *)
  (* inv BSIM. rename X into BSIM. *)
  (* red. intros w2 VSE2 INV2. *)
  (* generalize (inv_match_symtbl cc I1 I2 BSIM_INV w2 se1 se2 ccw INV2 MSENV). *)
  (* intros (w1 & INV1). *)
  (* assert (VSE1: Genv.valid_for (skel L1) se1). *)
  (* (** TODO: use match_senv to prove it but match_senv does not guarantee the *)
  (* backward valid_for? *)   *)
  (* admit.  *)
  (* exploit SAFE; eauto. *)
  (* intros LTSSAFE1. *)
  (* (* use bsim_lts *) *)
  (* inv BSIM. generalize (bsim_lts se1 se2 ccw MSENV VSE1). *)
  (* intros bsim_prop. inv bsim_prop. *)
Admitted.

End SAFETY_PRESERVATION.