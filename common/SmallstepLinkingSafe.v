Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep SmallstepSafe.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

(** Module safety : similar to the preservation of invariant in LTS *)

(* Safety should be irrelevant to the trace *)
Definition safe {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  forall s' t,
    Star L s t s' ->
    (exists r, final_state L s' r)
    \/ (exists q, at_external L s' q)
    \/ (exists t, exists s'', Step L s' t s'').

Lemma safe_implies {liA liB st} (L: lts liA liB st) s:
  safe L s ->
  Smallstep.safe L s.
Proof.
  intros. red. intros.
  eapply H. eauto.
Qed.

Lemma star_safe:
  forall {liA liB st} (L: lts liA liB st) s s' t,
  Star L s t s' -> safe L s -> safe L s'.
Proof.
  intros; red; intros. eapply H0. eapply star_trans; eauto.
Qed.

Definition not_stuck {liA liB st} (L: lts liA liB st) (s: st) : Prop :=
  (exists r, final_state L s r)
  \/ (exists q, at_external L s q)
  \/ (exists t, exists s', Step L s t s').

Definition partial_safe {liA liB st} (L: lts liA liB st) (err_state: st -> Prop) (s: st) : Prop :=
  forall s' t,
  Star L s t s' ->
  ((exists r, final_state L s' r)
  \/ (exists q, at_external L s' q)
  \/ (exists t, exists s'', Step L s' t s''))
  \/ err_state s'.

Lemma star_partial_safe:
  forall {liA liB st} (L: lts liA liB st) err s s' t,
  Star L s t s' -> partial_safe L err s -> partial_safe L err s'.
Proof.
  intros; red; intros. eapply H0. eapply star_trans; eauto.
Qed.

Lemma partial_safe_implies {liA liB st} (L: lts liA liB st) err_state s:
  partial_safe L err_state s ->
  SmallstepSafe.partial_safe L err_state s.
Proof.
  intros. red. intros.
  eapply H. eauto.
Qed.


(* Definition partial_safe {liA liB st} mem_error (L: lts liA liB st) (s: st) : Prop := *)
(*   (exists r, final_state L s r) *)
(*   \/ (exists q, at_external L s q) *)
(*   \/ (exists t, exists s', Step L s t s') *)
(*   \/ (mem_error liA liB st L s). *)

(* well-formed reachable state in module requires some restriction on
incoming query and reply *)
Inductive reachable {liA liB st} (IA: invariant liA) (IB: invariant liB) (L: lts liA liB st) (wI: inv_world IB) (s: st) : Prop :=
| initial_reach: forall q s0 t
    (VQ: valid_query L q = true)
    (WT: query_inv IB wI q)
    (INIT: initial_state L q s0)
    (STEP: Star L s0 t s),
    reachable IA IB L wI s
| external_reach: forall q r s1 s2 t w
    (* s1 also must be reachable. TODO: s1 should be in at_external? *)
(*     Otherwise we cannot prove reachable state is sound *)
    (REACH: reachable IA IB L wI s1)
    (ATEXT: at_external L s1 q)
    (WTQ: query_inv IA w q)
    (WTR: reply_inv IA w r)
    (AFEXT: after_external L s1 r s2)
    (STEP: Star L s2 t s),
    reachable IA IB L wI s.

Lemma step_reachable {liA liB st} IA IB (L: lts liA liB st) s1 t s2 w:
  Step L s1 t s2 ->
  reachable IA IB L w s1 ->
  reachable IA IB L w s2.
Proof.
  intros STEP REA.
  inv REA.
  - eapply initial_reach; eauto.
    eapply star_right; eauto.
  - eapply external_reach; eauto.
    eapply star_right; eauto.
Qed.

Lemma star_reachable {liA liB st} IA IB (L: lts liA liB st) s1 t s2 w:
  Star L s1 t s2 ->
  reachable IA IB L w s1 ->
  reachable IA IB L w s2.
Proof.
  induction 1.
  auto.
  intros. eapply IHstar.
  eapply step_reachable; eauto.
Qed.


Record lts_safe {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: lts liA liB S -> S -> Prop) (wI: inv_world IB) :=
  {
    reachable_safe: forall s,
      reachable IA IB L wI s ->
      SI L s;
    
    (* properties of compositionality *)
    initial_progress: forall q,
      valid_query L q = true ->
      query_inv IB wI q ->
      (exists s, initial_state L q s);
    
    external_progress: forall s q,
      reachable IA IB L wI s ->
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s');

    final_progress: forall s r,
      reachable IA IB L wI s ->
      final_state L s r ->
      reply_inv IB wI r;    
  }.


(** lts_safe_triple is hoare-triple representation of lts_safe, but it
is unused for now *)

(* state s can be reachable from state s0 *)
Inductive reachable_from {liA liB st} (IA: invariant liA) (IB: invariant liB) (L: lts liA liB st) (wI: inv_world IB) (s0 s: st) : Prop :=
| internal_reach_from: forall t
    (STEP: Star L s0 t s),
    reachable_from IA IB L wI s0 s
| external_reach_from: forall q r s1 s2 t w
    (REACH: reachable_from IA IB L wI s0 s1)
    (ATEXT: at_external L s1 q)
    (WTQ: query_inv IA w q)
    (WTR: reply_inv IA w r)
    (AFEXT: after_external L s1 r s2)
    (STEP: Star L s2 t s),
    reachable_from IA IB L wI s0 s.


Definition lts_safe_triple_body {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (wI: inv_world IB) (s0: S) : Prop :=
  (* safe *)
  (forall s, reachable_from IA IB L wI s0 s ->
        not_stuck L s)
  (* correct *)
  /\ (forall s r, reachable_from IA IB L wI s0 s ->
            final_state L s r ->
            reply_inv IB wI r)
  (* external call (not suppored in standard Hoare triple) *)
  /\ (forall s q ,reachable_from IA IB L wI s0 s ->
            at_external L s q ->
            exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
                    forall r, reply_inv IA wA r ->
                         (exists s', after_external L s r s')).


(* assume that SI in lts_safe is instantiated with not_stuck *)
Definition lts_safe_triple {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (wI: inv_world IB) : Prop :=
  forall q, valid_query L q = true ->
       query_inv IB wI q ->
       (* initial progress *)
       (exists s, initial_state L q s)
       (* safe, correct and external progress *)
       /\ (forall s, initial_state L q s ->
               lts_safe_triple_body se L IA IB wI s).


(** Definition of module safety  *)

Definition module_safe_se {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI se :=
  forall w,
    symtbl_inv IB w se ->
    lts_safe se (L se) IA IB SI w.

Definition module_safe {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI :=
  forall se,
    Genv.valid_for (skel L) se ->
    module_safe_se L IA IB SI se.

(** Proof of lts_safe by the method of preservation and progress *)

(* silightly different from lts_preserves in Invariant.v *)
Record lts_invariant_preserves {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (IS: inv_world IB -> S -> Prop) (w: inv_world IB) :=
  {
    preserves_step s t s':
      IS w s ->
      Step L s t s' ->
      IS w s';
    preserves_initial_state q s:
      valid_query L q = true ->
      query_inv IB w q ->
      initial_state L q s ->
      IS w s;
    (** Why? *)
    preserves_external s s' q r wA:
      IS w s ->
      at_external L s q ->
      query_inv IA wA q ->
      reply_inv IA wA r ->
      after_external L s r s' ->
      IS w s';
  }.

(* not_stuck is hard code in lts_invariant_progress *)
Record lts_invariant_progress {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (IS: inv_world IB -> S -> Prop) (w: inv_world IB) :=
  {
    progress_internal_state: forall s,
      IS w s ->
      not_stuck L s;

    progress_initial_state: forall q,
      valid_query L q = true ->
      query_inv IB w q ->
      (exists s, initial_state L q s);
    
    progress_external_state: forall s q,
      IS w s ->
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress *)
                   (exists s', after_external L s r s');

    progress_final_state: forall s r,
      IS w s ->
      final_state L s r ->
      reply_inv IB w r;
  }.


Record module_safe_components {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) :=
  Module_safe_components
  {
    msafe_invariant: inv_world IB -> state L -> Prop;

    msafe_preservation: forall se wB,
      symtbl_inv IB wB se ->
      Genv.valid_for (skel L) se ->
      lts_invariant_preserves (L se) IA IB msafe_invariant wB;

    msafe_progress: forall se wB,
      symtbl_inv IB wB se ->
      Genv.valid_for (skel L) se ->
      lts_invariant_progress se (L se) IA IB msafe_invariant wB;
  }.

(* For some specific example, we need to fix the symbol table *)
Record module_safe_se_components {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) se :=
  Module_safe_se_components
  {
    msafe_se_invariant: inv_world IB -> state L -> Prop;

    msafe_se_preservation: forall wB,
      symtbl_inv IB wB se ->
      lts_invariant_preserves (L se) IA IB msafe_se_invariant wB;

    msafe_se_progress: forall wB,
      symtbl_inv IB wB se ->
      lts_invariant_progress se (L se) IA IB msafe_se_invariant wB;
  }.


Lemma star_preserves_invariant {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB): forall w s t s' IS (PRE: lts_invariant_preserves L IA IB IS w),
    IS w s ->
    Star L s t s' ->
    IS w s'.
Proof.
  induction 3. auto.
  apply IHstar. eapply preserves_step; eauto.
Qed.

Lemma reachable_preserves_invariant {liA liB S} (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB): forall w s IS (PRE: lts_invariant_preserves L IA IB IS w),
    reachable IA IB L w s ->
    IS w s.
Proof.
  induction 2.
  - eapply star_preserves_invariant; eauto.
    eapply preserves_initial_state; eauto.
  - eapply star_preserves_invariant. 3: eapply STEP. eauto.
    eapply preserves_external; eauto.
Qed.

(* soundness of module_safe_components *)
Lemma module_safe_components_sound {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB):
  module_safe_components L IA IB ->
  module_safe L IA IB not_stuck.
Proof.
  intros SAFE. inv SAFE.
  red. intros se VSE w WTSE.
  exploit msafe_preservation0; eauto. intros PRE.
  exploit msafe_progress0; eauto. intros PRO.
  constructor.
  (* reachable not stuck *)
  - intros s REACH.
    eapply reachable_preserves_invariant with (IS:= msafe_invariant0) in REACH; auto.
    eapply progress_internal_state; eauto.
  (* initial_progress *)
  - eapply progress_initial_state; eauto.
  (* external_progress *)
  - intros s q REACH.
    eapply progress_external_state; eauto.
    eapply reachable_preserves_invariant; eauto.
  (* final_progress *)
  - intros s r REACH.
    eapply progress_final_state; eauto.
    eapply reachable_preserves_invariant; eauto.
Qed.

Lemma module_safe_se_components_sound {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) se:
  module_safe_se_components L IA IB se ->
  module_safe_se L IA IB not_stuck se.
Proof.
  intros SAFE. inv SAFE.
  red. intros w WTSE.
  exploit msafe_se_preservation0; eauto. intros PRE.
  exploit msafe_se_progress0; eauto. intros PRO.
  constructor.
  (* reachable not stuck *)
  - intros s REACH.
    eapply reachable_preserves_invariant with (IS:= msafe_se_invariant0) in REACH; auto.
    eapply progress_internal_state; eauto.
  (* initial_progress *)
  - eapply progress_initial_state; eauto.
  (* external_progress *)
  - intros s q REACH.
    eapply progress_external_state; eauto.
    eapply reachable_preserves_invariant; eauto.
  (* final_progress *)
  - intros s r REACH.
    eapply progress_final_state; eauto.
    eapply reachable_preserves_invariant; eauto.
Qed.
  

(* Propeties of reachable state in composed semantics *)
Section REACH.

Context {li} (I: invariant li) (L: bool -> semantics li li). 
Context (se: Genv.symtbl).
Context (w: inv_world I).
(* A generalized wf_state specifying rechable property and invariant world in the frame *)

Inductive wf_frames : list (frame L) -> inv_world I -> Prop :=
| wf_frames_nil: wf_frames nil w
| wf_frames_cons: forall i s q w1 w2 fms
    (WF: wf_frames fms w1)
    (VSE1: symtbl_inv I w1 se)
    (FREACH: reachable I I (L i se) w1 s)
    (EXT: at_external (L i se) s q)
    (WTQ: query_inv I w2 q)
    (* (VSE2: symtbl_inv I w2 se) *)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I w2 r ->
               exists s', after_external (L i se) s r s'),
    wf_frames ((st L i s) :: fms) w2.

Inductive wf_state : list (frame L) -> Prop :=
| wf_state_cons: forall i s k w1
    (WFS: wf_frames k w1)
    (VSE: symtbl_inv I w1 se)
    (SREACH: reachable I I (L i se) w1 s),
    wf_state (st L i s :: k).


Section SAFE.

Hypothesis (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
Hypothesis (SAFE: forall i, module_safe_se (L i) I I not_stuck se).

Lemma step_wf_state sk s1 t s2:
  Step (SmallstepLinking.semantics L sk se) s1 t s2 ->
  wf_state s1 ->
  wf_state s2.
Proof.
  intros STEP WF.
  inv STEP.
  - inv WF. subst_dep.
    econstructor; eauto.
    eapply step_reachable; eauto.
  - inv WF. subst_dep.
    (* external_progress of s *)    
    exploit (@external_progress li); eauto. eapply SAFE; eauto.
    intros (wA & SYMBINV & QINV & AFTER).
    econstructor; eauto.
    econstructor; eauto.
    eapply initial_reach; eauto.
    econstructor; eauto.
  - inv WF. subst_dep.
    exploit (@final_progress li); eauto. eapply SAFE; eauto.
    intros WTR.
    inv WFS. subst_dep.
    econstructor; eauto.
    eapply external_reach; eauto.
    eapply star_refl.
Qed.

Lemma star_wf_state sk s1 t s2:
  Star (SmallstepLinking.semantics L sk se) s1 t s2 ->
  wf_state s1 ->
  wf_state s2.
Proof.
  induction 1; auto.
  intros WF. eapply IHstar.
  eapply step_wf_state; eauto.
Qed.


Lemma reachable_wf_state sk s (WTSE: symtbl_inv I w se):
  reachable I I (SmallstepLinking.semantics L sk se) w s ->
  wf_state s.
Proof.
  induction 1.
  - eapply star_wf_state; eauto.
    inv INIT.
    econstructor; eauto.
    econstructor.
    eapply initial_reach; eauto.
    eapply star_refl.
  - eapply star_wf_state; eauto.
    inv AFEXT. inv ATEXT. inv IHreachable. subst_dep.
    econstructor; eauto. 
    eapply external_reach; eauto.
    eapply star_refl.
Qed.

End SAFE.

End REACH.


  
Lemma compose_safety {li} (I: invariant li) L1 L2 L:
  module_safe L1 I I not_stuck ->
  module_safe L2 I I not_stuck ->
  compose L1 L2 = Some L ->
  module_safe L I I not_stuck.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  red. intros se w VALID INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  destruct i.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (SAFE: forall i, module_safe_se (L i) I I not_stuck se).
  { intros i. generalize (VALIDSE i). intros VSE.
    destruct i; simpl; auto. }
  constructor.
  (* rechable not stuck *)
  - intros s WFREACH.    
    exploit (@reachable_wf_state li); eauto.
    intros WFST.
    (* destruct the frames to case analyze the top frame *)
    destruct s. inv WFST.
    destruct f. inv WFST. subst_dep.
    (* s0 is not stuck because (L i) is safe *)
    exploit (@reachable_safe li li (state (L i))); eauto.
    eapply SAFE; eauto. intros SAFES0.
    (* case analysis of not_stuck of s0 *)
    destruct SAFES0 as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
    (* s0 in final state *)
    + destruct s.
      (* composed semantics in final state *)
      * red. left. exists r.
        constructor. auto.
      (* composed semantics can make a step to caller *)
      * red. right. right.
        inv WFS.
        (* final_prgress in s0 *)
        exploit (@final_progress li). eapply SAFE.
        eapply VSE. eauto. eauto. intros WTR.        
        exploit PGS; eauto. intros (s1' & AFEXT).
        (* s0 can return a well-typed reply to s1 which is in at_external to make a step *)
        do 2 eexists.
        eapply step_pop; eauto.
    (* s0 in at_external state *)
    + exploit (@external_progress li); eauto.
      eapply SAFE; eauto.
      intros (wA & SYMBINV & QINV & AFTER). clear AFTER.
      destruct (orb (valid_query (L true se) q) (valid_query (L false se) q)) eqn: VQ.
      (* step_push *)
      * eapply orb_true_iff in VQ.
        red. right. right.
        destruct VQ as [VQ1|VQ2].
        -- exploit (@initial_progress li); eauto. eapply SAFE; eauto.
           intros (s1 & INIT1).
           do 2 eexists.        
           eapply step_push; eauto. 
        -- exploit (@initial_progress li); eauto. eapply SAFE; eauto.
           intros (s1 & INIT1).
           do 2 eexists.        
           eapply step_push; eauto.
      (* composed module in at_external *)
      * red. right. left.
        exists q. econstructor. eauto.
        eapply orb_false_iff in VQ. destruct VQ.
        intros. destruct j; auto.
    (* s0 can make a step *)
    + red. right. right.
      do 2 eexists. eapply step_internal. eauto.
  (* initial_progress *)
  - intros q VQ SQ. simpl in *.
    unfold SmallstepLinking.valid_query in VQ.
    eapply orb_true_iff in VQ. destruct VQ as [VQ1| VQ2].
    + exploit (@initial_progress li); eauto.
      eapply SAFE; eauto.
      intros (s0 & INIT).
      eexists. econstructor; eauto.
    + exploit (@initial_progress li); eauto.
      eapply SAFE; eauto.
      intros (s0 & INIT).
      eexists. econstructor; eauto.
  (* external_progress *)
  - intros s q REACH EXT. inv EXT.
    eapply reachable_wf_state in REACH; eauto.
    inv REACH. subst_dep.
    exploit (@external_progress li); eauto. eapply SAFE; eauto.
    intros (wA & SYMBINV & QINV & AFTER).
    exists wA. split; auto. split; auto.
    intros r WTR.
    exploit AFTER; eauto. intros (s1 & AFEXT).
    exists (st L i s1 :: k).
    constructor. auto.
  (* final_progress *)
  - intros s r REACH FINAL.
    inv FINAL.
    eapply reachable_wf_state in REACH; eauto. inv REACH. subst_dep.
    inv WFS.
    exploit (@final_progress li); eauto. eapply SAFE; eauto.
Qed.

(** Properties of lts_safe  *)

Lemma lts_safe_reachable_safe {li1 li2 S} se (L: lts li1 li2 S) I1 I2 w : forall s,
    lts_safe se L I1 I2 not_stuck w ->
    reachable I1 I2 L w s ->
    safe L s.
Proof.
  intros.
  red. intros.
  eapply reachable_safe in H.
  2: { eapply star_reachable; eauto. }
  eauto.
Qed.

(** An alternative safety definition *)

Section SAFEK.
  
(* lts_safek is an alternative definition of safety based on "safe in
k steps". One opportunity of this definition is to utilize bound model
checking. We treat SI as a special final state (but how to express its
disjointness?) *)

Inductive safek {liA liB St} (se: Genv.symtbl) (L: lts liA liB St) (IA: invariant liA) (IB: invariant liB) (SI: St -> Prop) (wI: inv_world IB) : nat -> St -> Prop :=
| safek_O: forall s,
    safek se L IA IB SI wI O s
| safek_step: forall s1 t s2 k
    (* Ensure that this internal state can make a step *)
    (STEP: Step L s1 t s2)
    (* We allow internal nondeterminism so every states in the next *)
(*     step must be safek. *)
    (SAFEK: forall t' s2', Step L s1 t' s2' ->
                      safek se L IA IB SI wI k s2'),
    safek se L IA IB SI wI (S k) s1
| safek_SI: forall s k
    (* SI as a special final state. It can be False to define total *)
(*     safe or memory_error to define partial safe *)
    (SINV: SI s),
    safek se L IA IB SI wI k s
| safek_final: forall s r k
    (FINAL: final_state L s r)
    (* The reply satisfies the post-condition *)
    (RINV: reply_inv IB wI r),
    safek se L IA IB SI wI k s
| safek_external: forall s1 k w q
    (ATEXT: at_external L s1 q)
    (SYMBINV: symtbl_inv IA w se)
    (QINV: query_inv IA w q)
    (* We require that the incoming reply satisfies its condition *)
    (AFEXT: forall r, reply_inv IA w r ->
                 exists s2, after_external L s1 r s2
                       /\ safek se L IA IB SI wI k s2),
    safek se L IA IB SI wI (S k) s1
.

(** Experiment safek based on internal multiple steps  *)
(* Inductive safek {liA liB St} (se: Genv.symtbl) (L: lts liA liB St) (IA: invariant liA) (IB: invariant liB) (SI: lts liA liB St -> St -> Prop) (wI: inv_world IB) : nat -> St -> Prop := *)
(* | safek_O: forall s, *)
(*     safek se L IA IB SI wI O s *)
(* | safek_step: forall s1 t s2 k *)
(*     (* Ensure that this internal state can make a step *) *)
(*     (STEP: Step L s1 t s2) *)
(*     (* We allow internal nondeterminism so every states in the next *) *)
(*     (* step must be safek. *) *)
(*     (SAFEK: forall t' s2', Plus L s1 t' s2' -> *)
(*                       safek se L IA IB SI wI k s2'), *)
(*     safek se L IA IB SI wI k s1 *)
(* | safek_SI: forall s k *)
(*     (* SI as a special final state. It can be False to define total *) *)
(* (* safe or memory_error to define partial safe *) *)
(*     (SINV: SI L s), *)
(*     safek se L IA IB SI wI k s *)
(* | safek_final: forall s r k *)
(*     (FINAL: final_state L s r) *)
(*     (* The reply satisfies the post-condition *) *)
(*     (RINV: reply_inv IB wI r), *)
(*     safek se L IA IB SI wI k s *)
(* | safek_external: forall s1 k w q *)
(*     (ATEXT: at_external L s1 q) *)
(*     (SYMBINV: symtbl_inv IA w se) *)
(*     (QINV: query_inv IA w q) *)
(*     (* We require that the incoming reply satisfies its condition *) *)
(*     (AFEXT: forall r, reply_inv IA w r -> *)
(*                  exists s2, after_external L s1 r s2 *)
(*                        /\ safek se L IA IB SI wI k s2), *)
(*     safek se L IA IB SI wI (S k) s1 *)
(* . *)
     

Definition lts_safek {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: S -> Prop) (wI: inv_world IB) :=  
  forall q,
    (* when the query is valid and satisfis the pre-condition *)
    valid_query L q = true ->
    query_inv IB wI q ->
    exists s, initial_state L q s
         (* This lts does not get stuck in any k steps *)
         /\ (forall k, safek se L IA IB SI wI k s).

(* This intermediate definition is used to prepare the activation for
the module in the proof of compositionality *)
Definition module_safek_se {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI se :=
  forall w,
    symtbl_inv IB w se ->
    lts_safek se (L se) IA IB SI w.

(* SI here takes symtbl as its first argument because in parctice the
SI may depend on the symtbl (such as memory_error_state) *)
Definition module_safek {liA liB} (L: semantics liA liB) (IA IB: invariant _) SI :=
  forall se,
    Genv.valid_for (skel L) se ->
    module_safek_se L IA IB (SI se) se.

(* Module total safety (SI is False) *)
Definition SIF {S} : Genv.symtbl -> S -> Prop := (fun _ _ => False).

Definition module_total_safek {liA liB} (L: semantics liA liB) (IA IB: invariant _) := module_safek L IA IB SIF.

(** Prove Safety by Invariant Preservation and Progress *)

Record lts_preserves_progress {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (IS: inv_world IB -> S -> Prop) (w: inv_world IB) (PS: S -> Prop) :=
  {
    internal_step_preserves: forall s t s',
      IS w s ->
      Step L s t s' ->
      IS w s';
    internal_state_progress: forall s,
      IS w s ->
      not_stuck L s \/ PS s;
    
    initial_preserves_progress: forall q,
      valid_query L q = true ->
      query_inv IB w q ->
      exists s, initial_state L q s
           /\ (forall s, initial_state L q s -> IS w s);

    external_preserves_progress: forall s q,
      IS w s ->
      at_external L s q ->
      exists wA, symtbl_inv IA wA se /\ query_inv IA wA q /\
              forall r, reply_inv IA wA r ->
                   (* after external progress, why it is different
                   from initial state? *)
                   (exists s', after_external L s r s'
                          /\ (forall s', after_external L s r s' -> IS w s'));

    final_state_preserves: forall s r,
      IS w s ->
      final_state L s r ->
      reply_inv IB w r;
  }.


Record module_type_safe_components {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) (PS: Genv.symtbl -> (state L) -> Prop) :=
  Module_type_safe_components
  {
    type_safe_invariant: Genv.symtbl -> inv_world IB -> state L -> Prop;

    type_safe_preservation_progress: forall se wB,
      symtbl_inv IB wB se ->
      Genv.valid_for (skel L) se ->
      lts_preserves_progress se (L se) IA IB (type_safe_invariant se) wB (PS se);
  }.

Definition module_type_safe {liA liB} (IA: invariant liA) (IB: invariant liB) (L: semantics liA liB) (PS: Genv.symtbl -> (state L) -> Prop) :=
  inhabited (@module_type_safe_components liA liB L IA IB PS).

(* property of safety invariant *)
Section SAFE_INV.
Context {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) PS se w SI
  (PRE: lts_preserves_progress se (L se) IA IB (SI se) w (PS se)).

(* for any state satisfies the invariant, then it is k-safe *)
Lemma lts_preserves_progress_safek: forall k s,
    SI se w s ->
    safek se (L se) IA IB (PS se) w k s.
Proof.
  induction k; intros s SINV.
  - econstructor.
  - exploit (@internal_state_progress liA); eauto.
    intros [A|B].
    + destruct A as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
      * eapply safek_final. eauto.
        eapply final_state_preserves; eauto.
      * exploit (@external_preserves_progress liA); eauto.
        intros (wA & SYM & QINV & AFEXT).
        eapply safek_external; eauto.
        intros. exploit AFEXT; eauto.
        intros (s' & AFEXT1 & SIEXT). exists s'. split; auto.
      * eapply safek_step; eauto.
        intros. eapply IHk. eauto.
        eapply internal_step_preserves; eauto.
    + eapply safek_SI. eauto.
Qed.

Lemma lts_preserves_progress_star: forall s t s',
    Star (L se) s t s' ->
    SI se w s ->
    SI se w s'.
Proof.
  induction 1; auto.
  intros. eapply IHstar. eapply internal_step_preserves; eauto.
Qed.  
  
End SAFE_INV.

 Lemma lts_preserves_progress_internal_safe {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) se w SI: forall s,
    lts_preserves_progress se (L se) IA IB (SI se) w (SIF se) ->
    SI se w s ->
    safe (L se) s.
Proof.
  intros s PRE SINV. red.
  intros.  
  exploit @lts_preserves_progress_star. eauto. eauto. auto.
  intros A.
  exploit @internal_state_progress. eauto. eauto. intros [B|C]; try contradiction.
  eauto.
Qed.

Lemma lts_preserves_progress_internal_partial_safe {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) se w SI err_state: forall s,
    lts_preserves_progress se (L se) IA IB (SI se) w (err_state se) ->
    SI se w s ->
    partial_safe (L se) (err_state se) s.
Proof.
  intros s PRE SINV. red.
  intros.  
  exploit @lts_preserves_progress_star. eauto. eauto. auto.
  intros A.
  exploit @internal_state_progress. eauto. eauto. intros [B|C]; try contradiction; eauto.
Qed.

(* soundness of module_safe_components *)
Lemma module_type_safe_sound {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) PS:
  module_type_safe IA IB L PS ->
  module_safek L IA IB PS.
Proof.
  intros [SAFE]. inv SAFE.
  red. intros se VSE w WTSE.
  exploit type_safe_preservation_progress0; eauto. intros PRE.
  red. intros q VQ QINV.
  exploit (@initial_preserves_progress liA); eauto.
  intros (inits & INIT & SINV1). exists inits. split; auto.
  intros. eapply lts_preserves_progress_safek; eauto.
Qed.

(** Compositionality *)

(* To prove safety under composition, we need some deterministic
properties in initial, external and final states. Nostep and noext are
used to ensure that each case of safek is disjoint *)

Record lts_open_determinate {liA liB st} (L: lts liA liB st) : Prop :=
  Interface_determ {
      od_initial_determ: forall q s1 s2,
        initial_state L q s1 -> initial_state L q s2 -> s1 = s2;
      od_at_external_nostep: forall s q,
        at_external L s q -> Nostep L s;
      od_at_external_determ: forall s q1 q2,
        at_external L s q1 -> at_external L s q2 -> q1 = q2;      
      od_after_external_determ: forall s r s1 s2,
        after_external L s r s1 -> after_external L s r s2 -> s1 = s2;
      od_final_nostep: forall s r,
        final_state L s r -> Nostep L s;
      od_final_noext: forall s r q,
        final_state L s r -> at_external L s q -> False;
      od_final_determ: forall s r1 r2,
        final_state L s r1 -> final_state L s r2 -> r1 = r2
    }.

Definition open_determinate {liA liB} (L: semantics liA liB) :=
  forall se, lts_open_determinate (L se).

(** Compositionality of module type safety *)

Section WITH_INV.

Context {li} (I: invariant li) (L: bool -> semantics li li).
Context (sk: AST.program unit unit) (se: Genv.symtbl).
Context (SAFE : forall i, module_type_safe_components (L i) I I SIF).

Inductive type_safe_frames w : list (frame L) -> inv_world I -> Prop :=
| type_safe_frames_nil: type_safe_frames w nil w
| type_safe_frames_cons: forall i s q w1 w2 fms
    (WF: type_safe_frames w fms w1)
    (VSE: symtbl_inv I w1 se)
    (EXT: at_external (L i se) s q)
    (WTQ: query_inv I w2 q)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I w2 r ->
               exists s', after_external (L i se) s r s'
                     /\ (forall s', after_external (L i se) s r s' ->
                              type_safe_invariant (L i) I I SIF (SAFE i) se w1 s')),
    type_safe_frames w ((st L i s) :: fms) w2.

Inductive type_safe_state w: list (frame L) -> Prop :=
| type_safe_state_cons: forall i s frs w1
    (WFS: type_safe_frames w frs w1)
    (VSE: symtbl_inv I w1 se)
    (TYSAFE: type_safe_invariant (L i) I I SIF (SAFE i) se w1 s),
    type_safe_state w (st L i s :: frs).

End WITH_INV.

Section COMPOSE_TYPE_SAFE.

Context {li} (I: invariant li) (L1 L2 L: semantics li li).


Lemma compose_total_type_safety:
  module_type_safe I I L1 SIF ->
  module_type_safe I I L2 SIF ->
  compose L1 L2 = Some L ->
  module_type_safe I I L SIF.
Proof.
  intros [SAFE1] [SAFE2] COMP.
  unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  assert (SAFE: forall i, module_type_safe_components (L i) I I SIF).
  { intros i. destruct i.
    eapply SAFE1; eauto.
    eapply SAFE2; eauto. }
  red. econstructor.
  eapply Module_type_safe_components with (type_safe_invariant := fun se w => type_safe_state I L se SAFE w).
  intros se wB SYM VSE.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  { destruct i.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto. }
  econstructor.
  - intros. inv H. inv H0; subst_dep.
    + econstructor; eauto.
      eapply internal_step_preserves; eauto.
      eapply SAFE; eauto. 
    + exploit @external_preserves_progress.
      eapply SAFE. eapply VSE0. eapply VALIDSE. eauto.
      eauto.
      intros (wA & A1 & A2 & A3).
      econstructor. 2: eapply A1.
      econstructor; eauto.
      exploit @initial_preserves_progress.
      eapply SAFE. eapply A1. eapply VALIDSE. eauto. eauto.
      intros (s & B1 & B2).
      eapply B2. eauto.
    + inv WFS. subst_dep.
      econstructor; eauto.
      exploit PGS. eapply final_state_preserves. eapply SAFE.
      eauto. eapply VALIDSE. eauto. eauto.
      intros (s & B1 & B2).
      eapply B2. eauto.
  - intros. inv H.
    exploit @internal_state_progress. eapply SAFE; eauto.
    eauto. intros A. destruct A.
    2: { contradiction. }
    left.
    destruct H as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
    + inv WFS.
      * left. exists r.
        econstructor. eauto.
      * do 2 right.
        exploit @final_state_preserves. eapply SAFE. eapply VSE0.
        all: eauto. intros VR.
        exploit PGS; eauto.
        intros (s' & B1 & B2).
        do 2 eexists.
        eapply step_pop; eauto.
    + exploit @external_preserves_progress. eapply SAFE. 1-4: eauto.
      intros (wA & A1 & A2 & A3).
      destruct (valid_query (L i se) q || valid_query (L (negb i) se) q) eqn: VQ.
      * assert (VQ1: exists j, valid_query (L j se) q = true).
        { eapply orb_true_iff in VQ. destruct VQ.
          1-2: eexists; eauto. }
        destruct VQ1. do 2 right.
        exploit @initial_preserves_progress. eapply SAFE. 1-4: eauto. 
        intros (s' & B1 & B2).        
        do 2 eexists.        
        eapply step_push; eauto.
      * right. left.
        exists q. econstructor. eauto.
        intros.
        eapply orb_false_iff in VQ as (B1 & B2).
        destruct i; destruct j; simpl in B2; auto.
    + do 2 right.
      do 2 eexists. eapply step_internal. eauto.
  (* initial state *)
  - intros q VQ QINV.
    simpl in VQ. eapply orb_true_iff in VQ.
    assert (VQ1: exists j, valid_query (L j se) q = true).
    { destruct VQ.
      1-2: eexists; eauto. }
    destruct VQ1 as (j & VQ1).
    exploit @initial_preserves_progress. eapply SAFE.
    1-4: eauto. intros (s & A1 & A2).
    exists (st L j s :: nil). split.
    econstructor; eauto.
    intros. inv H.
    (* The initial state is state (L i) instead of state (L j) *)
    exploit @initial_preserves_progress. eapply SAFE.
    1-4: eauto. intros (s' & B1 & B2).
    econstructor. econstructor.
    eauto. eauto.
  (* external *)
  - intros s q SINV EXT. inv EXT.
    inv SINV. subst_dep.
    exploit @external_preserves_progress. eapply SAFE.
    1-4: eauto. intros (wA & A1 & A2 & A3).
    exists wA. repeat apply conj; auto.
    intros. exploit A3; eauto. intros (s' & B1 & B2).
    eexists. split.
    econstructor; eauto.
    intros. inv H2. subst_dep. 
    econstructor; eauto.
  (* final *)
  - intros s r SINV FINAL. inv FINAL.
    inv SINV. subst_dep.
    inv WFS.
    eapply final_state_preserves. eapply SAFE.
    all: eauto.
Qed.

End COMPOSE_TYPE_SAFE.
    

(** *Experiment code: safety preservation using type preserving method *)


Section SAFETYK_PRESERVATION.

Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2).
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
Context (IA1 : invariant liA1) (IB1: invariant liB1).

(* Hypothesis L1_determ: open_determinate L1. *)
(* Hypothesis L2_determ: open_determinate L2. *)

(* why we need inhabited? *)
Lemma module_type_safe_preservation:
  module_type_safe IA1 IB1 L1 SIF ->
  backward_simulation ccA ccB L1 L2 ->
  module_type_safe (invcc IA1 ccA) (invcc IB1 ccB) L2 SIF.
Proof.
  intros [SAFE] [BSIM].
  destruct SAFE as (SINV & SAFE).
  inv BSIM.
  red. constructor.
  set (MINV:= fun se2 '(wB, ccwB) s2 => exists se1 i s1, bsim_match_states se1 se2 ccwB i s1 s2
                                                /\ match_senv ccB ccwB se1 se2
                                                /\ symtbl_inv IB1 wB se1
                                                /\ SINV se1 wB s1). 
  eapply Module_type_safe_components with (type_safe_invariant := MINV).  
  intros se2 (wB1 & ccwB) (se1 & SYM1 & MENV) VSE2.
  econstructor.
  (* step preservation *)
  - simpl. intros s2 t s2' (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1).
    intros STEP2.
    assert (VSE1: Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }
    edestruct @bsim_simulation as (i' & s1' & STEP1 & MINV1); eauto.
    (* prove sound state is internal safe *)
    eapply safe_implies.
    eapply lts_preserves_progress_internal_safe; eauto.
    exists se1', i', s1'. repeat apply conj; auto.
    (* prove plus preserves sound state *)
    destruct STEP1.    
    eapply lts_preserves_progress_star; eauto. eapply plus_star. eauto.
    destruct H.  eapply lts_preserves_progress_star; eauto.    
  (* internal_state_progress *)
  - simpl. intros s2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1).
    left.
    assert (VSE1: Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }
    eapply bsim_progress; eauto.
    (* prove sound state is internal safe *)
    eapply safe_implies.
    eapply lts_preserves_progress_internal_safe; eauto.
  (* initial_preserves_progress *)
  - intros q2 VQ2 (q1 & QINV2 & MQ).
    assert (VSE1: Genv.valid_for (skel L1) se1).
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }
    generalize (bsim_lts se1 se2 ccwB MENV VSE1). intros BSIMP.
    assert (VQ1: valid_query (L1 se1) q1 = true).
    { erewrite <- bsim_match_valid_query; eauto. }
    edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
    (* source initial progress *)
    edestruct @initial_preserves_progress as (s1 & INIT1 & SINV1); eauto.
    exploit EXIST; eauto.
    intros (s2 & INIT2).
    exists s2. split. auto.
    intros s2' INIT2'.
    exploit MATCH; eauto.
    intros (s1' & INIT1' & (i & MST)).
    red.  exists se1, i, s1'. repeat apply conj; auto.
  (* external_preserves_progress *)
  - intros s2 q2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1) ATEXT2.
    assert (VSE1: Genv.valid_for (skel L1) se1).
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }    
    assert (VSE1': Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }
    edestruct @bsim_match_external as (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MSENV2 & AFEXT); eauto.
    (* prove sound state is internal safe *)
    eapply safe_implies.
    eapply lts_preserves_progress_internal_safe; eauto.
    (* star preserves SINV *)
    assert (SINV1': SINV se1' wB1 s1').
    { eapply lts_preserves_progress_star; eauto. }
    edestruct @external_preserves_progress as (wA & SYMA & QINV1 & AFSAFE); eauto.     
    exists (wA, ccwA). repeat apply conj.
    econstructor; eauto.
    econstructor; eauto.
    (* after external *)
    intros r2 (r1 & RINV1 & MR).
    exploit AFEXT. eauto.
    intros [EXIST MATCH].
    exploit AFSAFE. eauto.
    intros (s1'' & AFST1 & SINV1'').
    exploit EXIST. eauto. intros (s2' & AFST2).
    exists s2'. split; auto.
    intros s2'' AFST2'.
    exploit MATCH; eauto.
    intros (s1''' & AFST1'' & (i' & MST')).
    red. exists se1', i', s1'''. repeat apply conj; eauto.
  (* final_state_preserves *)
  - intros s2 r2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1) FINAL2.
    assert (VSE1': Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsim_skel; eauto. }
    edestruct @bsim_match_final_states as (s1' & r1 & STAR & FINAL1 & MR); eauto.
    (* prove sound state is internal safe *)
    eapply safe_implies.
    eapply lts_preserves_progress_internal_safe; eauto.
    (* star preserves SINV *)
    assert (SINV1': SINV se1' wB1 s1').
    { eapply lts_preserves_progress_star; eauto. }
    exploit @final_state_preserves; eauto.
    intros RINV1. econstructor; eauto.
Qed.

End SAFETYK_PRESERVATION.

(** Safety preservation under forward simulation (without safe premise
but with progress property) *)

Section SAFETYK_PRESERVATION_FSIMG.

Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2).
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
Context (IA2 : invariant liA2) (IB2: invariant liB2).

Lemma module_type_safe_preservation_fsimg:
  module_type_safe IA2 IB2 L2 SIF ->
  forward_simulation_progress ccA ccB L1 L2 ->
  module_type_safe (ccinv ccA IA2) (ccinv ccB IB2) L1 SIF.
Proof.
  intros [SAFE] [FSIM].
  destruct SAFE as (SINV & SAFE).
  inv FSIM.
  red. constructor.
  set (MINV:= fun se1 '(ccwB, wB) s1 => exists se2 i s2, fsimg_match_states se1 se2 ccwB i s1 s2
                                                /\ match_senv ccB ccwB se1 se2
                                                /\ symtbl_inv IB2 wB se2
                                                /\ SINV se2 wB s2). 
  eapply Module_type_safe_components with (type_safe_invariant := MINV).  
  intros se1 (ccwB & wB2) (se2 & SYM2 & MENV) VSE1.
  econstructor.
  (* step preservation *)
  - simpl. intros s1 t s1' (se2' & i & s2 & MST & MSENV2 & SYM1 & SINV2).
    intros STEP1.
    assert (VSE2: Genv.valid_for (skel L2) se2').
    { erewrite <- match_senv_valid_for; eauto.
      erewrite <- fsimg_skel; eauto. }
    edestruct @fsim_simulation as (i' & s2' & STEP2 & MINV2); eauto.
    eapply fsimg_prop; eauto.
    exists se2', i', s2'. repeat apply conj; auto.
    (* prove plus preserves sound state *)
    destruct STEP2.    
    eapply lts_preserves_progress_star; eauto. eapply plus_star. eauto.
    destruct H.  eapply lts_preserves_progress_star; eauto.    
  (* internal_state_progress *)
  - simpl. intros s1 (se2' & i & s2 & MST & MSENV2 & SYM1 & SINV2).
    left.
    assert (VSE2: Genv.valid_for (skel L2) se2').
    { erewrite <- match_senv_valid_for; eauto.
      erewrite <- fsimg_skel; eauto. }
    eapply fsimg_progress; eauto.
    (* prove sound state is internal safe *)
    eapply safe_implies.
    eapply lts_preserves_progress_internal_safe; eauto.
  (* initial_preserves_progress *)
  - intros q1 VQ1 (q2 & QINV1 & MQ).
    generalize (fsimg_lts se1 se2 ccwB MENV VSE1). intros FSIMP.
    assert (VQ2: valid_query (L2 se2) q2 = true).
    { erewrite fsim_match_valid_query; eauto. eapply fsimg_prop; eauto. }
    (* target initial progress *)
    assert (VSE2: Genv.valid_for (skel L2) se2).
    { erewrite <- match_senv_valid_for; eauto.
      erewrite <- fsimg_skel; eauto. }
    edestruct @initial_preserves_progress as (s2 & INIT2 & SINV2); eauto.
    (* fsimg_initial_progress to show that L1 is initial_progress *)
    edestruct @fsimg_initial_progress as (s1 & INIT1); eauto.
    exists s1. split. auto.
    intros s1' INIT1'.
    exploit @fsim_match_initial_states; eauto.
    eapply fsimg_prop; eauto.
    intros (i & s2' & INIT2' & MST).
    red. exists se2, i, s2'. repeat apply conj; auto.
  (* external_preserves_progress *)
  - intros s1 q1 (se2' & i & s2 & MST & MSENV2 & SYM1 & SINV2) ATEXT1.
    assert (VSE2: Genv.valid_for (skel L2) se2).
    { erewrite <- match_senv_valid_for; eauto.
      erewrite <- fsimg_skel; eauto. }
    assert (VSE2': Genv.valid_for (skel L2) se2').
    { erewrite <- match_senv_valid_for. 2: eapply MSENV2.
      erewrite <- fsimg_skel; eauto. }
    edestruct @fsim_match_external as (ccwA & q2 & ATEXT2 & MQ & MSENV1 & AFEXT).
    eapply fsimg_prop; eauto. all: eauto.
    edestruct @external_preserves_progress as (wA & SYMA & QINV2 & AFSAFE); eauto.     
    exists (ccwA, wA). repeat apply conj.
    econstructor; eauto.
    econstructor; eauto.
    (* after external *)
    intros r1 (r2 & RINV2 & MR).
    exploit AFSAFE. eauto.
    intros (s2' & AFST2 & SINV2').
    edestruct @fsimg_external_progress as (s1' & AFEXT1'); eauto.
    exists s1'. split. auto.
    intros s1'' AFST1'.
    exploit AFEXT; eauto.
    intros (i' & s2'' & AFST2'' & MST').
    red. exists se2', i', s2''. repeat apply conj; eauto.
  (* final_state_preserves *)
  - intros s1 r1 (se2' & i & s2 & MST & MSENV2 & SYM1 & SINV2) FINAL1.
    assert (VSE2': Genv.valid_for (skel L2) se2').
    { erewrite <- match_senv_valid_for; eauto.
      erewrite <- fsimg_skel; eauto. }
    edestruct @fsim_match_final_states as (r2 & FINAL2 & MR). 
    eapply fsimg_prop; eauto. all: eauto.
    (* star preserves SINV *)
    exploit @final_state_preserves; eauto.
    intros RINV1. econstructor; eauto.
Qed.

End SAFETYK_PRESERVATION_FSIMG.


(** *End of Experiment code: safety preservation using type preserving method *)


(** *Experiment code: try to prove the preservation of partial safety under the error preserving backward simulation *)
               
Section PARTIAL_SAFETY_PRESERVATION.

Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2).
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
Context (IA1 : invariant liA1) (IB1: invariant liB1).
Context (err_state1: Genv.symtbl -> state L1 -> Prop) (err_state2: Genv.symtbl -> state L2 -> Prop).

Lemma module_partial_safe_preservation:
  module_type_safe IA1 IB1 L1 err_state1 ->
  backward_simulation_preserve_error ccA ccB L1 L2 err_state1 err_state2 ->
  module_type_safe (invcc IA1 ccA) (invcc IB1 ccB) L2 err_state2.
Proof.
  intros [SAFE] [BSIM].
  destruct SAFE as (SINV & SAFE).
  inv BSIM.
  red. constructor.
  set (MINV:= fun se2 '(wB, ccwB) s2 => exists se1 i s1, bsimp_match_states se1 se2 ccwB i s1 s2
                                                /\ match_senv ccB ccwB se1 se2
                                                /\ symtbl_inv IB1 wB se1
                                                /\ SINV se1 wB s1). 
  eapply Module_type_safe_components with (type_safe_invariant := MINV).  
  intros se2 (wB1 & ccwB) (se1 & SYM1 & MENV) VSE2.
  econstructor.
  (* step preservation *)
  - simpl. intros s2 t s2' (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1).
    intros STEP2.
    assert (VSE1: Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }
    edestruct @bsimp_simulation as (i' & s1' & STEP1 & MINV1); eauto.
    (* prove sound state is internal safe *)
    eapply partial_safe_implies.
    eapply lts_preserves_progress_internal_partial_safe; eauto.
    exists se1', i', s1'. repeat apply conj; auto.
    (* prove plus preserves sound state *)
    destruct STEP1.    
    eapply lts_preserves_progress_star; eauto. eapply plus_star. eauto.
    destruct H.  eapply lts_preserves_progress_star; eauto.    
  (* internal_state_progress *)
  - simpl. intros s2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1).
    assert (VSE1: Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }
    eapply bsimp_progress; eauto.
    (* prove sound state is internal safe *)
    eapply partial_safe_implies.
    eapply lts_preserves_progress_internal_partial_safe; eauto.
  (* initial_preserves_progress *)
  - intros q2 VQ2 (q1 & QINV2 & MQ).
    assert (VSE1: Genv.valid_for (skel L1) se1).
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }
    generalize (bsimp_lts se1 se2 ccwB MENV VSE1). intros BSIMP.
    assert (VQ1: valid_query (L1 se1) q1 = true).
    { erewrite <- bsimp_match_valid_query; eauto. }
    edestruct @bsimp_match_initial_states as [EXIST MATCH]; eauto.
    (* source initial progress *)
    edestruct @initial_preserves_progress as (s1 & INIT1 & SINV1); eauto.
    exploit EXIST; eauto.
    intros (s2 & INIT2).
    exists s2. split. auto.
    intros s2' INIT2'.
    exploit MATCH; eauto.
    intros (s1' & INIT1' & (i & MST)).
    red.  exists se1, i, s1'. repeat apply conj; auto.
  (* external_preserves_progress *)
  - intros s2 q2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1) ATEXT2.
    assert (VSE1: Genv.valid_for (skel L1) se1).
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }    
    assert (VSE1': Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }
    edestruct @bsimp_match_external as (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MSENV2 & AFEXT); eauto.
    (* prove sound state is internal safe *)
    eapply partial_safe_implies.
    eapply lts_preserves_progress_internal_partial_safe; eauto.
    (* star preserves SINV *)
    assert (SINV1': SINV se1' wB1 s1').
    { eapply lts_preserves_progress_star; eauto. }
    edestruct @external_preserves_progress as (wA & SYMA & QINV1 & AFSAFE); eauto.     
    exists (wA, ccwA). repeat apply conj.
    econstructor; eauto.
    econstructor; eauto.
    (* after external *)
    intros r2 (r1 & RINV1 & MR).
    exploit AFEXT. eauto.
    intros [EXIST MATCH].
    exploit AFSAFE. eauto.
    intros (s1'' & AFST1 & SINV1'').
    exploit EXIST. eauto. intros (s2' & AFST2).
    exists s2'. split; auto.
    intros s2'' AFST2'.
    exploit MATCH; eauto.
    intros (s1''' & AFST1'' & (i' & MST')).
    red. exists se1', i', s1'''. repeat apply conj; eauto.
  (* final_state_preserves *)
  - intros s2 r2 (se1' & i & s1 & MST & MSENV1 & SYM2 & SINV1) FINAL2.
    assert (VSE1': Genv.valid_for (skel L1) se1').
    { eapply match_senv_valid_for; eauto.
      erewrite bsimp_skel; eauto. }
    edestruct @bsimp_match_final_states as (s1' & r1 & STAR & FINAL1 & MR); eauto.
    (* prove sound state is internal safe *)
    eapply partial_safe_implies.
    eapply lts_preserves_progress_internal_partial_safe; eauto.
    (* star preserves SINV *)
    assert (SINV1': SINV se1' wB1 s1').
    { eapply lts_preserves_progress_star; eauto. }
    exploit @final_state_preserves; eauto.
    intros RINV1. econstructor; eauto.
Qed.

End PARTIAL_SAFETY_PRESERVATION.


(** *Experiment code about inductive defined open forward simulation  *)

Section FSIMK.

Context {liA1 liA2} (ccA: callconv liA1 liA2).
Context {liB1 liB2} (ccB: callconv liB1 liB2).
Context (se1 se2: Genv.symtbl) (wB: ccworld ccB).
Context {state1 state2: Type}.

Context (L1: lts liA1 liB1 state1) (L2: lts liA2 liB2 state2) (index: Type)
  (order: index -> index -> Prop).
  (* (match_states: index -> state1 -> state2 -> Prop). *)


Inductive fsimk : nat -> nat -> index -> state1 -> state2 -> Prop :=
| fsimk_step: forall i s1 s2 s1' t k n,
    Step L1 s1 t s1' ->
    (forall t' s1'',
        Step L1 s1 t' s1'' ->
        exists i' s2' m,
          (starN (step L2) (globalenv L2) (S m) s2 t' s2'
           /\ fsimk n (Nat.sub k (S m)) i' s1'' s2')
          \/ (starN (step L2) (globalenv L2) m s2 t' s2'
             /\ order i' i
             /\ fsimk n (Nat.sub k m) i' s1'' s2')) ->
    fsimk (S n) k i s1 s2
| fsimk_external: forall i s1 s2 w q1 q2 k n,
    at_external L1 s1 q1 ->
    at_external L2 s2 q2 ->
    match_query ccA w q1 q2 ->
    match_senv ccA w se1 se2 ->
    (forall r1 r2 s1',
        match_reply ccA w r1 r2 ->
        after_external L1 s1 r1 s1' ->
        exists i' s2', after_external L2 s2 r2 s2'                  
                  /\ fsimk n k i' s1' s2') ->
    fsimk (S n) (S k) i s1 s2
| fsimk_final: forall s1 s2 r1 r2 i n k,
    final_state L1 s1 r1 ->
    final_state L2 s2 r2 ->
    match_reply ccB wB r1 r2 ->
    fsimk n k i s1 s2
| fsimk_stuck: forall n k i s1 s2,
    ~ not_stuck L1 s1 ->
    fsimk n k i s1 s2
.

End FSIMK.

Section SAFEK_PRESERVATION.

Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2).
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
Context (IA1 : invariant liA1) (IB1: invariant liB1).

Hypothesis L1_determ: open_determinate L1.
Hypothesis L2_determ: open_determinate L2.

Section FSIMK.
  
Context (se1 se2: Genv.symtbl) (ccwB: ccworld ccB) (wB1: inv_world IB1) (index: Type)
  (order: index -> index -> Prop)
  (match_states: index -> (state L1) -> (state L2) -> Prop).

Context (MENV: match_senv ccB ccwB se1 se2).

Let fsimk n k i s1 s2 := fsimk ccA ccB se1 se2 ccwB (L1 se1) (L2 se2) index order n k i s1 s2. 

(* Lemma safak_preserved_under_fsimk: forall n k i s1 s2, *)
(*     fsimk n k i s1 s2 -> *)
(*     safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S n) s1 -> *)
(*     safek se2 (L2 se2) (invcc IA1 ccA) (invcc IB1 ccB) (SIF se1) (wB1, ccwB) k s2. *)
(* Proof. *)
(*   induction n; intros until s2; intros FSIM SAFE. *)
(*   - inv FSIM. *)
(*     admit. *)
(*     admit. *)
(*   - inv FSIM. *)
(*     +  *)
(*     (* use receptive to prove that t1**t2 must have length less than *)
(*     1. So we can use SAFE to prove that any step s1 take is also *)
(*     safek *) *)
(* Admitted.     *)

End FSIMK.

End SAFEK_PRESERVATION.
(** *end of Experiment code *)

(** * The following code is experiment code about safek preservation *)

(* The preservation of safety in k step *)

(* Section SAFETYK_PRESERVATION. *)

(* Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2). *)
(* Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2). *)
(* Context (IA1 : invariant liA1) (IB1: invariant liB1). *)

(* Hypothesis L1_determ: open_determinate L1. *)
(* Hypothesis L2_determ: open_determinate L2. *)

(* Section BSIM. *)
  
(* Context se1 se2 ccwB (wB1: inv_world IB1) bsim_index bsim_order bsim_match_states *)
(*   (BSIMP: bsim_properties ccA ccB se1 se2 ccwB (L1 se1) (L2 se2) bsim_index bsim_order (bsim_match_states se1 se2 ccwB)). *)

(* Context (MENV: match_senv ccB ccwB se1 se2). *)

(* Let mst i s1 s2 := bsim_match_states se1 se2 ccwB i s1 s2. *)
  

(* Lemma step_safek: forall s1 s2 t k *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1) *)
(*     (STEP: Step (L1 se1) s1 t s2), *)
(*     safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2. *)
(* Proof. *)
(*   intros.   *)
(*   inv SAFEK; eauto. *)
(*   + constructor. *)
(*   + eapply SAFEK0. eapply plus_one. eauto. *)
(*   + red in SINV. contradiction. *)
(*   + exfalso. *)
(*     eapply od_final_nostep; eauto. *)
(*   + exfalso. *)
(*     eapply od_at_external_nostep; eauto. *)
(* Qed. *)

(* Lemma star_safek: forall s1 s2 t k *)
(*     (STAR: Star (L1 se1) s1 t s2) *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1), *)
(*     safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2. *)
(* Proof. *)
(*   induction 1; intros; eauto. *)
(*   eapply IHSTAR. eapply step_safek; eauto. *)
(* Qed. *)

(* Lemma plus_safek: forall s1 s2 t k *)
(*     (PLUS: Plus (L1 se1) s1 t s2) *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1), *)
(*     safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2. *)
(* Proof. *)
(*   intros. inv PLUS. *)
(*   eapply star_safek; eauto. intros. *)
(*   eapply step_safek; eauto. *)
(* Qed. *)

(* (* The safe index must not be zero *) *)
(* Lemma safek_internal_safe : forall s1 k *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1), *)
(*     safe (L1 se1) s1. *)
(* Proof. *)
(*   unfold safe. induction 2. *)
(*   - inv SAFEK; eauto. *)
(*     red in SINV. contradiction. *)
(*   - eapply IHstar. *)
(*     intros. *)
(*     eapply step_safek; eauto. *)
(* Qed. *)

(* (* Prove by induction on k *) *)
(* (* Key proof of module_total_safek_preservation *) *)
(* Lemma bsim_safek_preservation: forall k s1 s2 i *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1) *)
(*     (MATCH: bsim_match_states se1 se2 ccwB i s1 s2), *)
(*     safek se2 (L2 se2) (invcc IA1 ccA) (invcc IB1 ccB) (SIF se1) (wB1, ccwB) k s2. *)
(* Proof. *)
(*   induction k; intros. *)
(*   econstructor. *)
(*   (* prove s1 is internal safe (to get Smallstep.safe) and then use *)
(*      bsim_progress *) *)
(*   generalize (safek_internal_safe s1 k SAFEK). intros ISAFE1. *)
(*   eapply safe_implies in ISAFE1. *)
(*   generalize (bsim_progress BSIMP i _ MATCH ISAFE1). *)
(*   (* 3 cases of s2 *) *)
(*   intros [(r2 & FINAL2)|[(q2 & ATEXT2)|(t2 & s2' & STEP2)]]. *)
(*   (* s2 is final state *) *)
(*   -  exploit (@bsim_match_final_states liA1); eauto. *)
(*     intros (s1' & r1 & STAT1 & FINAL1 & MR). *)
(*     (* prove s1' is safek *) *)
(*     assert (SAFEK1': safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1'). *)
(*     { eapply star_safek; eauto. } *)
(*     (* s1' have three cases, by determinism, it must be in final state *) *)
(*     inv SAFEK1'. *)
(*     + exfalso. *)
(*       eapply od_final_nostep; eauto. *)
(*     + red in SINV. contradiction. *)
(*     (* final state *) *)
(*     + eapply od_final_determ in FINAL1; eauto. subst. *)
(*       eapply safek_final. eauto. *)
(*       econstructor. split; eauto. *)
(*     + exfalso. *)
(*       eapply od_final_noext; eauto.   *)
(*   (* s2 is at_external state *) *)
(*   - exploit (@bsim_match_external liA1); eauto. *)
(*     intros (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MENV1 & AFEXT1). *)
(*     (* prove s1' is safek *) *)
(*     assert (SAFEK1': safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1'). *)
(*     { eapply star_safek; eauto. } *)
(*     inv SAFEK1'. *)
(*     + exfalso. *)
(*       eapply od_at_external_nostep; eauto. *)
(*     + red in SINV. contradiction. *)
(*     + exfalso. *)
(*       eapply od_final_noext; eauto. *)
(*     (* at_external *) *)
(*     + eapply od_at_external_determ in ATEXT1; eauto. subst. *)
(*       eapply safek_external. eauto. *)
(*       instantiate (1 := (w, ccwA)). *)
(*       (* symtbl_inv *) *)
(*       econstructor. split; eauto. *)
(*       (* query_inv *) *)
(*       econstructor. split; eauto. *)
(*       (* reply *) *)
(*       intros r2 (r1 & RINV1 & MR). *)
(*       exploit AFEXT; eauto. *)
(*       intros (s1'' & AFEXT'' & SAFEK''). *)
(*       (* use AFEXT1 *) *)
(*       exploit AFEXT1. eauto. *)
(*       intros [EXIST MATCHEXT]. *)
(*       exploit EXIST; eauto. intros (s2' & AFEXT2'). *)
(*       exploit MATCHEXT; eauto. *)
(*       intros (s1''' & AFEXT''' & (i' & MATCH')). *)
(*       (* use L1 after_external determinate to show s1'' = s1''' *) *)
(*       eapply od_after_external_determ in AFEXT''; eauto. subst. *)
(*       exists s2'. split; auto. *)
(*       eapply IHk. 2: eapply MATCH'. *)
(*       auto. *)
      
  (* (* s2 can take a step *) *)
  (* - eapply safek_step. eauto. *)
  (*   induction 1 using plus_ind2. *)
  (*   (* may be induction on the index? *) *)
    
  (*   intros. *)
  (*   (* consider that s1 may not take step, which would make inv SAFEK does not work *) *)
  (*   plus_ind2 *)
  (*   exploit (@bsim_simulation liA1); eauto. *)
  (*   intros (i' & s1' & OR & MATCH'). *)
  (*   destruct OR as [PLUS| (STAR & ORD)]. *)
  (*   + eapply  *)
  (*     eapply IHk. 2: eapply MATCH'. *)
  (*     eapply plus_safek; eauto. *)
  (*   + eapply IHk. 2: eapply MATCH'. *)
  (*     eapply star_safek; eauto. *)
(* Admitted. *)

(* Prove by induction on SAFEK *)
(* Key proof of module_total_safek_preservation *)
(* Lemma bsim_safek_preservation: forall k s1 *)
(*     (SAFEK: safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1) *)
(*     s2 i *)
(*     (MATCH: bsim_match_states se1 se2 ccwB i s1 s2), *)
(*     safek se2 (L2 se2) (invcc IA1 ccA) (invcc IB1 ccB) (SIF se1) (wB1, ccwB) k s2. *)
(* Proof. *)
(*   induction 1; intros. *)
(*   - econstructor. *)
(*   - destruct k. constructor. *)
(*     (* show that s2 is safek *) *)
(*     exploit SAFEK. eapply plus_one; eauto. intros SAFEKs2.     *)
(*     (* prove s1 is internal safe (to get Smallstep.safe) and then use *) *)
(*     (*   bsim_progress *) *)
(*     assert (ISAFE1: safe (L1 se1) s1). *)
(*     { red. destruct 1. *)
(*       + right. right. eauto. *)
(*       + eapply safek_internal_safe. eapply SAFEK. *)
(*         econstructor; eauto. eapply star_refl. }     *)
(*     eapply safe_implies in ISAFE1. *)
(*     generalize (bsim_progress BSIMP i _ MATCH ISAFE1). *)
(*     (* 3 cases of s0 *) *)
(*     intros [(r2 & FINAL2)|[(q2 & ATEXT2)|(t2 & s2' & STEP2)]].         *)
(*     (* s0 is final state *) *)
(*     + exploit (@bsim_match_final_states liA1); eauto. *)
(*       intros (s1' & r1 & STAR1 & FINAL1 & MR). *)
(*       (* s1 must not be final state because it can take a step! *) *)
(*       inv STAR1. exfalso. *)
(*       eapply od_final_nostep; eauto.       *)
(*       (* prove s1' is safek *) *)
(*       assert (SAFEK1': safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1'). *)
(*       { eapply SAFEK; eauto. *)
(*         econstructor; eauto. } *)
(*       (* s1' have three cases, by determinism, it must be in final state *) *)
(*       inv SAFEK1'. *)
(*       * exfalso. *)
(*         eapply od_final_nostep; eauto. *)
(*       * red in SINV. contradiction. *)
(*       (* final state *) *)
(*       * eapply od_final_determ in FINAL1; eauto. subst. *)
(*         eapply safek_final. eauto. *)
(*         econstructor. split; eauto. *)
(*       * exfalso. *)
(*         eapply od_final_noext; eauto. *)
(*     (* s1' is at_external state *) *)
(*     + exploit (@bsim_match_external liA1); eauto. *)
(*       intros (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MENV1 & AFEXT1). *)
(*       (* s1 must not be final state because it can take a step! *) *)
(*       inv STAR. exfalso. *)
(*       eapply od_at_external_nostep; eauto. *)
(*       (* prove s1' is safek *) *)
(*       assert (SAFEK1': safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1'). *)
(*       { eapply SAFEK; eauto. *)
(*         econstructor; eauto. } *)
(*       inv SAFEK1'. *)
(*       * exfalso. *)
(*         eapply od_at_external_nostep; eauto. *)
(*       * red in SINV. contradiction. *)
(*       * exfalso. *)
(*         eapply od_final_noext; eauto. *)
(*       (* at_external *) *)
(*       * eapply od_at_external_determ in ATEXT1; eauto. subst. *)
(*         eapply safek_external. eauto. *)
(*         instantiate (1 := (w, ccwA)). *)
(*         (* symtbl_inv *) *)
(*         econstructor. split; eauto. *)
(*         (* query_inv *) *)
(*         econstructor. split; eauto. *)
(*         (* reply *) *)
(*         intros r2 (r1 & RINV1 & MR). *)
(*         exploit AFEXT; eauto. *)
(*         intros (s1'' & AFEXT'' & SAFEK''). *)
(*         (* use AFEXT1 *) *)
(*         exploit AFEXT1. eauto. *)
(*         intros [EXIST MATCHEXT]. *)
(*         exploit EXIST; eauto. intros (s2' & AFEXT2'). *)
(*         exploit MATCHEXT; eauto. *)
(*         intros (s1''' & AFEXT''' & (i' & MATCH')). *)
(*         (* use L1 after_external determinate to show s1'' = s1''' *) *)
(*         eapply od_after_external_determ in AFEXT''; eauto. subst. *)
(*         exists s2'. split; auto. *)
(*         eapply H. 2: eapply MATCH'. *)
(*         auto. *)
      
(*   (* s1' is at_external state *) *)
(*   - exploit (@bsim_match_external liA1); eauto. *)
(*     intros (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MENV1 & AFEXT1). *)
(*     (* prove s1' is safek *) *)
(*     assert (SAFEK1': safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 (S k) s1'). *)
(*     { eapply star_safek; eauto. } *)
(*     inv SAFEK1'. *)
(*     + exfalso. *)
(*       eapply od_at_external_nostep; eauto. *)
(*     + red in SINV. contradiction. *)
(*     + exfalso. *)
(*       eapply od_final_noext; eauto. *)
(*     (* at_external *) *)
(*     + eapply od_at_external_determ in ATEXT1; eauto. subst. *)
(*       eapply safek_external. eauto. *)
(*       instantiate (1 := (w, ccwA)). *)
(*       (* symtbl_inv *) *)
(*       econstructor. split; eauto. *)
(*       (* query_inv *) *)
(*       econstructor. split; eauto. *)
(*       (* reply *) *)
(*       intros r2 (r1 & RINV1 & MR). *)
(*       exploit AFEXT; eauto. *)
(*       intros (s1'' & AFEXT'' & SAFEK''). *)
(*       (* use AFEXT1 *) *)
(*       exploit AFEXT1. eauto. *)
(*       intros [EXIST MATCHEXT]. *)
(*       exploit EXIST; eauto. intros (s2' & AFEXT2'). *)
(*       exploit MATCHEXT; eauto. *)
(*       intros (s1''' & AFEXT''' & (i' & MATCH')). *)
(*       (* use L1 after_external determinate to show s1'' = s1''' *) *)
(*       eapply od_after_external_determ in AFEXT''; eauto. subst. *)
(*       exists s2'. split; auto. *)
(*       eapply IHk. 2: eapply MATCH'. *)
(*       auto. *)
(*   -  *)
(*     exploit (@bsim_simulation liA1); eauto. *)
(*     intros (i' & s1' & OR & MATCH'). *)
(*     destruct OR as [PLUS| (STAR & ORD)]. *)
(*     + eapply  *)
(*       eapply IHk. 2: eapply MATCH'. *)
(*       eapply plus_safek; eauto. *)
(*     + eapply IHk. 2: eapply MATCH'. *)
(*       eapply star_safek; eauto. *)
(* Admitted. *)
      
(* End BSIM. *)


(* Lemma module_total_safek_preservation: *)
(*   module_total_safek L1 IA1 IB1 -> *)
(*   backward_simulation ccA ccB L1 L2 -> *)
(*   module_total_safek L2 (invcc IA1 ccA) (invcc IB1 ccB). *)
(* Proof. *)
(*   intros SAFE [BSIM]. *)
(*   red. intros se2 VSE2. *)
(*   red. intros (wB1 & ccwB) (se1 & SYM1 & MENV). *)
(*   intros q2 VQ2 (q1 & QINV2 & MQ). *)
(*   assert (VSE1: Genv.valid_for (skel L1) se1). *)
(*   { eapply match_senv_valid_for; eauto. *)
(*     erewrite bsim_skel; eauto. } *)
(*   inv BSIM. *)
(*   generalize (bsim_lts se1 se2 ccwB MENV VSE1). intros BSIMP. *)
(*   assert (VQ1: valid_query (L1 se1) q1 = true). *)
(*   { erewrite <- bsim_match_valid_query; eauto. }   *)
(*   (* initial_match *) *)
(*   exploit SAFE; eauto. *)
(*   intros (s1 & INIT1 & SAFE1). *)
(*   edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto. *)
(*   exploit EXIST; eauto. *)
(*   intros (s2 & INIT2). *)
(*   exploit MATCH; eauto. *)
(*   intros (s1' & INIT1' & (i & MST)). *)
(*   (* use initial_determ *) *)
(*   eapply od_initial_determ in INIT1; eauto. subst. *)
(*   (* use s2 as the initial state of L2 *) *)
(*   exists s2. split. auto. *)
(*   (** Key part: prove safek by generalization of s2 *) *)
(*   intros. exploit bsim_safek_preservation; eauto. *)
(* Qed. *)



(** *End of experiment code  *)







(** Cannot defined: Composition of safety_invariant (e.g., not_stuck
or partial_safe). Maybe we cannot define a general composed SI because
SI depends on the specific definition of the lts. For example,
at_external in one lts is an internal step in the composed lts *)

(* Let SI1 := SI (state L1). *)
(* Let SI2 := SI (state L2). *)
(* Let SI3 := SI (state L). *)

(* We need to prove SI3 implies SI1 or SI2 if L = L1 ⊕ L2 *)

(* How to use parametricity (or something else?) to prove this?? *)
(* Lemma parametricity_SI: forall se s3, *)
(*     compose L1 L2 = Some L -> *)
(*     SI3 (L se) s3 -> *)
(* how to construct s1 and s2 ????? *)
       (* SI1 (L1 se) s1 \/ SI2 (L2 se) s2 *)

(* Lemma lts_safek_le {liA liB S} se (L: lts liA liB S) (IA: invariant liA) (IB: invariant liB) (SI: lts liA liB S -> S -> Prop) (wI: inv_world IB): forall k1 k2 s, *)
(*     (k1 <= k2)%nat -> *)
(*     safek se L IA IB SI wI k2 s -> *)
(*     safek se L IA IB SI wI k1 s. *)
(* Admitted. *)
  
Section SAFEK_INTERNAL.

Context {li} (I: invariant li) (L: bool -> semantics li li).
Context (sk: AST.program unit unit) (se: Genv.symtbl).


(** Proof strategy of the compositionality of safek:

1. Definition of wfk_state. We define a general predicate (called
wfk_state) on the state of the composed semantics (i.e., list of
frame) to act as the safek in the composed semantics. It takes an
initial world of the composed semantics, the list of frame and a list
of natural number represting "k step safe" at each frame. The key
component of wfk_state is wfk_frames which takes similar arguments but
returns the emitted world from the top of the frames.

2. Lemma wf_state_safek. This lemma is the key of the composition
proof. It says that if the frames are well-formed (i.e., each frame is
safe in k steps) and the k step safety of the composed semantics is
larger than any k' step in the frames, then the state of the compose d
semantics is safe in k step.

2.1. To prove this lemma, we extract the top frame and use safety in
each module to perform case analysis of this frame. This frame can
take an internal step, at_external and final. At each case, we
construct the step of the composed semantics. For example, an internal
step in the top frame can be an internal step (step_internal) in the
composed semantics, but not a step_push/pop. But this properties
require that the module semantics are open_determinate.

3. Compositionality Lemma, just construct initial_state and apply
wf_state_safek.

 *)

(* For now, just use SIF as the SI. w is the initial world. The return
world is the world omitted by the at_external state in the top of the
frame *)
Inductive wfk_frames w : list (frame L) -> list nat -> inv_world I -> Prop :=
| wfk_frames_nil: wfk_frames w nil nil w
| wfk_frames_cons: forall i s q w1 w2 fms k kl
    (WF: wfk_frames w fms kl w1)
    (VSE1: symtbl_inv I w1 se)
    (EXT: at_external (L i se) s q)
    (WTQ: query_inv I w2 q)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I w2 r ->
                 exists s', after_external (L i se) s r s'
                       (* Is (forall k) too strong? The choice of k depends on w2... *)
                     /\ safek se (L i se) I I (SIF se) w1 k s'),
    wfk_frames w ((st L i s) :: fms) (k :: kl) w2.

Inductive wfk_state w: list (frame L) -> list nat -> Prop :=
| wfk_state_cons: forall i s frs w1 k kl
    (WFS: wfk_frames w frs kl w1)
    (VSE: symtbl_inv I w1 se)
    (SAFEK: safek se (L i se) I I (SIF se) w1 k s),
    wfk_state w (st L i s :: frs) (k :: kl).

Hypothesis L_determ: forall i, open_determinate (L i).
Hypothesis (SAFE: forall i, module_safek_se (L i) I I (SIF se) se).

Lemma wf_state_safek: forall k kl s w
    (WF: wfk_state w s kl)
    (GT: forall n, In n kl -> (k <= n)%nat),
    safek se (SmallstepLinking.semantics L sk se) I I (SIF se) w k s.
Proof.
  induction k; intros.
  econstructor.
  inv WF.
  (* s0 can make one step *)
  exploit GT. econstructor. eauto. intros LE.
  destruct k0. lia.
  inv SAFEK.
  (* s0 takes one module local internal step *)
  - eapply safek_step.
    eapply step_internal; eauto.
    intros t1 s1 STEP1.
    (* case analysis of STEP1 *)
    inv STEP1; subst_dep.
    (* internal step of (L i) *)
    * eapply IHk.
      instantiate (1 := k0 :: kl0).      
      econstructor; eauto.
      intros. inv H. lia. exploit GT. eapply in_cons. eauto. lia.
    (* contradition: s0 cannot take internal step and external step meanwhile *)
    * exfalso.
      eapply od_at_external_nostep; eauto.
      eapply L_determ; eauto.
    (* contradition: final and one step cannot appear meanwhile *)
    * exfalso.
      eapply od_final_nostep; eauto.
      eapply L_determ; eauto.
  (* SIF is False *)
  - red in SINV. contradiction.
  (* s0 is final state *)
  - destruct frs. 
    (* case 1: final state in the composed semantics *)
    + eapply safek_final. econstructor; eauto.
      inv WFS. auto.
    (* case 2: step_pop *)
    + destruct f. inv WFS. subst_dep.
      exploit PGS; eauto. intros (s' & AFEXT & SAFEEXT).      
      eapply safek_step.
      (* can take a step *)
      eapply step_pop; eauto.
      (* all next steps are safek *)
      intros.
      (* use determinism to show that s2' can be only the after_external state *)
      inv H; subst_dep.
      * exfalso.
        eapply od_final_nostep; eauto.
        eapply L_determ; eauto.
      (* s0 cannot be final and at_external states *)
      * exfalso.
        eapply od_final_noext; eauto.
        eapply L_determ; eauto.
      * (* use open_determinate to show the reply and after_external state are equal *)
        eapply od_final_determ in FINAL; eauto. subst.
        eapply od_after_external_determ in AFEXT; eauto. subst.
        (* use IHk *)
        eapply IHk. instantiate (1 := k1 :: kl).
        econstructor; eauto.
        exploit GT. instantiate (1 := k1). intuition. intros.
        intros. inv H0. lia.
        exploit GT. eapply in_cons. eapply in_cons; eauto.
        lia.
        1-2: eapply L_determ; eauto.
  (* s0 is at_external state *)
  - destruct (orb (valid_query (L true se) q) (valid_query (L false se) q)) eqn: VQ.
    (* case1: step_push *)
    + eapply orb_true_iff in VQ.      
      destruct VQ as [VQ1|VQ2].
      * (* construct initial state *)
        generalize (SAFE true w0 SYMBINV q VQ1 QINV).
        intros (inits & INIT & SAFEK).
        eapply safek_step. eapply step_push; eauto.
        intros.
        (* internal step of the composed semantics must be step_push (by determinism) *)
        inv H; subst_dep.
        -- exfalso.
           eapply od_at_external_nostep; eauto.
           eapply L_determ; eauto.
        -- eapply od_at_external_determ in ATEXT; eauto. subst.
           (* what if q is valid in two modules??? *)
           generalize (SAFE j w0 SYMBINV q H6 QINV).
           intros (initj & INITj & SAFEKj).
           eapply od_initial_determ in H7; eauto. subst.
           eapply IHk. instantiate (1 := k :: k0 :: kl0).
           econstructor. econstructor; eauto. auto.
           eauto.
           (* Gt properties *)
           intros. inv H. lia.
           inv H0. exploit GT. instantiate (1 := S n). econstructor. auto.
           lia.
           exploit GT. eapply in_cons. eauto. lia.
           1-2: eapply L_determ; eauto.
        -- exfalso.
           eapply od_final_noext; eauto.
           eapply L_determ; eauto.
      (* The same as the above case *)
      * (* construct initial state *)
        generalize (SAFE false w0 SYMBINV q VQ2 QINV).
        intros (inits & INIT & SAFEK).
        eapply safek_step. eapply step_push; eauto.
        intros.
        (* internal step of the composed semantics must be step_push (by determinism) *)
        inv H; subst_dep.
        -- exfalso.
           eapply od_at_external_nostep; eauto.
           eapply L_determ; eauto.
        -- eapply od_at_external_determ in ATEXT; eauto. subst.
           (* what if q is valid in two modules??? *)
           generalize (SAFE j w0 SYMBINV q H6 QINV).
           intros (initj & INITj & SAFEKj).
           eapply od_initial_determ in H7; eauto. subst.
           eapply IHk. instantiate (1 := k :: k0 :: kl0).
           econstructor. econstructor; eauto. auto.
           eauto.
           (* Gt properties *)
           intros. inv H. lia.
           inv H0. exploit GT. instantiate (1 := S n). econstructor. auto.
           lia.
           exploit GT. eapply in_cons. eauto. lia.
           1-2: eapply L_determ; eauto.
        -- exfalso.
           eapply od_final_noext; eauto.
           eapply L_determ; eauto.
    (* case 2: composed semantics is at_external *)
    + eapply safek_external.
      econstructor. eauto.
      eapply orb_false_iff in VQ. destruct VQ.
      destruct j; auto.
      eauto. eauto.
      intros.
      exploit AFEXT; eauto.
      intros (s1 & AFEXT1 & SAFEK1).
      exists (st L i s1 :: frs). split.
      econstructor; eauto.
      (* safek *)
      eapply IHk. instantiate (1 := k0 :: kl0).
      econstructor; eauto.
      intros. inv H0.
      exploit GT. econstructor. eauto. lia.
      exploit GT. eapply in_cons. eauto. lia.
Qed.
  
End SAFEK_INTERNAL.
  
Section COMPOSE_SAFETY.

Context {li} (I: invariant li) (L1 L2 L: semantics li li).
    
Hypothesis L1_determ: open_determinate L1.
Hypothesis L2_determ: open_determinate L2.

Lemma compose_total_safek:
  module_total_safek L1 I I ->
  module_total_safek L2 I I ->
  compose L1 L2 = Some L ->
  module_total_safek L I I.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  red. intros se VALID w INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  { destruct i.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto. }
  assert (SAFE: forall i, module_safek_se (L i) I I (SIF se) se).
  { intros i. generalize (VALIDSE i). intros VSE.
    destruct i.
    eapply SAFE1; eauto.
    eapply SAFE2; eauto. }
  (* prove lts_safek *)
  red. intros q VQ QINV.
  assert (VQi: exists i, valid_query (L i se) q = true).
  { simpl in VQ. unfold SmallstepLinking.valid_query in VQ.
    apply orb_true_iff in VQ. destruct VQ; eauto. }
  destruct VQi as (iq & VQi).
  (* construct initial state *)
  exploit SAFE; eauto. intros (inits & INIT & SAFEK).
  exists (st L iq inits :: nil). split.
  econstructor; eauto.
  (* prove safek *)
  intros. eapply wf_state_safek; eauto.
  (* open_determinate *)
  destruct i; auto.
  (* wfk_state *)
  instantiate (1 := k :: nil). econstructor; eauto. econstructor.
  intros. inv H. lia. inv H0.
Qed.


End COMPOSE_SAFETY.

End SAFEK.



(** Unfinished: The following code is a more general module_safety
property which supports different invariant in incoming side and
outgoing side *)

Definition compose_invariant {li} (incoming: bool) (Ia Ib: invariant li) :=
  {| inv_world := (inv_world Ia * inv_world Ib);
    symtbl_inv '(wa, wb) se := symtbl_inv Ia wa se /\ symtbl_inv Ib wb se;
    query_inv '(wa, wb) q := if incoming then (query_inv Ia wa q /\ query_inv Ib wb q)
                             else (query_inv Ia wa q \/ query_inv Ib wb q);
    reply_inv '(wa, wb) r := if incoming then (reply_inv Ia wa r \/ reply_inv Ib wb r)
                             else (reply_inv Ia wa r \/ reply_inv Ib wb r); |}.

(* The starting world of a frame, defined by sum type *)
Variant frame_world {li} (I: bool -> invariant li) := fw (i: bool) (w: inv_world (I i)).

(* Propeties of reachable state in composed semantics *)
Section REACH.

Context {li} (I1 I2: invariant li) (L: bool -> semantics li li). 
Context (se: Genv.symtbl).
Context (w: inv_world I1 * inv_world I2).

Let Iin := fun i:bool => if i then I1 else I2.
Let Iout := fun i:bool => if i then I2 else I1.

Definition getw (i: bool) (w: inv_world I1 * inv_world I2) : inv_world (Iin i) :=
  match i with
  | true => (fst w)
  | false => (snd w)
  end.


Definition setw (i: bool) (w1: inv_world I1 * inv_world I2) : inv_world (Iout i) -> inv_world I1 * inv_world I2 :=
  match i with 
  | true => fun w2 => (fst w1, w2)
  | false => fun w2 => (w2, snd w1)
  end.

(* A generalized wf_state specifying rechable property and invariant world in the frame *)

(* Inductive wf_frames : list (frame L) -> (inv_world I1 * inv_world I2) -> Prop := *)
(* | wf_frames_nil: wf_frames nil w *)
(* | wf_frames_cons: forall i s q w1 w2 fms *)
(*     (WF: wf_frames fms w1) *)
(*     (VSE1: symtbl_inv (Iin i) (getw i w1) se) *)
(*     (FREACH: reachable (Iout i) (Iin i) (L i se) (getw i w1) s) *)
(*     (EXT: at_external (L i se) s q) *)
(*     (WTQ: query_inv (Iout i) w2 q) *)
(*     (PGS: forall r, reply_inv (Iout i) w2 r -> *)
(*                exists s', after_external (L i se) s r s'), *)
(*     wf_frames ((st L i s) :: fms) (setw i w1 w2). *)


(* Inductive wf_state : list (frame L) -> Prop := *)
(* | wf_state_cons: forall i s k w1 *)
(*     (WFS: wf_frames k w1) *)
(*     (VSE: symtbl_inv (Iin i) (getw i w1) se) *)
(*     (SREACH: reachable (Iout i) (Iin i) (L i se) (getw i w1) s),                    *)
(*     wf_state (st L i s :: k). *)

End REACH.

(** Proof of compositionality of module safe *)

Lemma compose_safety_general {li} (I1 I2: invariant li) L1 L2 L:
  module_safe L1 I2 I1 not_stuck ->
  module_safe L2 I1 I2 not_stuck ->
  compose L1 L2 = Some L ->
  module_safe L (compose_invariant false I1 I2) (compose_invariant true I1 I2) not_stuck.
Proof.
  intros SAFE1 SAFE2 COMP. unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  set (L := fun i:bool => if i then L1 else L2).
  set (Iin := fun i:bool => if i then I1 else I2).
  set (Iout := fun i:bool => if i then I2 else I1).
  red. intros se VALID w INV.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  destruct i.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  eapply Genv.valid_for_linkorder.
  eapply (link_linkorder _ _ _ Hsk). eauto.
  assert (SAFE: forall i, module_safe_se (L i) (Iout i) (Iin i) not_stuck se).
  { intros i. generalize (VALIDSE i). intros VSE.
    destruct i; simpl; auto. }
  constructor.
  (* rechable not stuck *)
Admitted.

(** End of this unfinished general compose_safety  *)

(* Record bsim_invariant {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) : Type := *)
(*   { *)
(*     (* incoming_query2 and outgoing_query2 are used to establish *)
(*     match_states between reachable states *) *)
(*     incoming_query2: forall w2 se2, *)
(*       symtbl_inv I2 w2 se2 -> *)
(*       exists ccw w1 se1, *)
(*         match_senv cc ccw se1 se2 *)
(*         /\ symtbl_inv I1 w1 se1 *)
(*         /\ (forall q2, query_inv I2 w2 q2 -> *)
(*                  exists q1, match_query cc ccw q1 q2 *)
(*                        /\ query_inv I1 w1 q1 *)
(*                        /\ (* outgoing_reply1 is embedded here because it is *)
(*                             stated in w2. It is used to establish progress *)
(*                             properties *) *)
(*                          forall r1 r2, reply_inv I1 w1 r1 -> *)
(*                                   match_reply cc ccw r1 r2 -> *)
(*                                   reply_inv I2 w2 r2); *)

(*     (** So ugly! used to establish reachable_match *) *)
(*     outgoing_query2: forall w1 w2 ccw q1 q2 r2, *)
(*       query_inv I2 w2 q2 -> *)
(*       match_query cc ccw q1 q2 -> *)
(*       query_inv I1 w1 q1 -> *)
(*       (* incoming_reply2 is embedded here *) *)
(*       reply_inv I2 w2 r2 -> *)
(*       exists r1, reply_inv I1 w1 r1 /\ *)
(*               match_reply cc ccw r1 r2; *)

(*     (* outgoing_query1 and incoming_reply1 are used to establish *)
(*     progress properties *) *)
(*     outgoing_query1: forall w1 ccw q1 q2 se1 se2, *)
(*       query_inv I1 w1 q1 -> *)
(*       symtbl_inv I1 w1 se1 -> *)
(*       match_query cc ccw q1 q2 -> *)
(*       match_senv cc ccw se1 se2 -> *)
(*       exists w2 , query_inv I2 w2 q2 *)
(*                 /\ symtbl_inv I2 w2 se2 *)
(*                 /\ (* why here is incoming_reply2 ??? to establish after_external progress *) *)
(*                   forall r2, reply_inv I2 w2 r2 -> *)
(*                         exists r1, reply_inv I1 w1 r1 *)
(*                               /\ match_reply cc ccw r1 r2;     *)
    
(*   }. *)


(* What is this? *)
Record preservable_inv {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) : Type :=
  { query_inv_preserve: forall w1 wcc wcc' q1 q2 q1',
      query_inv I1 w1 q1 ->
      match_query cc wcc q1 q2 ->
      match_query cc wcc' q1' q2 ->
      query_inv I1 w1 q1';
  }.


(* Using constructive target invariant to prove safe preservatin *)
(* Section SAFETY_PRESERVATION_CONSTRUCT. *)

(* Context {li1 li2} (cc: callconv li1 li2). *)
(* Context (L1: semantics li1 li1) (L2: semantics li2 li2). *)
(* Context (I1 : invariant li1) (I2: invariant li2). *)

(* Hypothesis (INVPRE: preservable_inv cc I1). *)

(* Section BSIM. *)
  
(* Context se1 se2 wcc (w1: inv_world I1) bsim_index bsim_order bsim_match_states *)
(*   (BSIMP: bsim_properties cc cc se1 se2 wcc (L1 se1) (L2 se2) bsim_index bsim_order (bsim_match_states se1 se2 wcc)). *)

(* Context (MENV: match_senv cc wcc se1 se2). *)

(* (* Hypothesis (INQ: forall q1' wcc' wA', *) *)
(* (*                match_query cc wcc' q1' q2 -> *) *)
(* (*                query_inv IA wA' q1 -> *) *)
(* (*                query_inv IA wA' q1'). *) *)


(* Let match_states := bsim_match_states se1 se2 wcc. *)

(* Lemma bsim_simulation_star_under_lts_safe: forall s2 t s2', *)
(*     Star (L2 se2) s2 t s2' -> *)
(*     forall i s1, safe (L1 se1) s1 -> *)
(*             match_states i s1 s2 -> *)
(*             exists i', exists s1', Star (L1 se1) s1 t s1' /\ match_states i' s1' s2'. *)
(* Proof. *)
(*   induction 1; intros. *)
(*   exists i; exists s1; split; auto. apply star_refl. *)
(*   exploit (@bsim_simulation li1); eauto. *)
(*   eapply safe_implies. auto. *)
(*   intros [i' [s2' [A B]]]. *)
(*   exploit IHstar. 2: eauto. *)
(*   destruct A. *)
(*   eapply star_safe. eapply plus_star; eauto. auto. *)
(*   destruct H4. eapply star_safe; eauto.   *)
(*   intros [i'' [s2'' [C D]]]. *)
(*   exists i''; exists s2''; split; auto. eapply star_trans; eauto. *)
(*   intuition auto. apply plus_star; auto. *)
(* Qed. *)


(* Lemma bsim_reachable_match: forall s2, *)
(*     reachable (invcc_out I1 cc) (invcc_in I1 cc) (L2 se2) (w1, wcc) s2 -> *)
(*     lts_safe se1 (L1 se1) I1 I1 not_stuck w1 -> *)
(*     exists s1 i, reachable I1 I1 (L1 se1) w1 s1 *)
(*             /\ bsim_match_states se1 se2 wcc i s1 s2. *)
(* Proof. *)
(*   induction 1; intros SAFE. *)
(*   (* initial_reach *) *)
(*   - destruct WT as (q1 & MQ & QINV1).  *)
(*     assert (VQ1: valid_query (L1 se1) q1 = true). *)
(*     { erewrite <- bsim_match_valid_query; eauto. } *)
(*     (* initial_match *) *)
(*     edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto. *)
(*     (* L1 is not stuck in initial states *) *)
(*     exploit (@initial_progress li1); eauto. *)
(*     intros (s1 & INIT1). *)
(*     exploit EXIST; eauto. intros INIT2. *)
(*     exploit MATCH. eapply INIT1. eapply INIT. *)
(*     intros (s1' & INIT1' & (i & MATCH')). *)
(*     (* prove bsim_simulation_star *) *)
(*     exploit bsim_simulation_star_under_lts_safe; eauto. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*     eapply initial_reach; eauto. eapply star_refl. *)
(*     intros (i' & s1'' & STAR1 & MATCH''). *)
(*     exists s1'', i'. split. *)
(*     eapply star_reachable. eauto. *)
(*     eapply initial_reach; eauto. *)
(*     eapply star_refl. auto. *)
(*   (* external reach *) *)
(*   - exploit IHreachable; eauto. *)
(*     intros (s1' & i1 & REACH1 & MATCH1). *)
(*     (* external_simulation *) *)
(*     exploit (@bsim_match_external li1); eauto. *)
(*     eapply safe_implies. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*     intros (wcc' & s1'' & q1 & STAR1 & ATEXT1 & MQ1 & MSE1 & AFEXT1). *)
(*     eapply star_reachable in STAR1; eauto. *)
(*     (* external_progress in L1 *) *)
(*     exploit (@external_progress li1); eauto. *)
(*     intros (w1' & SYM1 & QINV1 & AFEXT2). *)
(*     (* get the well-typed query and reply *) *)
(*     exploit WTR; eauto. intros (r1 & MQ & RINV1). *)
(*     (* construct the matched after_external state *) *)
(*     exploit AFEXT1; eauto. *)
(*     intros [EXIST MATCH]. *)
(*     exploit AFEXT2; eauto. *)
(*     intros (s' & AFEXT1''). *)
(*     exploit MATCH; eauto. *)
(*     intros (s1'0 & AFEXT'0 & (i & MATCH')). *)
(*     (* prove bsim_simulation_star *) *)
(*     exploit bsim_simulation_star_under_lts_safe; eauto. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*     eapply external_reach; eauto. eapply star_refl. *)
(*     intros (i' & s1''0 & STAR2 & MATCH''). *)
(*     exists s1''0, i'. split; auto. *)
(*     eapply star_reachable. eauto. *)
(*     eapply external_reach; eauto. *)
(*     eapply star_refl. *)
(* Qed. *)

(* End BSIM. *)
  
(* Lemma module_safety_preservation:   *)
(*   module_safe L1 I1 I1 not_stuck -> *)
(*   backward_simulation cc cc L1 L2 -> *)
(*   module_safe L2 (invcc_out I1 cc) (invcc_in I1 cc) not_stuck. *)
(* Proof. *)
(*   intros SAFE [BSIM]. *)
(*   red. intros se2 VSE2. *)
(*   red. intros (w1, wcc) SYM2. *)
(*   (* construct se1 *) *)
(*   destruct SYM2 as (se1 & SYM1 & MSE). *)
(*   (* generalize (@incoming_query2 li1 li2 cc I1 I2 BSIM_INV _ _ SYM2). *) *)
(*   (* intros (wcc & w1 & se1 & MSE & SYM1 & INQ).    *) *)
(*   assert (VSE1: Genv.valid_for (skel L1) se1). *)
(*   { eapply match_senv_valid_for; eauto. *)
(*     erewrite bsim_skel; eauto. } *)
(*   exploit SAFE; eauto. *)
(*   intros LTSSAFE1. *)
(*   destruct BSIM. *)
(*   generalize (bsim_lts se1 se2 wcc MSE VSE1). intros BSIMP. *)
(*   econstructor. *)
(*   (* reachable_safe *) *)
(*   - intros s2 REACH2. *)
(*     exploit bsim_reachable_match; eauto. *)
(*     intros (s1 & i & REACH1 & MATCH). *)
(*     (* s1 is not_stuck *) *)
(*     exploit (@reachable_safe li1); eauto. *)
(*     (** NOTSTUCK1 is useless because one step in target program may *)
(*     correspond to multiple steps in source program, so the property of *)
(*     only one step not stuck in source program is not useful *) *)
(*     intros NOTSTUCK1. *)
(*     (* We use bsim_progress! *) *)
(*     eapply bsim_progress; eauto. *)
(*     eapply safe_implies. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*   (* initial progress *) *)
(*   - intros q2 VQ QINV2. *)
(*     destruct QINV2 as (q1 & QINV1 & MQ). *)
(*     (* exploit INQ; eauto. *) *)
(*     (* intros (q1 & MQ & QINV1 & FINAL). *) *)
(*     assert (VQ1: valid_query (L1 se1) q1 = true). *)
(*     { erewrite <- bsim_match_valid_query; eauto. } *)
(*     (* initial_match *) *)
(*     edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto. *)
(*     (* L1 is not stuck in initial states *) *)
(*     exploit (@initial_progress li1); eauto. *)
(*     intros (s1 & INIT). eapply EXIST. eauto. *)
(*   (* external_progress *) *)
(*   - intros s2 q2 REACH2 ATEXT2. *)
(*     exploit bsim_reachable_match; eauto. *)
(*     intros (s1 & i & REACH1 & MATCH). *)
(*     (* external_simulation *) *)
(*     exploit (@bsim_match_external li1); eauto. *)
(*     eapply safe_implies. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*     intros (wcc' & s1'' & q1 & STAR1 & ATEXT1 & MQ1 & MSE1 & AFEXT1). *)
(*     eapply star_reachable in STAR1; eauto. *)
(*     (* q1 is well-typed *) *)
(*     exploit (@external_progress li1);eauto. *)
(*     intros (w1' & SYM1' & QINV1 & AFEXT1'). *)
(*     (* construct w2 and q2 *) *)
(*     exists w1'. *)
(*     (* generalize (@outgoing_query1 li1 li2 cc I1 I2 BSIM_INV  _ _ _ _ _ _ QINV1 SYM1' MQ1 MSE1). *) *)
(*     (* intros (w2' & se2' & QINV2 & AFEXT2'). *) *)
(*     (* exists w2'. *) repeat apply conj; auto. *)
(*     simpl. exists se1, wcc'. auto. *)
(*     simpl. intros. eapply query_inv_preserve; eauto. *)
(*     simpl. intros r2 QINV2. *)
(*     exploit QINV2; eauto. intros (r1 & MR & RINV1). *)
(*     exploit AFEXT1'; eauto. intros (s1''' & A). *)
(*     exploit AFEXT1; eauto. intros [EXIST MATCH1]. *)
(*     eapply EXIST. eauto. *)
(*   (* final progress *) *)
(*   - intros s r REACH2 FS2. *)
(*     simpl. *)
(*     exploit bsim_reachable_match; eauto. *)
(*     intros (s1 & i & REACH1 & MATCH). *)
(*     (* final_simulation *) *)
(*     edestruct (@bsim_match_final_states li1) as (s1' & r1 & STAR & FS1 & MR); eauto. *)
(*     eapply safe_implies. *)
(*     eapply lts_safe_reachable_safe; eauto. *)
(*     exists r1. split; eauto. *)
(*     eapply final_progress. eauto. *)
(*     eapply star_reachable; eauto. *)
(*     auto. *)
(* Qed. *)
    
    
(* End SAFETY_PRESERVATION_CONSTRUCT. *)


(* similar to ccref *)
Record inv_alternate {li1 li2} (cc: callconv li1 li2) (I1: invariant li1) (I2: invariant li2) : Type :=
  {
    (* incoming_query2 and outgoing_query2 are used to establish *)
(*     match_states between reachable states *)
    incoming_query2: forall w2 se2,
      symtbl_inv I2 w2 se2 ->
      exists ccw w1 se1,
        match_senv cc ccw se1 se2
        /\ symtbl_inv I1 w1 se1
        /\ (forall q2, query_inv I2 w2 q2 ->
                 exists q1, match_query cc ccw q1 q2
                       /\ query_inv I1 w1 q1
                       /\ (* outgoing_reply1 is embedded here because it is *)
(*                             stated in w2. It is used to establish progress *)
(*                             properties *)
                         forall r1 r2, reply_inv I1 w1 r1 ->
                                  match_reply cc ccw r1 r2 ->
                                  reply_inv I2 w2 r2);

    (* outgoing_query1 and incoming_reply1 are used to establish *)
(*     progress properties *)
    outgoing_query1: forall w1 ccw q1 q2 se1 se2,
      query_inv I1 w1 q1 ->
      symtbl_inv I1 w1 se1 ->
      match_query cc ccw q1 q2 ->
      match_senv cc ccw se1 se2 ->
      exists w2 , query_inv I2 w2 q2
                /\ symtbl_inv I2 w2 se2
                /\ (* why here is incoming_reply2 ??? to establish after_external progress *)
                  forall r2, reply_inv I2 w2 r2 ->
                        exists r1, reply_inv I1 w1 r1
                              /\ match_reply cc ccw r1 r2;
    
  }.


Record inv_determinate {li} (I: invariant li) : Type :=
  { outgoing_query_det: forall w w' q,
      query_inv I w q ->
      query_inv I w' q ->
      w = w';
  }.


(** Safety Preservation Under Backward Simulation *)

Section SAFETY_PRESERVATION.

Context {li1 li2} (cc: callconv li1 li2).
Context (L1: semantics li1 li1) (L2: semantics li2 li2).
Context (I1 : invariant li1) (I2: invariant li2).

Hypothesis BSIM_INV: inv_alternate cc I1 I2.

Hypothesis INV_DET: inv_determinate I2.

Section BSIM.
  
Context se1 se2 wcc (w1: inv_world I1) (w2: inv_world I2) bsim_index bsim_order bsim_match_states            
  (BSIMP: bsim_properties cc cc se1 se2 wcc (L1 se1) (L2 se2) bsim_index bsim_order (bsim_match_states se1 se2 wcc)).

Context (MENV: match_senv cc wcc se1 se2).

Hypothesis (INQ: forall q2 : query li2,
               query_inv I2 w2 q2 ->
               exists q1 : query li1,
                 match_query cc wcc q1 q2 /\
                   query_inv I1 w1 q1 /\
                   (forall (r1 : reply li1) (r2 : reply li2),
                       reply_inv I1 w1 r1 -> match_reply cc wcc r1 r2 -> reply_inv I2 w2 r2)).


Let match_states := bsim_match_states se1 se2 wcc.

Lemma bsim_simulation_star_under_lts_safe: forall s2 t s2',
    Star (L2 se2) s2 t s2' ->
    forall i s1, safe (L1 se1) s1 ->
            match_states i s1 s2 ->
            exists i', exists s1', Star (L1 se1) s1 t s1' /\ match_states i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s1; split; auto. apply star_refl.
  exploit (@bsim_simulation li1); eauto.
  eapply safe_implies. auto.
  intros [i' [s2' [A B]]].
  exploit IHstar. 2: eauto.
  destruct A.
  eapply star_safe. eapply plus_star; eauto. auto.
  destruct H4. eapply star_safe; eauto.  
  intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition auto. apply plus_star; auto.
Qed.


Lemma bsim_reachable_match: forall s2,
    reachable I2 I2 (L2 se2) w2 s2 ->
    lts_safe se1 (L1 se1) I1 I1 not_stuck w1 ->
    exists s1 i, reachable I1 I1 (L1 se1) w1 s1
            /\ bsim_match_states se1 se2 wcc i s1 s2
            /\ (forall (r1 : reply li1) (r2 : reply li2),
                       reply_inv I1 w1 r1 -> match_reply cc wcc r1 r2 -> reply_inv I2 w2 r2).
Proof.
  induction 1; intros SAFE.
  (* initial_reach *)
  - exploit INQ; eauto.
    intros (q1 & MQ & QINV1 & FINAL).    
    assert (VQ1: valid_query (L1 se1) q1 = true).
    { erewrite <- bsim_match_valid_query; eauto. }
    (* initial_match *)
    edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
    (* L1 is not stuck in initial states *)
    exploit (@initial_progress li1); eauto.
    intros (s1 & INIT1).
    exploit EXIST; eauto. intros INIT2.
    exploit MATCH. eapply INIT1. eapply INIT.
    intros (s1' & INIT1' & (i & MATCH')).
    (* prove bsim_simulation_star *)
    exploit bsim_simulation_star_under_lts_safe; eauto.
    eapply lts_safe_reachable_safe; eauto.
    eapply initial_reach; eauto. eapply star_refl.
    intros (i' & s1'' & STAR1 & MATCH'').
    exists s1'', i'. split.
    eapply star_reachable. eauto.
    eapply initial_reach; eauto.
    eapply star_refl. auto.
  (* external reach *)
  - exploit IHreachable; eauto.
    intros (s1' & i1 & REACH1 & MATCH1 & FINAL).
    (* external_simulation *)
    exploit (@bsim_match_external li1); eauto.
    eapply safe_implies.
    eapply lts_safe_reachable_safe; eauto.
    intros (wcc' & s1'' & q1 & STAR1 & ATEXT1 & MQ1 & MSE1 & AFEXT1).
    eapply star_reachable in STAR1; eauto.
    (* external_progress in L1 *)
    exploit (@external_progress li1); eauto.
    intros (w1' & SYM1 & QINV1 & AFEXT2).    
    (* get the reply *)   
    exploit (@outgoing_query1 li1 li2); eauto.
    intros (w2' & QINV2' & SYM2' & RINV2').
    assert (w = w2').
    { eapply outgoing_query_det; eauto. }
    subst.
    exploit RINV2'; eauto.    
    intros (r1 & RINV1 & MR).
    (* construct after_external state in L1 *)
    exploit AFEXT2; eauto.
    intros (s1''' & AFEXT1'').
    (* construct the matched after_external state *)
    exploit AFEXT1; eauto.
    intros [EXIST MATCH].
    exploit MATCH; eauto.
    intros (s1'0 & AFEXT'0 & (i & MATCH')).
    (* prove bsim_simulation_star *)
    exploit bsim_simulation_star_under_lts_safe; eauto.
    eapply lts_safe_reachable_safe; eauto.
    eapply external_reach; eauto. eapply star_refl.
    intros (i' & s1''0 & STAR2 & MATCH'').
    exists s1''0, i'. split; auto.
    eapply star_reachable. eauto.
    eapply external_reach; eauto.
    eapply star_refl.
Qed.

    
End BSIM.
  
Lemma module_safety_preservation:  
  module_safe L1 I1 I1 not_stuck ->
  backward_simulation cc cc L1 L2 ->
  module_safe L2 I2 I2 not_stuck.
Proof.
  intros SAFE [BSIM].
  red. intros se2 VSE2.
  red. intros w2 SYM2.
  (* construct se1 *)
  generalize (@incoming_query2 li1 li2 cc I1 I2 BSIM_INV _ _ SYM2).
  intros (wcc & w1 & se1 & MSE & SYM1 & INQ).   
  assert (VSE1: Genv.valid_for (skel L1) se1).
  { eapply match_senv_valid_for; eauto.
    erewrite bsim_skel; eauto. }
  exploit SAFE; eauto.
  intros LTSSAFE1.
  destruct BSIM.
  generalize (bsim_lts se1 se2 wcc MSE VSE1). intros BSIMP.
  econstructor.
  (* reachable_safe *)
  - intros s2 REACH2.
    exploit bsim_reachable_match; eauto.
    intros (s1 & i & REACH1 & MATCH & FINAL).
    (* s1 is not_stuck *)
    exploit (@reachable_safe li1); eauto.
    (** NOTSTUCK1 is useless because one step in target program may
    correspond to multiple steps in source program, so the property of
    only one step not stuck in source program is not useful *)
    intros NOTSTUCK1.
    (* We use bsim_progress! *)
    eapply bsim_progress; eauto.
    eapply safe_implies.
    eapply lts_safe_reachable_safe; eauto.
  (* initial progress *)
  - intros q2 VQ QINV2.
    exploit INQ; eauto.
    intros (q1 & MQ & QINV1 & FINAL).
    assert (VQ1: valid_query (L1 se1) q1 = true).
    { erewrite <- bsim_match_valid_query; eauto. }
    (* initial_match *)
    edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
    (* L1 is not stuck in initial states *)
    exploit (@initial_progress li1); eauto.
    intros (s1 & INIT). eapply EXIST. eauto.
  (* external_progress *)
  - intros s2 q2 REACH2 ATEXT2.
    exploit bsim_reachable_match; eauto.
    intros (s1 & i & REACH1 & MATCH & FINAL).
    (* external_simulation *)
    exploit (@bsim_match_external li1); eauto.
    eapply safe_implies.
    eapply lts_safe_reachable_safe; eauto.
    intros (wcc' & s1'' & q1 & STAR1 & ATEXT1 & MQ1 & MSE1 & AFEXT1).
    eapply star_reachable in STAR1; eauto.
    (* q1 is well-typed *)
    exploit (@external_progress li1);eauto.
    intros (w1' & SYM1' & QINV1 & AFEXT1').
    (* construct w2 and q2 *)
    generalize (@outgoing_query1 li1 li2 cc I1 I2 BSIM_INV  _ _ _ _ _ _ QINV1 SYM1' MQ1 MSE1).
    intros (w2' & se2' & QINV2 & AFEXT2').
    exists w2'. repeat apply conj; auto.
    (* after external *)
    intros r2 RINV2.
    exploit AFEXT2'; eauto.
    intros (r1 & RINV1 & MR).
    exploit AFEXT1; eauto.
    intros [EXIST MATCHEXT].
    exploit AFEXT1'; eauto. intros (s1' & A).    
    eapply EXIST. eauto.
  (* final_progress *)
  - intros s r REACH2 FS2.
    exploit bsim_reachable_match; eauto.
    intros (s1 & i & REACH1 & MATCH & FINAL).
    (* final_simulation *)
    edestruct (@bsim_match_final_states li1) as (s1' & r1 & STAR & FS1 & MR); eauto.
    eapply safe_implies.
    eapply lts_safe_reachable_safe; eauto.
    eapply FINAL; eauto.
    eapply final_progress. eauto.
    eapply star_reachable; eauto.
    auto.
Qed.    
    
End SAFETY_PRESERVATION.

(* The preservation of safety in k step *)

Section SAFETYK_PRESERVATION.

Context {liA1 liA2 liB1 liB2} (ccA: callconv liA1 liA2) (ccB: callconv liB1 liB2).
Context (L1: semantics liA1 liB1) (L2: semantics liA2 liB2).
Context (IA1 : invariant liA1) (IB1: invariant liB1).

Hypothesis L1_determ: open_determinate L1.
Hypothesis L2_determ: open_determinate L2.

Section BSIM.
  
Context se1 se2 ccwB (wB1: inv_world IB1) bsim_index bsim_order bsim_match_states            
  (BSIMP: bsim_properties ccA ccB se1 se2 ccwB (L1 se1) (L2 se2) bsim_index bsim_order (bsim_match_states se1 se2 ccwB)).

Context (MENV: match_senv ccB ccwB se1 se2).

Let mst i s1 s2 := bsim_match_states se1 se2 ccwB i s1 s2.


(* (n,k)-simulation-diagram. To prove this, we need s1 is safe
(internally). But how can we prove internal safe in after
external??. What about treating the nk_sim_diagram as the composition
of safek in the source and the simulation? *)
(* Inductive nk_sim_diagram : state L1 -> state L2 -> nat -> nat -> Prop := *)
(* | nk_sim_O: forall s1 s2 n, *)
(*     (* The target cannot take a step *) *)
(*     nk_sim_diagram s1 s2 n O *)
(* | nk_sim_step: forall s1 s2 n k *)
(*     (STEP: forall s2' tr, Step (L2 se2) s2 tr s2' -> *)
(*                     exists i s1' n1, *)
(*                       starN (step (L1 se1)) (globalenv (L1 se1)) n1 s1 tr s1' *)
(*                       /\ mst i s1' s2' *)
(*                       (* we should ensure n is enough *) *)
(*                       /\ (n1 <= n)%nat *)
(*                       /\ nk_sim_diagram s1' s2' (n-n1)%nat k), *)
(*     nk_sim_diagram s1 s2 n (S k) *)
(* | nk_sim_external: forall s1 s2 n k *)
(*     (ATEXT: forall q2, *)
(*         at_external (L2 se2) s2 q2 -> *)
(*         exists ccwA s1' q1 n1, *)
(*           starN (step (L1 se1)) (globalenv (L1 se1)) n1 s1 E0 s1' *)
(*           /\ (n1 <= n)%nat *)
(*           /\ at_external (L1 se1) s1' q1 *)
(*           /\ match_query ccA ccwA q1 q2 *)
(*           /\ match_senv ccA ccwA se1 se2 *)
(*           /\ (forall r1 r2, *)
(*                 match_reply ccA ccwA r1 r2 -> *)
(*                 (* we do not need bsim_match_cont_exist but *) *)
(*                 after_external (L2 se2) s2 r2 s2' -> *)
(*                 exists i s1'', *)
(*                   after_external (L1 se1) s1' r1 s1'' *)
(*                   /\ mst i s1'' s2' *)
(*                   /\ nk_sim_diagram s1'' s2' (n-n1) k)), *)
(*     nk_sim_diagram s1 s2 (S n) (S k) *)
(* . *)

  

Lemma step_safek: forall s1 s2 t
    (SAFEK: forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1)
    (STEP: Step (L1 se1) s1 t s2),
    forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2.    
Proof.
  intros.
  generalize (SAFEK (S k)). intros SAFE1.
  inv SAFE1; eauto.
  + red in SINV. contradiction.
  + exfalso.
    eapply od_final_nostep; eauto.
  + exfalso.
    eapply od_at_external_nostep; eauto.
Qed.

Lemma star_safek: forall s1 s2 t
    (STAR: Star (L1 se1) s1 t s2)
    (SAFEK: forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1),
    forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2.    
Proof.
  induction 1; intros; eauto.
  eapply IHSTAR. eapply step_safek; eauto.
Qed.

Lemma plus_safek: forall s1 s2 t
    (PLUS: Plus (L1 se1) s1 t s2)
    (SAFEK: forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1),
    forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s2.    
Proof.
  intros. inv PLUS.
  eapply star_safek; eauto. intros.
  eapply step_safek; eauto. 
Qed.


(* Lemma external_safek: forall s1 s2 t *)
(*     (SAFEK: forall k, safek se1 (L1 se1) IA1 IB1 SIF wB1 k s1) *)
(*     (STEP: Step (L1 se1) s1 t s2), *)
(*     forall k, safek se1 (L1 se1) IA1 IB1 SIF wB1 k s2.     *)
(* Proof. *)

Lemma safek_internal_safe : forall s1
    (SAFEK: forall k, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 k s1),
    safe (L1 se1) s1.
Proof.
  unfold safe. induction 2.
  - generalize (SAFEK 1%nat). intros SAFE1.
    inv SAFE1; eauto.
    red in SINV. contradiction.
  - eapply IHstar.
    intros.
    eapply step_safek; eauto.
Qed.
      
(* Key proof of module_total_safek_preservation *)
Lemma bsim_safek_preservation: forall k s1 s2 i
    (SAFEK: forall n, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 n s1)
    (MATCH: bsim_match_states se1 se2 ccwB i s1 s2),
    safek se2 (L2 se2) (invcc IA1 ccA) (invcc IB1 ccB) (SIF se1) (wB1, ccwB) k s2.
Proof.
  induction k; intros.
  econstructor.
  (* prove s1 is internal safe (to get Smallstep.safe) and then use
  bsim_progress *)
  generalize (safek_internal_safe s1 SAFEK). intros ISAFE1.
  eapply safe_implies in ISAFE1.
  generalize (bsim_progress BSIMP i _ MATCH ISAFE1).
  (* 3 cases of s2 *)
  intros [(r2 & FINAL2)|[(q2 & ATEXT2)|(t2 & s2' & STEP2)]].
  (* s1' is final state *)
  - exploit (@bsim_match_final_states liA1); eauto.
    intros (s1' & r1 & STAT1 & FINAL1 & MR).
    (* prove s1' is safek *)
    assert (SAFEK1': forall n : nat, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 n s1').
    { eapply star_safek; eauto. }
    generalize (SAFEK1' 1%nat). intros SAFE1.
    (* s1' have three cases, by determinism, it must be in final state *)
    inv SAFE1.
    + exfalso.
      eapply od_final_nostep; eauto.
    + red in SINV. contradiction.
    (* final state *)
    + eapply od_final_determ in FINAL1; eauto. subst.
      eapply safek_final. eauto.
      econstructor. split; eauto.
    + exfalso.
      eapply od_final_noext; eauto.
  (* s1' is at_external state *)
  - exploit (@bsim_match_external liA1); eauto.
    intros (ccwA & s1' & q1 & STAR & ATEXT1 & MQ & MENV1 & AFEXT1).
    (* prove s1' is safek *)
    assert (SAFEK1': forall n : nat, safek se1 (L1 se1) IA1 IB1 (SIF se1) wB1 n s1').
    { eapply star_safek; eauto. }
    generalize (SAFEK1' (S k)%nat). intros SAFE1.
    inv SAFE1.
    + exfalso.
      eapply od_at_external_nostep; eauto.
    + red in SINV. contradiction.
    + exfalso.
      eapply od_final_noext; eauto.
    (* at_external *)
    + eapply od_at_external_determ in ATEXT1; eauto. subst.      
      eapply safek_external. eauto.
      instantiate (1 := (w, ccwA)).
      (* symtbl_inv *)
      econstructor. split; eauto.
      (* query_inv *)
      econstructor. split; eauto.
      (* reply *)
      intros r2 (r1 & RINV1 & MR).
      exploit AFEXT; eauto.
      intros (s1'' & AFEXT'' & SAFEK'').
      (* use AFEXT1 *)
      exploit AFEXT1. eauto.
      intros [EXIST MATCHEXT].
      exploit EXIST; eauto. intros (s2' & AFEXT2').
      exploit MATCHEXT; eauto.
      intros (s1''' & AFEXT''' & (i' & MATCH')).
      (* use L1 after_external determinate to show s1'' = s1''' *)
      eapply od_after_external_determ in AFEXT''; eauto. subst.      
      exists s2'. split; auto.
      eapply IHk. 2: eapply MATCH'.
      (** Difficult *)
      admit.
  - eapply safek_step; eauto.
    intros t' s2'' STEP.
    exploit (@bsim_simulation liA1); eauto.
    intros (i' & s1' & OR & MATCH').
    destruct OR as [PLUS| (STAR & ORD)].
    + eapply IHk. 2: eapply MATCH'.
      eapply plus_safek; eauto.
    + eapply IHk. 2: eapply MATCH'.
      eapply star_safek; eauto.
Admitted.
      
End BSIM.



Lemma module_total_safek_preservation:
  module_total_safek L1 IA1 IB1 ->
  backward_simulation ccA ccB L1 L2 ->
  module_total_safek L2 (invcc IA1 ccA) (invcc IB1 ccB).
Proof.
  intros SAFE [BSIM].
  red. intros se2 VSE2.
  red. intros (wB1 & ccwB) (se1 & SYM1 & MENV).
  intros q2 VQ2 (q1 & QINV2 & MQ).
  assert (VSE1: Genv.valid_for (skel L1) se1).
  { eapply match_senv_valid_for; eauto.
    erewrite bsim_skel; eauto. }
  inv BSIM.
  generalize (bsim_lts se1 se2 ccwB MENV VSE1). intros BSIMP.
  assert (VQ1: valid_query (L1 se1) q1 = true).
  { erewrite <- bsim_match_valid_query; eauto. }  
  (* initial_match *)
  exploit SAFE; eauto.
  intros (s1 & INIT1 & SAFE1).
  edestruct @bsim_match_initial_states as [EXIST MATCH]; eauto.
  exploit EXIST; eauto.
  intros (s2 & INIT2).
  exploit MATCH; eauto.
  intros (s1' & INIT1' & (i & MST)).
  (* use initial_determ *)
  eapply od_initial_determ in INIT1; eauto. subst.
  (* use s2 as the initial state of L2 *)
  exists s2. split. auto.
  (** Key part: prove safek by generalization of s2 *)
  intros. exploit bsim_safek_preservation; eauto.
Qed.

End SAFETYK_PRESERVATION.
