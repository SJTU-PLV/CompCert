Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep SmallstepSafe.
Require Import Linking.
Require Import Classical.
Require Import Invariant.
Require Import SmallstepLinkingSafe.

(** This file is used to record the experiment code of defining open
safety as reachable safety. *)


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
Abort.

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


(** * The Preservation of Reachable Safety under Backward Simulation which requires Unreasonable Conditions (The definition of inv_alternate) *)

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
