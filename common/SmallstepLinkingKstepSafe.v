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
safety as "safety in k steps". *)

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

Definition module_total_safek {liA liB} (L: semantics liA liB) (IA IB: invariant _) := module_safek L IA IB SIF.

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


(* soundness of module_safe_components *)
Lemma module_type_safe_sound {liA liB} (L: semantics liA liB) (IA: invariant liA) (IB: invariant liB) PS:
  module_type_safe IA IB L PS ->
  module_safek L IA IB PS.
Proof.
  intros [SAFE]. inv SAFE.
  red. intros se VSE w WTSE.
  exploit type_safe_preservation_progress; eauto. intros PRE.
  red. intros q VQ QINV.
  exploit (@initial_preserves_progress liA); eauto.
  intros (inits & INIT & SINV1). exists inits. split; auto.
  intros. eapply lts_preserves_progress_safek; eauto.
Qed.

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


End FSIMK.

End SAFEK_PRESERVATION.
(** *end of Experiment code *)


(** * Compositionality of safek  *)

  
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
Abort.
      
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
  intros. (* exploit bsim_safek_preservation; eauto. *)
Abort.

End SAFETYK_PRESERVATION.
