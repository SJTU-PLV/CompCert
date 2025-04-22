Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Globalenvs.
Require Import LanguageInterface.
Require Import SmallstepLinking Smallstep SmallstepSafe.
Require Import Linking.
Require Import Classical.
Require Import Invariant.

(** This file contains the definition of open safety called
module_type_safe and the propertis of Horizontal Composition and
Vertical Preservation *)

(* internal safety  *)
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

(* progress state *)
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

(** * Safety Defined by Invariant Preservation and Progress *)

(* Module total safety (SI is False) *)
Definition SIF {S} : Genv.symtbl -> S -> Prop := (fun _ _ => False).

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
(* Lemma lts_preserves_progress_safek: forall k s, *)
(*     SI se w s -> *)
(*     safek se (L se) IA IB (PS se) w k s. *)
(* Proof. *)
(*   induction k; intros s SINV. *)
(*   - econstructor. *)
(*   - exploit (@internal_state_progress liA); eauto. *)
(*     intros [A|B]. *)
(*     + destruct A as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]]. *)
(*       * eapply safek_final. eauto. *)
(*         eapply final_state_preserves; eauto. *)
(*       * exploit (@external_preserves_progress liA); eauto. *)
(*         intros (wA & SYM & QINV & AFEXT). *)
(*         eapply safek_external; eauto. *)
(*         intros. exploit AFEXT; eauto. *)
(*         intros (s' & AFEXT1 & SIEXT). exists s'. split; auto. *)
(*       * eapply safek_step; eauto. *)
(*         intros. eapply IHk. eauto. *)
(*         eapply internal_step_preserves; eauto. *)
(*     + eapply safek_SI. eauto. *)
(* Qed. *)

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


(** A simple safety composition with the same safety interface in both sides  *)
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

Local Open Scope inv_scope.

(** The general form of compositionality of open safety *)

Section WITH_INV.

Context {li} (I1 I2: invariant li) (L: bool -> semantics li li).
Context (sk: AST.program unit unit) (se: Genv.symtbl).

Context (SAFE1 : module_type_safe_components (L true) I1 I2 SIF).
Context (SAFE2 : module_type_safe_components (L false) I2 I1 SIF).
(* Context (SAFE : forall i, module_type_safe_components (L false) (Il i) (Ir i) SIF). *)

Let I := I1 ⊎ I2.

(* | type_safe_frames_gen_cons1: forall (i: bool) s q (w1: inv_world I1) (w2: inv_world I2) w' fms *)
(*     (VSE: symtbl_inv (Ir i) *)
(*             (match i as i' return inv_world (Ir i') with | true => w1 | false => w2 end) *)
(*             se) *)
(*     (WF: type_safe_frames_gen w fms (match i return inv_world I with | true => inl w1 | false => inr w2 end)) *)
(*     (EXT: at_external (L i se) s q) *)
(*     (WTQ: query_inv (Il i) w' q) *)
(*     (* desrible progress property here *) *)
(*     (PGS: forall r, reply_inv (Il i) w' r -> *)
(*                exists s', after_external (L i se) s r s' *)
(*                      /\ (forall s', after_external (L i se) s r s' -> *)
(*                               match i with *)
(*                               | true => type_safe_invariant (L i) (Il i) (Ir i) SIF (SAFE i) se w1 s' *)
(*                               | false => type_safe_invariant (L i) (Il i) (Ir i) SIF (SAFE i) se w2 s' *)
(*                               end)), *)
(*     type_safe_frames_gen w ((st L i s) :: fms) (match i with | true => inl w' | false => inr w' end). *)


Inductive type_safe_frames_gen (w: inv_world I) : list (frame L) -> inv_world I -> Prop :=
| type_safe_frames_gen_nil: type_safe_frames_gen w nil w
| type_safe_frames_gen_cons1: forall s q w1 w2 fms
    (WF: type_safe_frames_gen w fms (inr w2))
    (VSE: symtbl_inv I2 w2 se)
    (EXT: at_external (L true se) s q)
    (WTQ: query_inv I1 w1 q)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I1 w1 r ->
               exists s', after_external (L true se) s r s'
                     /\ (forall s', after_external (L true se) s r s' ->
                              type_safe_invariant (L true) I1 I2 SIF SAFE1 se w2 s')),
    type_safe_frames_gen w ((st L true s) :: fms) (inl w1)
| type_safe_frames_gen_cons2: forall s q w1 w2 fms
    (WF: type_safe_frames_gen w fms (inl w1))
    (VSE: symtbl_inv I1 w1 se)
    (EXT: at_external (L false se) s q)
    (WTQ: query_inv I2 w2 q)
    (* desrible progress property here *)
    (PGS: forall r, reply_inv I2 w2 r ->
               exists s', after_external (L false se) s r s'
                     /\ (forall s', after_external (L false se) s r s' ->
                              type_safe_invariant (L false) I2 I1 SIF SAFE2 se w1 s')),
    type_safe_frames_gen w ((st L false s) :: fms) (inr w2)
.

Inductive type_safe_state_gen w: list (frame L) -> Prop :=
| type_safe_state_gen_cons1: forall s frs w2
    (WFS: type_safe_frames_gen w frs (inr w2))
    (VSE: symtbl_inv I2 w2 se)
    (TYSAFE: type_safe_invariant (L true) I1 I2 SIF SAFE1 se w2 s),
    type_safe_state_gen w (st L true s :: frs)
| type_safe_state_gen_cons2: forall s frs w1
    (WFS: type_safe_frames_gen w frs (inl w1))
    (VSE: symtbl_inv I1 w1 se)
    (TYSAFE: type_safe_invariant (L false) I2 I1 SIF SAFE2 se w1 s),
    type_safe_state_gen w (st L false s :: frs)
.

End WITH_INV.


Section COMPOSE_TYPE_SAFE_GENERAL.
  
Context {li} (I1 I2: invariant li) (L1 L2 L': semantics li li).

Let L (i: bool) := if i then L1 else L2.

(* used to make sure that the query_inv of I1 and I2 in (I1 ⊎ I2) are
disjoint *)
Hypothesis valid_query_disjoint1: forall w q se,
    symtbl_inv I1 w se ->
    Genv.valid_for (skel L1) se ->
    query_inv I1 w q ->
    valid_query (L1 se) q = false.

Hypothesis valid_query_disjoint2: forall w q se,
    symtbl_inv I2 w se ->
    Genv.valid_for (skel L2) se ->
    query_inv I2 w q ->
    valid_query (L2 se) q = false.

Hypothesis external_not_valid_query: forall i se s q,
    Smallstep.at_external (L i se) s q ->
    Smallstep.valid_query (L i se) q = false.

Let Il (i: bool) := match i with | true => I1 | false => I2 end.
Let Ir (i: bool) := match i with | true => I2 | false => I1 end.

Lemma compose_total_type_safety_general:
  module_type_safe I1 I2 L1 SIF ->
  module_type_safe I2 I1 L2 SIF ->
  compose L1 L2 = Some L' ->
  module_type_safe (I1 ⊎ I2) (I1 ⊎ I2) L' SIF.
Proof.
  intros [SAFE1] [SAFE2] COMP.
  unfold compose in *. unfold option_map in *.
  destruct (link (skel L1) (skel L2)) as [sk|] eqn:Hsk; try discriminate. inv COMP.
  assert (SAFE: forall i, module_type_safe_components (L i) (Il i) (Ir i) SIF).
  { intros i. destruct i.
    eapply SAFE1; eauto.
    eapply SAFE2; eauto. }
  red. econstructor.
  eapply Module_type_safe_components with (type_safe_invariant := fun se w => type_safe_state_gen I1 I2 L se (SAFE true) (SAFE false) w).
  intros se wB SYM VSE.
  assert (VALIDSE: forall i, Genv.valid_for (skel (L i)) se).
  { destruct i.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto.
    eapply Genv.valid_for_linkorder.
    eapply (link_linkorder _ _ _ Hsk). eauto. }
  econstructor.
  - intros. inv H.
    (* true *)
    + inv H0; subst_dep.
      * econstructor; eauto.
        eapply internal_step_preserves; eauto.
        eapply (SAFE true); eauto. 
      * exploit @external_preserves_progress.
        eapply (SAFE true). eapply VSE0. eapply VALIDSE. eauto.
        eauto.
        intros (wA & A1 & A2 & A3).
        exploit (external_not_valid_query true). eapply H3.
        intros VQF. destruct j; simpl in VQF; try rewrite H6 in VQF. inv VQF.
        econstructor. 2: eapply A1.
        econstructor; eauto.
        exploit @initial_preserves_progress.
        eapply (SAFE false). eapply A1. eapply VALIDSE. eauto. eauto.
        intros (s & B1 & B2).
        eapply B2. eauto.
      * inv WFS. subst_dep.
        econstructor; eauto.
        exploit PGS. eapply final_state_preserves. eapply (SAFE true).
        eauto. eapply VALIDSE. eauto. eauto.
        intros (s & B1 & B2).
        eapply B2. eauto.
    (* false *)
    + inv H0; subst_dep.
      * econstructor; eauto.
        eapply internal_step_preserves; eauto.
        eapply (SAFE false); eauto. 
      * exploit @external_preserves_progress.
        eapply (SAFE false). eapply VSE0. eapply VALIDSE. eauto.
        eauto.
        intros (wA & A1 & A2 & A3).
        exploit (external_not_valid_query false). eapply H3.
        intros VQF. destruct j; simpl in VQF; try rewrite H6 in VQF. 2: inv VQF.
        econstructor. 2: eapply A1.
        econstructor; eauto.
        exploit @initial_preserves_progress.
        eapply (SAFE true). eapply A1. eapply VALIDSE. eauto. eauto.
        intros (s & B1 & B2).
        eapply B2. eauto.
      * inv WFS. subst_dep.
        econstructor; eauto.
        exploit PGS. eapply final_state_preserves. eapply (SAFE false).
        eauto. eapply VALIDSE. eauto. eauto.
        intros (s & B1 & B2).
        eapply B2. eauto.
  - intros. inv H.
    (* true *)
    + exploit @internal_state_progress. eapply (SAFE true); eauto.
      eauto. intros A. destruct A.
      2: { contradiction. }
      left.
      destruct H as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
      * inv WFS.
        -- left. exists r.
           econstructor. eauto.
        -- do 2 right.
           exploit @final_state_preserves. eapply (SAFE true). eapply VSE0.
           all: eauto. intros VR.
           exploit PGS; eauto.
           intros (s' & B1 & B2).
           do 2 eexists.
           eapply step_pop; eauto.
      * exploit @external_preserves_progress. eapply (SAFE true). 1-4: eauto.
        intros (wA & A1 & A2 & A3).
        destruct (valid_query (L false se) q) eqn: VQ.
        -- exploit @initial_preserves_progress. eapply (SAFE false). 1-4: eauto. 
           intros (s' & B1 & B2).        
           do 2 right. do 2 eexists.        
           eapply step_push with (j := false); eauto.
        -- right. left.
           exists q. econstructor. eauto.
           intros. destruct j; auto.
           eapply (external_not_valid_query true). eauto.
      * do 2 right.
        do 2 eexists. eapply step_internal. eauto.
    (* false *)
    + exploit @internal_state_progress. eapply (SAFE false); eauto.
      eauto. intros A. destruct A.
      2: { contradiction. }
      left.
      destruct H as [(r & FINAL)|[(q & EXT)|(t1 & s1 & STEP1)]].
      * inv WFS.
        -- left. exists r.
           econstructor. eauto.
        -- do 2 right.
           exploit @final_state_preserves. eapply (SAFE false). eapply VSE0.
           all: eauto. intros VR.
           exploit PGS; eauto.
           intros (s' & B1 & B2).
           do 2 eexists.
           eapply step_pop; eauto.
      * exploit @external_preserves_progress. eapply (SAFE false). 1-4: eauto.
        intros (wA & A1 & A2 & A3).
        destruct (valid_query (L true se) q) eqn: VQ.
        -- exploit @initial_preserves_progress. eapply (SAFE true). 1-4: eauto. 
           intros (s' & B1 & B2).        
           do 2 right. do 2 eexists.        
           eapply step_push with (j := true); eauto.
        -- right. left.
           exists q. econstructor. eauto.
           intros. destruct j; auto.
           eapply (external_not_valid_query false). eauto.
      * do 2 right.
        do 2 eexists. eapply step_internal. eauto.
  (* initial state *)
  - intros q VQ QINV.
    simpl in VQ. eapply orb_true_iff in VQ.
    (* With valid_query_disjoint. We can prove that QINV must relate
    the query in the same module as the valid_query *)
    destruct VQ as [VQ1 | VQ2].
    + simpl in QINV. destruct wB as [w1|w2].
      eapply valid_query_disjoint1 in QINV; try eapply SYM.
      2: { eapply (VALIDSE true). }
      rewrite VQ1 in QINV.
      congruence.
      simpl in SYM.
      exploit @initial_preserves_progress. eapply (SAFE true).
      1-4: eauto. intros (s & A1 & A2).
      exists (st L true s :: nil). split.
      econstructor; eauto.
      intros. inv H.
      (* The initial state is state (L i) instead of state (L j) *)
      exploit @initial_preserves_progress. eapply (SAFE true).
      1-4: eauto. intros (s' & B1 & B2).
      destruct i.
      2: { eapply valid_query_disjoint2 in QINV; try eapply SYM.
           2: { eapply (VALIDSE false). }
           rewrite H0 in QINV.           
           congruence. }      
      econstructor. econstructor.
      eauto. eauto.
    + simpl in QINV. destruct wB as [w1|w2].
      2: { eapply valid_query_disjoint2 in QINV; try eapply SYM.
           2: { eapply (VALIDSE false). }
           rewrite VQ2 in QINV.
           congruence. }
      simpl in SYM.
      exploit @initial_preserves_progress. eapply (SAFE false).
      1-4: eauto. intros (s & A1 & A2).
      exists (st L false s :: nil). split.
      econstructor; eauto.
      intros. inv H.
      (* The initial state is state (L i) instead of state (L j) *)
      exploit @initial_preserves_progress. eapply (SAFE false).
      1-4: eauto. intros (s' & B1 & B2).
      destruct i.
      eapply valid_query_disjoint1 in QINV; try eapply SYM.
      2: { eapply (VALIDSE true). }
      rewrite H0 in QINV.           
      congruence.
      econstructor. econstructor.
      eauto. eauto.
  (* external *)
  - intros s q SINV EXT. inv EXT.
    destruct i.
    + inv SINV. subst_dep.
      exploit @external_preserves_progress. eapply (SAFE true).
      1-4: eauto. intros (wA & A1 & A2 & A3).
      exists (inl wA). repeat apply conj; auto.
      intros. simpl in H1. exploit A3; eauto. intros (s' & B1 & B2).
      eexists. split.
      econstructor; eauto.
      intros. inv H2. subst_dep.
      econstructor; eauto.
    + inv SINV. subst_dep.
      exploit @external_preserves_progress. eapply (SAFE false).
      1-4: eauto. intros (wA & A1 & A2 & A3).
      exists (inr wA). repeat apply conj; auto.
      intros. simpl in H1. exploit A3; eauto. intros (s' & B1 & B2).
      eexists. split.
      econstructor; eauto.
      intros. inv H2. subst_dep.
      econstructor; eauto.
  (* final *)
  - intros s r SINV FINAL. inv FINAL.
    destruct i.
    + inv SINV. subst_dep.
      simpl in TYSAFE.
      inv WFS. simpl.
      eapply final_state_preserves. eapply (SAFE true).
      all: eauto.
    + inv SINV. subst_dep.
      simpl in TYSAFE.
      inv WFS. simpl.
      eapply final_state_preserves. eapply (SAFE false).
      all: eauto.
Qed.

End COMPOSE_TYPE_SAFE_GENERAL.


(** * Preservation of Open Safety under the Backward Simulation *)


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


(** *Safety preservation under forward simulation with progress property *)

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


(** * Preservation of Open Partial Safety using Backward Simulation which Preserves Errors *)
               
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
