Require Export LogicalRelations.
Require Export List.
Require Export Globalenvs.
Require Export Events.
Require Export LanguageInterface.

Require Import Axioms.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Memory.

Require Export CallconvBig.

(** Algebraic structures on calling conventions. *)

(** * Refinement and equivalence *)

(** ** Definition *)

(** The following relation asserts that the calling convention [cc] is
  refined by the calling convention [cc'], meaning that any
  [cc']-simulation is also a [cc]-simulation. *)

(** cc1: internal, i.e. injp ⋅ injp
    cc2: external, i.e. injp  *)


(** We are trying to define the ccref_outgoing with respect to the "living wp1, however,
    to show from [wp1 *-> (get w1)] we can construct w2 and show [wp2 *-> (get w2)], we still
    have to show that wp1 and wp2 are recording the same injected memories. Such relation has to be **defined**
    in some way "*)

Import GS. 
Definition ccref_outgoing {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop) :=
  forall wp1 wp2 w1 se1 se2 q1 q2,
    match_senv cc1 w1 se1 se2 ->
    match_query cc1 w1 q1 q2 ->
    wp1 *-> (get w1) ->
    match12 wp1 wp2 ->
    exists w2,
      wp2 *-> (get w2) /\
      match_senv cc2 w2 se1 se2 /\
      match_query cc2 w2 q1 q2 /\
      forall r1 r2 (wp2': gworld cc2),
        get w2 o-> wp2' ->
        match_reply cc2 (set w2 wp2') r1 r2 ->
        exists (wp1' : gworld cc1),
        get w1 o-> wp1' /\
        match_reply cc1 (set w1 wp1') r1 r2 /\
        match12 wp1' wp2'.            

Definition ccref_incoming {li1 li2} (cc1 cc2: callconv li1 li2) (match12 : gworld cc1 -> gworld cc2 -> Prop):=
  forall w2 se1 se2 q1 q2,
    match_senv cc2 w2 se1 se2 ->
    match_query cc2 w2 q1 q2 ->
    exists (w1: ccworld cc1) ,
      match_senv cc1 w1 se1 se2 /\
      match_query cc1 w1 q1 q2 /\
      match12 (get w1) (get w2) /\
        (forall r1 r2 wp1 wp2 wp1',
        match12 wp1 wp2 ->    
        get w1 o-> wp1' -> wp1 *-> wp1' ->
        match_reply cc1 (set w1 wp1') r1 r2 ->
        exists (wp2' : gworld cc2),
        (* match12 wp1' wp2' ->*)
        get w2 o-> wp2' /\ wp2 *-> wp2' /\
        match_reply cc2 (set w2 wp2') r1 r2).


Record cctrans' {li1 li2} (cc1 cc2: callconv li1 li2) :=
  Callconv_Trans{
        match12 : gworld cc1 -> gworld cc2 -> Prop;
        big_step_incoming : ccref_incoming cc1 cc2 match12;
        big_step_outgoing : ccref_outgoing cc1 cc2 match12;
      }.

  
Lemma open_fsim_cctrans' {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans' cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct X as [match12 INCOM OUTGO].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
    set (ms se1 se2 (w2 : ccworld cc2) (wp2: gworld cc2) idx s1 s2 :=
         exists w1 (wp1 : gworld cc1),
           match_states se1 se2 w1 wp1 idx s1 s2 /\
             match_senv cc1 w1 se1 se2 /\
             match12 (get w1) (get w2) /\
             match12 wp1 wp2 /\
             (forall r1 r2 wp1 wp2 wp1', match12 wp1 wp2 -> (get w1) o-> wp1' -> wp1 *-> wp1' -> match_reply cc1 (set w1 wp1') r1 r2 ->
            exists (wp2' : gworld cc2), (get w2) o-> wp2' /\ wp2 *-> wp2' /\ match_reply cc2 (set w2 wp2') r1 r2)).
  eapply Forward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply fsim_match_valid_query; eauto.
  - intros q1 q2 s1 Hq' Hs1 Ho.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hf); auto.
    edestruct @fsim_match_initial_states as (i & s2 & Hs2 & Hs); eauto.
    exists i, s2. split; auto. red. exists wB,(get wB). repeat apply conj; eauto.
  - intros gw i s1 s2 r1 (wB & gw' & Hs & Hse & HmB & Hm & Hf) Hr1.
    edestruct @fsim_match_final_states as (r2 & gw1 & Hr2 & ACCO1 & ACCI1 & Hr); eauto.
    exploit Hf; eauto. intros (gw2 &  ACCO2 & Hr2'). exists r2.
    exists gw2. intuition auto.
  - (*the most tricky part*)
    intros gw2 i s1 s2 qA1 (wB & gw1 & Hs & Hse & HmB & Hm & Hf) HqA1.
    edestruct @fsim_match_external as (wA & qA2 & Hacc1 & HqA2 & HqA & HseA & ?); eauto.
    edestruct OUTGO as (wA' & Hm' & HseA' & HqA' & Hr); eauto.
    exists wA', qA2. intuition auto.
    exploit Hr; eauto. intros (wp1' & ACCO1 & MR1 & Hm'').
    edestruct H as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto. exists wB. exists wp1'.
    intuition auto.
  - intros s1 t s1' Hs1' gw2 i s2 (wB & gw1 & Hs & Hse & Hr').
   edestruct @fsim_simulation as (i' & s2' & Hs2' & Hs'); eauto.
    exists i', s2'. split; auto.
    econstructor; eauto.
Qed.

Lemma open_bsim_cctrans' {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    backward_simulation cc1 L1 L2 ->
    cctrans' cc1 cc2 ->
    backward_simulation cc2 L1 L2.
  (*cc1 : injp @ injp cc2: injp*)
Proof.
  intros.
  destruct X as [match12 INCOM OUTGO].
  inv H.
  destruct X as [index order match_states SKEL PROP WF].
  constructor.
    set (ms se1 se2 (w2 : ccworld cc2) (wp2: gworld cc2) idx s1 s2 :=
         exists w1 (wp1 : gworld cc1),
           match_states se1 se2 w1 wp1 idx s1 s2 /\
             match_senv cc1 w1 se1 se2 /\
             match12 (get w1) (get w2) /\
             match12 wp1 wp2 /\
             (forall r1 r2 wp1 wp2 wp1', match12 wp1 wp2 -> (get w1) o-> wp1' -> wp1 *-> wp1' -> match_reply cc1 (set w1 wp1') r1 r2 ->
            exists (wp2' : gworld cc2), (get w2) o-> wp2' /\ wp2 *-> wp2' /\ match_reply cc2 (set w2 wp2') r1 r2)).
  eapply Backward_simulation with order ms; auto.
  intros se1 se2 wB' Hse' Hse1.
  split.
  - intros q1 q2 Hq'.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Hr); auto.
    eapply bsim_match_valid_query; eauto.
  - intros q1 q2 Hq'. 
    constructor.
    + intros s1 Hi.
    destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hf); auto.
    edestruct @bsim_match_initial_states as (Hi1 & Hi2); eauto.
    + intros s1 s2 His Hit.
      destruct (INCOM wB' se1 se2 q1 q2) as (wB & Hse & Hq & Htrans & Hf); auto.
      edestruct @bsim_match_initial_states as (Hi1 & Hi2); eauto.
      exploit Hi2; eauto. intros [s1' [A B]].
      eexists. split. eauto. inv B. econstructor; eauto.
      red. exists wB,(get wB). repeat apply conj; eauto.
  - intros gw i s1 s2 r2 (wB & gw' & Hs & Hse & HmB & Hm & Hf) Hsafe1 Hr2.
    edestruct @bsim_match_final_states as (s1' & r1 & gw1 & Hstar1 & Hr1 & ACCO1 & ACCI1 & Hr); eauto.
    exploit Hf; eauto. intros (gw2 &  ACCO2 & ACCI2 & Hr2'). exists s1'. exists r1.
    exists gw2. intuition auto.
  - (*the most tricky part*)
    intros gw2 i s1 s2 qA2 (wB & gw1 & Hs & Hse & HmB & Hm & Hf) Hsafe1 HqA2.
    edestruct @bsim_match_external as (wA & s1' & qA1 & Hstar1 & HqA1 & Hacc1 & HqA & HseA & ?); eauto.
    edestruct OUTGO as (wA' & Hm' & HseA' & HqA' & Hr); eauto.
    exists wA', s1', qA1. intuition auto.
    exploit Hr; eauto. intros (wp1' & ACCO1 & MR1 & Hm'').
    exploit H. eauto. eauto. intro Hrex2. inv Hrex2.
    split. eauto.
    intros. exploit bsim_match_cont_match; eauto.
    intros [s1'' [A B]]. eexists. split. eauto. inv B. econstructor; eauto.
    red. exists wB. exists wp1'.
    intuition eauto.
  - intros. destruct H as [a [b [c [d [e [f g]]]]]].
    eapply @bsim_progress; eauto.
  - intros s2 t s2' Hs2' gw2 i s1 (wB & gw1 & Hs & Hse & Hr') Hsafe1.
   edestruct @bsim_simulation as (i' & s1' & Hs1' & Hs'); eauto.
   exists i', s1'. split; auto.
   econstructor; eauto.
Qed.


Definition cctrans {li1 li2} cc1 cc2 :=
  inhabited (@cctrans' li1 li2 cc1 cc2).

Global Instance cctrans_preo li1 li2 :
  PreOrder (@cctrans li1 li2).
Proof.
  constructor.
  - constructor. econstructor. instantiate (1:= eq).
    econstructor; eauto. repeat apply conj; eauto.
    intros. subst. eexists. eauto.
    econstructor; eauto. repeat apply conj; eauto.
    subst. auto.
  - red. intros L1 L2 L3 [X] [Y]. inv X. inv Y.
    rename match13 into match12. rename match14 into match23.
    constructor. econstructor.
    instantiate (1:= fun w1 w3 => exists w2, match12 w1 w2 /\ match23 w2 w3).
    + red. intros w3 se1 se2 q1 q2 Hs3 Hq3.
      exploit big_step_incoming1; eauto.
      intros (w2 & Hs2 & Hq2 & M23 & Hr2).
      exploit big_step_incoming0; eauto.
      intros (w1 & Hs1 & Hq1 & M12 & Hr1).
      exists w1. repeat apply conj; eauto.
      intros r1 r2 wp1 wp3 wp1' [wp2 [Ms12 Ms23]] ACE1 ACI1 Hr1'.
      exploit Hr1; eauto. intros (wp2' & ACE2 & ACI2 & Hr2').
      exploit Hr2; eauto.
    + red. intros wp1 wp3 w1 se1 se2 q1 q2 Hs1 Hq1 ACI1 [wp2 [Ms12 Ms23]].
      exploit big_step_outgoing0; eauto.
      intros (w2 & ACI2 & Hs2 & Hq2 & Hr2).
      exploit big_step_outgoing1; eauto.
      intros (w3 & ACI3 & Hs3 & Hq3 & Hr3).
      exists w3. repeat apply conj; eauto.
      intros r1 r2 wp3' ACO3 Hr3'.
      exploit Hr3; eauto. intros (wp2' & ACE2 & Hr2' & Hsq23).
      exploit Hr2; eauto. intros (wp1' & ACE1 & Hr1' & Hsq12).
      exists wp1'. repeat apply conj; eauto.
Qed.

Global Instance open_fsim_cctrans:
  Monotonic
    (@GS.forward_simulation)
    (forallr - @ liA1, forallr - @ liA2, cctrans ++>
     subrel).
Proof.
  intros li1 li2 cc1 cc2 [Ht] sem1 sem2 L1.
  eapply open_fsim_cctrans'; eauto.
Qed.

Global Instance open_bsim_cctrans:
  Monotonic
    (@GS.backward_simulation)
    (forallr - @ liA1, forallr - @ liA2, cctrans ++>
     subrel).
Proof.
  intros li1 li2 cc1 cc2 [Ht] sem1 sem2 L1.
  eapply open_bsim_cctrans'; eauto.
Qed.

Global Instance cc_compose_ref li1 li2 li3:
  Proper (cctrans ++> cctrans ++> cctrans) (@cc_compose li1 li2 li3).
Proof.
  intros cca cca' [[matcha Hia Hoa]] ccb ccb' [[matchb Hib Hob]].
  constructor. econstructor. instantiate (1:= fun w w' => matcha (fst w) (fst w') /\
                                                          matchb (snd w) (snd w')).
  - red. intros [se2 [wa' wb']] se1 se3 q1 q3 [Hsa' Hsb'] [q2 [Hqa' Hqb']].
    exploit Hia; eauto. intros (wa & Hsa & Hqa & Msa & Hra).
    edestruct Hib as (wb & Hsb & Hqb & Msb & Hrb); eauto.
    exists (se2, (wa, wb)). repeat apply conj; eauto.
    constructor; eauto. econstructor; eauto.
    intros r1 r3 [wpa wpb] [wpa' wpb'] [wpa1 wpb1]
      [Msa1 Msb1] [ACEa ACEb] [ACIa ACIb] [r2 [Hra' Hrb']].
    simpl in *.
    edestruct Hra as (wpa2' & ACEa' & ACIa' & Hra2'); eauto.
    edestruct Hrb as (wpb2' & ACEb' & ACIb' & Hrb2'); eauto.
    exists (wpa2', wpb2'). intuition auto. simpl.
    split; eauto. split; eauto.
    exists r2. split; auto.
  - red. intros [wpa wpb] [wpa' wpb'] [se2 [wa wb]] se1 se3 q1 q3
           [Hsa' Hsb'] [q2 [Hqa' Hqb']] [ACIa ACIb] [Msa Msb].
    cbn in ACIa, ACIb, Msa, Msb.
    exploit Hoa; eauto. intros (wa' & ACIa' & Msa' & Mqa' & Hra').
    exploit Hob; eauto. intros (wb' & ACIb' & Msb' & Mqb' & Hrb').
    exists (se2, (wa', wb')). repeat apply conj; eauto.
    constructor; eauto. econstructor; eauto.
    intros r1 r3 [wpa2' wpb2'] [ACEa ACEb] [r2 [Hra Hrb]].
    simpl in ACEa, ACEb, Hra, Hrb.
    edestruct Hra' as (wpa2 & ACEa1 & Hra2 & Msa1); eauto.
    edestruct Hrb' as (wpb2 & ACEb1 & Hrb2 & Msb1); eauto.
    exists (wpa2, wpb2). intuition auto. simpl.
    split; eauto.
    exists r2. split; auto.
Qed.

Infix "@" := GS.cc_compose (at level 30, right associativity).

Lemma cctrans_split_1 : forall {A B C} (cc : GS.callconv B C) (cc1 cc2: GS.callconv A B),
    cctrans cc1 cc2 ->
    cctrans (cc1 @ cc) (cc2 @ cc).
Proof.
  intros. rewrite H. reflexivity.
Qed.







