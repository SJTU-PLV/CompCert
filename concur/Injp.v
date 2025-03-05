Require Import Conventions Mach Asm.
Require Import CKLR LanguageInterface.
Require Import Locations CallConv.
Require Import Inject InjectFootprint CA CallconvBig.

Set Implicit Arguments.

Require Import RelationClasses.
Require Import Relations.


(* injp_acc *)

(** injp_acci: the internal transition: thread id remains the same, also no new threads introduced
               the private(unmapped or outofreach) memory of other threads are unchanged *)

(** free_preserved : The internal execution should keep the free operation of public memory. *)

(** Issue: the passes using [Mem.free_left_inject] *may* break this relation, we need to check them
    They are: Inliningproof, Separation, Serverproof (*should be ok*) *)

(** Note : the injp_acce as rely condition is used to protect [local] (i.e. blocks of this thread) and [private] (i.e. unmapped or outofreach) memory

    The [injp_acci] is introduced as an guarantee condition for *switch* provided by big_step internal accessibility. Therefore, it can protect only [external] memory. Such restriction applies to not only [Mem.unchanged_on], but also other properties.


 *)
(*
Definition inject_separated_external (f f' : meminj) (m1 m2: mem) :=
  forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) -> fst b1 <> Mem.tid (Mem.support m1) ->
                 ~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2.

Definition inject_separated_internal (f f' : meminj) (m1 m2: mem) :=
  forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) -> fst b1 = Mem.tid (Mem.support m1) ->
                 ~ Mem.valid_block m1 b1 /\ ~ Mem.valid_block m2 b2.
*)

Lemma inject_separated_imply_e: forall f f' m1 m2,
    inject_separated f f' m1 m2 -> inject_separated_external f f' m1 m2.
Proof.
  intros. red. intros. eapply H; eauto.
Qed.

Lemma inject_separated_imply_i: forall f f' m1 m2,
    inject_separated f f' m1 m2 -> inject_separated_internal f f' m1 m2.
Proof.
  intros. red. intros. eapply H; eauto.
Qed.

Hint Resolve inject_separated_imply_e : core.
Hint Resolve inject_separated_imply_i : core.

Inductive injp_acci : relation injp_world :=
    injp_acci_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2')
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_i (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_i (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_external f f' m1 m2 ->
                     inject_incr_local f f' m1 ->
                     free_preserved f m1 m1' m2' ->
                     injp_acci (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

(** injp_acce: the transition for external calls: when the current thread takes the control again (thread id is the same), new threads may be introduced
               the private memory of the current thread is unchanged by other threads *)
Inductive injp_acce :  relation injp_world :=
    injp_acce_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                       (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_e (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_e (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_internal f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     injp_acce (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Record unchanged_on_g (P : block -> Z -> Prop) (m_before m_after : mem) : Prop :=
  mk_unchanged_on_g
    { unchanged_on_thread_g : (Mem.next_tid (Mem.support m_before) <= Mem.next_tid (Mem.support m_after))%nat
                              /\ Mem.tid (Mem.support m_before) <> Mem.tid (Mem.support m_after);
      unchanged_on_g' : Mem.unchanged_on (Mem.thread_internal_P P m_before) m_before m_after }.

Definition free_preserved_g j m1 m1' m2' :=
  forall b1 ofs1 b2 delta,
    j b1 = Some (b2, delta) -> fst b1 = Mem.tid (Mem.support m1) ->
    Mem.perm m1 b1 ofs1 Max Nonempty -> ~ Mem.perm m1' b1 ofs1 Max Nonempty ->
    ~ Mem.perm m2' b2 (ofs1 + delta) Max Nonempty.

(** injp_accg: the transition for one thread [t] to another (usually the current running) thread,
               New threads may be introduced, the thread [t] has switched out and never runs again yet, thus its
               private memory is unchanged *)
Inductive injp_accg : relation injp_world :=
    injp_accg_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                       (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                     injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     unchanged_on_g (loc_unmapped f) m1 m1' ->
                     unchanged_on_g (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_internal f f' m1 m2 ->
                     inject_separated_noglobal f f' ->
                     free_preserved_g f m1 m1' m2' ->
                     injp_accg (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').


Instance injp_acci_preo : PreOrder injp_acci.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. intros. congruence.
    + red. intros. congruence.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + red. eauto.
    + split. eauto. apply Mem.unchanged_on_refl.
    + split. eauto. apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
    + red. intros. congruence.
    + red. intros. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hb1 Hb2 Hr1 Hr2 Hp1 Hp2 [S1 H1] [S2 H2] Hi Hs1 Hs2 Hf].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hb1' Hb2' Hr1' Hr2' Hp1' Hp2' [S1' H1'] [S2' H2'] Hi' Hs1' Hs2' Hf']; subst.
    constructor.
    + red. intros. destruct (Mem.sup_dec b (Mem.support m1')).
      exploit Hb1; eauto. exploit Hb1'; eauto.
      inv S1. congruence.
    + red. intros. destruct (Mem.sup_dec b (Mem.support m2')).
      exploit Hb2; eauto. exploit Hb2'; eauto.
      inv S2. congruence.
    + red. intros. eapply Hr1; eauto. eapply Hr1'; eauto.
      inversion H1. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + red. intros. eapply Hr2; eauto. eapply Hr2'; eauto.
      inversion H2. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
    + split. eauto.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped, Mem.thread_external_P. simpl.
      intros b1 _ [Hb Hb0'] Hb1''. split.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs1; eauto. contradiction. auto.
      inv S1. congruence.
    + split. eauto.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach, Mem.thread_external_P. simpl.
      intros b2 ofs2 [Hbb2 Hbb2'] Hv. split. intros b1 delta Hb'.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply Hi in Hb; split; congruence); subst.
        specialize (Hbb2 b1 delta Hb). intro. apply Hbb2.
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs1; eauto.
        inv Hm. inv mi_thread. inv Hms. rewrite H0.
        inversion Hm'. inv mi_thread. erewrite Hjs0; eauto.
      * inv S2. congruence.
    + eapply inject_incr_trans; eauto.
    + intros b1 b2 delta Hb Hb'' Htid.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs1; eauto.
      * edestruct Hs1'; eauto. inv S1. congruence.
        intuition eauto using Mem.valid_block_unchanged_on.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs2; eauto.
      * exploit Hs2'; eauto. intro. destruct S1. congruence.
    + red. intros.
      destruct (Mem.perm_dec m1' b1 ofs1 Max Nonempty).
      * eapply Hf'; eauto. inv S1. congruence.
      * red in Hp2'. intro. apply Hp2' in H5.
        eapply Hf; eauto. inv H2. apply unchanged_on_support.
        eapply Mem.valid_block_inject_2; eauto.
Qed.

Instance injp_acce_preo : PreOrder injp_acce.
Proof.
  split.
  - intros [f m1 m2].
    constructor.
    + red. intros. congruence.
    + red. intros. congruence.
    + red. eauto.
    + red. eauto.
    + split. split; eauto. apply Mem.unchanged_on_refl.
    + split. split; eauto. apply Mem.unchanged_on_refl.
    + apply inject_incr_refl.
    + intros b ofs. congruence.
    + red. intros. congruence.
  - intros w1 w2 w3 H12 H23.
    destruct H12 as [f m1 m2 Hm f' m1' m2' Hm' Hr1 Hr2 Hp1 Hp2 [S1 H1] [S2 H2] Hi Hs1 Hs2].
    inversion H23 as [? ? ? ? f'' m1'' m2'' Hm'' Hr1' Hr2' Hp1' Hp2' [S1' H1'] [S2' H2'] Hi' Hs1' Hs2']; subst.
    constructor.
    + red. intros. eapply Hr1; eauto. eapply Hr1'; eauto.
      inversion H1. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + red. intros. eapply Hr2; eauto. eapply Hr2'; eauto.
      inversion H2. apply unchanged_on_support; eauto.
      intros. intro. eapply H3; eauto.
    + intros b ofs p Hb ?.
      eapply Hp1, Hp1'; eauto using Mem.valid_block_unchanged_on.
    + intros b ofs p Hb ?.
      eapply Hp2, Hp2'; eauto using Mem.valid_block_unchanged_on.
    + split. inv S1. inv S1'. split. lia. congruence.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_unmapped, Mem.thread_internal_P. simpl.
      intros b1 _ [Hb Hb0'] Hb1''. split.
      destruct (f' b1) as [[b2 delta] | ] eqn:Hb'; eauto.
      edestruct Hs1; eauto. contradiction. auto.
      inv S1. congruence.
    + split. inv S2. inv S2'. split. lia. congruence.
      eapply mem_unchanged_on_trans_implies_valid; eauto.
      unfold loc_out_of_reach, Mem.thread_external_P. simpl.
      intros b2 ofs2 [Hbb2 Hbb2'] Hv. split. intros b1 delta Hb'.
      destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
            by (eapply Hi in Hb; split; congruence); subst.
        specialize (Hbb2 b1 delta Hb). intro. apply Hbb2.
        eapply Hp1; eauto. eapply Mem.valid_block_inject_1; eauto.
      * edestruct Hs1; eauto.
        inv Hm. inv mi_thread. inv Hms. rewrite H0.
        inversion Hm'. inv mi_thread. erewrite Hjs0; eauto.
      * inv S2. congruence.
    + eapply inject_incr_trans; eauto.
    + intros b1 b2 delta Hb Hb'' HT.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs1; eauto.
      * edestruct Hs1'; eauto. inv S1. congruence.
        intuition eauto using Mem.valid_block_unchanged_on.
    + intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply Hi' in Hb'; split; congruence); subst.
        eapply Hs2; eauto.
      * edestruct Hs2'; eauto.
Qed.

(*
Instance injp_accg_refl : Reflexive injp_accg.
Proof.
  intros [f m1 m2].
    constructor; auto.
    + red. eauto.
    + red. eauto.
    + split. auto. apply Mem.unchanged_on_refl.
    + apply Mem.unchanged_on_refl.
    + intros b ofs. congruence.
Qed.
*)



(** The properties about the preservation of injp accessibility
    by corresponding memory operations on related memories. *)

Lemma unchanged_on_tl_i : forall m P m',
    Mem.unchanged_on_tl P m m' ->
    Mem.unchanged_on_i P m m'.
Proof.
  intros. inv H. split. auto. eapply Mem.unchanged_on_implies; eauto.
  intros. apply H.
Qed.

Lemma unchanged_on_tl_e : forall m P m',
    Mem.unchanged_on_tl P m m' ->
    Mem.unchanged_on_e P m m'.
Proof.
  intros. inv H. split. inv unchanged_on_thread_tl. split. lia. auto.
  eapply Mem.unchanged_on_implies; eauto.
  intros. apply H.
Qed.

Record injp_world' :=
  injpw' {
    injpw_meminj : meminj;
    injpw_m: mem;
    injpw_tm: mem;
    }.

Inductive injp_acc_tl' : relation injp_world' :=
  injp_acc_tl_intro' : forall (f : meminj) (m1 m2 : mem) (f' : meminj) 
                        (m1' m2' : mem)
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                      injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_tl (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_tl (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated f f' m1 m2 ->
                     inject_incr_local f f' m1->
                     free_preserved f m1 m1' m2' ->
                     injp_acc_tl' (injpw' f m1 m2) (injpw' f' m1' m2').

(* thread_local, the local accessibility for internel transitions and builtin functions
   which only change public memories  *)
Inductive injp_acc_tl : relation injp_world :=
    injp_acc_tl_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2')
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                      injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_tl (loc_unmapped f) m1 m1' ->
                     Mem.unchanged_on_tl (loc_out_of_reach f m1) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated f f' m1 m2 ->
                     inject_incr_local f f' m1->
                     free_preserved f m1 m1' m2' ->
                     injp_acc_tl (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Lemma injp_acc_tl_i : forall w1 w2, injp_acc_tl w1 w2 -> injp_acci w1 w2.
Proof.
  intros. inv H. constructor; eauto using unchanged_on_tl_i.
Qed.

Lemma injp_acc_tl_e : forall w1 w2, injp_acc_tl w1 w2 -> injp_acce w1 w2.
Proof.
  intros. inv H. constructor; eauto using unchanged_on_tl_e.
  eapply inject_incr_local_noglobal; eauto.
Qed.

Lemma injp_acc_tl_alloc1: forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2',
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, 0) ->
    (forall b, b<> b1 -> f' b = f b) ->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f' m1' m2').
Proof.
  intros. constructor.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H. eauto. intros [|]. subst.
    apply Mem.alloc_result in H. subst. reflexivity. congruence.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H0. eauto. intros [|]. subst.
    apply Mem.alloc_result in H0. subst. reflexivity. congruence.
  - eauto using Mem.ro_unchanged_alloc.
  - eauto using Mem.ro_unchanged_alloc.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - assumption.
  - red. intros b b' delta Hb Hb'.
    assert (b = b1).
    {
      destruct (eq_block b b1); eauto.
      rewrite H3 in Hb'; eauto.
      congruence.
    }
    assert (b' = b2) by congruence.
    subst.
    split; eauto using Mem.fresh_block_alloc.
  - red. intros.
    destruct (eq_block b0 b1). subst.
    apply Mem.alloc_result in H. rewrite H. reflexivity.
    erewrite H3 in H5. congruence. auto.
  - red. intros. exfalso. apply H7. eauto with mem.
Qed.


Lemma injp_acc_tl_alloc: forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2' Hm Hm',
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, 0) ->
    (forall b, b<> b1 -> f' b = f b) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_alloc1. apply H. apply H0. all : eauto.
  intro X. inv X. constructor; eauto.
Qed.

Lemma injp_acc_tl_alloc'1: forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2' d,
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, d) ->
    inject_separated f f' m1 m2 ->
    inject_incr_local f f' m1->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f' m1' m2' ).
Proof.
  intros. constructor.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H. eauto. intros [|]. subst.
    apply Mem.alloc_result in H. subst. reflexivity. congruence.
  - red. intros.
    exploit Mem.valid_block_alloc_inv. apply H0. eauto. intros [|]. subst.
    apply Mem.alloc_result in H0. subst. reflexivity. congruence.
  - eauto using Mem.ro_unchanged_alloc.
  - eauto using Mem.ro_unchanged_alloc.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b1); eauto; subst.
    eelim (Mem.fresh_block_alloc m1); eauto.
  - intros b ofs p Hb Hp.
    eapply Mem.perm_alloc_inv in Hp; eauto.
    destruct (eq_block b b2); eauto; subst.
    eelim (Mem.fresh_block_alloc m2); eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - eapply Mem.alloc_unchanged_on_tl; eauto.
  - assumption.
  - auto. 
  - auto. 
  - red. intros. exfalso. apply H8. eauto with mem.
Qed.

Lemma injp_acc_tl_alloc': forall f f' m1 m2 b1 b2 lo1 hi1 lo2 hi2 m1' m2' Hm Hm' d,
    Mem.alloc m1 lo1 hi1 = (m1',b1) ->
    Mem.alloc m2 lo2 hi2 = (m2',b2) ->
    inject_incr f f' ->
    f' b1 = Some (b2, d) ->
    inject_separated f f' m1 m2 ->
    inject_incr_local f f' m1->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_alloc'1. apply H. apply H0. all: eauto.
  intro. inv H5.
  constructor; eauto.
Qed.

Lemma injp_acc_tl_free': forall f m1 m2 b1 b2 delta lo1 sz m1' m2',
    Mem.free m1 b1 lo1 (lo1 + sz) = Some m1' ->
    Mem.free m2 b2 (lo1 + delta) (lo1 + sz + delta) = Some m2' ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f m1' m2').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_free in H3; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_free in H3; eauto. congruence.
  - eauto using Mem.ro_unchanged_free.
  - eauto using Mem.ro_unchanged_free.
  - red. eauto using Mem.perm_free_3.
  - red. eauto using Mem.perm_free_3.
  - eapply Mem.free_unchanged_on_tl; eauto.
    intros. intro. congruence.
  - eapply Mem.free_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.free_range_perm; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. 
    eapply Mem.perm_free_inv in H as Hd; eauto. destruct Hd.
    + destruct H6. subst. rewrite H1 in H2. inv H2.
      eapply Mem.perm_free_2; eauto. lia.
    + congruence.
Qed.

Lemma injp_acc_tl_free: forall f m1 m2 b1 b2 delta lo1 sz m1' m2' Hm Hm',
    Mem.free m1 b1 lo1 (lo1 + sz) = Some m1' ->
    Mem.free m2 b2 (lo1 + delta) (lo1 + sz + delta) = Some m2' ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_free'. apply H. apply H0. eauto.
  intros X. inv X. constructor; eauto.
Qed.

Lemma injp_acc_tl_free_0': forall f m1 m2 b1 b2 delta sz m1' m2' sz',
    Mem.free m1 b1 0 sz = Some m1' ->
    Mem.free m2 b2 delta sz' = Some m2' ->
    f b1 = Some (b2, delta) ->
    sz' = sz + delta ->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f m1' m2').
Proof.
  intros. exploit injp_acc_tl_free'.
  replace sz with (0 + sz) in H by lia. eauto.
  rewrite !Z.add_0_l. subst sz'. eauto. eauto.
  intro. apply H3.
Qed.

Lemma injp_acc_tl_free_0: forall f m1 m2 b1 b2 delta sz m1' m2' Hm Hm' sz',
    Mem.free m1 b1 0 sz = Some m1' ->
    Mem.free m2 b2 delta sz' = Some m2' ->
    f b1 = Some (b2, delta) ->
    sz' = sz + delta ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_free.
  replace sz with (0 + sz) in H by lia. eauto.
  rewrite !Z.add_0_l. subst sz'. eauto. eauto.
  intro. apply H3.
Qed.

Lemma injp_acc_tl_store' : forall f chunk v1 v2 b1 b2 ofs1 delta m1 m2 m1' m2',
    Mem.store chunk m1 b1 ofs1 v1 = Some m1' ->
    Mem.store chunk m2 b2 (ofs1 + delta) v2 = Some m2' ->
    (* Val.inject f v1 v2 -> *)
    f b1 = Some (b2,delta) ->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f m1' m2').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_store in H3; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_store in H3; eauto. congruence.
  - eauto using Mem.ro_unchanged_store.
  - eauto using Mem.ro_unchanged_store.
  - red. eauto using Mem.perm_store_2.
  - red. eauto using Mem.perm_store_2.
  - eapply Mem.store_unchanged_on_tl; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.store_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs H'.
    eelim H'; eauto.
    edestruct (Mem.store_valid_access_3 chunk m1); eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply H2; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. exfalso. apply H5. eauto with mem.
Qed.

Lemma injp_acc_tl_store : forall f chunk v1 v2 b1 b2 ofs1 delta m1 m2 m1' m2' Hm Hm',
    Mem.store chunk m1 b1 ofs1 v1 = Some m1' ->
    Mem.store chunk m2 b2 (ofs1 + delta) v2 = Some m2' ->
    (* Val.inject f v1 v2 -> *)
    f b1 = Some (b2,delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_store'. apply H. apply H0. eauto.
  intros X. inv X. constructor; eauto.
Qed.

Lemma injp_acc_tl_storev : forall f chunk v1 v2 a1 a2 m1 m2 m1' m2' Hm Hm',
    Mem.storev chunk m1 a1 v1 = Some m1' ->
    Mem.storev chunk m2 a2 v2 = Some m2' ->
    Val.inject f a1 a2 -> (* Val.inject f v1 v2 -> *)
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. unfold Mem.storev in *. destruct a1; try congruence.
  inv H1.
  erewrite Mem.address_inject in H0. 2: apply Hm. 3: eauto.
  eapply injp_acc_tl_store; eauto.
  apply Mem.store_valid_access_3 in H.
  destruct H as [A B].
  apply A. destruct chunk; simpl; lia.
Qed.

Lemma injp_acc_tl_storebytes'1 : forall f b1 b2 ofs1 delta vs1 vs2 m1 m2 m1' m2',
    Mem.storebytes m1 b1 ofs1 vs1 = Some m1' ->
    Mem.storebytes m2 b2 (ofs1 + delta) vs2 = Some m2' ->
    length vs1 = length vs2 ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl' (injpw' f m1 m2) (injpw' f m1' m2').
Proof.
  intros. constructor.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H4; eauto. congruence.
  - red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H4; eauto. congruence.
  - eauto using Mem.ro_unchanged_storebytes.
  - eauto using Mem.ro_unchanged_storebytes.
  - red. eauto using Mem.perm_storebytes_2.
  - red. eauto using Mem.perm_storebytes_2.
  - eapply Mem.storebytes_unchanged_on_tl; eauto.
    unfold loc_unmapped. congruence.
  - eapply Mem.storebytes_unchanged_on_tl; eauto.
    unfold loc_out_of_reach.
    intros ofs Hofs HH. 
    eelim HH; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; [ | eapply perm_any_N].
    eapply Mem.storebytes_range_perm; eauto.
    extlia.
  - apply inject_incr_refl.
  - apply inject_separated_refl.
  - red. intros. congruence.
  - red. intros. exfalso. apply H6. eauto with mem.
Qed.

Lemma injp_acc_tl_storebytes' : forall f b1 b2 ofs1 delta vs1 vs2 m1 m2 m1' m2' Hm Hm',
    Mem.storebytes m1 b1 ofs1 vs1 = Some m1' ->
    Mem.storebytes m2 b2 (ofs1 + delta) vs2 = Some m2' ->
    length vs1 = length vs2 ->
    f b1 = Some (b2, delta) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. exploit injp_acc_tl_storebytes'1. apply H. apply H0. all: eauto.
  intro X. inv X. constructor; eauto.
Qed.

Lemma injp_acc_tl_storebytes : forall f b1 b2 ofs1 ofs2 vs1 vs2 m1 m2 m1' m2' Hm Hm',
    Mem.storebytes m1 b1 (Ptrofs.unsigned ofs1) vs1 = Some m1' ->
    Mem.storebytes m2 b2 (Ptrofs.unsigned ofs2) vs2 = Some m2' ->
    length vs1 = length vs2 ->
    Val.inject f (Vptr b1 ofs1) (Vptr b2 ofs2) ->
    injp_acc_tl (injpw f m1 m2 Hm) (injpw f m1' m2' Hm').
Proof.
  intros. destruct vs1.
  - destruct vs2; inv H1.
    constructor.
    + red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H3; eauto. congruence.
    + red. intros. unfold Mem.valid_block in *.
    erewrite Mem.support_storebytes in H3; eauto. congruence.
    + eauto using Mem.ro_unchanged_storebytes.
    + eauto using Mem.ro_unchanged_storebytes.
    + red. eauto using Mem.perm_storebytes_2.
    + red. eauto using Mem.perm_storebytes_2.
    + eapply Mem.storebytes_unchanged_on_tl; eauto.
      unfold loc_unmapped. inv H2. congruence.
    + eapply Mem.storebytes_unchanged_on_tl; eauto.
      simpl. intro. extlia.
    + apply inject_incr_refl.
    + apply inject_separated_refl.
    + red. intros. congruence.
    + red. intros. exfalso. apply H5. eauto with mem.
  - inv H2.
    eapply injp_acc_tl_storebytes'; eauto.
    erewrite <- Mem.address_inject; eauto.
    eapply Mem.perm_storebytes_1; eauto.
    apply Mem.storebytes_range_perm in H.
    eapply H. simpl. lia.
Qed.


(* The internal changes which may change the [private] regions which are not in the
   initial world *)

(** able to change: 1. all public 
                    2. private : only local & not in initial 

    unchanged : private & ( other threads \/ in intial)
*)

(** This should indicate acci, which says that private & other threads are unchanged *)
Inductive injp_acc_small (w0: injp_world) : relation injp_world :=
    injp_acc_small_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
                        (m1' m2' : mem) (Hm' : Mem.inject f' m1' m2') j m10 m20 Hm0
                     (Hnb1: new_block_local m1 m1')
                     (Hnb2:new_block_local m2 m2'),
                     w0 = injpw j m10 m20 Hm0 ->
                     Mem.ro_unchanged m1 m1' ->
                     Mem.ro_unchanged m2 m2' ->
                      injp_max_perm_decrease m1 m1' ->
                     injp_max_perm_decrease m2 m2' ->
                     Mem.unchanged_on_tl (fun b ofs => loc_unmapped f b ofs /\
                                        (fst b <> Mem.tid (Mem.support m1) \/ Mem.valid_block m10 b)) m1 m1' ->
                     Mem.unchanged_on_tl (fun b ofs => loc_out_of_reach f m1 b ofs /\
                                        (fst b <> Mem.tid (Mem.support m1) \/ Mem.valid_block m20 b)) m2 m2' ->
                     inject_incr f f' ->
                     inject_separated_external f f' m1 m2 ->
                     inject_incr_local f f' m1->
                     inject_separated f f' m10 m20 ->
                     free_preserved f m1 m1' m2' ->
                     injp_acc_small w0 (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').

Lemma injp_acce_small : forall w0 w1 w2,
    injp_acce w0 w1 -> injp_acc_small w0 w1 w2 -> injp_acce w0 w2.
Proof.
  intros.
  inv H. inv H0. inv H12.
  destruct H5 as [[S51 S52] H5].
  destruct H6 as [[S61 S62] H6].
  destruct H17 as [[S171 S172] H17].
  destruct H18 as [[S181 S182] H18].
  econstructor; eauto.
  - eapply Mem.ro_unchanged_trans; eauto. inv H5. auto.
  - eapply Mem.ro_unchanged_trans; eauto. inv H6. auto.
  - red. intros. eapply H3; eauto. eapply H15; eauto. inv H5.
    apply unchanged_on_support. auto.
  - red. intros. eapply H4; eauto. eapply H16; eauto. inv H6.
    apply unchanged_on_support. auto.
  - split. constructor. lia. congruence.
    eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. destruct H. split; auto. red in H.
    destruct (f' b) as [[? ?]|] eqn: Hf'.
    exploit H8; eauto. intros [X Y]. congruence.
    auto.
  - split. constructor. lia. congruence.
    eapply mem_unchanged_on_trans_implies_valid; eauto.
    intros. simpl. destruct H. split; auto. red in H.
    red. intros. destruct (j b0) as [[b' d']|] eqn:Hj.
    apply H7 in Hj as Heq. rewrite H11 in Heq. inv Heq.
    intro. eapply H; eauto. eapply H3; eauto using Mem.valid_block_inject_1.
    exploit H8; eauto. inv Hm. inv mi_thread. inv Hms.
    rewrite H22. inversion Hm'. inv mi_thread.
    erewrite Hjs0; eauto.
    intros [X Y]. congruence.
  - eapply inject_incr_trans; eauto.
  - intros b1 b2 delta Hb Hb'' Ht.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H19 in Hb'; split; congruence); subst.
        eapply H8; eauto.
      * eauto.
  - intros b1 b2 delta Hb Hb''.
      destruct (f' b1) as [[xb2 xdelta] | ] eqn:Hb'.
      * assert (xb2 = b2 /\ xdelta = delta) as [? ?]
          by (eapply H19 in Hb'; split; congruence); subst.
        eapply H9; eauto.
      * eapply inject_incr_local_noglobal; eauto.
Qed.

Lemma injp_acc_small_acci : forall w0 w1 w2,
    injp_acc_small w0 w1 w2 ->
    injp_acci w1 w2.
Proof.
  intros. inv H. constructor; eauto.
  - destruct H5. split; auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split. auto. left. auto.
  - destruct H6. split; auto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. destruct H. split. auto. left. inv Hm.
    inv mi_thread. inv Hms. congruence.
Qed.

Lemma inject_tid: forall j m1 m2,
    Mem.inject j m1 m2 -> Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2).
Proof.
  intros. inv H. inv mi_thread. inv Hms. auto.
Qed.

Lemma inject_block_tid : forall j m1 m2 b1 b2 d,
    Mem.inject j m1 m2 ->
    j b1 = Some (b2, d) ->
    fst b1 = fst b2.
Proof.
  intros. inv H. inv mi_thread. eapply Hjs; eauto.
Qed.


Program Instance injp_world_id : World injp_world :=
    {
      w_state := injp_world;
      w_lens := lens_id;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.

Import GS.
Program Definition c_injp : callconv li_c li_c :=
  {|
    ccworld := injp_world;
    ccworld_world := injp_world_id;
    match_senv w := CKLR.match_stbls injp w;
    match_query := cc_c_query injp;
    match_reply := cc_c_reply injp;    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.


Program Instance lens_injp_locset : Lens (signature * injp_world) injp_world :=
  {
    get := snd;
    set := fun w wp => (fst w, wp);
  }.

Program Instance injp_world_id_l : World (signature * injp_world) :=
    {
      w_state := injp_world;
      w_lens := lens_injp_locset;
      w_acci := injp_acci;
      w_acce := injp_acce;
      w_acci_trans := injp_acci_preo;
    }.
(* cc_locset *)
Program Definition locset_injp : callconv li_locset li_locset :=
  {|
    ccworld := signature * injp_world;
    ccworld_world := injp_world_id_l;
    match_senv w := CKLR.match_stbls injp (snd w);
    match_query w := cc_locset_query injp (fst w) (snd w);
    match_reply w := cc_locset_reply injp (fst w) (snd w);    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Program Definition mach_injp : callconv li_mach li_mach :=
  {|
    ccworld := injp_world;
    ccworld_world := injp_world_id;
    match_senv w := CKLR.match_stbls injp w;
    match_query := cc_mach_mq injp;
    match_reply := cc_mach_mr injp;    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.

Program Definition asm_injp : callconv li_asm li_asm :=
  {|
    ccworld := injp_world;
    ccworld_world := injp_world_id;
    match_senv w := CKLR.match_stbls injp w;
    match_query := cc_asm_match' injp;
    match_reply := cc_asm_match injp;    
  |}.
Next Obligation.
  inv H. inv H0. auto.
Qed.
Next Obligation.
  intros. inv H. erewrite <- Genv.valid_for_match; eauto.
Qed.
