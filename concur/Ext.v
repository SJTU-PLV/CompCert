Require Import Conventions Mach Asm.
Require Import CKLR LanguageInterface.
Require Import Locations CallConv.
Require Import Extends CA CallconvBig.

Import GS.
Inductive ext_acci : relation ext_world :=
    ext_acci_intro : forall (m1 m2 : mem) (Hm : Mem.extends m1 m2) 
                     (m1' m2' : mem) (Hm' : Mem.extends m1' m2')
                     (TID1: Mem.tid (Mem.support m1) = Mem.tid (Mem.support m1'))
                     (TID2: Mem.tid (Mem.support m2) = Mem.tid (Mem.support m2'))
                     (SUP1: Mem.sup_include (Mem.support m1) (Mem.support m1'))
                     (SUP2: Mem.sup_include (Mem.support m2) (Mem.support m2'))
                     (MPD1: Mem.max_perm_decrease m1 m1')
                     (MPD2: Mem.max_perm_decrease m2 m2')
                     (FREEP: free_preserved_ext m1 m1' m2'),
                     ext_acci (extw m1 m2 Hm) (extw m1' m2' Hm').

Instance ext_acci_preo : PreOrder ext_acci.
Proof.
  split.
  - intros [m1 m2 Hm]. constructor; eauto; try red; intros; auto.
  - intros [m1 m2 Hm] [m1' m2' Hm'] [m1'' m2'' Hm''] HA HB.
    inv HA. inv HB. constructor; eauto; try congruence.
    + red. intros. apply MPD1. auto. apply MPD0. apply SUP1. auto. auto.
    + red. intros. apply MPD2. auto. apply MPD3. apply SUP2. auto. auto.
    + red in FREEP, FREEP0.
      red. intros.
      destruct (Mem.perm_dec m1' b ofs Max Nonempty).
      * eapply FREEP0; eauto. congruence.
      * intro. eapply FREEP; eauto. apply MPD3; auto.
        apply SUP2. inv Hm. rewrite <- mext_sup.
        eapply Mem.perm_valid_block; eauto.
Qed.

Lemma ext_acci_free : forall m m' tm tm' Hm b lo hi Hm',
    Mem.free m b lo hi = Some m' ->
    Mem.free tm b lo hi = Some tm' ->
    ext_acci (extw m tm Hm) (extw m' tm' Hm').
Proof.
  intros. constructor; eauto;
    try erewrite <- Mem.support_free; eauto;
    try red; intros; eauto with mem.
  eapply Mem.perm_free_inv in H2; eauto. destruct H2; auto.
  destruct H2. subst.
  eapply Mem.perm_free_2; eauto.
Qed.

Lemma ext_acci_store : forall m m' tm tm' Hm chunk b ofs v1 v2 Hm',
    Mem.store chunk m b ofs v1 = Some m' ->
    Mem.store chunk tm b ofs v2 = Some tm' ->
    ext_acci (extw m tm Hm) (extw m' tm' Hm').
Proof.
  intros. constructor; eauto;
    try erewrite <- Mem.support_store; eauto;
    try red; intros; eauto with mem.
Qed.

Lemma ext_acci_storev : forall m m' tm tm' Hm chunk a1 a2 v1 v2 Hm',
    Mem.storev chunk m a1 v1 = Some m' ->
    Mem.storev chunk tm a2 v2 = Some tm' ->
    Val.lessdef a1 a2 ->
    ext_acci (extw m tm Hm) (extw m' tm' Hm').
Proof.
  intros. inv H1; try inv H.
  destruct a2; inv H0. inv H2. eapply ext_acci_store; eauto.
Qed.
(*
Lemma ext_acci_storebytes : forall m m' tm tm' Hm b ofs vs1 vs2 Hm',
    Mem.storebytes m b ofs vs1 = Some m' ->
    Mem.storebytes tm b ofs vs2 = Some tm' ->
    Val.lessdef_list vs1 vs2 ->
    ext_acci (extw m tm Hm) (extw m' tm' Hm').
Proof.
  intros. constructor; eauto;
    try erewrite <- Mem.support_free; eauto;
    try red; intros; eauto with mem.
  eapply Mem.perm_free_inv in H2; eauto. destruct H2; auto.
  destruct H2. subst.
  eapply Mem.perm_free_2; eauto.
Qed.
*)
Lemma ext_acci_alloc : forall m m' tm tm' Hm b1 b2 lo1 hi1 lo2 hi2 Hm',
    Mem.alloc m lo1 hi1 = (m', b1) ->
    Mem.alloc tm lo2 hi2 = (tm', b2) ->
    ext_acci (extw m tm Hm) (extw m' tm' Hm').
Proof.
  intros. apply Mem.support_alloc in H as S1. apply Mem.support_alloc in H0 as S2.
  constructor; eauto. rewrite S1. eauto. rewrite S2. reflexivity.
  rewrite S1. eauto with mem. rewrite S2. eauto with mem.
  red. intros. eauto with mem.
  red. intros. eauto with mem.
  red. intros. eauto with mem.
Qed.

Inductive ext_acce : relation ext_world :=
    ext_acce_intro : forall (m1 m2 : mem) (Hm : Mem.extends m1 m2) 
                     (m1' m2' : mem) (Hm' : Mem.extends m1' m2')
                     (TID1: Mem.tid (Mem.support m1) = Mem.tid (Mem.support m1'))
                     (TID2: Mem.tid (Mem.support m2) = Mem.tid (Mem.support m2'))
                     (SUP1: Mem.sup_include (Mem.support m1) (Mem.support m1'))
                     (SUP2: Mem.sup_include (Mem.support m2) (Mem.support m2'))
                     (MPD1: Mem.max_perm_decrease m1 m1')
                     (MPD2: Mem.max_perm_decrease m2 m2'),
                     ext_acce (extw m1 m2 Hm) (extw m1' m2' Hm').


Definition free_preserved_ext_g (m1 m1' m2': mem) : Prop :=
  forall b ofs, fst b = Mem.tid (Mem.support m1) ->
           Mem.perm m1 b ofs Max Nonempty ->
           ~ Mem.perm m1' b ofs Max Nonempty ->
           ~ Mem.perm m2' b ofs Max Nonempty.


Inductive ext_accg : relation ext_world :=
    ext_accg_intro : forall (m1 m2 : mem) (Hm : Mem.extends m1 m2) 
                     (m1' m2' : mem) (Hm' : Mem.extends m1' m2')
                     (TID1: Mem.tid (Mem.support m1) <> Mem.tid (Mem.support m1'))
                     (TID2: Mem.tid (Mem.support m2) <> Mem.tid (Mem.support m2'))
                     (SUP1: Mem.sup_include (Mem.support m1) (Mem.support m1'))
                     (SUP2: Mem.sup_include (Mem.support m2) (Mem.support m2'))
                     (MPD1: Mem.max_perm_decrease m1 m1')
                     (MPD2: Mem.max_perm_decrease m2 m2')
                     (FREEP: free_preserved_ext_g m1 m1' m2'),
      ext_accg (extw m1 m2 Hm) (extw m1' m2' Hm').

Instance ext_acce_preo : PreOrder ext_acce.
Proof.
  split.
  - intros [m1 m2 Hm]. constructor; eauto; try red; intros; auto.
  - intros [m1 m2 Hm] [m1' m2' Hm'] [m1'' m2'' Hm''] HA HB.
    inv HA. inv HB. constructor; eauto; try congruence.
    + red. intros. apply MPD1. auto. apply MPD0. apply SUP1. auto. auto.
    + red. intros. apply MPD2. auto. apply MPD3. apply SUP2. auto. auto.
Qed.

Lemma ext_acci_acce : forall w1 w2, ext_acci w1 w2 -> ext_acce w1 w2.
Proof. intros. inv H. constructor; eauto. Qed.

Hint Resolve ext_acci_acce : core.

Program Instance ext_world_id : World ext_world :=
    {
      w_state := ext_world;
      w_lens := lens_id;
      w_acci := ext_acci;
      w_acce := ext_acce;
      w_acci_trans := ext_acci_preo;
    }.

Program Definition c_ext : callconv li_c li_c :=
  {|
    ccworld := ext_world;
    ccworld_world := ext_world_id;
    match_senv w := eq;
    match_query := cc_c_query ext;
    match_reply := cc_c_reply ext;    
  |}.


Program Instance lens_ext_locset : Lens (signature * ext_world) ext_world :=
  {
    get := snd;
    set := fun w wp => (fst w, wp);
  }.

Program Instance ext_world_id_l : World (signature * ext_world) :=
    {
      w_state := ext_world;
      w_lens := lens_ext_locset;
      w_acci := ext_acci;
      w_acce := ext_acce;
      w_acci_trans := ext_acci_preo;
    }.

Program Definition locset_ext : callconv li_locset li_locset :=
  {|
    ccworld := signature * ext_world;
    ccworld_world := ext_world_id_l;
    match_senv w := eq;
    match_query w := cc_locset_query ext (fst w) (snd w);
    match_reply w := cc_locset_reply ext (fst w) (snd w);    
  |}.


Program Definition mach_ext : callconv li_mach li_mach :=
   {|
    ccworld := ext_world;
    ccworld_world := ext_world_id;
    match_senv w := eq;
    match_query := cc_mach_mq ext;
    match_reply := cc_mach_mr ext;    
  |}.

Program Definition asm_ext : callconv li_asm li_asm :=
   {|
    ccworld := ext_world;
    ccworld_world := ext_world_id;
    match_senv w := eq;
    match_query := cc_asm_match' ext;
    match_reply := cc_asm_match ext;    
  |}.
