Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Values Memory.
Require Import Conventions Mach Asm.
Require Import CKLR.
Require Import Locations CallConv.
Require Import Inject InjectFootprint.

(*
   cc_c_asm_injp   ≡    c_injp @  ≡ c_injp @
                        cc_c_asm    cc_c_locset @
                                    cc_locset_mach @
                                    cc_mach_asm
 *)

(** Definition of CA, the pure structure calling convention between C and assembly.
In CA, the only difference between the source and target memories is the outgoing arguments *)
  Record cc_ca_world :=
    caw{
        caw_sg : signature;
        caw_rs : regset;
        caw_m : mem
      }.

Definition make_locset_rs (rs: regset) (m:mem) (sp: val) (l:loc):=
  match l with
    |R r => rs (preg_of r)
    |S Outgoing ofs ty =>
      let v := load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) in Val.maketotal v
    |_ => Vundef
  end.

Inductive cc_c_asm_mq : cc_ca_world -> c_query -> query li_asm -> Prop:=
  cc_c_asm_mq_intro sg args m (rs: regset) tm (ls : Locmap.t):
    let sp := rs#SP in let ra := rs#RA in let vf := rs#PC in
    args = (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) ->
    ls = make_locset_rs rs tm sp ->
    args_removed sg sp tm m ->
    Val.has_type sp Tptr ->
    Val.has_type ra Tptr ->
    valid_blockv (Mem.support tm) sp ->
    vf <> Vundef -> ra <> Vundef ->
    cc_c_asm_mq
      (caw sg rs tm)
      (cq vf sg args m)
      (rs,tm).

Definition rs_getpair (p: rpair preg) (rs : regset) :=
  match p with
    |One r => rs r
    |Twolong r1 r2 => Val.longofwords (rs r1) (rs r2)
  end.

Inductive cc_c_asm_mr : cc_ca_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_mr_intro sg res tm m' tm' (rs rs' :regset) :
     let sp := rs#SP in
     res = rs_getpair (map_rpair preg_of (loc_result sg)) rs' ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     Mem.unchanged_on (not_init_args (size_arguments sg) sp) m' tm' ->
     Mem.unchanged_on (loc_init_args (size_arguments sg) sp) tm tm' ->
     Mem.support m' = Mem.support tm' ->
     (forall b ofs k p, loc_init_args (size_arguments sg) sp b ofs ->
                       ~ Mem.perm m' b ofs k p) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_mr
       (caw sg rs tm)
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm : callconv li_c li_asm :=
  {|
    match_senv _ := eq;
    match_query := cc_c_asm_mq;
    match_reply := cc_c_asm_mr
  |}.
Next Obligation.
  split; auto.
Defined.


Definition rs_to_mrs (rs : regset) :=
  fun r: mreg => rs (preg_of r).

Lemma cc_ca_cllmma :
  ccref (cc_c_asm) (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
Proof.
  intros [sg rs tm] se1 se2 q1 q2 Hse. destruct Hse.
  intros Hq. inversion Hq. subst sg0 rs0 tm0 q1 q2.
  exists (se1,sg,(se1,(lmw sg (rs_to_mrs rs) tm sp),
      (rs,Mem.support tm))).
  repeat apply conj; cbn in *; eauto.
  - exists (lq vf sg ls m). split.
    econstructor; eauto.
    exists (mq vf sp ra (rs_to_mrs rs) tm). split. rewrite H3.
    econstructor; eauto.
    econstructor; eauto.
  - intros cr ar [lr [Hr1 [mr [Hr2 Hr3]]]].
    inv Hr1. inv Hr2. inv Hr3.
    econstructor; eauto.
    + destruct (loc_result sg).
      -- simpl. rewrite <- H13. rewrite H9. reflexivity. simpl. auto.
      -- simpl. f_equal.
         rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
         rewrite <- H13. rewrite H9. reflexivity. simpl. eauto.
    + intros. rewrite <- H13. rewrite H12. reflexivity. eauto.
Qed.

Lemma cc_cllmma_ca :
  ccref (cc_c_locset @ cc_locset_mach @ cc_mach_asm) (cc_c_asm).
Proof.
  intros [[se' sg] [[se'' w2] [rs tm]]] se''' se q1 q2 Hse Hq.
  destruct Hse. inv H. destruct H0. inv H. inv H0.
  destruct Hq as [lq [Hq1 [mq [Hq2 Hq3]]]]. cbn in *.
  inv Hq1. inv Hq2. inv Hq3.
  rename rs1 into mrs. rename m0 into tm.
  exists (caw sg rs tm).
  repeat apply conj; eauto.
  - econstructor; eauto.
    apply Axioms.extensionality.
    intro r. destruct r; simpl; eauto.
  - intros r1 r2 Hr. inv Hr.
    set (ls' loc :=
           match loc with
             |R r => rs' (preg_of r)
             |_ => Vundef
           end
        ).
    exists (lr ls'  m'). split.
    constructor; eauto.
    destruct (loc_result); simpl; eauto.
    exists (mr (rs_to_mrs rs') tm'). split.
    constructor; eauto.
    intros. unfold rs_to_mrs. rewrite H3. eauto. eauto.
    constructor; eauto.
    inversion H8. eauto.
Qed.

Lemma ca_cllmma_equiv :
  cceqv cc_c_asm (cc_c_locset @ cc_locset_mach @ cc_mach_asm).
Proof. split. apply cc_ca_cllmma. apply cc_cllmma_ca. Qed.


(** Definition of cc_c_asm_injp (CAinjp) as the general calling convention between C and assembly.
The memory and arguments are related by some injection function. *)

Record cc_cainjp_world :=
  cajw {
      cajw_injp: world injp;
      cajw_sg : signature;
      cajw_rs : regset;
    }.

Inductive cc_c_asm_injp_mq : cc_cainjp_world -> c_query -> query li_asm -> Prop:=
  cc_c_asm_injp_mq_intro sg args m j (rs: regset) tm tm0 vf
    (Hm: Mem.inject j m tm):
    let tsp := rs#SP in let tra := rs#RA in let tvf := rs#PC in
    let targs := (map (fun p => Locmap.getpair p (make_locset_rs rs tm tsp))
                      (loc_arguments sg)) in
    Val.inject_list j args targs ->
    Val.inject j vf tvf ->
    (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              loc_out_of_reach j m b ofs) ->
    Val.has_type tsp Tptr ->
    Val.has_type tra Tptr ->
    valid_blockv (Mem.support tm) tsp ->
    args_removed sg tsp tm tm0 -> (* The Outgoing arguments are readable and freeable in tm *)
    vf <> Vundef -> tra <> Vundef ->
    cc_c_asm_injp_mq
      (cajw (injpw j m tm Hm) sg rs)
      (cq vf sg args m)
      (rs,tm).

Inductive cc_c_asm_injp_mr : cc_cainjp_world -> c_reply -> reply li_asm -> Prop :=
  cc_c_asm_injp_mr_intro sg res j m tm Hm j' m' tm' Hm' (rs rs' :regset) :
     let tsp := rs#SP in
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     Val.inject j' res tres ->
     injp_acc (injpw j m tm Hm) (injpw j' m' tm' Hm') ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     cc_c_asm_injp_mr
       (cajw (injpw j m tm Hm) sg rs)
       (cr res m')
       (rs', tm').

Program Definition cc_c_asm_injp : callconv li_c li_asm :=
  {|
    match_senv w := match_stbls injp (cajw_injp w);
    match_query := cc_c_asm_injp_mq;
    match_reply := cc_c_asm_injp_mr
  |}.
Next Obligation.
  inv H. inv H1. eauto.
Qed.
Next Obligation.
  inv H.
  eapply Genv.valid_for_match in H1.
  split; intros.
  apply H1. auto.
  apply H1. auto.
Qed.


Lemma cc_injpca_cainjp :
  ccref (cc_c injp @ cc_c_asm) (cc_c_asm_injp).
Proof.
  intros [[se2 [j m tm Hm']] [sg rs]] se1 se2' q1 q2 Hse Hq.
  destruct Hse. inv H. destruct H0.
  destruct Hq as [q1' [Hq1 Hq2]]. cbn in *.
  inv Hq1. cbn in *. inv H1. rename m1 into m. rename m2 into tm0.
  inv Hq2. cbn in *. rename caw_m0 into tm. rename sg0 into sg.
  inv H14.
  - (*easy: no Outgoing part*)
    rename tm0 into tm.
    exists (cajw (injpw j m tm Hm3) sg rs).
    repeat apply conj; eauto.
    + constructor; eauto.
    + econstructor; eauto.
      intros. inv H3. red in H1. rewrite H1 in H6. extlia.
      constructor; eauto.
    + intros r1 r2 Hr. inversion Hr. subst.
      exists (cr tres tm'). split.
      * econstructor; eauto. split.
        instantiate (1:= injpw j' m' tm' Hm'0).
        inv H14.
        constructor; eauto.
        constructor; eauto.
        constructor; eauto.
      * constructor; eauto with mem.
        inv H14.
        eapply Mem.unchanged_on_implies; eauto.
        intros. inv H3. red in H1. rewrite H1 in H9. extlia.
        intros. inv H3. red in H1. rewrite H1 in H6. extlia.
  - (*with Outgoing part*)
    assert (Htm: Mem.inject j m tm).
    { clear - Hm3 H3. inversion Hm3.
      constructor; eauto.
      - inversion  mi_inj.
        constructor; eauto.
        + intros. eapply Mem.perm_free_3; eauto.
        + intros. assert (Mem.mem_contents tm0 = Mem.mem_contents tm).
          apply Mem.free_result in H3. rewrite H3. cbn. reflexivity.
          rewrite <- H1. eauto.
      - intros. unfold Mem.valid_block in *.
        erewrite <- Mem.support_free; eauto.
      - intros.
        eapply Mem.perm_free_inv in H0 as PERM; eauto.
        destruct PERM.
        + (* in freed region -> Source no perm *)
          right. intro. destruct H1 as [Hb Hofs]. subst b2.
          exploit Mem.perm_inject; eauto. intro PERMtm0.
          eapply Mem.perm_free_2 in H3 as NOPERMtm0; eauto.
        + eapply mi_perm_inv; eauto.
    }
    assert (INIT_OUT: forall (b : block) (ofs : Z), loc_init_args (size_arguments sg) (rs RSP) b ofs -> loc_out_of_reach j m b ofs ).
    {
       intros. inv H10. subst sp. rewrite <- H1 in H11. inv H11.
        eapply Mem.perm_free_2 in H3 as NOPERM; eauto.
        red. intros. intro.
        exploit Mem.perm_inject. apply H10. apply Hm3.  eauto.
        intros. replace (ofs - delta + delta) with ofs in H13 by lia.
        apply NOPERM. eauto with mem.
    }
    exists (cajw (injpw j m tm Htm) sg rs).
    repeat apply conj; eauto.
    + constructor; eauto.
      erewrite <- Mem.support_free; eauto.
    + econstructor; eauto.
      subst sp. rewrite <- H1.
      eapply args_removed_free; eauto.
    + intros r1 r2 Hr. inv Hr. subst sp tsp. inv H23.
      assert {tm'0| Mem.free tm' sb (offset_sarg sofs 0) (offset_sarg sofs (size_arguments sg)) = Some tm'0}.
      {
        apply Mem.range_perm_free.
        red. intros.
        apply Mem.free_range_perm in H3 as RANGEtm. red in RANGEtm.
        inversion H31.
        eapply unchanged_on_perm; eauto. apply INIT_OUT. rewrite <- H1.
        constructor; eauto. rewrite <- H1 in H18. inv H18. eauto.
      }
      destruct X as [tm'0 FREE'].
      assert (INJ' : Mem.inject j' m' tm'0).
      {
        eapply Mem.free_right_inject; eauto. intros.
        assert (loc_out_of_reach j' m' sb (ofs+ delta)).
        eapply loc_out_of_reach_incr; eauto.
        eapply INIT_OUT; eauto. rewrite <- H1. econstructor; eauto.
        eapply inject_implies_dom_in; eauto.
        inv H18. rewrite <- H1 in H13. inv H13. eauto.
        red in H13. exploit H13; eauto. replace (ofs + delta - delta) with ofs by lia.
        eauto with mem.
      }
      exists (cr tres tm'0). repeat apply conj; eauto.
      * econstructor. split.
        instantiate (1:= injpw j' m' tm'0 INJ').
        -- constructor; eauto.
           ++ apply Mem.ro_unchanged_memval_bytes. apply Mem.ro_unchanged_memval_bytes in H27.
              red. intros. destruct (loc_init_args_dec (size_arguments sg) (rs RSP) b ofs).
              rewrite <- H1 in l. inv l.
              exfalso.
              eapply Mem.perm_free_2 in FREE'; eauto.
              eapply Mem.free_unchanged_on with
                (P:= not_init_args (size_arguments sg) (rs RSP)) in FREE' as UNC1.
              2: {intros. intros. intro. apply H14. rewrite <- H1. constructor. eauto. }
              eapply Mem.free_unchanged_on with (P:= not_init_args (size_arguments sg) (rs RSP)) in H3 as UNC2.
              2: {intros. intros. intro. apply H14. rewrite <- H1. constructor. eauto. }
              eapply Mem.valid_block_free_2 in H10; eauto.
              inv UNC2. rewrite <- unchanged_on_perm in H12; eauto.
              inv UNC1. rewrite <- unchanged_on_perm0 in H11; eauto.
              exploit H27; eauto. intros [A B].
              rewrite <- unchanged_on_perm; eauto.
              rewrite unchanged_on_contents; eauto.
              rewrite unchanged_on_contents0; eauto.
              inversion H31. apply unchanged_on_support1; eauto.
           ++ red. intros. red in H29.
              exploit Mem.perm_free_3; eauto. intro PERMtm'.
              exploit H29; eauto. unfold Mem.valid_block.
              erewrite <- Mem.support_free; eauto.
              intro PERMtm.
              eapply Mem.perm_free_1; eauto.
              eapply Mem.perm_free_4; eauto.
           ++ exploit Mem.free_mapped_unchanged_on; eauto.
              intros. eapply INIT_OUT; eauto. rewrite <- H1. constructor; eauto.
              intros [tm''0 [FREE'' UNC]].
              rewrite FREE' in FREE''. inv FREE''. eauto.
          ++ red. intros. exploit H33; eauto. intros [A B].
             split; eauto with mem.
        -- constructor; cbn; eauto.
      * constructor; eauto.
        -- eapply Mem.free_unchanged_on'; eauto.
           intros. intro. red in H11. apply H11.
           rewrite <- H1. constructor; eauto.
        -- eapply Mem.unchanged_on_implies; eauto.
        -- erewrite Mem.support_free. reflexivity. eauto.
        -- intros. rewrite <- H1 in H10. inv H10.
           eapply Mem.perm_free_2; eauto.
Qed.

Lemma not_init_args_dec:
  forall sz sp b ofs,
    {not_init_args sz sp b ofs} + {~not_init_args sz sp b ofs}.
Proof.
  intros. destruct (loc_init_args_dec sz sp b ofs).
  right. red. auto. left. auto.
Qed.

Lemma not_init_args_expand:
  forall sz b ofs sb sofs,
    not_init_args sz (Vptr sb sofs) b ofs ->
    b <> sb \/ ofs < offset_sarg sofs 0
    \/ offset_sarg sofs sz <= ofs.
Proof.
  intros.
  red in H.
  destruct (eq_block b sb); destruct (zlt ofs (offset_sarg sofs 0));
    destruct (zle (offset_sarg sofs sz ) ofs ); intuition eauto.
  exfalso. eapply H. subst. constructor; eauto. lia.
Qed.

Lemma no_perm_out_of_reach:
  forall j m1 m2 b ofs,
    Mem.inject j m1 m2 ->
    (forall k p, ~ Mem.perm m2 b ofs k p) ->
    loc_out_of_reach j m1 b ofs.
Proof.
  intros. red. intros.
  intro. eapply Mem.perm_inject in H2; eauto.
  replace (ofs - delta + delta) with ofs in H2 by lia.
  eapply H0; eauto.
Qed.

Lemma inject_unchanged_on_inject:
  forall j m1 m2 m3 P,
    Mem.inject j m1 m2 ->
    Mem.unchanged_on P m2 m3 ->
    (forall b ofs, {P b ofs} + {~ P b ofs}) ->
    (forall b ofs, ~ P b ofs -> loc_out_of_reach j m1 b ofs) ->
    Mem.inject j m1 m3.
Proof.
  intros until P. intros INJ UNC DEC OUT. inversion INJ. inversion UNC.
  intros. constructor; eauto.
  - inversion mi_inj. constructor; eauto.
    + intros. eapply unchanged_on_perm; eauto.
      edestruct DEC; eauto. apply OUT in n. red in n. exfalso.
      eapply n; eauto. replace (ofs + delta - delta) with ofs by lia. eauto with mem.
    + intros. erewrite unchanged_on_contents; eauto.
      edestruct DEC; eauto. apply OUT in n. red in n. exfalso.
      eapply n; eauto. replace (ofs + delta - delta) with ofs by lia. eauto with mem.
  - intros. unfold Mem.valid_block in *. eauto with mem.
  - intros. destruct (Mem.perm_dec m1 b1 ofs Max Nonempty); eauto.
    left. eapply unchanged_on_perm in H0; eauto.
    exploit mi_perm_inv; eauto.
    intros [A|B]. auto. congruence.
    edestruct DEC; eauto. apply OUT in n. red in n. exfalso.
    eapply n; eauto. replace (ofs + delta - delta) with ofs by lia.
    auto.
Qed.

Lemma cc_cainjp__injp_ca :
  ccref (cc_c_asm_injp) (cc_c injp @ cc_c_asm).
Proof.
  intros [w sg rs] se1 se2 q1 q2 Hse Hq.
  destruct w as [j m tm1 Hm]. inv Hse. inv Hq.
  inv H15.
  - (* no Outgoing part*) rename tm0 into tm.
    exists (se2, (injpw j m tm Hm), caw sg rs tm). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. constructor; eauto.
    + econstructor; eauto. split.
      econstructor; eauto. constructor.
      econstructor; eauto. subst tsp0. eauto. constructor; eauto.
      subst tvf. inv H8; try congruence.
    + intros r1 r3 [r2 [Hr1 Hr2]]. destruct Hr1 as [w' [Hw Hr1]]. inv Hr1. inv Hr2.
      cbn in *. destruct w' as [j' m' tm'' Hm']. inv Hw. cbn in *.
      rename m2' into tm'0. inv H1. rename m1' into m'.
      assert (Htm': Mem.inject j' m' tm').
      {
        clear - H20 Hm11 H24.
        eapply inject_unchanged_on_inject; eauto.
        apply not_init_args_dec.
        intros. eapply no_perm_out_of_reach; eauto.
        intros. red in H. eapply H24.
        edestruct loc_init_args_dec; eauto. exfalso. eauto.
      }
      econstructor; eauto. instantiate (1:= Htm').
      * constructor; eauto.
        -- apply Mem.ro_unchanged_memval_bytes. red. intros.
           destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
           ++ inversion H21. eapply unchanged_on_perm in H3; eauto. split. eauto.
              inversion H25. symmetry. eapply unchanged_on_contents; eauto.
           ++ apply Mem.ro_unchanged_memval_bytes in H27.
              assert (PERMtm'0: Mem.perm tm'0 b ofs Cur Readable).
              { inversion H20. eapply unchanged_on_perm; eauto.
               inversion H31. apply unchanged_on_support0. eauto.
              }
              exploit H27; eauto.
              intros [PERMtm0 MVAL].
              split. eauto.
              inversion H20.
              rewrite unchanged_on_contents; eauto.
        -- red. intros. destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
           ++ (* in the Outgoing arguments region *)
             inversion H21. eapply unchanged_on_perm; eauto.
           ++ red in H27. eapply H29; eauto.
              inversion H20. eapply unchanged_on_perm; eauto.
              inversion H31. unfold Mem.valid_block in *. eauto with mem.
        -- constructor.
           ++ rewrite <- H22. inversion H31. eauto.
           ++ intros.
              destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
              ** inversion H21. eauto.
              ** etransitivity. inversion H31. eauto.
                 inversion H20. eapply unchanged_on_perm; eauto.
                 inversion H31. unfold Mem.valid_block in *. eauto with mem.
           ++ intros.
              destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
              ** inversion H21. eauto.
              ** etransitivity. inversion H20.
                 eapply unchanged_on_contents; eauto.
                 inversion H31.
                 eapply unchanged_on_perm0; eauto with mem.
                 inversion H31. eauto.
  - (* with Outgoing part *)
    assert (Htm0: Mem.inject j m tm0).
    {
      eapply Mem.free_right_inject; eauto. intros.
      red in H9. exploit H9; eauto. subst tsp0. rewrite <- H.
      econstructor; eauto.
      replace (ofs + delta - delta) with ofs by lia.
      eauto with mem.
    } 
    exists (se2, (injpw j m tm0 Htm0), caw sg rs tm1). repeat apply conj; eauto.
    + constructor; eauto. constructor; eauto. erewrite Mem.support_free; eauto.
      constructor; eauto.
    + econstructor; eauto. split.
      econstructor; eauto. constructor.
      econstructor; eauto. constructor. subst tsp0.
      rewrite <- H. econstructor; eauto. subst tvf. inv H8; try congruence.
    + intros r1 r3 [r2 [Hr1 Hr2]]. destruct Hr1 as [w' [Hw Hr1]]. inv Hr1. inv Hr2.
      destruct w' as [j' m' tm'' Hm']. inv Hw.
      rename m2' into tm'0. inv H13. rename m1' into m'. cbn in H12.
      assert (Htm': Mem.inject j' m' tm').
      {
        eapply inject_unchanged_on_inject; eauto.
        apply not_init_args_dec.
        intros. eapply no_perm_out_of_reach; eauto.
        intros. eapply H28.
        edestruct loc_init_args_dec; eauto. exfalso. eauto.
      }
      econstructor; eauto. instantiate (1:= Htm').
      * constructor; eauto.
        -- apply Mem.ro_unchanged_memval_bytes. red. intros.
           destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
           ++ inversion H25. eapply unchanged_on_perm in H15; eauto. split. eauto.
              inversion H25. symmetry. eapply unchanged_on_contents; eauto.
           ++ apply Mem.ro_unchanged_memval_bytes in H31.
              assert (PERMtm'0: Mem.perm tm'0 b ofs Cur Readable).
              { inversion H24. eapply unchanged_on_perm; eauto.
               inversion H35. apply unchanged_on_support0.
               erewrite  Mem.support_free; eauto.
              }
              eapply Mem.free_unchanged_on with (P:= not_init_args (size_arguments sg) (rs RSP))
                in H0 as UNCF.
              2: {intros. intros. intro. apply H20. unfold tsp0 in *. rewrite <- H. constructor. eauto. }
              assert (NOWRITtm0 : ~ Mem.perm tm0 b ofs Max Writable).
              intro. apply H18. eapply Mem.perm_free_3; eauto.
              exploit H31; eauto. eapply Mem.valid_block_free_1; eauto.
              intros [PERMtm0 MVAL].
              split. eapply Mem.perm_free_3; eauto.
              inversion H24.
              rewrite unchanged_on_contents; eauto.
              inversion UNCF. rewrite <- unchanged_on_contents0; eauto.
              eapply unchanged_on_perm0; eauto.
        -- red. intros. destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
           ++ (* in the Outgoing arguments region *)
             inversion H25. eapply unchanged_on_perm; eauto.
           ++ eapply Mem.perm_free_3; eauto.
              red in H31. eapply H33; eauto.
              unfold Mem.valid_block in *. erewrite Mem.support_free; eauto.
              inversion H24. eapply unchanged_on_perm; eauto.
              unfold Mem.valid_block in *. rewrite H26.
              eapply Mem.perm_valid_block; eauto.
        -- constructor.
           ++ rewrite <- H26. erewrite <- Mem.support_free. 2: eauto.
              inversion H35. eauto.
           ++ intros.
              destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
              ** inversion H25. eauto.
              ** etransitivity. instantiate (1:= Mem.perm tm0 b ofs k p).
                 split; intro. eapply Mem.perm_free_1; eauto.
                 subst sp tsp0. rewrite <- H in n.
                 eapply not_init_args_expand; eauto.
                 eapply Mem.perm_free_3; eauto.
                 etransitivity. inversion H35. eapply unchanged_on_perm; eauto.
                 unfold Mem.valid_block in *. erewrite Mem.support_free; eauto.
                 inversion H24. eapply unchanged_on_perm; eauto.
                 unfold Mem.valid_block in *. erewrite <- Mem.support_free in H15. 2: eauto.
                 inversion H35; eauto.
           ++ intros.
              destruct (loc_init_args_dec (size_arguments sg) sp b ofs).
              ** inversion H25. eauto.
              ** etransitivity. inversion H24. eapply unchanged_on_contents; eauto.
                 inversion H35. eapply unchanged_on_perm0; eauto.
                 apply Mem.perm_valid_block in H15.
                 eapply Mem.valid_block_free_1; eauto.
                 eapply Mem.perm_free_1; eauto.
                 subst sp tsp0. rewrite <- H in n.
                 eapply not_init_args_expand; eauto.
                 etransitivity. inversion H35. eapply unchanged_on_contents; eauto.
                 eapply Mem.perm_free_1; eauto.
                 subst sp tsp0. rewrite <- H in n.
                 eapply not_init_args_expand; eauto.
                 apply Mem.free_result in H0. rewrite H0. reflexivity.
        -- red. intros. exploit H37; eauto. intros [A B].
           split; eauto with mem.
Qed.


Lemma cainjp__injp_ca_equiv:
  cceqv cc_c_asm_injp (cc_c injp @ cc_c_asm).
Proof. split. apply cc_cainjp__injp_ca. apply cc_injpca_cainjp. Qed.

