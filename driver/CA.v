Require Import Coqlib Errors.
Require Import AST Linking Smallstep Invariant CallconvAlgebra.
Require Import Values Memory.
Require Import Conventions Mach Asm.
Require Import CKLR.
Require Import Locations CallConv.
Require Import Inject InjectFootprint.
Require Import MemFootprint.

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

(** Experiment code for flatening CAinjp into a safety interface *)

Record inv_asm_cc_injp_world :=
  inv_asmcc_w {
      inv_asmcc_fp: mem_valid_world;
      inv_asmcc_sg: signature;
      inv_asmcc_rs : regset;
    }.

Local Open Scope mfp_scope.

(* Safety interface for asm query that contains the asm-level calling
convention and the memory protection *)
Inductive inv_asm_cc_injp_q (P: invariant li_c) : inv_world P -> inv_asm_cc_injp_world -> query li_asm -> Prop :=
  inv_asm_cc_injp_q_intro tm mfp (rs: regset) m0 sg wP
    (Hm: memory_valid mfp tm):
    let tsp := rs#SP in let tra := rs#RA in let tvf := rs#PC in
    let targs := (map (fun p => Locmap.getpair p (make_locset_rs rs tm tsp))
                    (loc_arguments sg)) in
    valid_val_list mfp targs ->
    valid_val mfp tvf ->
    (forall b ofs, loc_init_args (size_arguments sg) tsp b ofs ->
              mfp ! b ## ofs = false) ->
    Val.has_type tsp Tptr ->
    Val.has_type tra Tptr ->
    valid_blockv (Mem.support tm) tsp ->
    args_removed sg tsp tm m0 -> (* The Outgoing arguments are readable and freeable in tm *)
    (* Do we actually need these? *)
    tra <> Vundef ->
    tvf <> Vundef ->
    (* safety assertions for the C query *)
    query_inv P wP (cq tvf sg targs tm) ->
    inv_asm_cc_injp_q P
      wP
      (inv_asmcc_w (mvw mfp tm Hm) sg rs)
      (rs,tm).

(* Convention of allocating registers for the C arguments *)
Inductive cc_c_asm_args_q: signature -> query li_c -> query li_asm -> Prop :=
  cc_c_asm_args_q_intro sg m (rs: regset) :
    let tsp := rs#SP in let vf := rs#PC in
    let args := (map (fun p => Locmap.getpair p (make_locset_rs rs m tsp))
                      (loc_arguments sg)) in
    vf <> Vundef -> 
    cc_c_asm_args_q
      sg
      (cq vf sg args m)
      (rs, m).


(* Safety interface for asm reply that contains the asm-level calling
convention and the memory protection *)
Inductive inv_asm_cc_injp_r (P: invariant li_c) : inv_world P -> inv_asm_cc_injp_world -> reply li_asm -> Prop :=
  inv_asm_cc_injp_r_intro sg mfp tm Hm mfp' tm' Hm' (rs rs' :regset) wP:
     let tsp := rs#SP in
     let tres := rs_getpair (map_rpair preg_of (loc_result sg)) rs' in
     valid_val mfp' tres ->
     mvw_acc (mvw mfp tm Hm) (mvw mfp' tm' Hm') ->
     (forall r, is_callee_save r = true -> rs' (preg_of r) = rs (preg_of r)) ->
     rs'#SP = rs#SP -> rs'#PC = rs#RA ->
     (* safety assertions for the C reply *)
     reply_inv P wP (cr tres tm') ->
     inv_asm_cc_injp_r P
       wP
       (inv_asmcc_w (mvw mfp tm Hm) sg rs)
       (rs', tm').

(* Convention of allocating registers for the C return value *)
Inductive cc_c_asm_res_r: signature -> reply li_c -> reply li_asm -> Prop :=
  cc_c_asm_res_r_intro sg m (rs: regset):
    let res := rs_getpair (map_rpair preg_of (loc_result sg)) rs in
    cc_c_asm_res_r
      sg
      (cr res m)
      (rs, m).

(* It parametrizes over an safety interface *)
Definition inv_asm_cc_injp (P: invariant li_c) : invariant li_asm :=
  {| inv_world := (inv_world P * inv_asm_cc_injp_world);
    symtbl_inv '(wP, w) se := symtbl_inv P wP se /\ mem_valid_stbl (inv_asmcc_fp w) se;
    query_inv '(wP, w) q := inv_asm_cc_injp_q P wP w q;
    reply_inv '(wP, w) r := inv_asm_cc_injp_r P wP w r; |}.

Program Definition cc_c_asm_args_res : callconv li_c li_asm :=
  {|
    match_senv _ := eq;
    match_query := cc_c_asm_args_q;
    match_reply := cc_c_asm_res_r;
  |}.
Next Obligation.
  split; intros; auto.
Defined.

Require Import InvariantAlgebra.

Local Open Scope inv_scope.

(** TODO: construct target footprint from the injection *)
Definition tm_fp (j: meminj_inv) : memfp := 
  NMap.map _ _ (fun zm => Maps.ZMap.map (fun elt => match elt with | Some _ => true | None => false end) zm) j.

Lemma inject_implies_valid_memory: forall m tm j,
    Mem.inject j m tm ->
    memory_valid (tm_fp (inv_inj j m)) tm.
Admitted.

Lemma inject_implies_valid_val: forall v1 v2 j m,
    Val.inject j v1 v2 ->
    valid_val (tm_fp (inv_inj j m)) v2.
Admitted.

Lemma inject_implies_valid_val_list: forall vl1 vl2 j m,
    Val.inject_list j vl1 vl2 ->
    valid_val_list (tm_fp (inv_inj j m)) vl2.
Admitted.

Lemma tm_fp_out_of_reach: forall j m b ofs,
    loc_out_of_reach j m b ofs ->
    (tm_fp (inv_inj j m)) ! b ## ofs = false.
Admitted.


(** Construct the inverse injection *)

(* TODO: one problem is how to find the largest consecutive memory
regions for building a source block *)
Definition tm_inv_inj' (invj: meminj_inv) (tm tm': mem) (mfp': memfp) : meminj_inv :=
  invj.

Definition m_inv_inj (invj: meminj_inv) (tm: mem) (mfp: memfp) : meminj_inv :=
  invj.


(** Construct the outgoing source memory with the new inverse injection *)

(* TODO: Iterate the tm' and construct memory values to update m *)
Definition m'_from_invj' (invj': meminj_inv) (m tm': mem) : mem := m.

(* TODO: construct incoming source memory. We should only construct
blocks for the largest consecutive footprint in the target memory *)
Definition m_from_mfp (mfp: memfp) (tm: mem) : meminj * mem := 
  (Mem.flat_inj (Mem.support tm), tm).

(* top level theorem of the injp construction for outgoing reply *)
Lemma mfp_outgoing_constr: forall j m tm (INJ: Mem.inject j m tm) Hm mfp' tm' Hm',
    let invj := inv_inj j m in
    let mfp := tm_fp invj in
    mvw_acc (mvw mfp tm Hm) (mvw mfp' tm' Hm') ->
    exists j' m' INJ',
      injp_acc (injpw j m tm INJ) (injpw j' m' tm' INJ')
      (* move this property to other places *)
      /\ (forall v', valid_val mfp' v' -> 
              exists v, Val.inject j' v v').
Admitted.

Lemma incoming_constr_inject: forall mfp tm (Hm: memory_valid mfp tm),
    exists j m, Mem.inject j m tm
           (* move this property to other places *)
           /\ (forall tv, valid_val mfp tv -> 
                    (* v <> Vundef is necessary for vf <> Vundef *)
                     exists v, Val.inject j v tv /\ v <> Vundef)
           /\ (forall tvl, valid_val_list mfp tvl -> 
                    exists vl, Val.inject_list j vl tvl).
Proof.
  intros.
  (* use m_from_mfp to construct j and m *)
Admitted.

(* This property classifies those safety interfaces that are preserved
up to the memory injeciton. It says that the safety interface is
irrelavent to the injection (i.e., the name of the memory block) *)
Record c_interface_up_to_inj (P: invariant li_c) : Prop :=
  { c_interface_up_to_inj_incoming:
    forall w1 args1 args2 vf1 vf2 m1 m2 sg j,
      query_inv P w1 (cq vf1 sg args1 m1) ->
      Mem.inject j m1 m2 ->
      Val.inject j vf1 vf2 ->
      Val.inject_list j args1 args2 ->
      exists w2, query_inv P w2 (cq vf2 sg args2 m2)
            /\ (forall vres1 vres2 m1' m2' j',
                  reply_inv P w2 (cr vres2 m2') ->
                  Mem.inject j' m1' m2' ->
                  Val.inject j' vres1 vres2 ->
                  reply_inv P w1 (cr vres1 m1'));
    
    c_interface_up_to_inj_outgoing:
    forall w2 args1 args2 vf1 vf2 m1 m2 sg j,
      query_inv P w2 (cq vf2 sg args2 m2) ->
      Mem.inject j m1 m2 ->
      Val.inject j vf1 vf2 ->
      Val.inject_list j args1 args2 ->
      exists w1, query_inv P w1 (cq vf1 sg args1 m1)
            /\ (forall vres1 vres2 m1' m2' j',
                  reply_inv P w1 (cr vres1 m1') ->
                  Mem.inject j' m1' m2' ->
                  Val.inject j' vres1 vres2 ->
                  reply_inv P w2 (cr vres2 m2'));
  }.
    

Lemma c_asm_inv_cainjp: forall P (UINJ: c_interface_up_to_inj P),
    invref 
      (P @! cc_c_asm_injp)
      (inv_asm_cc_injp P).
Proof.
  intros. red.
  intros (wP1 & wca) se2 q2 (se1 & SYM1 & MSENV) (q1 & QINV1 & MQ).
  (** TODO: iterate over the ~loc_out_of_reach to construct mfp *)
  destruct wca as [[j m tm Hm] sg rs]. 
  (* construct wP2 *)
  inv MQ.
  exploit (c_interface_up_to_inj_incoming _ UINJ); eauto. intros (wP2 & QINV2 & RINV2). 
  set (invj := inv_inj j m).
  exists (wP2, inv_asmcc_w (mvw (tm_fp invj) tm (inject_implies_valid_memory m tm j Hm1)) sg rs). 
  split. 2: split.
  (* symbol table: it needs to add requirements for symbol tables in UINJ *)
  - admit.
  (* query *)
  - simpl. econstructor.  4-10: eauto.
      * eapply inject_implies_valid_val_list; eauto.
      * eapply inject_implies_valid_val; eauto.
      * intros. eapply tm_fp_out_of_reach; eauto.
      * fold tvf. inv H5; auto; try congruence.
  - intros r2 RINV'. inv RINV'.
    (** TODO: construct a source memory m' such that (m, tm) ~->_injp (m', tm') *)
    exploit mfp_outgoing_constr; eauto. 
    instantiate (1 := Hm1). intros (j' & m' & INJ' & INJP & VP).
    (* construct source return value *)
    exploit VP; eauto. intros (res1 & VINJ_RES).
    exists (cr res1 m'). 
    split.
    + eapply RINV2; eauto. 
    + inv INJP. econstructor; eauto.
      econstructor; eauto.
Admitted.

Lemma cainjp_c_asm_inv: forall P (UINJ: c_interface_up_to_inj P),
    invref       
      (inv_asm_cc_injp P)
      (P @! cc_c_asm_injp).
Proof.
  intros. red.
  intros (wP & [mfp sg rs]) se2 q2 (SYM1 & SYM2) QINV. inv QINV.
  (* construct a source memory and an injection *)
  edestruct incoming_constr_inject as (j & m & INJ & VINJ & VLINJ); eauto. 
  (* P preserves up to the injection *)
  exploit VLINJ; eauto. intros (args & VLINJ1).
  exploit VINJ; eauto. intros (vf & VINJ1 & NUN).
  exploit (c_interface_up_to_inj_outgoing P UINJ); eauto.
  intros (wP2 & (RI1 & RI2)).
  exists (wP2, cajw (injpw j m tm INJ) sg rs).
  split. 2: split.
  (* symbol table *)
  - admit.
  - exists (cq vf sg args m). split.
    + auto.
    + econstructor; eauto.
      (* loc_out_of_reach *)
      * admit.
  - intros tr (r & RINV1 & RINV2). inv RINV2.
    exploit RI2; eauto. intros RINV1'.
    simpl. 
    exploit inject_implies_valid_memory. eapply Hm'. intros MVAL'.
    eapply inv_asm_cc_injp_r_intro with (mfp' := tm_fp (inv_inj j' m')) (Hm' := MVAL'); eauto.
    eapply inject_implies_valid_val; eauto.
    (* mvw_acc *)
    inv H17.
    econstructor; eauto.
    (* unchanged_on: specified to the construction of mfp' *)
    admit. admit. admit.
Admitted.

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


(* CAinjp is equivalent to CL @ cc_stacking injp @ MA where we do not
use LM *)
Lemma cc_cainjp_expand:
  ccref cc_c_asm_injp (cc_c_locset @ cc_stacking injp @ cc_mach_asm).
Proof.
  red. intros [[f m1 m4 Hm] sg rs4] se1 se2 q1 q2 Hse Hq.
  inv Hse. clear Hm1 Hm2 Hm3. inv Hq.
  (* Compute ccworld (cc_c_locset @ cc_stacking_injp @ cc_mach_asm). *)
  set (mrs3 mr := rs4 (preg_of mr)). rename tsp0 into sp4.
  set (ls2i := Locmap.init Vundef).
  set (ls3 := make_locset mrs3 m4 sp4).
  generalize (loc_arguments_always_one sg). intro Hone.
  generalize (loc_arguments_norepet sg). intro Hnorepet.
  assert (exists ls2, (fun p : rpair loc => Locmap.getpair p ls2) ## (loc_arguments sg) = args /\
                   forall l : loc,  loc_external sg l  -> Val.inject f (ls2 l) (ls3 l)).
  { generalize dependent args.
    induction loc_arguments; cbn; intros.
    - inv H7. exists ls2i. split. auto. intros. constructor.
    - inv H7. exploit IHl; eauto. intros.
      exploit Hone. right. eauto. auto.
      inv Hnorepet. auto.
      exploit Hone. left. reflexivity. intros [la Hla].
      intros [rs1 [A B]].
      exists (setpairloc a v rs1). split.
      + simpl. f_equal.  rewrite Hla.
        erewrite setpairloc_gsspair; eauto.
        rewrite <- A.
        apply map_ext_in. intros. exploit Hone; eauto.
        right. eauto. intros [la0 Hla0]. rewrite Hla0.
        erewrite setpairloc_gso1; eauto. rewrite Hla. reflexivity.
        inv Hnorepet. congruence.
      + intros. rewrite Hla.
        destruct (Loc.eq la l0).
        * subst. erewrite setpairloc_gss; eauto. 
        * erewrite setpairloc_gso. 2: eauto. eauto. auto.
  }
  destruct H as [ls2 [Hargs Hargsinj]].
  exists (se1, sg, (se2, stkw injp (injpw f m1 m4 Hm) sg ls2 mrs3 sp4 m4 ,(rs4, Mem.support m4))).
  repeat apply conj; eauto.
  + econstructor; eauto. constructor. split. econstructor; eauto. constructor.
  + exists (lq vf sg ls2 m1). split. econstructor; eauto.
    exists (mq tvf sp4 tra mrs3 m4). split. econstructor; eauto.
    intros. specialize (Hargsinj (R r)). exploit Hargsinj. constructor. eauto.
    split. eauto with mem. split. intros.
    {
      intros. inv H15. rewrite H0 in H. extlia.
      do 2 eexists. split.  reflexivity. 
      split; eauto.
      eapply Mem.free_range_perm; eauto.
    }
    {
      intros. inv H15. apply tailcall_possible_reg in H. inv H. eauto.
      exploit H12; eauto. intros [v4 Hl]. exists v4. split. eauto.
      specialize (Hargsinj (S Outgoing ofs ty)). exploit Hargsinj; eauto. constructor. eauto.
      unfold ls3. simpl. rewrite <- H0. setoid_rewrite Hl. eauto.
    }
    simpl. auto.
    econstructor; eauto. subst tvf. inv H8; try congruence.
  + intros r1 r2. rename r2 into r4. intros (r2 & Hr1 & r3 & Hr2 & Hr3). 
    inv Hr1. inv Hr2. simpl in Hr3. inv Hr3. rename m' into m1''.
    rename m2' into m4''.
    inv H23.
    eapply cc_c_asm_injp_mr_intro with (j' := f0) (Hm' := Hm0); eauto.
    destruct (loc_result_always_one sg) as [r Hr]. rewrite Hr. simpl. rewrite <- H13. eapply H21.
    rewrite Hr. constructor. reflexivity. 
    intros. rewrite <- H13. rewrite <- H22; eauto.
Qed.



Lemma inject_list_in {A: Type}:
  forall (l : list A)
    (map1 map2: A -> val) j, (forall a, In a l -> Val.inject j (map1 a) (map2 a)) ->
                                    Val.inject_list j map1##l  map2##l.
Proof.
  induction l; intros.
  - constructor.
  - simpl. constructor. eapply H. left. auto.
    eapply IHl. intros. apply H. right. auto.
Qed.

Lemma cc_cainjp_collapse:
  ccref (cc_c_locset @ cc_stacking injp @ cc_mach_asm) cc_c_asm_injp.
Proof.
  red. intros ((xse & sg) & ((xse2 & [[j' m1' m4' Hm'] xsg ls2 mrs3 sp4 xm4]) & [rs4 xsup])).
  intros se1 se4 q1 q4 [Hse1 [Hse2 Hse3]] [q2 [Hq1 [q3 [Hq2 Hq3]]]]. 
  inv Hse1. inv Hse2. inv Hse3. inv Hq1. inv Hq2. inv Hq3.
  inv H17.
  rename xm4 into m4'. rename m into m1'.
  exists (cajw (injpw j' m1' m4' Hm') sg rs4).
  repeat apply conj; eauto.
  + simpl. constructor; eauto.
  + assert (exists m4'_, args_removed sg (rs4 RSP) m4' m4'_).
    {
      destruct H16 as [A [B C]].
      destruct (Z_gt_dec (size_arguments sg) 0).
      + exploit B; eauto. intros (sb & sofs & Hsp4 & Hrangep & Hofs).
        apply Mem.range_perm_free in Hrangep. destruct Hrangep as [m4_ Hfree].
        exists m4_. rewrite Hsp4.
        eapply args_removed_free; eauto.
        intros. exploit C; eauto. intros [v [D E]].
        exists v. rewrite <- Hsp4. auto.
      + exists m4'. constructor. red. 
        generalize (size_arguments_above sg). intro. lia.
    } destruct H as [m4'_ REMOVE].
    simpl. econstructor; eauto.
    { eapply inject_list_in.
      intros. apply loc_arguments_always_one in H as Ho. destruct Ho as [l0 Ho]. subst a.
      simpl.
      apply loc_arguments_external in H. inv H.
      simpl. rewrite <- H12. eauto.
      simpl. destruct H16 as [A [B C]]. exploit C; eauto. intros [v [Hl Hinj]].
      setoid_rewrite Hl. eauto.
    }
  + intros r1 r2 Hr. simpl in Hr. inv Hr.
    assert (ACC: injp_acc (injpw j' m1' m4' Hm') (injpw j'0 m' tm' Hm'0)).
    { inv H21. econstructor; eauto. }    
    rename m' into m1''. rename tm' into m4''.
    set (ls2' := Locmap.setpair (loc_result sg) res (Locmap.init Vundef)).
    destruct (loc_result_always_one sg) as [r Hr]. subst tres. rewrite Hr in *. simpl in H7.
    econstructor. instantiate (1 := (lr ls2' m1'')). split. econstructor; eauto.
    unfold ls2'. simpl. rewrite Hr.
    cbn. rewrite Locmap.gss. reflexivity.
    set (mrs3' := fun mr => (rs' (preg_of mr))).
    exists (mr mrs3' m4''). split. econstructor; eauto.
    rewrite Hr. simpl. intros. inv H. unfold ls2'. rewrite Hr. simpl. rewrite Locmap.gss.
    simpl. unfold mrs3'. eauto. inv H0.
    intros. unfold mrs3'. eauto. rewrite H12. rewrite <- H22; eauto.
    simpl. auto.
    inv ACC.  eapply Mem.unchanged_on_implies; eauto.
    intros.
    {
      inv ACC.
      red. intros. specialize (H18 _ _ H). red in H18. intro Hpm1''.
      inv H.
      destruct (subinj_dec j' j'0 _ _ _ H31 H0).
      eapply H18; eauto. eapply H27; eauto. eapply Mem.valid_block_inject_1; eauto.
      exploit H32; eauto. rewrite <- H1 in H10. simpl in H10.
      inv H10.
      intros [A B]. apply B. eauto.
    }
    econstructor; eauto. inv ACC. destruct H29. auto.
Qed.
