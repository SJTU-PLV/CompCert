Require Import Coqlib Coqlib Maps.
Require Import AST Integers Floats Values Memory Events Globalenvs Smallstep.
Require Import Asm Asmgen Asmgenproof0.
Require Import AsmRegs.
Require Import Errors.

(** instructions which have no relationship with stack *)
Definition stk_unrelated_instr (i: instruction) :=
  match i with
    Pallocframe _ _ _
  | Pfreeframe _ _ _
  | Pcall_s _ _
  | Pcall_r _ _
  | Pret => false
  | _ => true
  end.

(** modify RSP register *)
(* Useful Lemmas *)
Lemma nextinstr_rsp:
  forall sz rs, nextinstr sz rs RSP = rs RSP.
Proof.
  unfold nextinstr.
  intros; rewrite Pregmap.gso; congruence.
Qed.

Lemma nextinstr_nf_rsp:
  forall sz rs, nextinstr_nf sz rs RSP = rs RSP.
Proof.
  unfold nextinstr_nf.
  intros. rewrite nextinstr_rsp.
  rewrite undef_regs_other; auto.
  simpl; intuition subst; congruence.
Qed.

Section INSTRSIZE.
Variable instr_size : instruction -> Z.
Variable init_sup: sup.
Hypothesis instr_size_bound : forall i, 0 < instr_size i <= Ptrofs.max_unsigned.

Definition asm_instr_unchange_rsp (i : instruction) : Prop :=
  forall ge f rs m rs' m' live,
    stk_unrelated_instr i = true ->
    Asm.exec_instr instr_size init_sup ge f i rs m = Next' rs' m' live ->
    rs # RSP = rs' # RSP.

 Lemma find_instr_eq:
  forall code ofs i,
     find_instr instr_size ofs code = Some i -> In i code.
 Proof.
   intro code. induction code.
   - intros. inv H.
   - intros. simpl in H.
     destruct (zeq ofs 0) eqn:EQ.
     + inv H. simpl. auto.
     + apply IHcode in H.
       simpl. right. auto.
 Qed.

 Lemma in_find_instr:
   forall code i,
     In i code -> exists ofs, find_instr instr_size ofs code = Some i.
  Proof.
    induction code; intros.
    - inv H.
    - destruct H. exists 0. simpl. congruence.
      apply IHcode in H. destruct H. exists (x+instr_size a).
      simpl. destr.
      apply find_instr_ofs_pos in H; eauto.
      generalize (instr_size_bound a). extlia.
      replace (x + instr_size a - instr_size a) with x by lia. auto.
Qed.

Definition asm_internal_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ofs f i,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr instr_size ofs (fn_code f) = Some i ->
    asm_instr_unchange_rsp i.

(* Builtin Step *)
Definition asm_builtin_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ofs f ef args res (rs: regset) m vargs t vres rs' m',
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    find_instr instr_size ofs f.(fn_code) = Some (Pbuiltin ef args res) ->
    eval_builtin_args ge rs (rs RSP) m args vargs ->
    external_call ef ge vargs m t vres m' ->
    ~ in_builtin_res res RSP ->
    rs' = nextinstr_nf (Ptrofs.repr (instr_size (Pbuiltin ef args res)))
              (set_res res vres
                       (undef_regs (map preg_of (Machregs.destroyed_by_builtin ef)) rs)) ->
    rs # RSP = rs' # RSP.

(* Extenal Step *)
Definition asm_external_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  forall b ef args res rs m t rs' m',
    Genv.find_funct_ptr ge b = Some (External ef) ->
    extcall_arguments rs m (ef_sig ef) args ->
    external_call ef ge args m t res m' ->
    rs' = ((set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) #PC <- (rs RA)) #RA <- Vundef ->
    rs # RSP = rs' # RSP.


Definition asm_prog_unchange_rsp (ge: Genv.t Asm.fundef unit) : Prop :=
  asm_internal_unchange_rsp ge /\
  asm_builtin_unchange_rsp ge /\
  asm_external_unchange_rsp ge.

(** Proof *)

Lemma set_pair_no_rsp:
  forall p res rs,
    no_rsp_pair p ->
    set_pair p res rs RSP = rs RSP.
Proof.
  destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition.
Qed.

Lemma asm_external_unchange_rsp1 (ge: Genv.t Asm.fundef unit) :
  asm_external_unchange_rsp ge.
Proof.
  red. intros.
  subst.
  assert (NORSPPAIR: no_rsp_pair (loc_external_result (ef_sig ef))).
  {
    red. unfold loc_external_result.
    remember (Conventions1.loc_result (ef_sig ef)) as Mpair.
    destruct Mpair; simpl.
    - destruct r; try (simpl; congruence).
    - split. destruct rhi; try (simpl; congruence).
      destruct rlo; try (simpl; congruence).
  }
  repeat rewrite Pregmap.gso by (congruence).
  rewrite set_pair_no_rsp; eauto.
Qed.



Definition written_regs i : list preg :=
    match i with
    (** Moves *)
    | Pmov_rr rd _
    | Pmovl_ri rd _
    | Pmovq_ri rd _
    | Pmov_rs rd _
    | Pmovl_rm rd _
    | Pmovq_rm rd _ => IR rd :: nil
    | Pmovl_mr a rs
    | Pmovq_mr a rs => nil
    | Pmovsd_ff rd _ 
    | Pmovsd_fi rd _ 
    | Pmovsd_fm rd _ => FR rd :: nil
    | Pmovsd_mf a r1 => nil
    | Pmovss_fi rd _ 
    | Pmovss_fm rd _ => FR rd :: nil
    | Pmovss_mf a r1 => nil
    | Pfldl_m a  => ST0 :: nil
    | Pfstpl_m a => ST0 :: nil
    | Pflds_m a => ST0 :: nil
    | Pfstps_m a => ST0 :: nil
    (** Moves with conversion *)
    | Pmovb_mr a rs 
    | Pmovw_mr a rs => nil
    | Pmovzb_rr rd _ 
    | Pmovzb_rm rd _  
    | Pmovsb_rr rd _ 
    | Pmovsb_rm rd _  
    | Pmovzw_rr rd _ 
    | Pmovzw_rm rd _  
    | Pmovsw_rr rd _ 
    | Pmovsw_rm rd _  
    | Pmovzl_rr rd _ 
    | Pmovsl_rr rd _ 
    | Pmovls_rr rd => IR rd :: nil
    | Pcvtsd2ss_ff rd _ => FR rd :: nil
    | Pcvtss2sd_ff rd _ => FR rd :: nil
    | Pcvttsd2si_rf rd _=> IR rd :: nil
    | Pcvtsi2sd_fr rd _ => FR rd :: nil
    | Pcvttss2si_rf rd _=> IR rd :: nil
    | Pcvtsi2ss_fr rd _ => FR rd :: nil
    | Pcvttsd2sl_rf rd _=> IR rd :: nil
    | Pcvtsl2sd_fr rd _ => FR rd :: nil
    | Pcvttss2sl_rf rd _ => IR rd :: nil
    | Pcvtsl2ss_fr rd _  => FR rd :: nil
    (* (** Integer arithmetic *) *)
    | Pleal rd _ 
    | Pleaq rd _
    | Pnegl rd
    | Pnegq rd
    | Paddl_ri rd _ 
    | Paddq_ri rd _
    | Psubl_ri rd _ 
    | Psubq_ri rd _ 
    | Psubl_rr rd _
    | Psubq_rr rd _
    | Pimull_rr rd _
    | Pimulq_rr rd _
    | Pimull_ri rd _ 
    | Pimulq_ri rd _ => IR rd :: nil
    | Pimull_r r1 
    | Pimulq_r r1 
    | Pmull_r r1  
    | Pmulq_r r1  => IR RAX :: IR RDX :: nil
    | Pcltd 
    | Pcqto => IR RDX :: nil
    | Pdivl r1  
    | Pdivq r1  
    | Pidivl r1 
    | Pidivq r1 => IR RAX :: IR RDX :: nil
    | Pandl_rr rd _ 
    | Pandq_rr rd _ 
    | Pandl_ri rd _ 
    | Pandq_ri rd _ 
    | Porl_rr rd _ 
    | Porq_rr rd _ 
    | Porl_ri rd _  
    | Porq_ri rd _  
    | Pxorl_r rd
    | Pxorq_r rd
    | Pxorl_rr rd _ 
    | Pxorq_rr rd _ 
    | Pxorl_ri rd _  
    | Pxorq_ri rd _  
    | Pnotl rd 
    | Pnotq rd 
    | Psall_rcl rd
    | Psalq_rcl rd
    | Psall_ri  rd _     
    | Psalq_ri  rd _     
    | Pshrl_rcl rd
    | Pshrq_rcl rd
    | Pshrl_ri  rd _     
    | Pshrq_ri  rd _     
    | Psarl_rcl rd
    | Psarq_rcl rd
    | Psarl_ri  rd _     
    | Psarq_ri  rd _     
    | Pshld_ri  rd _ _
    | Prorl_ri  rd _     
    | Prorq_ri  rd _     => IR rd :: nil
    | Pcmpl_rr  _ _    
    | Pcmpq_rr  _ _    
    | Pcmpl_ri  _ _    
    | Pcmpq_ri  _ _    
    | Ptestl_rr _ _    
    | Ptestq_rr _ _    
    | Ptestl_ri _ _    
    | Ptestq_ri _ _    => nil
    | Pcmov     c rd _  
    | Psetcc    c rd    => IR rd :: nil
    (* (** Floating-point arithmetic *) *)
    | Paddd_ff   rd _  
    | Psubd_ff   rd _  
    | Pmuld_ff   rd _  
    | Pdivd_ff   rd _  
    | Pnegd rd 
    | Pabsd rd => FR rd :: nil
    | Pcomisd_ff r1 r2  => nil
    | Pxorpd_f   rd           (**r [xor] with self = set to zero *)
    | Padds_ff   rd _  
    | Psubs_ff   rd _  
    | Pmuls_ff   rd _  
    | Pdivs_ff   rd _
    | Pmaxsd rd _
    | Pminsd rd _
    | Pnegs rd          
    | Pabss rd          => FR rd :: nil
    | Pcomiss_ff r1 r2  => nil
    | Pxorps_f   rd     => FR rd :: nil
    (* (** Branches and calls *) *)
    | Pjmp_l _
    | Pjcc _ _
    | Pjcc2 _ _ _ => nil
    | Pjmptbl r tbl => IR RAX :: IR RDX :: nil

    | Pret => nil
    (* (** Saving and restoring registers *) *)
    | Pmov_mr_a _ _   
    | Pmovsd_mf_a _ _ => nil
    | Pmov_rm_a rd _   => IR rd :: nil
    | Pmovsd_fm_a rd _ => FR rd :: nil

    (* (** Pseudo-instructions *) *)
    | Plabel l => nil
    | Pallocframe _ _ _ => IR RAX :: IR RSP :: nil
    | Pfreeframe sz ofs_ra  ofs_link  => IR RSP :: nil

    | Pbuiltin ef args res => nil
    | _ => nil
    end.

  Ltac simpl_not_in NIN :=
    let H1 := fresh in
    let H2 := fresh in
    first [ apply Decidable.not_or in NIN; destruct NIN as [H1 H2]; simpl_not_in H2
          | idtac ].

  Lemma exec_load_rsp:
    forall(ge: genv) sz K m1 am rs1 f0 rs2 m2 live,
      exec_load ge sz K m1 am rs1 f0 = Next' rs2 m2 live ->
      forall r,
        ~ In  r (PC :: RA :: CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: f0 :: nil) ->
      rs2 r = rs1 r.
  Proof.
    intros ge' sz K m1 am rs1 f0 rs2 m2 live LOAD.
    unfold exec_load in LOAD. destr_in LOAD. inv LOAD.
    simpl.
    unfold nextinstr_nf.
    intros.
    simpl_not_in H.
    simpl. simpl_regs. auto.
  Qed.

  Lemma exec_store_rsp:
    forall  (ge:genv) sz K m1 am rs1 f0 rs2 m2 (l: list preg) live,
      exec_store ge sz K m1 am rs1 f0 l = Next' rs2 m2 live ->
      forall r,
        ~ In  r (PC :: RA :: CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: l) ->
      rs2 r = rs1 r.
  Proof.
    intros ge' sz K m1 am rs1 f0 rs2 m2 l live STORE.
    unfold exec_store in STORE. repeat destr_in STORE.
    simpl.
    unfold nextinstr_nf.
    intros.
    simpl_not_in H.
    simpl. simpl_regs.
    rewrite Asmgenproof0.undef_regs_other. auto. intros; intro; subst. congruence.
  Qed.
  
  Lemma exec_instr_only_written_regs:
    forall (ge: Genv.t Asm.fundef unit) rs1 m1 rs2 m2 f i r live,
      Asm.exec_instr instr_size init_sup ge f i rs1 m1 = Next' rs2 m2 live ->
      ~ In  r (PC :: RA :: CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: written_regs i) ->
      rs2 # r = rs1 # r.
  Proof.
    intros ge rs1 m1 rs2 m2 f i r live EI NIN.
    simpl in NIN.
    simpl_not_in NIN. rename H7 into NIN.
    destruct i; simpl in *; repeat destr_in EI;
      unfold nextinstr_nf, compare_ints, compare_longs, compare_floats, compare_floats32, Op.maxf, Op.minf; simpl; simpl_not_in NIN;
        simpl_regs; eauto;
          match goal with
            H: exec_load _ _ _ _ _ _ _  = _ |- _ =>
            eapply exec_load_rsp; simpl; eauto; intuition
          | H: exec_store _ _ _ _ _ _ _ _  = _ |- _ =>
            try now (eapply exec_store_rsp; simpl; eauto; simpl; intuition)
          | _ => idtac
          end.
    repeat destr; simpl_regs; auto.
    repeat destr; simpl_regs; auto.
    Ltac solvegl H := unfold goto_label in H; repeat destr_in H; simpl_regs; auto.
    solvegl H7.
    solvegl H7.
    solvegl H7.
    solvegl H7.
  Qed.

  Definition check_asm_instr_no_rsp i :=
    negb (in_dec preg_eq RSP (written_regs i)).

  Definition check_asm_code_no_rsp c : bool :=
    forallb (fun i => negb (stk_unrelated_instr i) || check_asm_instr_no_rsp i) c.

  Lemma check_asm_instr_no_rsp_correct i:
    check_asm_instr_no_rsp i = true ->
    asm_instr_unchange_rsp i.
  Proof.
    red; intros. symmetry.
    eapply exec_instr_only_written_regs. eauto.
    simpl. intro A. decompose [or] A; try congruence.
    unfold check_asm_instr_no_rsp in H. unfold proj_sumbool in H. destr_in H. simpl in H. congruence.
  Qed.

  Definition asm_code_no_rsp (c : Asm.code) : Prop :=
    forall i,
      In i c ->
      asm_instr_unchange_rsp i.

  Lemma check_asm_code_no_rsp_correct c:
    check_asm_code_no_rsp c = true ->
    asm_code_no_rsp c.
  Proof.
    red; intros.
    unfold check_asm_code_no_rsp in H. rewrite forallb_forall in H.
    eapply H in H0. destruct (stk_unrelated_instr i) eqn:STK. simpl in H0. eapply check_asm_instr_no_rsp_correct; eauto.
    red; congruence.
  Qed.

  Lemma preg_of_not_rsp:
    forall m x,
      preg_of m = x ->
      x <> RSP.
  Proof.
    unfold preg_of. intros; subst.
    destruct m; congruence.
  Qed.

  Lemma ireg_of_not_rsp:
    forall m x,
      Asmgen.ireg_of m = Errors.OK x ->
      IR x <> RSP.
  Proof.
    unfold Asmgen.ireg_of.
    intros m x A.
    destr_in A. inv A.
    eapply preg_of_not_rsp in Heqp.
    intro; subst. congruence.
  Qed.

  Lemma freg_of_not_rsp:
    forall m x,
      Asmgen.freg_of m = Errors.OK x ->
      FR x <> RSP.
  Proof.
    unfold Asmgen.freg_of.
    intros m x A. destr_in A. 
  Qed.


  Ltac solve_rs:=
    match goal with
    | |- not (@eq preg _ (IR RSP)) => solve [ eapply preg_of_not_rsp; eauto
                                     | eapply ireg_of_not_rsp; eauto
                                     | eapply freg_of_not_rsp; eauto
                                     | congruence ]
    | |- _ => idtac
    end.


  Lemma loadind_no_rsp:
    forall ir o t m ti i
      (IN : In i ti)
      (TI : loadind ir o t m nil = OK ti),
      ~ In (IR RSP) (written_regs i).
  Proof.
    unfold loadind. intros. destruct t;destruct m;destruct Archi.ptr64;try congruence;
    simpl in TI;try monadInv TI;try destruct IN;try simpl in H;try congruence;
    subst;simpl;intro EQ;repeat destr_in EQ;try congruence.
  Qed.

  Lemma storeind_no_rsp:
    forall ir o t m ti i
      (IN : In i ti)
      (TI : storeind m ir o t nil = OK ti),
      ~ In (IR RSP) (written_regs i).
  Proof.
    unfold storeind. intros. destruct t;destruct m;destruct Archi.ptr64;try congruence;
    simpl in TI;try monadInv TI;try destruct IN;try simpl in H;try congruence;
    subst;simpl;intro EQ;repeat destr_in EQ;try congruence.
Qed.

  Ltac solve_in_regs :=
    repeat match goal with
           | H: mk_mov _ _ _ = _ |- _ => unfold mk_mov in H; repeat destr_in H
           | H: OK _ = OK _ |- _ => inv H
           | H: mk_intconv _ _ _ _ = _ |- _ => unfold mk_intconv in H
           | H: bind _ _ = _ |- _ => monadInv H
           | IN: In _ (_ :: _) |- _ => destruct IN as [IN | IN]; inv IN; simpl in *
           | IN: In _ (_ ++ _) |- _ => rewrite in_app in IN; destruct IN as [IN|IN]
           | OR: _ \/ _ |- _ => destruct OR as [OR|OR]; inv OR; simpl
           | |- ~ (_ \/ _) => apply Classical_Prop.and_not_or
           | |- ~ _ /\ ~ _ => split; auto
           | H: False |- _ => destruct H
           | H: In _ nil |- _ => destruct H
           | IN: In _ _ |- _ => repeat destr_in IN; simpl in *
           | _ => simpl in *; solve_rs; auto
           end.

  Lemma transl_cond_no_rsp:
    forall cond l c c' i
      (INV: stk_unrelated_instr i = true)
      (TC : transl_cond cond l c = OK c')
      (IN: In i c'),
      ~ In (IR RSP) (written_regs i) \/ In i c.
  Proof.
    intros.
    destruct cond; simpl in TC; repeat destr_in TC; simpl;
      unfold mk_setcc, mk_setcc_base in *; simpl in *;
        solve_in_regs; simpl; auto.
    unfold floatcomp; destr; solve_in_regs.
    unfold floatcomp; destr; solve_in_regs.
    unfold floatcomp32; destr; solve_in_regs.
    unfold floatcomp32; destr; solve_in_regs.
  Qed.

  Lemma transl_op_no_rsp:
    forall op l r c' i
      (INV: stk_unrelated_instr i = true)
      (TC : transl_op op l r nil = OK c')
      (IN: In i c'),
      ~ In (IR RSP) (written_regs i).
  Proof.
    intros.
    destruct op; simpl in TC; repeat destr_in TC; simpl;solve_in_regs.
    
    destruct (Archi.ptr64 || low_ireg x);monadInv  EQ2;
    destruct r;unfold ireg_of in EQ1; simpl in EQ1; monadInv  EQ1;
      destr_in IN;simpl;solve_in_regs.

    destruct (Archi.ptr64 || low_ireg x);monadInv  EQ2;
    destruct r;unfold ireg_of in EQ1; simpl in EQ1; monadInv  EQ1;
    destr_in IN;simpl;solve_in_regs.

    eapply transl_cond_no_rsp in EQ0; eauto.
    destruct EQ0; auto.
    unfold mk_setcc, mk_setcc_base in *; simpl in *.
    solve_in_regs; solve_rs.

    unfold transl_sel in EQ2.
    (* destruct r;unfold ireg_of in EQ; simpl in EQ; monadInv  EQ. *)
    destruct ireg_eq;subst;monadInv EQ2;try destr_in IN;simpl;solve_in_regs.
    eapply transl_cond_no_rsp in EQ3; eauto.
    destruct EQ3; auto.
    unfold mk_sel in *; simpl in *.
    destruct testcond_for_condition;monadInv  EQ0;
    destr_in H;
    solve_in_regs; solve_rs.
                                
Qed.

  (* should put this section in Asmgen.v *)
Section AsmgenFacts.

  
Lemma mk_setcc_app:
  forall cond x c,
    mk_setcc cond x c = mk_setcc cond x nil ++ c.
Proof.
  unfold mk_setcc, mk_setcc_base.
  intros. repeat destr.
Qed.

Lemma transl_cond_app:
  forall a b cond lr tc,
    transl_cond cond lr (a ++ b) = OK tc ->
    exists tc', transl_cond cond lr a = OK tc' /\ tc = tc' ++ b.
Proof.
  intros a b cond lr tc TC.
  unfold transl_cond in *.
  repeat destr_in TC; monadInv H0; rewrite EQ, ? EQ1; simpl; eauto.
Qed.
  
Lemma transl_op_eq:
  forall op lr r c tc,
    transl_op op lr r c = OK tc ->
    exists ti,
      transl_op op lr r nil = OK ti /\ tc = ti ++ c.
Proof.
  intros op lr r c tc TO.
  destruct op; simpl in *; repeat destr_in TO; eauto; try (monadInv H0; rewrite EQ; simpl; now eauto).
  - unfold mk_mov in *. repeat destr_in H0; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl.
    unfold mk_intconv in *. repeat destr_in EQ2; eauto.
  - unfold mk_shrximm.  eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - unfold mk_shrxlimm. destr. eauto. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. repeat destr; eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ, EQ1. simpl. eauto.
  - monadInv H0. rewrite EQ.
    rewrite mk_setcc_app in EQ0.
    edestruct transl_cond_app as (tc' & TC & APP); eauto.
  - monadInv H0. rewrite EQ. unfold transl_sel in *.
    destruct ireg_eq eqn:EQI.
    cbn [bind]. rewrite EQ1. cbn [bind].
    rewrite EQI. simpl. monadInv  EQ2. eauto.
    cbn [bind]. rewrite EQ1. cbn [bind].
    rewrite EQI. monadInv EQ2.
    destruct testcond_for_condition.
    simpl in *. monadInv EQ0. eapply transl_cond_app.
    simpl. auto.

    simpl in *. monadInv  EQ0.
    simpl in *. monadInv  EQ0. eapply transl_cond_app.
     simpl. auto.    
Qed.


Lemma transl_load_eq:
  forall m a l m0 c tc
    (TI : transl_load m a l m0 c = OK tc),
  exists ti, transl_load m a l m0 nil = OK ti /\ tc = ti ++ c.
Proof.
  intros.
  unfold transl_load. monadInv TI. destruct m;monadInv EQ0;rewrite EQ;
  cbn [bind]; rewrite EQ1;cbn [bind];eauto.
 
Qed.

Lemma mk_storebyte_eq:
  forall x x0 c tc
    (EQ1 : mk_storebyte x x0 c = OK tc),
  exists ti, mk_storebyte x x0 nil = OK ti /\ tc = ti ++ c.
Proof.
  unfold mk_storebyte.
  intros. repeat (destr; eauto); inv EQ1; eauto.
Qed.


Lemma transl_store_eq:
  forall m a l m0 c tc
    (TI : transl_store m a l m0 c = OK tc),
  exists ti, transl_store m a l m0 nil = OK ti /\ tc = ti ++ c.
Proof.
  intros.
  unfold transl_store. monadInv TI. rewrite EQ; simpl.
  repeat destr_in EQ0; monadInv H0; rewrite EQ0; simpl; eauto using mk_storebyte_eq.
Qed.

Lemma mk_jcc_app:
  forall cond x c,
    mk_jcc cond x c = mk_jcc cond x nil ++ c.
Proof.
  unfold mk_jcc.
  intros. repeat destr.
Qed.
  
Lemma transl_instr_eq:
  forall f i ax c tc,
    transl_instr f i ax c = OK tc ->
    exists ti,
      transl_instr f i ax nil = OK ti /\ tc = ti ++ c.
Proof.
  intros f i ax c tc TI.
  destruct i; simpl in *.
  - unfold loadind in *.
    destruct t;destruct preg_of;try monadInv TI; repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.

  - unfold storeind in *. destruct t;destruct preg_of;try monadInv TI; repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.
  - destr.
    unfold loadind in *.
    destruct t;destruct preg_of;try monadInv TI; repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.
    destruct Archi.ptr64;monadInv  TI;repeat destr_in EQ; simpl; eauto.

    monadInv TI. unfold loadind in *.
    destruct t;destruct preg_of;try monadInv EQ;
    repeat destr_in EQ0;
    simpl; eauto;
    destruct Archi.ptr64;monadInv  EQ;repeat destr_in EQ; simpl; eauto.
   
  - edestruct transl_op_eq as (ti & TOP & EQ); eauto.
  - eauto using transl_load_eq.
  - eauto using transl_store_eq.
  - destr_in TI; monadInv TI; rewrite ? EQ; simpl; eauto.
  - destr_in TI; monadInv TI; rewrite ? EQ; simpl; eauto.
  - inv TI; eauto.
  - inv TI; eauto.
  - inv TI; eauto.
  - eapply transl_cond_app; eauto. erewrite <- mk_jcc_app. auto.
  - monadInv TI; rewrite EQ; simpl; eauto.
  - inv TI. eauto.
Qed.

End AsmgenFacts.

  Lemma transl_code_no_rsp:
    forall f c b c' i
      (INV: stk_unrelated_instr i = true)
      (TC : transl_code f c b = OK c')
      (IN: In i c'),
      ~ In (IR RSP) (written_regs i).
  Proof.

    induction c; simpl; intros; eauto. inv TC. easy.
    monadInv TC.
    edestruct transl_instr_eq as (ti & TI & EQti). eauto. subst.
    rewrite in_app in IN.
    destruct IN as [IN|IN]; eauto.
    clear EQ EQ0.
    destruct a; simpl in TI; repeat destr_in TI; eauto using loadind_no_rsp, storeind_no_rsp.
    - monadInv H0. unfold loadind in EQ0. destruct Tptr;simpl in EQ0;try monadInv EQ0.
      simpl in IN. destruct IN as [IN|IN]. inv IN. simpl. intuition congruence. eapply loadind_no_rsp; eauto.
      destruct IN as [IN|IN]. inv IN. simpl. intuition congruence. eapply loadind_no_rsp; eauto.
      destruct Archi.ptr64;monadInv EQ0.
      destruct IN as [IN|IN]. inv IN. simpl. intuition congruence. eapply loadind_no_rsp; eauto.
      destruct Archi.ptr64;monadInv EQ0.
      destruct IN as [IN|IN]. inv IN. simpl. intuition congruence. eapply loadind_no_rsp; eauto.
    - eapply transl_op_no_rsp; eauto.
    - unfold transl_load in H0. monadInv H0. destruct m; solve_in_regs;
      monadInv  EQ0.
    - unfold transl_store in H0. monadInv H0. destruct m;solve_in_regs;try monadInv EQ0.
      unfold mk_storebyte in EQ2. destruct (Archi.ptr64 || low_ireg x1).
      monadInv EQ2. destr_in IN. simpl. auto.
      simpl in H. congruence.
      destruct  (addressing_mentions x0 RAX);monadInv EQ2;destr_in IN.
      simpl;intuition congruence.
      destr_in H;simpl;try intuition congruence.
      destr_in H0;simpl;try intuition congruence.
      simpl;intuition congruence.
      destr_in H;simpl;try intuition congruence.

      unfold mk_storebyte in EQ2. destruct (Archi.ptr64 || low_ireg x1).
      monadInv EQ2. destr_in IN. simpl. auto.
      simpl in H. congruence.
      destruct  (addressing_mentions x0 RAX);monadInv EQ2;destr_in IN.
      simpl;intuition congruence.
      destr_in H;simpl;try intuition congruence.
      destr_in H0;simpl;try intuition congruence.
      simpl;intuition congruence.
      destr_in H;simpl;try intuition congruence.
      
    - solve_in_regs.
    - solve_in_regs.
    - solve_in_regs.
    - solve_in_regs.
    - solve_in_regs.
    - solve_in_regs.
    - solve_in_regs.
    - eapply transl_cond_no_rsp in H0 ; eauto. destruct H0; auto.
      unfold mk_jcc in *; simpl in *.
      solve_in_regs; solve_rs; auto.
    - solve_in_regs.
    - solve_in_regs.
  Qed.

Lemma asmgen_no_change_rsp:
    forall f tf,
      transf_function instr_size f = OK tf ->
      check_asm_code_no_rsp (fn_code tf) = true.
  Proof.
    unfold check_asm_code_no_rsp.
    intros. rewrite forallb_forall.
    unfold check_asm_instr_no_rsp.
    unfold proj_sumbool.
    intros. destruct (stk_unrelated_instr x) eqn:INV. simpl.
    destr. exfalso.
    monadInv H. repeat destr_in EQ0.
    monadInv EQ. repeat destr_in EQ1. simpl in *.
    destruct H0. subst. simpl in *. congruence.
    rewrite Asmgenproof0.transl_code'_transl_code in EQ0.
    eapply transl_code_no_rsp in EQ0; eauto. simpl. auto.
  Qed.

Lemma asm_external_unchange_rsp_valid (ge: Genv.t Asm.fundef unit) :
  asm_external_unchange_rsp ge.
Proof.
  red. intros.
  subst.
  assert (NORSPPAIR: no_rsp_pair (loc_external_result (ef_sig ef))).
  {
    red. unfold loc_external_result.
    remember (Conventions1.loc_result (ef_sig ef)) as Mpair.
    destruct Mpair; simpl.
    - destruct r; try (simpl; congruence).
    - split. destruct rhi; try (simpl; congruence).
      destruct rlo; try (simpl; congruence).
  }
  repeat rewrite Pregmap.gso by (congruence).
  rewrite set_pair_no_rsp; eauto.
Qed.

Lemma preg_notin_rsp: forall l,
    preg_notin RSP l.
Proof.
  induction l. constructor.
  simpl. destruct l.
  generalize (preg_of_not_rsp a). intro. intro. symmetry in H0. eapply H in H0. congruence.
  split.  generalize (preg_of_not_rsp a). intro. intro. symmetry in H0. eapply H in H0. congruence.
  auto.
Qed.

Lemma asm_builtin_unchange_rsp_valid (ge: Genv.t Asm.fundef unit) :
  asm_builtin_unchange_rsp ge.
Proof.
  red. intros.
  subst.
  assert (NORSPPAIR: no_rsp_pair (loc_external_result (ef_sig ef))).
  {
    red. unfold loc_external_result.
    remember (Conventions1.loc_result (ef_sig ef)) as Mpair.
    destruct Mpair; simpl.
    - destruct r; try (simpl; congruence).
    - split. destruct rhi; try (simpl; congruence).
      destruct rlo; try (simpl; congruence).
  }
  repeat rewrite Pregmap.gso by (congruence).
  rewrite nextinstr_nf_rsp.
  rewrite set_res_other; eauto.
  rewrite undef_regs_other_2. auto.
  apply preg_notin_rsp.
Qed.
(*
Lemma asm_internal_unchange_rsp_valid (ge: Genv.t Asm.fundef unit):
  asm_internal_unchange_rsp ge.
Proof.
  red. intros. apply 
*)
(** modify abstract stack *)
Definition asm_instr_unchange_sup (i : instruction) : Prop :=
  stk_unrelated_instr i = true ->
  forall ge rs m rs' m' f live,
    Asm.exec_instr instr_size init_sup ge f i rs m = Next' rs' m' live ->
    Mem.support m = Mem.support m' /\
    (forall b o k p, Mem.perm m b o k p <-> Mem.perm m' b o k p).


Lemma exec_store_support:
    forall (ge: Genv.t Asm.fundef unit) sz k m1 a rs1 rs l rs2 m2 live,
      exec_store ge sz k m2 a rs1 rs l = Next' rs2 m1 live ->
      Mem.support m2 = Mem.support m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
Proof.
    intros ge sz k m1 a rs1 rs l rs2 m2 live STORE.
    unfold exec_store in STORE; repeat destr_in STORE.
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite <- Mem.support_store. 2: eauto.
    split; auto.
    split; intros.
    eapply Mem.perm_store_1; eauto.
    eapply Mem.perm_store_2; eauto.
Qed.

Lemma exec_load_support:
    forall (ge: Genv.t Asm.fundef unit) sz k m1 a rs1 rs rs2 m2 live,
      exec_load ge sz k m2 a rs1 rs = Next' rs2 m1 live ->
      Mem.support m2 = Mem.support m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
Proof.
    intros ge sz k m1 a rs1 rs rs2 m2 live LOAD.
    unfold exec_load in LOAD; destr_in LOAD.
Qed.

Lemma goto_label_support:
  forall (ge: Genv.t Asm.fundef unit) f l m1 rs1 rs2 m2 live,
    goto_label instr_size ge f l rs1 m2 = Next' rs2 m1 live ->
    Mem.support m2 = Mem.support m1 /\
    (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
Proof.
    intros ge f l m1 rs1 rs2 m2 live GOTO.
    unfold goto_label in GOTO; repeat destr_in GOTO.
Qed.

Lemma asm_prog_unchange_sup (i : instruction) :
  asm_instr_unchange_sup i.
Proof.
  intro.
    intros ge0 rs1 m1 rs2 m2 f live EI.
      destruct i; simpl in H; try discriminate;
        unfold exec_instr in EI; simpl in EI; repeat destr_in EI;
          first [ split;[reflexivity|tauto]
                | now (eapply exec_load_support; eauto)
                | now (eapply exec_store_support; eauto)
                | now ( eapply goto_label_support; eauto)
                | idtac ].
    Unshelve. all: auto. exact (Ptrofs.repr (instr_size (Pmov_mr_a a rs))).
    exact Mint32. exact PC.
Qed.

(** modify memory *)
Lemma exec_store_unchange_support:
  forall ge sz k a rs m r l rs' m' live,
    Asm.exec_store ge sz k m a rs r l = Next' rs' m' live ->
    Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  intros ge sz k a rs m r l rs' m' live STORE.
  unfold exec_store in STORE. repeat destr_in STORE.
  apply Mem.support_storev in Heqo.
  rewrite Heqo. apply Mem.sup_include_refl.
Qed.

Lemma exec_load_unchange_support:
  forall ge sz k a m rs rd rs' m' live,
    exec_load ge sz k m a rs rd = Next' rs' m' live ->
    Mem.sup_include (Mem.support m) (Mem.support m').
Proof.
  intros ge sz k a m rs rd rs' m' live LOAD.
  unfold exec_load in LOAD. destr_in LOAD.
Qed.

Definition asm_instr_unchange_support (i : instruction) : Prop :=
  forall ge rs m rs' m' f live,
    Asm.exec_instr instr_size init_sup ge f i rs m = Next' rs' m' live ->
    Mem.sup_include (Mem.support m) (Mem.support m').

Lemma asm_prog_unchange_support (i : instruction) :
  asm_instr_unchange_support i.
Proof.
  red. intros *. intros EI. unfold exec_instr in EI.
  destruct i; simpl in EI; inv EI; try (apply Mem.sup_include_refl);
      first [ now (eapply exec_load_unchange_support; eauto)
            | now (eapply exec_store_unchange_support; eauto)
            | now (repeat destr_in H0)
            | unfold goto_label in H0; repeat destr_in H0].
  + rewrite (Mem.support_store _ _ _ _ _ _ Heqo1).
    rewrite (Mem.support_store _ _ _ _ _ _ Heqo0).
    eapply Mem.sup_include_trans. 2: eapply Mem.sup_include_record_frame; eauto.
    apply Mem.sup_include_alloc in Heqp. simpl in Heqp.
    eapply Mem.sup_include_trans. eauto.
    simpl. unfold Mem.sup_push_stage.  intro. destruct b; simpl; auto.
  + unfold free' in Heqo1. destr_in Heqo1.
    erewrite <- Mem.support_free. 2:eauto.
    eapply Mem.sup_include_pop_stage; eauto.
    inv Heqo1. eapply Mem.sup_include_pop_stage; eauto.
Qed.

  Section WITH_SAEQ.

    Variable (ge tge: Genv.t Asm.fundef unit).
    Hypothesis (SADDR_EQ: forall id ofs, Genv.symbol_address ge id ofs = Genv.symbol_address tge id ofs).

(*    Lemma eval_ros_same: forall ros rs,
        eval_ros tge ros rs = eval_ros ge ros rs.
    Proof.
      unfold eval_ros. intros.
      destruct ros; auto.
    Qed.
*)
    Lemma eval_addrmode32_same: forall a rs,
        eval_addrmode32 ge a rs = eval_addrmode32 tge a rs.
    Proof.
      intros. unfold eval_addrmode32.
      destruct a. destruct base, ofs, const; auto.
      - destruct p, p0; congruence.
      - destruct p; congruence.
      - destruct p, p0; congruence.
      - destruct p; congruence.
    Qed.

    Lemma eval_addrmode64_same: forall a rs,
        eval_addrmode64 ge a rs = eval_addrmode64 tge a rs.
    Proof.
      intros. unfold eval_addrmode64.
      destruct a. destruct base, ofs, const; auto.
      - destruct p, p0; congruence.
      - destruct p; congruence.
      - destruct p, p0; congruence.
      - destruct p; congruence.
    Qed.

    Lemma eval_addrmode_same: forall a rs,
        eval_addrmode ge a rs = eval_addrmode tge a rs.
    Proof.
      intros. unfold eval_addrmode. destruct Archi.ptr64.
      - eapply eval_addrmode64_same; eauto.
      - eapply eval_addrmode32_same; eauto.
    Qed.

    End WITH_SAEQ.
End INSTRSIZE.
