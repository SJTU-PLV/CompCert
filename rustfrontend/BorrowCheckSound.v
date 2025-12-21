Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs Linking.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown MoveChecking.
Require Import MoveCheckingFootprint1.
Require Import StkBorPermission RustIRbor.
Require Import RegionLiveness BorrowCheckDomain.
Require Import BorrowCheckPolonius BorrowCheck BorrowCheckInv.
Require Import Wfsimpl.
Require Import Separation.
(* use free_list related lemmas *)
Require SimplLocalsproof.

Import ListNotations.
Local Open Scope error_monad_scope.
Local Open Scope inv_scope.
Local Open Scope sep_scope.

Section BORROW_CHECK.

Variable prog: program.
(* Variable w: rs_own_world. *)
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Let L := semantics prog se.
Let ge := globalenv se prog.

(* composite environment *)
Let ce := ge.(genv_cenv).

(* Definition mod_sg := match w with *)
(*                     | rsw sg _ _ _ => sg *)
(*                     end. *)

(* Let wt_state := wt_state prog se mod_sg. *)

(* split move_check_program_spec into the following hypotheses to simplify the proof *)
Hypothesis CONSISTENT: composite_env_consistent ce.

Hypothesis COMP_RANGE: forall id co, ce ! id = Some co -> co_sizeof co <= Ptrofs.max_unsigned.
Hypothesis COMP_LEN: forall id co, ce ! id = Some co -> list_length_z (co_members co) <= Int.max_unsigned.
Hypothesis COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)).
(* Hypothesis FUN_CHECK:  forall id fd, *)
(*     In (id, Gfun fd) prog.(prog_defs) -> *)
(*     move_check_fundef_spec ce fd. *)

(* Result of the init analysis and the result of the move checking *)

Let INIT_AN : Type := (PMap.t IM.t * PMap.t IM.t * PathsMap.t).

Let move_check_stmt (ae: INIT_AN) body cfg s ts := match_stmt get_init_info ae (move_check_stmt ce) (check_cond_expr ce) body cfg s ts.

(* Result of the loans-flow analysis and the result of the borrow
checking *)

Let LOANS_AN : Type := (PMap.t RegionSet.t * PMap.t LoansEnv.t).

Let borrow_check_stmt (ae: LOANS_AN) regs f cfg s ts := match_stmt (get_borck_result regs f cfg) ae (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg s ts.    
    

(*********** Properties for the evaluation of place and expression ****************** *)

Lemma sizeof_in_range: forall ty,
    valid_type ty = true ->
    sizeof ce ty <= Ptrofs.max_unsigned.
Proof.
  destruct ty; simpl; rewrite maxv; try lia.
  destruct i; lia.
  destruct f; lia.
  destruct Archi.ptr64; lia.
  destruct Archi.ptr64; lia.
  congruence.
  destruct (ce ! i) eqn: A; try lia. 
  generalize (COMP_RANGE i c A). rewrite maxv. auto.
  destruct (ce ! i) eqn: A; try lia. 
  generalize (COMP_RANGE i c A). rewrite maxv. auto.
Qed.

(*** Old version code  *)

(*

(* The locations evaluated by get_loc_footprint_map and eval_place are
the same. To support reference, we should provide that regions in p
are live and the invariant for the loans environment and stacked
borrow memory *)
Lemma eval_place_get_loc_footprint_map_equal: forall m le p fpm fp b1 ofs1 b2 ofs2 own stk1 stk2 af
    (GFP: get_loc_footprint_map le (path_of_place p) fpm = Some (b1, ofs1, fp))
    (WT: wt_place le ce p)
    (WFENV: wf_env fpm ce m le)
    (EVAL: eval_place ce le m stk1 p b2 ofs2 stk2 af)
    (MM: mmatch fpm ce m le own)
    (DOM: dominators_is_init own p = true),
    b1 = b2
    /\ ofs1 = Ptrofs.unsigned ofs2
    (* It is used to strengthen this lemma *)
    /\ wt_footprint ce (typeof_place p) fp
    /\ ofs1 + sizeof ce (typeof_place p) <= Ptrofs.max_unsigned.
Proof.
  induction p; intros.
  - inv EVAL. simpl in GFP. rewrite H5 in GFP.
    destruct (fpm ! i) eqn: FP; try congruence. inv GFP.
    repeat apply conj; auto.
    simpl. exploit wf_env_footprint; eauto.
    intros (fp0 & A1 & A2). rewrite FP in A1. inv A1. auto.
    simpl. inv WT. eapply sizeof_in_range. auto.
  - inv EVAL. simpl in GFP. destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv. eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    exploit IHp. 1-6: eauto. inv WT. eauto.
    intros (A1 & A2 & A3 & A4). subst.
    simpl in G2. destruct fp3; try congruence.
    destruct (find_fields i fpl) eqn: FIND; try congruence. repeat destruct p0.
    inv G2. inv A3. rewrite H3 in H0. inv H0.
    exploit find_fields_some. eauto. intros (B1 & B2). subst.
    exploit WT2. eauto.
    intros (fty & C1 & C2 & C3).
    rewrite H8 in CO. inv CO.
    rewrite H9 in C2. inv C2.
    (* some range properties *)
    rewrite H3 in *. simpl in A4. rewrite H8 in A4.
    exploit field_offset_in_max_range1. 1-5: eauto.
    intros (R1 & R2 & R3).
    (* some rewrite *)
    inv WT. rewrite H3 in WT3. inv WT3.
    rewrite H8 in WT4. inv WT4.
    rewrite C1 in WT5. inv WT5. 
    repeat apply conj; auto.
    rewrite Ptrofs.add_unsigned; auto.
    (** range proof obligation *)
    rewrite !Ptrofs.unsigned_repr; auto.
    rewrite !Ptrofs.unsigned_repr; auto.        
  - inv EVAL. inv WT. destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    (* Tbox *)
    + inv WT2. inv H2; simpl in *; try congruence. inv H.
      destruct (path_of_place p) eqn: POP. 
      exploit get_loc_footprint_map_app_inv; eauto.
      intros (b3 & ofs3 & fp3 & G1 & G2).
      unfold dominators_is_init in DOM. simpl in DOM.
      eapply andb_true_iff in DOM. destruct DOM as (D1 & D2).
      exploit IHp; eauto.
      intros (A1 & A2 & A3 & A4). subst.
      simpl in G2. destruct fp3; try congruence. inv G2.
      inv A3.
      exploit MM. erewrite POP. eauto. auto. intros (BM & FULL).
      inv BM. rewrite H0 in LOAD. inv LOAD.
      repeat apply conj; auto. lia.
    (** TODO: reference  *)
    + admit.
    (* simpl. eapply sizeof_in_range; eauto. *)
  - inv EVAL. simpl in GFP. destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    unfold dominators_is_init in *. simpl in DOM.
    eapply andb_true_iff in DOM. destruct DOM as (A & B).
      assert (DOM1: dominators_is_init own p = true).
    { destruct p; simpl in *; auto.
      eapply andb_true_iff. auto. }
    exploit IHp; eauto. inv WT. eauto.
    intros (A1 & A2 & A3 & A4). subst.
    simpl in G2. destruct fp3; try congruence. rewrite H3 in G2.
    destruct ident_eq in G2; try congruence.
    destruct List.list_eq_dec in G2; try congruence.
    destruct ident_eq in G2; try congruence. inv G2.
    rewrite H3 in A3. inv A3.
    rewrite H4 in CO. inv CO.
    rewrite H11 in FOFS. inv FOFS.
    (* some range properties *)
    rewrite H3 in *. simpl in A4. rewrite H4 in A4.
    exploit variant_field_offset_in_max_range1. 1-5: eauto.
    intros (R1 & R2 & R3).
    (* some rewrite *)
    inv WT. rewrite H3 in WT2. inv WT2.
    rewrite H4 in WT3. inv WT3.
    repeat apply conj; auto.
    rewrite Ptrofs.add_unsigned.
    (** range proof obligation *)
    rewrite !Ptrofs.unsigned_repr; auto.
    rewrite !Ptrofs.unsigned_repr; auto.
    exploit valid_owner_place_footprint. erewrite POP. eauto. eauto.
    intros (fp' & ofs' & ofs1 & G2 & VFP & OFS).
    exploit MM. eapply G2. auto.
    intros (BM' & FULL').
    assert (BM1: bmatch ce m b1 (Ptrofs.unsigned ofs) (fp_enum id orgs tag0 fid ofs0 fp)).
    { rewrite OFS. eapply valid_owner_bmatch. eauto. eauto. }
    inv BM1.
    simpl in H5. rewrite H5 in TAG0. inv TAG0.
    rewrite Int.unsigned_repr in H10. rewrite H10 in TAG. inv TAG.
    simpl. auto.
    (* tag is in range *)
    generalize (list_nth_z_range _ _ TAG).
    generalize (COMP_LEN id co H4). lia.
    rewrite FTY in WT4. inv WT4.
    auto.
Admitted.


(* This lemma is used to state that the location of a place is
unchanged if the memory location in [bs] is unchanged. [bs] is the
location of the dominator of [p]. It is used to prove the soundness of
enum assignment where we need to prove that the results of the
evaluation of p are the same *)
Lemma eval_place_footprint_unchanged: forall p m b1 b2 ofs1 ofs2 fpm own le fp,
    get_loc_footprint_map le (path_of_place p) fpm = Some (b1, ofs1, fp) ->
    eval_place ce le m p b2 ofs2 ->
    mmatch fpm ce m le own ->
    dominators_is_init own p = true ->
    list_norepet (footprint_of_env le ++ flat_fp_map fpm) ->
    (* These premises are used to reuse eval_place_get_loc_footprint_map_equal *)
    wf_env fpm ce m le ->
    wt_place le ce p ->
    exists bs,
      (* We have to consider that we cannot change the location of the
      tag field if p is an enum, very difficult. But we can just
      ignore the changing in b2 because changing the tag does not
      affect the field offset *)
      (* (forall m' b3 ofs3, Mem.unchanged_on (fun b' ofs' => In b' bs) m m' -> *)
      (*                eval_place ce le m' p b3 ofs3 -> *)
      (*                b2 = b3 /\ ofs2 = ofs3) *)
      (forall m', Mem.unchanged_on (fun b' ofs' => In b' bs \/ (b' = b2 /\ ~ ((Ptrofs.unsigned ofs2 <= ofs' < Ptrofs.unsigned ofs2 + sizeof ce (typeof_place p))))) m m' ->
             eval_place ce le m' p b2 ofs2)
      /\ list_norepet bs
      /\ incl bs (footprint_of_env le ++ flat_fp_map fpm)
      /\ list_disjoint bs (b2 :: footprint_flat fp).
      (* /\ Ptrofs.unsigned ofs + sizeof ce (typeof_place p) <= Ptrofs.max_unsigned. *)
Proof.
  induction p; intros until fp; intros GFP PADDR MM DOM NOREP WFENV WTP.
  - inv PADDR. simpl in *.
    rewrite H3 in GFP.
    destruct (fpm!i) eqn: A; try congruence.
    inv GFP.
    exists nil. repeat apply conj.
    + intros. econstructor; eauto.
    + constructor.
    + eapply incl_nil_l.
    + red. intros. inv H.
  - exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (A1 & A2 & A3 & A4). subst.
    inv PADDR. simpl in *.
    destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b1 & ofs1 & fp1 & GFP1 & GFP2). simpl in GFP2.
    destr_fp_field fp1 GFP2. inv GFP2.
    inv WTP.
    (* some rewrite *)
    rewrite H3 in WT2. inv WT2.
    rewrite H6 in WT3. inv WT3.
    exploit IHp; eauto.
    intros (bs & UNC & NOREP1 & INCL & DIS).
    (** FIXME: range proof with very bad structure *)
    exploit eval_place_get_loc_footprint_map_equal. rewrite POP.
    all: eauto.
    intros (C1 & C2 & C3 & C4). subst.
    exploit field_offset_in_range_eq; eauto.
    rewrite <- H3. eauto. intros (OFSEQ & R1 & R2).
    exists bs. repeat apply conj; eauto.
    + intros. econstructor; eauto.
      eapply UNC. eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. destruct H0; auto.
      destruct H0; subst.
      right. split; auto.
      intro. eapply H5. rewrite H1 in H0.
      (* range proof *)
      rewrite OFSEQ in *. rewrite H3. lia.
    + red. intros. eapply DIS; auto.
      inv H0. simpl. auto.
      eapply in_cons. simpl. eapply in_flat_map; eauto.
  - exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (A1 & A2 & A3 & A4). subst.
    inv PADDR. simpl in *.
    destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b1 & ofs1 & fp1 & GFP1 & GFP2). simpl in GFP2.
    destruct fp1; try congruence. inv GFP2.
    assert (DOM1: dominators_is_init own p = true).
    { unfold dominators_is_init in DOM. simpl in DOM.
      eapply andb_true_iff in DOM. destruct DOM. auto. }
    inv WTP.
    exploit IHp; eauto.
    intros (bs & UNC & NOREP1 & INCL & DIS).
    exists (l :: bs).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    rewrite POP. eauto.
    intros (D1 & D2 & D3 & D4). subst.
    repeat apply conj; eauto.
    + intros.
      exploit type_deref_some; eauto. intros PTY.
      rewrite PTY in *.
      inv H4; simpl in *; try congruence.      
      econstructor. eapply UNC.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros.
      destruct H4; auto. destruct H4; subst. auto.
      rewrite PTY in *.
      eapply deref_loc_value; eauto.
      eapply Mem.load_unchanged_on; eauto.
      simpl. intros. auto.
    + econstructor; auto.
      intro. eapply DIS; eauto. simpl. auto.
    + eapply incl_cons; auto.
      eapply get_loc_footprint_map_in_range; eauto.
    + red. intros.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3).
      inv H.
      * exploit get_loc_footprint_map_norepet; eauto.
        intros (E1 & E2). simpl in *.
        inv H0.
        -- intro. eapply E2. auto.
        -- intro. eapply E2. subst. auto.
      * intro. subst. eapply DIS; eauto.
        simpl. eauto.
  - exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (A1 & A2 & A3 & A4). subst.
    inv PADDR. simpl in *.
    destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b1 & ofs1 & fp1 & GFP1 & GFP2). simpl in GFP2.
    rewrite H3 in GFP2.
    destruct fp1; try congruence.
    destruct ident_eq; try congruence; destruct list_eq_dec; try congruence; destruct ident_eq;  try congruence; subst. inv GFP2.
    inv WTP.
    (* some rewrite *)
    rewrite H3 in WT2. inv WT2.
    rewrite H4 in WT3. inv WT3.
    assert (DOM1: dominators_is_init own p = true).
    { unfold dominators_is_init in *. simpl in DOM.
      eapply andb_true_iff in DOM. destruct DOM as (A & B).
      destruct p; simpl in *; auto.
      eapply andb_true_iff. auto. }
    exploit IHp; eauto.
    intros (bs & UNC & NOREP1 & INCL & DIS).
    exists bs. repeat apply conj; eauto.
    + intros.
      (** FIXME: range proof with very bad structure *)
      exploit eval_place_get_loc_footprint_map_equal. rewrite POP.
      all: eauto.
      intros (C1 & C2 & C3 & C4). subst.
      exploit variant_field_offset_in_range_eq; eauto.
      rewrite <- H3. eauto. intros (OFSEQ & R1 & R2 & R3).      
      econstructor; eauto.
      * eapply UNC. eapply Mem.unchanged_on_implies; eauto.
        simpl. intros.
        destruct H0; auto.
        destruct H0; subst; auto.
        right. split; auto.
        intro. eapply H7.
        rewrite OFSEQ in *. rewrite H1 in *. rewrite H3. lia.
      * eapply Mem.load_unchanged_on; eauto.
        simpl. intros. right. split; auto.
        rewrite H1. rewrite OFSEQ. lia.
Qed.

(* The footprint contained in the location of a place *)
Lemma eval_place_sound: forall e m p b ofs own fpm (* init uninit universe *)
    (EVAL: eval_place ce e m p b ofs)
    (MM: mmatch fpm ce m e own)
    (WFOWN: wf_env fpm ce m e)
    (WT: wt_place (env_to_tenv e) ce p)
    (* (SOWN: sound_own own init uninit universe) *)
    (* evaluating the address of p does not require that p is
    owned. Shallow own is used in bmatch *)
    (POWN: dominators_is_init (* init uninit universe *) own p = true),
  exists fp (* ce' *) (* phl *),
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, (Ptrofs.unsigned ofs), fp)
    /\ wt_footprint ce (typeof_place p) fp
    (* range *)
    /\ (Ptrofs.unsigned ofs) + (sizeof ce (typeof_place p)) <= Ptrofs.max_unsigned
    (* we need to consider the assignment to this place *)
    /\ Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof ce (typeof_place p)) Cur Freeable
    (* range_perm cannot guarantee that b is a valid block *)
    /\ Mem.valid_block m b
.
Proof.
  induction 1; intros.
  (* Plocal *)
  - rewrite Ptrofs.unsigned_zero.
    exploit wf_env_footprint; eauto. intros (fp & FP & WTFP).
    exists fp. repeat apply conj. simpl. rewrite H. rewrite FP. auto.
    simpl. auto.
    simpl. eapply sizeof_in_range. inv WT. auto.
    eapply wf_env_freeable; eauto.
    eapply wf_env_freeable; eauto.    
  (* Pfield *)
  - inv WT.
    (* two type facts, reduce one *)
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    exploit IHEVAL. 1-5: auto.
    intros (fp & PFP & WTFP & RAN0 & FREE). rewrite H in RAN0. simpl in RAN0.
    (** Inversion of WTFP *)
    rewrite H in WTFP. inv WTFP; simpl in *; try congruence.
    rewrite H0 in *. inv CO.
    exploit WT0; eauto. intros (ffp & fofs & INFPL & FOFS& WTFP1).
    (* construct some range hypotheses *)
    exploit field_offset_in_max_range; eauto.
    intros (R1 & R2 & R3). 
    rewrite H1 in FOFS. inv FOFS. 
    (* exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN). *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr; auto.
    exists ffp. repeat apply conj; auto.
    (* get_loc_footprint_map *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl.  rewrite INFPL. auto.
    (* permission *)
    exploit field_offset_in_range_complete; eauto.
    intros R4.
    red. intros. eapply FREE. rewrite H. simpl.
    rewrite H0. lia.
    (* valid_block *)
    eapply FREE.
  (* Pdowncast *)
  - inv WT.
    rewrite H in WT2. inv WT2. rewrite H0 in WT3. inv WT3.
    (** TODO: make it a lemma: prove p's dominators are init *)
    (** It is impossible to be proved  *)
    assert (PDOM: dominators_is_init (* init uninit universe *) own p = true).
    { unfold dominators_is_init in *. simpl in *.
      eapply andb_true_iff in POWN. destruct POWN as (A & B).
      destruct p; simpl in *; auto.
      eapply andb_true_iff. auto. }
    (** Prove that p is_init  *)
    exploit IHEVAL. 1-5: auto.
    intros (fp & PFP & WTFP & RAN0 & PERM).
    rewrite H in RAN0. simpl in RAN0. rewrite H0 in RAN0.
    (* construct some range hypotheses *)
    exploit variant_field_offset_in_max_range; eauto.
    intros (R1 & R2 & R3). 
    (* produce some range requirement *)
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr; auto.
    (** Prove that p is_init: NO!! We can only show that (valid_owner
    p) is init *)
    exploit valid_owner_place_footprint. eauto. eauto. intros (fp1 & ofs1 & fofs1 & PFP1 & VOFS1 & OFSEQ).
    unfold dominators_must_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).
    exploit MM. eauto. auto.
    (* valid owner's bmatch implies subfield bmatch *)
    intros (BM & FULL).
    assert (BM1: bmatch ce m b (Ptrofs.unsigned ofs) fp).
    { rewrite OFSEQ. eapply valid_owner_bmatch. eauto. eauto. }
    rewrite H in WTFP. (* inv BM1. *)
    (* rewrite some redundant premises *)
    simpl in H1. 
    inv WTFP; simpl in *; try congruence. inv BM1.
    inv BM1. rewrite H1 in TAG0. inv TAG0. rewrite Int.unsigned_repr in H2.
    (* do some rewrting *)
    rewrite H0 in CO. inv CO.
    rewrite H2 in TAG. inv TAG. simpl.
    rewrite H3 in FOFS. inv FOFS.
    exists fp0. repeat apply conj.
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto. simpl.
    rewrite H. repeat destruct ident_eq; simpl; try congruence.
    destruct list_eq_dec; simpl; try congruence.
    auto.
    lia.
    (* permission *)
    rewrite H in PERM. simpl in PERM. rewrite H0 in PERM.
    exploit variant_field_offset_in_range_complete; eauto.
    intros (R4 & R5). red. intros. eapply PERM. lia.
    eapply PERM.
    generalize (list_nth_z_range _ _ TAG).
    generalize (COMP_LEN id0 co CO). 
    lia.
  (* Pderef *)
  - inv WT.
    unfold dominators_must_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).    
    exploit IHEVAL; eauto.
    intros (fp & PFP & WTFP & RAN0 & PERM).
    exploit MM. eauto. auto.
    intros (BM & FULL). destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2.
    inv WTFP; inv BM; simpl in *; try congruence.
    exists fp0. repeat apply conj.    
    (* prove ofs' = 0 *)
    inv H; simpl in *; try congruence.
    simpl in *. inv H0. rewrite LOAD in H1. inv H1.
    rewrite Ptrofs.unsigned_zero.    
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl. auto.
    (* wt_footprint *)
    simpl. auto.
    (* range proof: first show that ofs' is zero *)
    inv H; simpl in *; try congruence.
    inv H0. rewrite LOAD in H1. inv H1. rewrite Ptrofs.unsigned_zero.
    lia.
    (* permission *)
    inv H; simpl in *; try congruence.
    inv H0. rewrite LOAD in H1. inv H1.
    red. intros. eapply VRES.
    generalize (size_chunk_pos Mptr).
    rewrite Ptrofs.unsigned_zero in H. lia.
    inv H; simpl in *; try congruence.
    inv H0. rewrite LOAD in H1. inv H1.
    (* valid_block *)
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies. eapply Mem.load_valid_access. eauto.
    constructor.
Qed.

(* The location of the member is sem_wt_loc. It is used in the invariant of dropstate *)
Inductive member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : member -> Prop :=
| member_footprint_struct: forall fofs fid fty
    (STRUCT: co.(co_sv) = Struct)
    (FOFS: field_offset ce fid co.(co_members) = OK fofs)
    (FTY: field_type fid co.(co_members) = OK fty)
    (WTLOC: sem_wt_loc ce m fp b (ofs + fofs))
    (WTFP: wt_footprint ce fty fp),
    member_footprint m co b ofs fp (Member_plain fid fty)
.

(* hacking: simulate the deref_loc_rec to get the path, footprint and
location of the value. fp is the start of the footprint. *)
Inductive deref_loc_rec_footprint (m: mem) (b: block) (ofs: Z) (fty: type) (fp: footprint) : list type -> block -> Z -> type -> footprint -> Prop :=
| deref_loc_rec_footprint_nil:
  deref_loc_rec_footprint m b ofs fty fp nil b ofs fty fp
| deref_loc_rec_footprint_cons: forall ty tys fp2 b1 ofs1 b2 sz
    (* simulate type_to_drop_member_state *)
    (DEREF: deref_loc_rec_footprint m b ofs fty fp tys b1 ofs1 (Tbox ty) (fp_box b2 sz fp2))
    (TYSZ: sz = sizeof ce ty)
    (* Properties of bmatch *)
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b2 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (PERM: Mem.range_perm m b2 (- size_chunk Mptr) sz Cur Freeable)
    (RANGE: 0 < sz <= Ptrofs.max_unsigned),
    deref_loc_rec_footprint m b ofs fty fp ((Tbox ty) :: tys) b2 0 ty fp2.

*)

(********* End of Old version code  *)

(** TODO  *)
Inductive drop_member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : option drop_member_state -> Prop :=.

(* This relation is used to show that rfp can be split into the same
structure of the list of place, the returned footprint is the
dereference of the first place of this list and the return path is the
dereference of the first place. *)
Inductive sound_split_fully_own_place (root_ph: path) (rfp: footprint) : list place -> footprint -> path -> Prop :=
| sound_split_nil: sound_split_fully_own_place root_ph rfp nil rfp root_ph
| sound_split_cons: forall id pj p l fp b sz
    (PHEQ: (id, pj) = (path_of_place p))
    (* The result fp_box should be the value stored in p *)
    (SOUND: sound_split_fully_own_place root_ph rfp l (fp_box b sz fp) (id, pj))
    (SHALLOW_OWN: shallow_owned fp = true),
    sound_split_fully_own_place root_ph rfp (p :: l) fp (id, pj ++ [proj_deref]).

(** TODO: where to put wt_place/path? We should provide (wt_path
root_ph) and (wt_footprint rfp) outside this definition so that we can
prove wt_path/footprint for the place in drop_place_state *)
Inductive sound_drop_place_state (root_ph: path) (rfp: footprint) : option drop_place_state -> Prop :=
| sound_dps_none: sound_drop_place_state root_ph rfp None
| sound_dps_comp: forall p l ph fp
    (SPLIT: sound_split_fully_own_place root_ph rfp l fp ph)
    (FULL_INIT: deep_init fp = true)
    (PHEQ: ph = path_of_place p),
    sound_drop_place_state root_ph rfp (Some (drop_fully_owned_comp p l))
| sound_dps_box: forall l ph fp
    (SPLIT: sound_split_fully_own_place root_ph rfp l fp ph)
    (* It implies that the value of fp can be drop *)
    (SHALLOW_INIT: shallow_init fp = true),
    sound_drop_place_state root_ph rfp (Some (drop_fully_owned_box l)).

(* soundness of continuation: the execution of current function cannot
modify the footprint maintained by the continuation *)


Inductive sound_cont : INIT_AN -> LOANS_AN -> statement -> rustcfg -> cont -> cfg_kinfo -> mem -> fp_frame -> Prop :=
| sound_Kstop: forall init_an loans_an body cfg nret m
    (RET: cfg ! nret = Some Iend),
    sound_cont init_an loans_an body cfg Kstop (mk_cfg_kinfo nret None None nret) m fpf_emp
| sound_Kseq: forall init_an loans_an body cfg s ts k pc next cont brk nret m fpf
    (MSTMT: move_check_stmt init_an body cfg s ts (mk_cfg_info pc next cont brk nret))
    (MCONT: sound_cont init_an loans_an body cfg k (mk_cfg_kinfo next cont brk nret) m fpf),
    sound_cont init_an loans_an body cfg (Kseq s k) (mk_cfg_kinfo pc cont brk nret) m fpf
| sound_Kloop: forall init_an loans_an body cfg s ts k body_start loop_jump_node exit_loop nret contn brk m fpf
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: move_check_stmt init_an body cfg s ts (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (MCONT: sound_cont init_an loans_an body cfg k (mk_cfg_kinfo exit_loop contn brk nret) m fpf),
    sound_cont init_an loans_an body cfg (Kloop s k) (mk_cfg_kinfo loop_jump_node (Some loop_jump_node) (Some exit_loop) nret) m fpf
| sound_Kcall: forall init_an loans_an body cfg k nret f e own p m fpf
    (MSTK: sound_stacks (Kcall p f e own k) m fpf)
    (RET: cfg ! nret = Some Iend),
    (* (WFOWN: wf_own_env e ce own), *)
    sound_cont init_an loans_an body cfg (Kcall p f e own k) (mk_cfg_kinfo nret None None nret) m fpf
| sound_Kdropplace: forall f st ps nret cfg pc cont brk k own1 own2 e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit live loans_env MP
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, loans_env))
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) (live, loans_env) f.(fn_body) cfg k (mk_cfg_kinfo pc cont brk nret) m fpf)
    (MCKINV: move_check_inv own2 fpm)
    (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP)
    (MPRED: m |= MP)
    (** VERY DIFFICULT: Invariant of drop_place_state *)
    (* (SDP: sound_drop_place_state e m fpm own1 rfp st) *)
    (MOVESPLIT: move_split_places own1 ps = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst ps))
    (* all places in drops are wt_place *)
    (* (WTPS: Forall (fun p => wt_place e ge p) (map fst ps)) *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (* (WFOWN: wf_own_env e ce own1) *)
    (FULL: (forall p full, In (p, full) ps -> is_full (own_universe own1) p = full))
    (* (WTRFP: wt_footprint ce rfpty rfp) *),
    sound_cont (maybeInit, maybeUninit, universe) (live, loans_env) f.(fn_body) cfg (Kdropplace f st ps e own1 k) (mk_cfg_kinfo pc cont brk nret) m (fpf_func fpm fpf)
| sound_Kdropcall: forall init_an loans_an body cfg k pc cont brk nret fpf st co fp ofs b membs fpl id m
    (CO: ce ! id = Some co)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (* (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs) *)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned)
    (** Do we need some separation properties? *)
    (SOUND: sound_cont init_an loans_an body cfg k (mk_cfg_kinfo pc cont brk nret) m fpf),
    (* (INFRM: In b (flat_fp_frame fpf)) *)
    (* (CONTDIS: ~ In b (footprint_flat fp ++ flat_map footprint_flat fpl)), *)
    sound_cont init_an loans_an body cfg (Kdropcall id (Vptr b ofs) st membs k) (mk_cfg_kinfo pc cont brk nret) m (fpf_drop b (Ptrofs.unsigned ofs) fpl fpf)

with sound_stacks : cont -> mem -> fp_frame -> Prop :=
| sound_stacks_stop: forall m,
    sound_stacks Kstop m fpf_emp
| sound_stacks_call: forall f nret cfg pc contn brk k own1 own2 p e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit live loans_env MP
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, loans_env))
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) (live, loans_env) f.(fn_body) cfg k (mk_cfg_kinfo pc contn brk nret) m fpf)
    (MCKINV: move_check_inv own2 fpm)
    (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP)
    (MPRED: m |= MP)
    (* (WFENV: wf_env fpm ce m e) *)
    (* we need to maintain this invariant for p's evaluation when
    function return *)
    (DOM: dominators_is_init own1 p = true)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe),
    (* (WFOWN: wf_own_env e ce own1), *)
    sound_stacks (Kcall p f e own1 k) m (fpf_func fpm fpf).
    

(** TODO: invariant for the borrow checking  *)
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s ts pc next cont brk nret k e own m fpm fpf mayinit mayuninit live LoansEnv loans_env bor_stk MP
    (* The init and loans-flow analysis results *)
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The result of move checking and borrow checking *)
    (MCK_STMT: move_check_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s ts (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt (live, LoansEnv) (regset_fun f) f cfg s ts (mk_cfg_info pc next cont brk nret))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f.(fn_body) cfg k (mk_cfg_kinfo next cont brk nret) m fpf)
    (* Init-analysis overapproximates the ownership environment *)
    (OWN: sound_own own mayinit mayuninit universe)
    (* Invariant of the move checking *)
    (MCKINV: move_check_inv own fpm)
    (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP)
    (MPRED: m |= MP)            (** Coherent relation between fpm and memory *)
    (* Invariant of the borrow checking *)
    (BORCK_INV: borrow_check_inv ce (live!!pc) loans_env fpm bor_stk),
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    (* we need to maintain the well-formed invariant of own_env *)
    (* (WFENV: wf_env fpm ce m e) *)
    (* invariant of the own_env *)
    (* (WFOWN: wf_own_env e ce own), *)
    sound_state (State f s k e own bor_stk m)
| sound_dropplace: forall f cfg entry maybeInit maybeUninit universe next cont brk nret st drops k e own1 own2 m fpm fpf mayinit mayuninit live LoansEnv loans_env bor_stk MP ROOTMP root_ph rb rofs emp_rfp rfp root_ty
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f.(fn_body) cfg k (mk_cfg_kinfo next cont brk nret) m fpf)
    (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (* This relation indicates that we should move out root_ph's
    footprint from fpm because root_ph has been moved out from own1 *)
    (MCKINV: move_check_inv own1 fpm)
    (* Invariant of the borrow checking *)
    (LOANS_ST: LoansEnv!!next = LoansEnv.State loans_env)
    (BORCK_INV: borrow_check_inv ce (live!!next) loans_env fpm bor_stk)
    (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP)
    (MPRED: m |= ROOTMP ** MP)
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    (* emp_rfp should not own its resource value, i.e., if it is
    fp_box b sz fp, then fp is fp_emp; more precisely, it should be
    equal to (clear_footprint_rec rfp) *)
    (ROOT_PATH: get_owner_loc_footprint_map root_ph fpm = Some (rb, rofs, emp_rfp))
    (ROOT_WTLOC: sem_wt_loc ce rfp rb rofs ROOTMP)
    (ROOT_TY: wt_path ce fpm root_ph = OK root_ty)
    (ROOT_WTFP: wt_footprint ce root_ty rfp)
    (* all the paths of the place in st can be found in rfp and the found
    footprint is shallow/deep_init *)
    (SDP: sound_drop_place_state root_ph rfp st)
    (* big step update of the own_env *)
    (MOVESPLIT: move_split_places own1 drops = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst drops))
    (* fullspec is used to maintain the invariant between is_full and the full flags *)
    (FULLSPEC: forall p full, In (p, full) drops -> is_full (own_universe own1) p = full)
    (* all places in drops are wt_place *)
    (WTPS: Forall (fun p => wt_place fpm ge p) (map fst drops)),
    (* (WF: wf_env fpm ce m e) *)
    (* we just want to make rfp well structured (e.g., field names are
    norepet and the size of blocks are in range) *)
    (* (WTRFP: wt_footprint ce rfpty rfp)  *)
    (* (WFOWN: wf_own_env e ce own1), *)
    (* no need to maintain borrow check domain in dropplace? But how
    to record the pc and next statement? *)
    sound_state (Dropplace f st drops k e own1 bor_stk m)
| sound_dropstate: forall init_an loans_an body cfg next cont brk nret id co fp fpl b ofs st m membs k fpf bor_stk MP
    (CO: ce ! id = Some co)
    (* The key is how to prove semantics well typed can derive the
    following two properties *)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (* all the remaining members are semantically well typed *)
    (* (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs) *)
    (CONT: sound_cont init_an loans_an body cfg k (mk_cfg_kinfo next cont brk nret) m fpf)
    (COHERENT: coherent_fpf ce (fpf_drop b (Ptrofs.unsigned ofs) fpl fpf) MP)
    (MPRED: m |= DROPMP ** MP)
    (* The location of the composite to be dropped is not in the
    current footprint ! Note that it may resides in fpf! *)
    (* (DIS: ~ In b (footprint_flat fp ++ flat_map footprint_flat fpl)) *)
    (* b is in fpf to make sure that changing the memory outside
    flat_fp does not change b *)
    (* (INFRM: In b (flat_fp_frame fpf)) *)
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned),
    sound_state (Dropstate id (Vptr b ofs) st membs k bor_stk m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k bor_stk
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL: list_forall2 (sem_wt_val ce m) fpl args)
    (* Used in assign_loc_sound in function entry proof *)
    (ANORM: val_casted_list args tyargs)
    (* (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl) *)
    (STK: sound_stacks k m fpf),
    (* also disjointness of fpl and fpf *)
    sound_state (Callstate vf args k bor_stk m)
| sound_returnstate: forall sg fpf flat_fp m k retty rfp v Hm bor_stk
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = retty)
    (WTVAL: sem_wt_val ce m rfp v)
    (CAST: val_casted v retty)
    (* (WTFP: wt_footprint ce retty rfp) *)
    (STK: sound_stacks k m fpf)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm)),
    sound_state (Returnstate v k bor_stk m)
.



End BORROW_CHECK.


(** TODO: the interface for the borrow checking *)
Definition rs_bor : invariant li_rs_bor := inv_bot.

Definition own2bor (I: invariant li_rs) : invariant li_rs_bor :=
  {| inv_world := inv_world I;
    symtbl_inv := symtbl_inv I;
    query_inv w (q: query li_rs_bor) := (query_inv I w q);
    reply_inv w (r: reply li_rs_bor) := (reply_inv I w r); |}.

(* Given a module [M], if it passes the borrow checking and it does
not contain errors except for memory errors at its source semantics,
then its stacked borrow semantics (which is defined by adding stacked
borrow rules to the original RustIR semanitcs) has no undefined
behavior. As our semantics are open, we should specify the
rely-guarantee conditions at the module boundaries to restrict the
interference with the unknown environment. We use the interface
[rs_bor] to represent this condition. *)
Lemma borrow_check_soundness_stacked_borrow (P Q: invariant li_rs) (M M': RustIR.program) :
  module_type_safe P Q (RustIRown.semantics M) (RustIRown.mem_error M) ->  
  borrow_check_program M = OK M' ->
  module_type_safe ((own2bor P) @@ rs_bor) ((own2bor Q) @@ rs_bor) (RustIRbor.semantics M) SIF.
Proof.
Admitted.


Definition rs_bor1 : invariant li_rs :=
  {| inv_world := inv_world rs_bor;
    symtbl_inv := symtbl_inv rs_bor;
    query_inv w (q: query li_rs) := exists stk, query_inv rs_bor w (rsbor_q q stk);
    reply_inv w (r: reply li_rs) := exists stk, reply_inv rs_bor w (rsbor_r r stk) |}.

(* When module [M] has no UB in the stacked borrow semantics, it also
has no UB in the orignal semantics, under the interface [rs_bor1 q :=
exists stk, rs_bor (q, stk)]. *)
Theorem borrow_check_safe (P Q: invariant li_rs) (M M': RustIR.program) :
  module_type_safe P Q (RustIRown.semantics M) (RustIRown.mem_error M) ->  
  borrow_check_program M = OK M' ->
  module_type_safe (P @@ rs_bor1) (Q @@ rs_bor1) (RustIRown.semantics M) SIF.
Proof.
Admitted.
