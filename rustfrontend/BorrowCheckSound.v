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
Require Import MoveChecking.
Require Import MoveCheckingFootprint1.
Require Import RustIRspec RustIRsem.
Require Import RegionLiveness BorrowCheckDomain.
Require Import BorrowCheckPolonius BorrowCheck BorrowCheckInv.
Require Import Wfsimpl.
Require Import Separation Listmisc.
(* use free_list related lemmas *)
Require SimplLocalsproof.

Import ListNotations.
Local Open Scope error_monad_scope.
Local Open Scope inv_scope.
Local Open Scope sep_scope.

(* The final theorem of borrow checking depends on the instance of
opaque types *)

Section ADT_ENV.

Context {ame: adt_mem_env}.

Notation footprint := (@footprint ame).
Notation fp_map := (@fp_map ame).
Notation fp_frame := (@fp_frame ame).
Notation ae := (fun id => (ame id).(mem_pure_adt)).
Notation sval := (@sval ae).
Notation sv_map := (@sv_map ae).

Section BORROW_CHECK.

Variable prog: program.
(* Variable w: rs_own_world. *)
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Let L := semantics prog se.
Let ge := globalenv se prog.
Let tge := RustIR.globalenv se prog.
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

Let borrow_check_stmt_rel (ae: LOANS_AN) regs f cfg s ts := match_stmt (get_borck_result regs f cfg) ae (borrow_check_stmt f) borrow_check_cond_expr f.(fn_body) cfg s ts.    
    

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



(* hacking: simulate the deref_loc_rec to get the path, footprint and
location of the value. fp is the start of the footprint. *)
Inductive deref_loc_rec_footprint (fty: type) (fp: footprint) : list type -> type -> footprint -> Prop :=
| deref_loc_rec_footprint_nil:
  deref_loc_rec_footprint fty fp nil fty fp
| deref_loc_rec_footprint_cons: forall ty tys fp1 b 
    (* simulate type_to_drop_member_state *)
    (DEREF: deref_loc_rec_footprint fty fp tys (Tbox ty) (fp_box b fp1)),
    deref_loc_rec_footprint fty fp ((Tbox ty) :: tys) ty fp1.

    (* (DROPMEMB: drop_member_footprint co fpl1 fpl2 st membs) *)
    (* (* all the remaining members are well formed *) *)
    (* (WTFIELDS: Forall2 (fp_match_field ce co (wt_footprint ce)) (fpl1 ++ fpl2) (co_members co)) *)
    (* (SHALLOWINIT: forallb (fun '(_, (_, ffp)) => shallow_init ffp) fpl1 = true) *)
    (* (DEEPINIT: forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl2 = true) *)


(* co is used to state that this footprint is wt_footprint, membs are
the remaining members to be dropped so their footprint should be
deep_init. How to simplify this definition (lots of redundancy) *)
Inductive drop_member_footprint (co_id: ident) (co: composite) : footprint -> option drop_member_state -> members -> Prop :=
| drop_member_fp_none_struct: forall fpl1 fpl2 membs
    (STRUCT: co_sv co = Struct)
    (* all the members are well formed *)
    (WTFIELDS: Forall2 (fp_match_field ce co (wt_footprint ce)) (fpl1 ++ fpl2) (co_members co))
    (* The remaining members are also well formed (an alternative
    definition is make membs a suffix of (co_members co) *)
    (WTMEMBS: Forall2 (fp_match_field ce co (wt_footprint ce)) fpl2 membs)
    (* fpl1 should have enough permission *)
    (SHALLOW_OWN: forallb (fun '(_, (_, ffp)) => shallow_owned ffp) fpl1 = true)
    (DEEP_INIT: forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl2 = true),
    drop_member_footprint co_id co (fp_struct co_id (fpl1 ++ fpl2)) None membs
| drop_member_fp_none_enum: forall ffp tagz fid fofs
    (STRUCT: co_sv co = TaggedUnion)
    (SHALLOW_OWN: shallow_owned ffp = true),
    (* We have dropped this enum, so the tagz/fid/fofs are not important *)
    drop_member_footprint co_id co (fp_enum co_id tagz fid fofs ffp) None nil
| drop_member_fp_comp_struct: forall fid fofs fty tyl fp1 compty base fpl1 fpl2 ffp membs
    (STRUCT: co_sv co = Struct)
    (FOFS: field_noalign_offset ce fid co.(co_members) = OK (base, fofs))
    (* all the members are well formed *)
    (WTFIELDS: Forall2 (fp_match_field ce co (wt_footprint ce)) (fpl1 ++ (fid, ((base, fofs), ffp)):: fpl2) (co_members co))
    (* The remaining members are also well formed (an alternative
    definition is make membs a suffix of (co_members co) *)
    (WTMEMBS: Forall2 (fp_match_field ce co (wt_footprint ce)) fpl2 membs)
    (* fpl1 should have enough permission *)
    (SHALLOW_OWN: forallb (fun '(_, (_, ffp)) => shallow_owned ffp) fpl1 = true)
    (DEEP_INIT: forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl2 = true)
    (* Structure of ffp *)
    (FFP: deref_loc_rec_footprint fty ffp tyl compty fp1)
    (** fp1 deeply init or fp deeply init? *)
    (DINIT: deep_init fp1 = true),
    drop_member_footprint co_id co (fp_struct co_id (fpl1 ++ (fid, ((base, fofs), ffp)):: fpl2)) (Some (drop_member_comp fid fty compty tyl)) membs
| drop_member_fp_comp_enum: forall fid fofs fty tyl fp1 compty ffp tagz
    (STRUCT: co_sv co = TaggedUnion)
    (* Structure of ffp *)
    (FFP: deref_loc_rec_footprint fty ffp tyl compty fp1)
    (** fp1 deeply init or fp deeply init? *)
    (DINIT: deep_init fp1 = true),
    drop_member_footprint co_id co (fp_enum co_id tagz fid fofs ffp) (Some (drop_member_comp fid fty compty tyl)) nil
| drop_member_fp_box_struct: forall fid fofs fty tyl fp1 compty base fpl1 fpl2 ffp membs
    (** The only difference between this case and
    drop_member_fp_comp_struct is SHALLOW_OWN1 *)
    (STRUCT: co_sv co = Struct)
    (FOFS: field_noalign_offset ce fid co.(co_members) = OK (base, fofs))
    (* all the members are well formed *)
    (WTFIELDS: Forall2 (fp_match_field ce co (wt_footprint ce)) (fpl1 ++ (fid, ((base, fofs), ffp)):: fpl2) (co_members co))
    (* The remaining members are also well formed (an alternative
    definition is make membs a suffix of (co_members co) *)
    (WTMEMBS: Forall2 (fp_match_field ce co (wt_footprint ce)) fpl2 membs)
    (* fpl1 should have enough permission *)
    (SHALLOW_OWN: forallb (fun '(_, (_, ffp)) => shallow_owned ffp) fpl1 = true)
    (DEEP_INIT: forallb (fun '(_, (_, ffp)) => deep_init ffp) fpl2 = true)
    (* Structure of ffp *)
    (FFP: deref_loc_rec_footprint fty ffp tyl compty fp1)
    (* Because we need to free the location of fp1, it should be shalloly owned *)
    (SHALLOW_OWN1: shallow_owned fp1 = true),
    drop_member_footprint co_id co (fp_struct co_id (fpl1 ++ (fid, ((base, fofs), ffp)):: fpl2)) (Some (drop_member_box fid fty tyl)) membs
| drop_member_fp_box_enum: forall fid fofs fty tyl fp1 compty ffp tagz
    (STRUCT: co_sv co = TaggedUnion)
    (* Structure of ffp *)
    (FFP: deref_loc_rec_footprint fty ffp tyl compty fp1)
    (SHALLOW_OWN1: shallow_owned fp1 = true),
    drop_member_footprint co_id co (fp_enum co_id tagz fid fofs ffp) (Some (drop_member_box fid fty tyl)) nil.


(** The following code about Dropplace/Kdropplace invariant is not
used because we do borrow checking after drop elaboration.  *)
(* This relation is used to show that rfp can be split into the same
structure of the list of place, the returned footprint is the
dereference of the first place of this list and the return path is the
dereference of the first place. *)
(* Inductive sound_split_fully_own_place (root_ph: path) (rfp: footprint) : list place -> footprint -> path -> Prop := *)
(* | sound_split_nil: sound_split_fully_own_place root_ph rfp nil rfp root_ph *)
(* | sound_split_cons: forall id pj p l fp b sz *)
(*     (PHEQ: (id, pj) = (path_of_place p)) *)
(*     (* The result fp_box should be the value stored in p *) *)
(*     (SOUND: sound_split_fully_own_place root_ph rfp l (fp_box b sz fp) (id, pj)) *)
(*     (SHALLOW_OWN: shallow_owned fp = true), *)
(*     sound_split_fully_own_place root_ph rfp (p :: l) fp (id, pj ++ [proj_deref]). *)

(** TODO: where to put wt_place/path? We should provide (wt_path
root_ph) and (wt_footprint rfp) outside this definition so that we can
prove wt_path/footprint for the place in drop_place_state *)
(* Inductive sound_drop_place_state (root_ph: path) (rfp: footprint) : option drop_place_state -> Prop := *)
(* | sound_dps_none: sound_drop_place_state root_ph rfp None *)
(* | sound_dps_comp: forall p l ph fp *)
(*     (SPLIT: sound_split_fully_own_place root_ph rfp l fp ph) *)
(*     (FULL_INIT: deep_init fp = true) *)
(*     (PHEQ: ph = path_of_place p), *)
(*     sound_drop_place_state root_ph rfp (Some (drop_fully_owned_comp p l)) *)
(* | sound_dps_box: forall l ph fp *)
(*     (SPLIT: sound_split_fully_own_place root_ph rfp l fp ph) *)
(*     (* It implies that the value of fp can be drop *) *)
(*     (SHALLOW_INIT: shallow_init fp = true), *)
(*     sound_drop_place_state root_ph rfp (Some (drop_fully_owned_box l)). *)

(** Invariant for Dropplace/Kdropplace *)

(* | sound_dropplace: forall f cfg entry maybeInit maybeUninit universe next cont brk nret st drops k e own1 own2 m fpm fpf mayinit mayuninit live LoansEnv loans_env bor_stk MP ROOTMP root_ph rb rofs emp_rfp rfp root_ty *)
(*     (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))    *)
(*     (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv)) *)
(*     (CONT: sound_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f.(fn_body) cfg k (mk_cfg_kinfo next cont brk nret) m fpf) *)
(*     (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit))) *)
(*     (OWN: sound_own own2 mayinit mayuninit universe) *)
(*     (* This relation indicates that we should move out root_ph's *)
(*     footprint from fpm because root_ph has been moved out from own1 *) *)
(*     (MCKINV: move_check_inv own1 fpm) *)
(*     (* Invariant of the borrow checking *) *)
(*     (LOANS_ST: LoansEnv!!next = LoansEnv.State loans_env) *)
(*     (BORCK_INV: borrow_check_inv ce (live!!next) loans_env fpm bor_stk) *)
(*     (COHERENT: coherent_fpf ce (fpf_func fpm fpf) MP) *)
(*     (MPRED: m |= ROOTMP ** MP) *)
(*     (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *) *)
(*     (* emp_rfp should not own its resource value, i.e., if it is *)
(*     fp_box b sz fp, then fp is fp_emp; more precisely, it should be *)
(*     equal to (clear_footprint_rec rfp) *) *)
(*     (ROOT_PATH: get_owner_loc_footprint_map root_ph fpm = Some (rb, rofs, emp_rfp)) *)
(*     (ROOT_WTLOC: sem_wt_loc ce rfp rb rofs ROOTMP) *)
(*     (ROOT_TY: wt_path ce fpm root_ph = OK root_ty) *)
(*     (ROOT_WTFP: wt_footprint ce root_ty rfp) *)
(*     (* all the paths of the place in st can be found in rfp and the found *)
(*     footprint is shallow/deep_init *) *)
(*     (SDP: sound_drop_place_state root_ph rfp st) *)
(*     (* big step update of the own_env *) *)
(*     (MOVESPLIT: move_split_places own1 drops = own2) *)
(*     (* ordered property of the split places used to prove sound_state after the dropplace *) *)
(*     (ORDERED: move_ordered_split_places_spec own1 (map fst drops)) *)
(*     (* fullspec is used to maintain the invariant between is_full and the full flags *) *)
(*     (FULLSPEC: forall p full, In (p, full) drops -> is_full (own_universe own1) p = full) *)
(*     (* all places in drops are wt_place *) *)
(*     (WTPS: Forall (fun p => wt_place fpm ge p) (map fst drops)), *)
(*     (* (WF: wf_env fpm ce m e) *) *)
(*     (* we just want to make rfp well structured (e.g., field names are *)
(*     norepet and the size of blocks are in range) *) *)
(*     (* (WTRFP: wt_footprint ce rfpty rfp)  *) *)
(*     (* (WFOWN: wf_own_env e ce own1), *) *)
(*     (* no need to maintain borrow check domain in dropplace? But how *)
(*     to record the pc and next statement? *) *)
(*     sound_state (Dropplace f st drops k e own1 bor_stk m) *)

(************* End of Unused Dropplace/Kdropplace invariant *)


Record wf_fpm (f: function) (externs: list ident) (fpm: fp_map) : Prop :=
  { wf_fpm_local_vars: forall id ty, 
      In (id, ty) (f.(fn_params) ++ f.(fn_vars)) ->
      exists b fp, fpm ! id = Some (b, 0, None, ty, fp);

    wf_fpm_external_vars: forall id,
      In id externs ->      
      exists b ofs r ty fp, fpm ! id = Some (b, ofs, Some r, ty, fp);

    wf_fpm_disjoint_local_externs: forall id,
      In id (field_idents (f.(fn_params) ++ f.(fn_vars))) ->
      In id externs ->
      False;

 }.


(* soundness of continuation: the execution of current function cannot
modify the footprint maintained by the continuation *)

(* fp_frame is the nearest stack frame's footprint frame; We return
the memory predicate instead of defining coherent_fpf is because we do
not clear (which is just a design choice) the footprint passed via
reference to callee. *)
Inductive match_cont: INIT_AN -> LOANS_AN -> function -> rustcfg -> RustIRspec.cont -> cont -> cfg_kinfo -> fp_frame -> massert -> Prop :=
| match_Kstop: forall init_an loans_an f cfg nret
    (RET: cfg ! nret = Some Iend),
    match_cont init_an loans_an f cfg RustIRspec.Kstop Kstop (mk_cfg_kinfo nret None None nret) fpf_emp STrue
| match_Kseq: forall init_an loans_an f cfg s ts k pc next cont brk nret fpf tk MP
    (MCK_STMT: move_check_stmt init_an f.(fn_body) cfg s ts (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt_rel loans_an (regset_fun f) f cfg s ts (mk_cfg_info pc next cont brk nret))
    (MCONT: match_cont init_an loans_an f cfg k tk (mk_cfg_kinfo next cont brk nret) fpf MP),
    match_cont init_an loans_an f cfg (RustIRspec.Kseq s k) (Kseq s tk) (mk_cfg_kinfo pc cont brk nret) fpf MP
| match_Kloop: forall init_an loans_an f cfg s ts k body_start loop_jump_node exit_loop nret contn brk fpf tk MP
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MCK_STMT: move_check_stmt init_an f.(fn_body) cfg s ts (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (BORCK_STMT: borrow_check_stmt_rel loans_an (regset_fun f) f cfg s ts (mk_cfg_info body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret))
    (MCONT: match_cont init_an loans_an f cfg k tk (mk_cfg_kinfo exit_loop contn brk nret) fpf MP),
    match_cont init_an loans_an f cfg (RustIRspec.Kloop s k) (Kloop s tk) (mk_cfg_kinfo loop_jump_node (Some loop_jump_node) (Some exit_loop) nret) fpf MP
| match_Kcall: forall init_an loans_an f1 cfg k nret f2 e p fpf ns svm tk phl MP
    (MSTK: match_stacks (RustIRspec.Kcall p f2 phl ns svm k) (Kcall (Some p) f2 e tk) fpf MP)
    (RET: cfg ! nret = Some Iend),
    (* (WFOWN: wf_own_env e ce own), *)
    match_cont init_an loans_an f1 cfg (RustIRspec.Kcall p f2 phl ns svm k)  (Kcall (Some p) f2 e tk) (mk_cfg_kinfo nret None None nret) fpf MP

with match_stacks : RustIRspec.cont -> cont -> fp_frame -> massert -> Prop :=
| match_stacks_call: forall f nret cfg pc contn brk k p e stk maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit live loans_env LoansEnv mayinit0 mayuninit0 MP1 MP2 tk phl ns fpm1
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* Invariant for continuation *)
    (CONT: match_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k tk (mk_cfg_kinfo pc contn brk nret) fpf MP2)
    (* may(un)init0 are the intermediate state of this function call
    statement before initializing p *)
    (MAY_INIT: mayinit = add_place universe p mayinit0)
    (MAY_UNINIT: mayuninit = remove_place p mayuninit0)
    (* we need to maintain this invariant for p's evaluation when
    function return *)
    (DOM: dominators_must_init mayinit0 mayuninit0 universe p = true)
    (* Invariant of the move checking. *)
    (MCKINV: move_check_inv mayinit0 mayuninit0 universe fpm)
    (* Invariant of the borrow checking *)
    (BORCK_INV: borrow_check_inv ce (live!!pc) loans_env fpm stk)
    (* coherent relation is defined on the fpm whose passed reference
    footprint is cleared. *)
    (FPM: clear_fpm_passed_ref_footprint fpm (map fst phl) = OK fpm1)
    (COH: coherent_fpm ge fpm1 MP1), 
    match_stacks (RustIRspec.Kcall p f phl ns fpm k) (Kcall (Some p) f e tk) (fpf_func fpm fpf) (MP1 ** MP2).
    
(* The invariant of the continuation of dropstate is a little
different. Note that the drop operation in RustIRspec is a big step
operation. *)
Inductive match_drop_cont (f: function) : RustIRspec.cont -> cont -> fp_frame -> massert -> Prop :=
| match_drop_Kcall: forall nret cfg pc contn brk k e stk maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit live live_st loans_env LoansEnv tk MP
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* We use the liveness information before this pc instead of after this pc *)
    (LIVE_ST: RegionLiveness.transfer f cfg (regset_fun f) pc (live !! pc) = live_st)
    (* Invariant for continuation *)
    (MCONT: match_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k tk (mk_cfg_kinfo pc contn brk nret) fpf MP)
    (** Invariant of the move checking. *)
    (MCKINV: move_check_inv mayinit mayuninit universe fpm)
    (* Invariant of the borrow checking *)
    (BORCK_INV: borrow_check_inv ce live_st loans_env fpm stk),
    match_drop_cont f k (Kcall None f e tk) (fpf_func fpm fpf) MP
| match_Kdropcall: forall k fpf st co ofs b membs id ph fpm fp tk MP
    (CO: ce ! id = Some co)
    (GFP: get_owner_loc_footprint_map ph fpm = Some (b, Ptrofs.unsigned ofs, fp))
    (* drop_member_footprint says that fp matches (co, st, membs) *)
    (DROPMEMB: drop_member_footprint id co fp st membs)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned)
    (** Do we need some separation properties? *)
    (MCONT: match_drop_cont f k tk (fpf_func fpm fpf) MP),
    match_drop_cont f k (Kdropcall id (Vptr b ofs) st membs tk) (fpf_func fpm fpf) MP.

(** TODO: invariant for the borrow checking  *)
Inductive match_states: RustIRspec.state -> state -> Prop :=
| match_regular_state: forall f cfg entry maybeInit maybeUninit universe s ts pc next cont brk nret k m fpm fpf mayinit mayuninit live live_st LoansEnv loans_env loans_env1 MP ns tk FMP
    (* The init and loans-flow analysis results *)
    (INITAN: InitAnalysis.analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (LOANSAN: loans_flow_analyze ce f cfg entry = OK (live, LoansEnv))
    (* The result of move checking and borrow checking *)
    (MCK_STMT: move_check_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s ts (mk_cfg_info pc next cont brk nret))
    (BORCK_STMT: borrow_check_stmt_rel (live, LoansEnv) (regset_fun f) f cfg s ts (mk_cfg_info pc next cont brk nret))
    (* The init set and loans environment of the current pc *)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (LOANS_ST: LoansEnv!!pc = LoansEnv.State loans_env)
    (* The invariant is defined on the a variant of loans_env whose
    dead region has been removed *)
    (KILL: loans_env1 = (LOrgEnv.apply_liveness live_st loans_env))
    (* We use the liveness information before this pc instead of after this pc *)
    (LIVE_ST: RegionLiveness.transfer f cfg (regset_fun f) pc (live !! pc) = live_st)
    (* Invariant for continuation *)
    (CONT: match_cont (maybeInit, maybeUninit, universe) (live, LoansEnv) f cfg k tk (mk_cfg_kinfo next cont brk nret) fpf FMP)
    (* Invariant of the move checking *)
    (MCKINV: move_check_inv mayinit mayuninit universe fpm)
    (COHERENT: coherent_fpm ce fpm MP)
    (MPRED: m |= MP ** FMP)            (** Coherent relation between fpm and memory *)
    (* Invariant of the borrow checking *)
    (BORCK_INV: borrow_check_inv ce live_st loans_env1 fpm fpm)
    (WFENV: wf_fpm f ns fpm),
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    (* we need to maintain the well-formed invariant of own_env *)
    (* (WFENV: wf_env fpm ce m e) *)
    (* invariant of the own_env *)
    (* (WFOWN: wf_own_env e ce own), *)
    match_states (RustIRspec.State f s k ns fpm) (State f s tk fpm m)
(** TODO: since we are proving RustIR simulates RustIRspec, drop semantics in RustIRspec is a big step, so there may be no need to relate dropstate? *)
| match_dropstate: forall id co fp b ofs st m membs k fpf MP fpm (p: place) FMP tk ns f
    (CO: ce ! id = Some co)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned)
    (* The location of the dropped place *)
    (GFP: get_owner_loc_footprint_map p fpm = Some (b, Ptrofs.unsigned ofs, fp))
    (* drop_member_footprint says that fp matches (co, st, membs) *)
    (DROPMEMB: drop_member_footprint id co fp st membs)
    (MCONT: match_drop_cont f k tk (fpf_func fpm fpf) FMP)
    (* fpl1 is the locations that have been dropped *)
    (COHERENT: coherent_fpm ce fpm MP)
    (MPRED: m |= MP ** FMP),
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)) *)
    match_states (RustIRspec.State f (Sdrop p) k ns fpm) (Dropstate id (Vptr b ofs) st membs tk m)
| match_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k MP1 MP2 MP3 out_fpl out_locs tk sargs sparams fun_id
    (* TODO: show that fun_id also points to this function *)
    (FUNC: Genv.find_funct ge vf = Some fd)    
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL_LIST: sem_wt_val_list ce fpl args MP1)
    (** output memory locations are sem_wt_loc *)
    (WTLOC_LIST: sem_wt_loc_list ce out_locs out_fpl MP2)
    (* Used in assign_loc_sound in function entry proof *)
    (ANORM: val_casted_list args tyargs)
    (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl)
    (MPRED: m |= MP1 ** MP2 ** MP3)
    (STK: match_stacks k tk fpf MP3)
    (** How to produce sargs and sparams *)
    (SARGS: map fp_to_sval fpl = sargs)
    (REF_PARAMS: map fp_to_sval out_fpl = map (fun '(_, _, sv) => sv) sparams),
    (** TODO: use fpl and out_fpl to define borrow check invariant *)
    (* also disjointness of fpl and fpf *)
    match_states (RustIRspec.Callstate fun_id sargs sparams k) (Callstate vf args tk m)
| sound_returnstate: forall sg fpf m k retty rfp v MP1 MP2 MP3 out_locs out_fpl tk sparams sv
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) tk = retty)
    (WTVAL: sem_wt_val ce rfp v MP1)
    (** output memory locations are sem_wt_loc *)
    (WTLOC_LIST: sem_wt_loc_list ce out_locs out_fpl MP2)
    (CAST: val_casted v retty)
    (WTFP: wt_footprint ce retty rfp)
    (MPRED: m |= MP1 ** MP2 ** MP3)    
    (STK: match_stacks k tk fpf MP3)
    (** How to produce sargs and sparams *)
    (SRET: fp_to_sval rfp = sv)
    (REF_PARAMS: map fp_to_sval out_fpl = sparams),
    (** TODO: use fpl and out_fpl to define borrow check invariant *)
    (* (ACC: rsw_acc w (rsw sg flat_fp m Hm)), *)
    match_states (RustIRspec.Returnstate sv sparams k) (Returnstate v tk m) 
.


(** Properties of evaluating place and expressions  *)

Notation get_owner_loc_footprint_map := (@get_owner_loc_footprint_map ame).

Ltac destr_get_fpm fpm id :=
  let GFP := fresh "GFP" in
  destruct (fpm ! id) as [((((?b & ?ofs) & ?r) & ?ty) & ?fp)|] eqn: GFP;
  match goal with
  | [H : context G [fpm_to_svm fpm] |- _ ] =>
      setoid_rewrite PTree.gmap1 in H;
      rewrite GFP in H;
      simpl in H
  end.

Ltac destr_path_of_place p :=
  destruct (path_of_place p) as (?pid & ?phl) eqn: ?POP.


Ltac destr_find_field H :=
  destruct find_field as [?p|] eqn: FIND in H; try congruence.

(* Graph properties of sv_map *)

Lemma get_owner_loc_footprint_map_to_sval: forall ph fpm b ofs fp sv,
    get_owner_loc_footprint_map ph fpm = Some (b, ofs, fp) ->
    get_owner_sval_map ph fpm = OK sv ->
    fp_to_sval fp = sv.
Admitted.

Lemma get_owner_path_sv_map_inv: forall id phl (svm: sv_map) ph vs,
    get_owner_path_sv_map (id, phl) svm = OK (ph, vs) ->
    exists r ty sv, 
      svm ! id = Some (r, ty, sv)
      /\ get_owner_path svm (id, nil) phl sv nil = OK (ph, vs).
Admitted.


Ltac inv_get_owner_path_svm H :=
  let GPH := fresh "GPH" in
  eapply get_owner_path_sv_map_inv in H as GPH;
  destruct GPH as (?r & ?ty & ?sv & ?G1 & ?G2).

(* If a path can be reached via (phl1 ++ phl2) then this reachable
path can be divided into two parts: one is reached from phl1 and one
is reach from phl2 *)
Lemma get_owner_path_app_inv: forall phl1 phl2 ph1 ph3 sv1 vs1 vs3 (svm: sv_map),
    get_owner_path svm ph1 (phl1 ++ phl2) sv1 vs1 = OK (ph3, vs3) ->
    exists ph2 vs2 sv2,
      get_owner_path svm ph1 phl1 sv1 vs1 = OK (ph2, vs2) 
      /\ get_owner_sval_map ph2 svm = OK sv2 
      /\ get_owner_path svm ph2 phl2 sv2 vs2 = OK (ph3, vs3).
Admitted.

Lemma get_owner_path_for_owner: forall svm ph sv,
    get_owner_sval_map ph svm = OK sv ->
    exists vs, @get_owner_path_sv_map ae ph svm = OK (ph, vs).
Admitted.

Ltac inv_get_owner_path_app H :=
  let GPH := fresh "GPH" in
  let GPH1 := fresh "GPH1" in
  let GVAL := fresh "GVAL" in
  let GPH2 := fresh "GPH2" in
  eapply get_owner_path_app_inv in H as GPH;
  destruct GPH as (?ph & ?vs & ?sv & GPH1 & GVAL & GPH2).

Lemma get_owner_sval_map_loc : forall phl id (fpm: fp_map) sv
    (GET_PH: get_owner_sval_map (id, phl) fpm = OK sv),
    exists b ofs fp, 
      get_owner_loc_footprint_map (id, phl) fpm = Some (b, ofs, fp).
Admitted.

Lemma get_owner_path_sv_map_eval_place: forall (p: place) fpm vs ph m live MP f externs
    (COH: coherent_fpm ce fpm MP)
    (MPRED: m |= MP)
    (FPM_INV: fpm_ref_loc_inv live fpm)
    (WTP: wt_place fpm ce p)
    (WF_FPM: wf_fpm f externs fpm)
    (** TODO: show that regions in p are live *)
    (LIVE_PH: is_live_path live fpm p = true)
    (GET_PH: get_owner_path_sv_map p fpm = OK (ph, vs)),
    exists b ofs fp, 
      get_owner_loc_footprint_map ph fpm = Some (b, ofs, fp)
      /\ eval_place ce fpm m p b (Ptrofs.repr ofs).
Proof.  
  induction p; intros.
  - simpl in *. destr_get_fpm fpm i; try congruence. inv GET_PH.
    simpl. rewrite GFP. exists b, ofs, fp. split; auto.
    inv WTP.
    (** TODO: prove that i is a local variable *)
    admit.
  - simpl in GET_PH.
    destr_path_of_place p.
    inv_get_owner_path_svm GET_PH.
    inv_get_owner_path_app G2.
    inv WTP.
    simpl in LIVE_PH. rewrite POP in LIVE_PH. 
    exploit IHp. 1-6: eauto.
    simpl. rewrite G1. eauto.
    intros (b1 & ofs1 & fp1 & A1 & A2).
    (* structure of sv0: how to prove that sv0 must not be opaque object? *)
    simpl in GPH2. destruct sv0; try congruence.
    destr_find_field GPH2. inv GPH2.
    exploit get_owner_loc_footprint_map_to_sval; eauto. intros SVEQ.
    destruct fp1; simpl in SVEQ; inv SVEQ.
    (* remaining proof: get_owner_loc_footprint_map_app and getting
    the field offset *)
    admit.
    (* We need to prove that p cannot access a field of an object *)
    admit.
  (* Pdefer *)
  - simpl in GET_PH.
    destr_path_of_place p.
    inv_get_owner_path_svm GET_PH.
    inv_get_owner_path_app G2.
    inv WTP.
    simpl in LIVE_PH. rewrite POP in LIVE_PH.     
    exploit IHp; eauto.
    simpl. rewrite G1. eauto.
    intros (b1 & ofs1 & fp1 & A1 & A2).
    (* structure of sv0 *)
    simpl in GPH2. destruct sv0; try congruence. inv GPH2.
    (* sv_box *)
    + exploit get_owner_loc_footprint_map_to_sval; eauto. intros SVEQ.
      destruct fp1; simpl in SVEQ; inv SVEQ.
      destruct ph0 as (?id & ?ph).
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      inv B1.
      rewrite B2, EQV in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      exists b, 0, fp1. split.
      (** we should prove that fp1 is not emp. This properties should
      be implied by dominators_owned *)
      admit.
      econstructor; eauto. 
      (** TODO: prove by wt_footprint? *)
      assert (PTY: typeof_place p = Tbox t) by admit.
      rewrite PTY. econstructor. reflexivity.
      simpl. rewrite Ptrofs.unsigned_repr. eauto. 
      (* prove by hasvalue *)
      admit.
    (* sv_ref *)
    + exploit get_owner_loc_footprint_map_to_sval; eauto. intros SVEQ.
      destruct fp1; simpl in SVEQ; inv SVEQ.
      monadInv GPH2.
      destruct ph0 as (?id & ?ph).
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      destruct ph as (?id & ?ph).
      (* Use invariant for reference *)
      exploit (FPM_INV (pid, phl)). simpl. rewrite G1. eauto. eauto.
      (* live path *)
      eauto.
      intros (?fp & GREF & DEEP_OWN).
      exists b, ofs, fp. split; auto.
      inv B1.
      rewrite B2, EQV in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      econstructor; eauto. 
      (** TODO: prove by wt_footprint? *)
      assert (PTY: exists org, typeof_place p = Treference org mut t) by admit.
      destruct PTY as (org & PTY).
      rewrite PTY. econstructor. reflexivity.
      simpl. rewrite Ptrofs.unsigned_repr. eauto. 
      admit.
  (* Pdowncast *)
  - admit.
Admitted.

(* Properties of evaluating expression *)

Lemma eval_pexpr_match: forall (pe: pexpr) sv fpm m live MP f externs
    (COH: coherent_fpm ce fpm MP)
    (MPRED: m |= MP)
    (FPM_INV: fpm_ref_loc_inv live fpm)
    (WF_FPM: wf_fpm f externs fpm)
    (WTEXPR: wt_pexpr fpm ce pe)
    (** TODO: show that regions in p are live *)
    (EVAL: eval_pexpr fpm pe = OK sv),
    exists v fp mp,
      Rustlightown.eval_pexpr ce fpm m tge pe v
      /\ @sem_wt_val ame ce fp v mp
      /\ massert_eqv mp STrue
      /\ fp_to_sval fp = sv.
Proof.  
Admitted.

(* What is the difference between this lemma and sem_wt_loc_split? *)
Lemma deref_loc_sem_wt_val: forall fp b ofs mp ty m
    (WTLOC: sem_wt_loc ce fp b ofs mp)
    (WTFP: wt_footprint ce ty fp)
    (MPRED: m |= mp),
    exists v mp1 mp2, 
      deref_loc ty m b (Ptrofs.repr ofs) v
      /\ sem_wt_loc ce (clear_footprint_rec fp) b ofs mp1
      /\ @sem_wt_val ame ce fp v mp2
      /\ massert_eqv mp (mp1 ** mp2).
Admitted.

(* We should write a more general lemma for it? *)
Lemma clear_footprint_map_coherent: forall id phl fpm1 b ofs fp mp mp1 mp2,
    get_owner_loc_footprint_map (id, phl) fpm1 = Some (b, ofs, fp) ->
    coherent_fpm ce fpm1 mp ->
    sem_wt_fp ce fp mp1 ->
    massert_eqv mp (mp2 ** mp1) ->
    exists fpm2, clear_footprint_map (id, phl) fpm1 = Some fpm2
            /\ coherent_fpm ce fpm2 mp2.
Admitted.

Lemma eval_expr_match: forall (e: expr) sv fpm1 m live MP f externs svm2
    (COH: coherent_fpm ce fpm1 MP)
    (MPRED: m |= MP)
    (FPM_INV: fpm_ref_loc_inv live fpm1)
    (WF_FPM: wf_fpm f externs fpm1)
    (WTEXPR: wt_expr fpm1 ce e)
    (** TODO: show that regions in p are live *)
    (EVAL: eval_expr fpm1 e = OK sv)
    (MOVEP: move_place_option fpm1 (moved_place e) = OK svm2),
    exists v fp fpm2 mp1 mp2,
      Rustlightown.eval_expr ce fpm1 m tge e v
      /\ move_place_option_fpm fpm1 (moved_place e) = Some fpm2
      /\ @sem_wt_val ame ce fp v mp1
      /\ massert_eqv MP (mp1 ** mp2)
      /\ coherent_fpm ce fpm2 mp2
      /\ fpm_to_svm fpm2 = svm2
      /\ fp_to_sval fp = sv.
Proof.  
  destruct e; intros.
  (* moveplace *)
  - simpl in EVAL.
    monadInv EVAL. inv WTEXPR.
    exploit get_owner_path_for_owner; eauto. intros (vs & GPH).
    exploit get_owner_path_sv_map_eval_place. 1-5: eauto.
    (* p is live *)
    admit.
    eapply GPH.
    intros (b & ofs & fp & A1 & A2).
    destr_path_of_place p.
    exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
    intros (mp1 & mp2 & B1 & B2).
    (* exploit (@sem_wt_loc_split ame). 2: eauto. *)
    (* we need to prove that fp is not opaque object, i.e., we cannot
    move from an opaque object *)  
    (* admit. *)
    (* intros (mp3 & mp4 & S1 & S2 & S3). *)
    rewrite B2 in MPRED.
    exploit deref_loc_sem_wt_val; eauto. instantiate (1 := typeof_place p).
    admit.
    eapply MPRED.
    intros (v & mp3 & mp4 & LOAD & WTLOC1 & WTVAL & MPEQ).
    rewrite MPEQ in MPRED.
    (** TODO: sem_wt_val should imply sem_wt_fp  *)
    assert (SEMFP: sem_wt_fp ce fp mp4) by admit.
    rewrite MPEQ in B2. rewrite <- sep_assoc in B2.
    exploit clear_footprint_map_coherent. 1-2: eauto. eapply SEMFP. eapply B2.
    intros (fpm2 & CLR & COH1).
    exists v, fp, fpm2, mp4, (mp2 ** mp3).
    do 4 (try apply conj); eauto.
    + econstructor. econstructor.
      eauto. eauto.
    (** TODO: we should consider valid_owner in clear_footprint_map_coherent  *)
    + simpl. admit.
    + rewrite B2. rewrite sep_assoc, <- sep_assoc, sep_comm. reflexivity.
    + do 3 (try apply conj); eauto.
      admit. admit.
  - simpl in EVAL. monadInv EVAL.
    inv WTEXPR. inv MOVEP.
    exploit eval_pexpr_match; eauto.
    intros (v & fp & mp & EVALP & WTVAL & MPEQ& FPEQ).
    exists v, fp, fpm1, STrue, MP.
    do 4 (try apply conj); eauto.
    + econstructor. auto.
    + eapply sem_wt_val_eqv. symmetry. eauto. auto.
    + eapply massert_eqv_pure_l.
Admitted.      

(* moving from a place preserves the borrow checking invariant
under the successful checking. But what is the effect of checking
for pure expr? *)
Lemma eval_expr_preserve_borchk_inv: forall fpm1 fpm2 e live le
    (MOVE_FPM: move_place_option_fpm fpm1 (moved_place e) = Some fpm2)
    (BORCHK_INV: @borrow_check_inv ame ce live le fpm1 fpm1)
    (CHECK: check_expr le e = OK tt)
    (EVAL: eval_expr fpm1 e = OK sv),
   @borrow_check_inv ame ce live le fpm2 fpm2
    (*  *)
    /\ (typeof e) sv fpm2
.
Admitted.

Ltac simpl_getIM IM :=
  generalize IM as IM1; intros;
  inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst;
  try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *.


Lemma step_simulation: forall s1 t s2 s1',
    RustIRspec.step ge s1 t s2 ->
    match_states s1 s1' ->
    exists s2', plus RustIRsem.step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  intros s1 t s2 s1' STEP MATCH. inv STEP.
  (* Sassign *)
  - inv MATCH. inv MCK_STMT. inv BORCK_STMT.
    (* unfold move check and borrow check result. TODO: write ltac for these *)
    simpl in TR. simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    simpl in TR0. rewrite LOANS_ST in TR0. 
    unfold borrow_check_stmt, borrow_check_stmt_aux, check_assignment in TR0.
    monadInv TR0. monadInv EQ.
    rename EQ0 into BORCK_EXPR. rename EQ1 into BORCKP.
    (* end of unfold *)
    set (live_st := (RegionLiveness.transfer f cfg (regset_fun f) pc live !! pc)) in *.
    set (loans_env1 := (LOrgEnv.apply_liveness live_st loans_env)) in *.
    assert (LIVE_EQ: live_st = reg_expr_live e (reg_assign_place p (live!!pc))).
    { unfold live_st. unfold RegionLiveness.transfer. rewrite SEL.
      rewrite STMT. reflexivity. }
    (** how to show that the regions in [e] and [p] are live, so that
    we can use the borrow check invariant *)
    (* evaluate expr *)
    exploit eval_expr_match. eauto. eapply MPRED. 
    eapply BORCK_INV. all: eauto. admit.
    intros (tv & tfp & fpm2 & mp1 & mp2 & TEVAL & FPMEQ & WTVAL & MEQ1 & COH1 & A1 & A2).
    (* evaluate assignee place: before that, we need to prove moving a
    place in the evaluation of expression preserve the borrow check
    invariant for the sv_map and fp_map *)
    
        
        

    
    


    rewrite MEQ1 in MPRED.
    

    exploit get_owner_path_sv_map_eval_place. eauto. eapply MPRED. 
    


End BORROW_CHECK.


Notation li_rs_spec := (@li_rs_spec ae).

(** TODO: the interface for the borrow checking *)
Definition rs_spec : invariant li_rs_spec := inv_bot.

Program Definition rs_bor : callconv li_rs_spec li_rs := 
{|  ccworld := unit;
    match_senv w := eq;
    match_query w q1 q2 := True;
    match_reply w r1 r2 := True;
  |}.
Solve All Obligations with
  cbn; intros; subst; try split; auto.

(* Given a RustIR module [M], if it passes the borrow checking, we
have two results: the first is that the RustIRspec semantics of [M] is
refined by the RustIRbor semantics of [M], so if [M]_RustIRspec is
safe then [M]_RustIRbor is safe; the second is that [M]_RustIRspec is
almost safe, except that it may reach some error states that cannot be
checked by the borrow checking, e.g., division-by-zero. The interface
of the refinement is defined as [rs_bor]. *)
Lemma borrow_check_refinement (P Q: invariant li_rs_spec) (M M': RustIR.program) :
  borrow_check_program M = OK M' ->
  (* It also shows that if RustIRspec is progress then RustIRbor is progress *)
  forward_simulation rs_bor rs_bor (RustIRspec.semantics M) (RustIRsem.semantics M).
Proof.
Admitted.

(** TODO: we should prove that RustIRspec is partial safe instead of
total safe. How to define its safety interface? *)
Theorem borrow_check_spec_safe (M M': RustIR.program) :
  borrow_check_program M = OK M' ->
  module_type_safe rs_spec rs_spec (RustIRspec.semantics M) SIF.
Proof.
Admitted.
