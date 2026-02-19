Require Import Coqlib.
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
Require Import RustIRspec RustIRsem.
Require Import RustIRspecMem.
Require Import BorrowCheckInv.
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
Notation state_spec := (@RustIRspec.state ame).

Section BORROW_CHECK_SIM.

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
(* Hypothesis COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)). *)
(* Hypothesis FUN_CHECK:  forall id fd, *)
(*     In (id, Gfun fd) prog.(prog_defs) -> *)
(*     move_check_fundef_spec ce fd. *)


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


(* Record wf_fpm (f: function) (externs: list ident) (fpm: fp_map) : Prop := *)
(*   { wf_fpm_local_vars: forall id ty,  *)
(*       In (id, ty) (f.(fn_params) ++ f.(fn_vars)) -> *)
(*       exists b fp, fpm ! id = Some (b, 0, None, ty, fp); *)

(*     wf_fpm_external_vars: forall id, *)
(*       In id externs ->       *)
(*       exists b ofs r ty fp, fpm ! id = Some (b, ofs, Some r, ty, fp); *)

(*     wf_fpm_disjoint_local_externs: forall id, *)
(*       In id (field_idents (f.(fn_params) ++ f.(fn_vars))) -> *)
(*       In id externs -> *)
(*       False; *)

(*  }. *)


(* We return the memory predicate instead of defining coherent_fpf is
because we do not clear (which is just a design choice) the footprint
passed via reference to callee. *)
Inductive match_cont: (@RustIRspec.cont ame) -> cont -> massert -> Prop :=
| match_Kstop:
    match_cont RustIRspec.Kstop Kstop STrue
| match_Kseq: forall s k tk MP
   (MCONT: match_cont k tk MP),
    match_cont (RustIRspec.Kseq s k) (Kseq s tk) MP
| match_Kloop: forall s k tk MP
   (MCONT: match_cont k tk MP),
    match_cont (RustIRspec.Kloop s k) (Kloop s tk) MP
| match_Kcall: forall k tk p ns fpm phl MP f
    (MSTK: match_stacks (RustIRspec.Kcall p f phl ns fpm k) (Kcall (Some p) f fpm tk) MP),
    match_cont (RustIRspec.Kcall p f phl ns fpm k) (Kcall (Some p) f fpm tk) MP

with match_stacks : (@RustIRspec.cont ame) -> cont -> massert -> Prop :=
| match_stacks_call: forall f k tk MP1 MP2 phl ns fpm fpm1 p
    (* We should set fp_emp to the inout parameters *)
    (FPM: clear_fpm_passed_ref_footprint fpm (map (fun '(id, (ph, _)) => ph) phl) = OK fpm1)
    (COH: coherent_fpm ge fpm1 MP1)
    (CONT: match_cont k tk MP2),
    match_stacks (RustIRspec.Kcall p f phl ns fpm k) (Kcall (Some p) f fpm tk) (MP1 ** MP2)
.
    

Inductive match_states: state_spec -> state -> Prop :=
| match_regular_states: forall f fpm MP FMP m k tk s ns
    (COHERENT: coherent_fpm ce fpm MP)
    (MCONT: match_cont k tk FMP)
    (MPRED: m |= MP ** FMP),
    match_states (RustIRspec.State f s k ns fpm (Mem.support m)) (State f s tk fpm m)
| match_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args k MP1 MP2 MP3 inout_fpm tk fun_id
    (* TODO: show that fun_id also points to this function *)
    (FUNC: Genv.find_funct ge vf = Some fd)    
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL_LIST: sem_wt_val_list ce fpl args MP1)
    (** output memory locations are sem_wt_loc *)
    (* (INOUTLOCS: map (fun '(b, ofs, _, _, _) => (b, ofs)) inout_params = inout_locs) *)
    (* (INOUTFPL: map snd inout_params = inout_fpl) *)
    (* (WTLOC_LIST: sem_wt_loc_list ce inout_locs inout_fpl MP2) *)
    (INOUT_FPM: coherent_fpm ce inout_fpm MP2)
    (* (ANORM: val_casted_list args tyargs) *)
    (WTFP: list_forall2 (wt_footprint ce inout_fpm) (type_list_of_typelist tyargs) fpl)
    (* (INOUT_TYL: map (fun '(_, _, ty, _) => ty) inout_params = tyl) *)
    (** TODO: move this property to borrow check invariant *)
    (WT_INOUTFPM: wt_fpm ce inout_fpm)
    (MPRED: m |= MP1 ** MP2 ** MP3)
    (STK: match_stacks k tk MP3),
    (* also disjointness of fpl and fpf *)
    match_states (RustIRspec.Callstate fun_id fpl inout_fpm (Mem.support m) k) (Callstate vf args tk m)
| match_returnstate: forall sg m k retty vfp v MP1 MP2 MP3 tk inout_fpm
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) tk = retty)
    (WTVAL: sem_wt_val ce vfp v MP1)
    (** inout memory locations are sem_wt_loc *)
    (* (INOUTLOCS: map (fun '(b, ofs, _, _, _) => (b, ofs)) inout_params = inout_locs) *)
    (* (INOUTFPL: map snd inout_params = inout_fpl) *)
    (* (INOUT_TYL: map (fun '(_, _, ty, _) => ty) inout_params = inout_tyl) *)
    (* (WTLOC_LIST: sem_wt_loc_list ce inout_locs inout_fpl MP2) *)
    (INOUT_FPM: coherent_fpm ce inout_fpm MP2)
    (* (CAST: val_casted v retty) *)
    (WTFP: wt_footprint ce inout_fpm retty vfp)
    (* (WT_INOUTFP: list_forall2 (wt_footprint ce) inout_tyl inout_fpl) *)
    (WT_INOUTFPM: wt_fpm ce inout_fpm)
    (MPRED: m |= MP1 ** MP2 ** MP3)    
    (STK: match_stacks k tk MP3),
    match_states (RustIRspec.Returnstate vfp inout_fpm (Mem.support m) k) (Returnstate v tk m).


(** Properties of evaluating place and expressions  *)

Notation get_owner_loc_footprint_map := (@get_owner_loc_footprint_map ame).

Ltac destr_get_fpm fpm id :=
  let GFP := fresh "GFP" in
  destruct (fpm ! id) as [((((?b & ?ofs) & ?r) & ?ty) & ?fp)|] eqn: GFP;
  match goal with
  | [H : context G [fpm_to_fpg] |- _ ] =>
      setoid_rewrite PTree.gmap1 in H;
      rewrite GFP in H;
      simpl in H
  end.

Ltac destr_path_of_place p :=
  destruct (path_of_place p) as (?pid & ?phl) eqn: ?POP.


Ltac destr_find_field H :=
  destruct find_field as [((?lo & ?hi) & ?ffp)|] eqn: FIND in H; try congruence.

(* Graph properties of sv_map *)


Lemma get_owner_path_map_inv: forall id phl (fpg: fp_graph) ph vs,
    get_owner_path_map (id, phl) fpg = OK (ph, vs) ->
    exists (fp: footprint),
      fpg ! id = Some fp
      /\ get_owner_path fpg (id, nil) phl fp nil = OK (ph, vs).
Admitted.


Ltac inv_get_owner_path_fpm H :=
  let GPH := fresh "GPH" in
  eapply get_owner_path_map_inv in H as GPH;
  destruct GPH as (?fp & ?G1 & ?G2).

(* If a path can be reached via (phl1 ++ phl2) then this reachable
path can be divided into two parts: one is reached from phl1 and one
is reach from phl2 *)
Lemma get_owner_path_app_inv: forall phl1 phl2 ph1 ph3 sv1 vs1 vs3 (fpm: fp_map),
    get_owner_path fpm ph1 (phl1 ++ phl2) sv1 vs1 = OK (ph3, vs3) ->
    exists ph2 vs2 sv2,
      get_owner_path fpm ph1 phl1 sv1 vs1 = OK (ph2, vs2) 
      /\ get_owner_footprint_map ph2 fpm = OK sv2 
      /\ get_owner_path fpm ph2 phl2 sv2 vs2 = OK (ph3, vs3).
Admitted.

Lemma get_owner_path_for_owner: forall (fpm: fp_map) ph fp,
    get_owner_footprint_map ph fpm = OK fp ->
    exists vs, get_owner_path_map ph fpm = OK (ph, vs).
Admitted.

Lemma get_owner_loc_footprint_map_eq: forall (fpm: fp_map) ph b ofs fp,
    get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp) ->
    get_owner_footprint_map ph fpm = OK fp.
Admitted.

Lemma get_owner_loc_footprint_map_app: forall id phl1 phl2 b1 ofs1 fp1 b2 ofs2 fp2 fpm,
    get_owner_loc_footprint_map (id, phl1) fpm = OK (b1, ofs1, fp1) ->
    get_owner_loc_footprint phl2 fp1 b1 ofs1 = OK (b2, ofs2, fp2) ->         
    get_owner_loc_footprint_map (id, phl1 ++ phl2) fpm = OK (b2, ofs2, fp2).
Admitted.

Lemma get_owner_loc_footprint_map_wt: forall phl id fpm b ofs fp,
    get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, fp) ->
    exists ty, wt_path ce fpm (id, phl) = OK ty
          /\ wt_footprint ce fpm ty fp.
Admitted.

Ltac inv_get_owner_path_app H :=
  let GPH := fresh "GPH" in
  let GPH1 := fresh "GPH1" in
  let GVAL := fresh "GVAL" in
  let GPH2 := fresh "GPH2" in
  eapply get_owner_path_app_inv in H as GPH;
  destruct GPH as (?ph & ?vs & ?fp & GPH1 & GVAL & GPH2).

(* Lemma get_owner_sval_map_loc : forall phl id (fpm: fp_map) fp *)
(*     (GET_PH: get_owner_footprint_map (id, phl) fpm = OK fp), *)
(*     exists b ofs fp,  *)
(*       get_owner_loc_footprint_map (id, phl) fpm = Some (b, ofs, fp). *)
(* Admitted. *)


Lemma get_owner_path_map_eval_place: forall (p: place) fpm vs ph m MP
    (COH: coherent_fpm ce fpm MP)
    (MPRED: m |= MP)
    (WT_FPM: wt_fpm ce fpm)
    (WTP: wt_place fpm ce p)
    (GET_PH: get_owner_path_map p fpm = OK (ph, vs)),
    exists b ofs fp,
      get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp)
      /\ eval_place ce fpm m p b (Ptrofs.repr ofs).
Proof.  
  induction p; intros.
  - simpl in *. 
    destr_get_fpm fpm i; try congruence. inv GET_PH.
    simpl. rewrite GFP. exists b, ofs, fp. split; auto.
    inv WTP.
    (** TODO: prove that i is a local variable *)
    admit.
  - simpl in GET_PH.
    destr_path_of_place p.
    inv_get_owner_path_fpm GET_PH.
    inv_get_owner_path_app G2.
    inv WTP.    
    exploit IHp. 1-6: eauto.
    simpl. rewrite G1. eauto.
    intros (b1 & ofs1 & fp1 & A1 & A2).
    (* structure of fp0: how to prove that fp0 must not be opaque
    object? *)
    simpl in GPH2. destruct fp0; try congruence.
    destr_find_field GPH2. inv GPH2.    
    exploit get_owner_loc_footprint_map_eq. eauto. intros A3.
    rewrite A3 in GVAL. inv GVAL.
    (* remaining proof: get_owner_loc_footprint_map_app and getting
    the field offset *)
    admit.
    (* We need to prove that p cannot access a field of an object *)
    admit.
  (* Pdefer *)
  - simpl in GET_PH.
    destr_path_of_place p.
    inv_get_owner_path_fpm GET_PH.
    inv_get_owner_path_app G2.
    inv WTP.
    exploit IHp; eauto.
    simpl. rewrite G1. eauto.
    intros (b1 & ofs1 & fp1 & A1 & A2).
    (* structure of fp0 *)
    simpl in GPH2. destruct fp0; try congruence.
    (* fp_box *)
    + inv GPH2.
      exploit get_owner_loc_footprint_map_eq; eauto. intros A3.
      rewrite A3 in GVAL. inv GVAL.
      (** TODO: we need some theorem like
      get_owner_loc_footprint_map_sem_wt_split *)
      destruct ph0 as (?id & ?ph).
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      inv B1.
      rewrite B2, EQV in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      exists b, 0, fp0. split.
      * eapply get_owner_loc_footprint_map_app; eauto.
      * econstructor; eauto.
        (** TODO: prove by wt_footprint? *)
        assert (PTY: typeof_place p = Tbox t) by admit.
        rewrite PTY. econstructor. reflexivity.
        simpl. rewrite Ptrofs.unsigned_repr. eauto.
        (* prove by hasvalue *)
        admit.
    (* fp_ref *)
    + destruct ph1 as [?ph1|]; try congruence.
      monadInv GPH2.
      exploit get_owner_loc_footprint_map_eq; eauto. intros A3.
      rewrite A3 in GVAL. inv GVAL.
      destruct ph0 as (?id & ?ph).
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      destruct ph as (?id & ?ph).
      inv B1.
      rewrite B2, EQV in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      (* Use invariant for reference *)
      exploit get_owner_loc_footprint_map_wt; eauto.
      intros (ty & WT3 & WT4). inv WT4.
      exists b, ofs, fp0. split; auto.
      econstructor; eauto. 
      (** TODO: may be difficult *)
      assert (PTY1: exists org, typeof_place p = Treference org mut t) by admit.
      destruct PTY1 as (org1 & PTY2).
      rewrite PTY2. econstructor. reflexivity.
      simpl. rewrite Ptrofs.unsigned_repr. eauto. 
      admit.
  (* Pdowncast *)
  - admit.
Admitted.

(* Properties of evaluating expression *)

(** We first need to define a relation for the snapshot of memory
(fpm, list of fp). We should also separate what the simulation need
(i.e., the separation predicate) and what is guaranteed by the dynamic
borrow check (i.e., the wt_fpm and borrow_check_inv). We may need to
add some invariant about "all path in the views are valid" in wt_fpm? *)

Lemma eval_pexpr_match: forall (pe: pexpr) vfp (fpm1 fpm2: fp_map) m MP FMP
    (COH: coherent_fpm ce fpm1 MP)
    (MPRED: m |= MP ** FMP)
    (WTPEXPR: wt_pexpr fpm1 ce pe)
    (WTFPM: wt_fpm ce fpm1)
    (EVAL: eval_pexpr fpm1 pe = OK (vfp, fpm2)),
    exists v mp,
      Rustlightown.eval_pexpr ce fpm1 m tge pe v
      /\ sem_wt_val ce vfp v mp
      /\ coherent_fpm ce fpm2 MP
      /\ m |= mp ** MP ** FMP.
Proof.
Admitted.

(* When we can successfully get the footprint from a path, then we can
move out this footprint and obtain the new memory predicate *)
Lemma get_owner_loc_footprint_map_clear_coherent: forall id phl fpm1 b ofs fp mp mp1 fpm2,
    get_owner_loc_footprint_map (id, phl) fpm1 = OK (b, ofs, fp) ->
    sem_wt_fp ce fp mp1 -> 
    coherent_fpm ce fpm1 mp ->
    clear_footprint_map ce (id, phl) fpm1 = OK fpm2 ->
    exists mp2,             
      coherent_fpm ce fpm2 mp2
      (* Because clear_footprint would set the location to fp_uninit
      which loses the information about the original value stored in
      that location, we can only prove implication instead of
      equivalence. *)
      /\ massert_imp mp (mp1 ** mp2).
Admitted.

(* What is the difference between this lemma and sem_wt_loc_split? *)
Lemma deref_loc_sem_wt_val: forall (fp: footprint) b ofs mp ty m fpm
    (WTLOC: sem_wt_loc ce fp b ofs mp)
    (* For now we only support by_value dereference *)
    (BYVAL: access_by_value ty = true)
    (WTFP: wt_footprint ce fpm ty fp)
    (MPRED: m |= mp),
    exists v mp1 mp2,
      deref_loc ty m b (Ptrofs.repr ofs) v
      /\ sem_wt_loc ce (clear_footprint_rec ce fp) b ofs mp1
      /\ sem_wt_val ce fp v mp2
      /\ massert_imp mp (mp1 ** mp2).
Admitted.

Lemma invalidate_conflict_ref_fpm_coherent_unchanged: forall phl id (fpm: fp_map) am mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (invalidate_conflict_ref_fpm (id, phl) am fpm) mp.
Admitted.

Lemma eval_expr_match: forall (e: expr) vfp (fpm1 fpm2: fp_map) m MP1 FMP 
    (COH: coherent_fpm ce fpm1 MP1)
    (MPRED: m |= MP1 ** FMP)
    (WTEXPR: wt_expr fpm1 ce e)
    (WTFPM: wt_fpm ce fpm1)
    (EVAL: eval_expr ce fpm1 e = OK (vfp, fpm2)),
    exists v mp MP2,
      Rustlightown.eval_expr ce fpm1 m tge e v
      /\ sem_wt_val ce vfp v mp
      /\ coherent_fpm ce fpm2 MP2
      /\ m |= mp ** MP2 ** FMP.
Proof.  
  destruct e; intros.
  (* moveplace *)
  - simpl in EVAL.
    monadInv EVAL. destruct x as (b & ofs).
    inv WTEXPR.
    exploit get_owner_path_for_owner; eauto. 
    eapply get_owner_loc_footprint_map_eq; eauto. intros (vs & GPH).
    exploit get_owner_path_map_eval_place; eauto. eapply MPRED.
    intros (b1 & ofs1 & fp & A1 & A2).
    rewrite A1 in EQ. inv EQ.
    destr_path_of_place p.
    (* Because we need to read the contents in the location of p, we
    use this lemma. *)
    exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
    intros (mp1 & mp2 & B1 & B2).
    (* exploit (@sem_wt_loc_split ame). 2: eauto. *)
    (* we need to prove that fp is not opaque object, i.e., we cannot
    move from an opaque object *)  
    (* admit. *)
    (* intros (mp3 & mp4 & S1 & S2 & S3). *)
    exploit deref_loc_sem_wt_val; eauto.     
    (** TODO; wt_footprint *)
    admit.
    eapply B2. eapply MPRED.
    intros (v & mp3 & mp4 & LOAD & WTLOC1 & WTVAL & MPIMP).
    (** TODO: sem_wt_val should imply sem_wt_fp  *)
    assert (SEMFP: sem_wt_fp ce vfp mp4) by admit.
    (* rewrite MPIMP in B2. rewrite <- sep_assoc in B2. *)
    exploit get_owner_loc_footprint_map_clear_coherent; eauto. 
    intros (mp5 & COH1 & MPIMP1).
    exists v, mp4, mp5.
    do 3 (try apply conj); eauto.
    + econstructor. econstructor.
      eauto. eauto.
    + eapply invalidate_conflict_ref_fpm_coherent_unchanged; eauto.
    + rewrite MPIMP1 in MPRED. 
      rewrite sep_assoc in MPRED.
      eapply MPRED.
  - simpl in EVAL. 
    inv WTEXPR. 
    exploit eval_pexpr_match; eauto.
    intros (v & mp & EVALP & WTVAL & COH1 & MPRED1).
    exists v, mp, MP1.
    do 3 (try apply conj); eauto.
    + econstructor. auto.
Admitted.      

(* moving from a place preserves the borrow checking invariant
under the successful checking. But what is the effect of checking
for pure expr? *)
Lemma eval_expr_preserve_borchk_inv: forall (fpm1 fpm2: fp_map) e vfp
    (INV: borrow_check_inv fpm1)
    (WTFPM: wt_fpm ce fpm1)
    (WTEXPR: wt_expr fpm1 ce e)
    (EVAL: eval_expr ce fpm1 e = OK (vfp, fpm2)),
    borrow_check_fpg_vals_inv fpm2 [vfp]
    /\ wt_fpm ce fpm2
    /\ wt_footprint ce fpm2 (typeof e) vfp.
Proof.
  destruct e; intros.
  (* moveplace *)
  - simpl in EVAL.
    monadInv EVAL. destruct x as (b & ofs).
    inv WTEXPR. 

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
