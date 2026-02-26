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
Hypothesis WTPROG: wt_program prog.
(* Variable w: rs_own_world. *)
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.

(* Let L := RustIRspec.semantics prog se. *)
Let ge := globalenv se prog.
Let tge := RustIR.globalenv se prog.
(* composite environment *)
Let ce := ge.(genv_cenv).

Variable sg: rust_signature.

Let wt_state := @wt_state ame prog se sg.
Let borrowck_inv := @borrowck_inv ame prog se sg.

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
| match_callstate: forall vf fd m fpl args k MP1 MP2 MP3 inout_fpm tk fun_id
    (* TODO: show that fun_id also points to this function *)
    (FUNC: Genv.find_funct ge vf = Some fd)    
    (* arguments are semantics well typed *)
    (WTVAL_LIST: sem_wt_val_list ce fpl args MP1)
    (INOUT_FPM: coherent_fpm ce inout_fpm MP2)
    (* (ANORM: val_casted_list args tyargs) *)
    (MPRED: m |= MP1 ** MP2 ** MP3)
    (STK: match_stacks k tk MP3),
    (* also disjointness of fpl and fpf *)
    match_states (RustIRspec.Callstate fun_id fpl inout_fpm (Mem.support m) k) (Callstate vf args tk m)
| match_returnstate: forall m k vfp v MP1 MP2 MP3 tk inout_fpm
    (WTVAL: sem_wt_val ce vfp v MP1)
    (** inout memory locations are sem_wt_loc *)
    (INOUT_FPM: coherent_fpm ce inout_fpm MP2)
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

Ltac inv_get_owner_path_app H :=
  let GPH := fresh "GPH" in
  let GPH1 := fresh "GPH1" in
  let GVAL := fresh "GVAL" in
  let GPH2 := fresh "GPH2" in
  eapply get_owner_path_app_inv in H as GPH;
  destruct GPH as (?ph & ?vs & ?fp & GPH1 & GVAL & GPH2).

Ltac inv_get_owner_path_fpm H :=
  let GPH := fresh "GPH" in
  eapply get_owner_path_map_inv in H as GPH;
  destruct GPH as (?fp & ?G1 & ?G2).


Lemma get_owner_footprint_map_loc : forall phl id (fpm: fp_map) fp
    (GET_PH: get_owner_footprint_map (id, phl) fpm = OK fp),
    exists b ofs,
      get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, fp).
Admitted.


Lemma get_owner_path_map_eval_place: forall (p: place) fpm vs ph m MP
    (COH: coherent_fpm ce fpm MP)
    (MPRED: m |= MP)
    (WT_FPM: wt_fpm ce fpm)
    (WTP: wt_place fpm ce p)
    (REF_WF: fp_ref_loc_wf_fpm fpm)
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
    exploit (@get_owner_loc_footprint_map_eq ame). eauto. intros A3.
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
      exploit (@get_owner_loc_footprint_map_eq ame); eauto. intros A3.
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
      exploit (@get_owner_loc_footprint_map_eq ame); eauto. intros A3.
      rewrite A3 in GVAL. inv GVAL.
      destruct ph0 as (?id & ?ph).
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      destruct ph as (?id & ?ph).
      inv B1.
      rewrite B2, EQV in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      (* Use invariant for reference *)
      exploit (@get_owner_loc_footprint_map_wt ame); eauto.
      intros (ty & WT3 & WT4& WT5). 
      exploit (@get_owner_loc_footprint_map_fp_ref_wf ame); eauto.
      intros FP_REF_WF. inv FP_REF_WF.
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

Lemma invalidate_conflict_ref_fpm_wt_fpm_unchanged: forall phl id (fpm: fp_map) am,
    wt_fpm ce fpm ->
    wt_fpm ce (invalidate_conflict_ref_fpm (id, phl) am fpm).
Admitted.

Lemma invalidate_conflict_ref_fpm_fp_ref_wf_unchanged: forall phl id (fpm: fp_map) am,
    fp_ref_loc_wf_fpm fpm ->
    fp_ref_loc_wf_fpm (invalidate_conflict_ref_fpm (id, phl) am fpm).
Admitted.


Lemma invalidate_conflict_ref_fpm_wt_footprint_unchanged: forall phl id (fpm: fp_map) am ty (fp: footprint),
    wt_footprint ce (fpm_to_tenv fpm) ty fp ->
    wt_footprint ce (fpm_to_tenv (invalidate_conflict_ref_fpm (id, phl) am fpm)) ty fp.
Admitted.


Lemma invalidate_conflict_ref_fpm_wt_place_unchanged: forall phl id (fpm: fp_map) am p,
    wt_place fpm ce p ->
    wt_place (invalidate_conflict_ref_fpm (id, phl) am fpm) ce p.
Admitted.


Lemma invalidate_conflict_ref_fpm_env_eq: forall phl id (fpm: fp_map) am,
    (fpm_to_env fpm) = (fpm_to_env (invalidate_conflict_ref_fpm (id, phl) am fpm)).
Admitted.

Lemma invalidate_conflict_ref_fpm_tenv_eq: forall phl id (fpm: fp_map) am,
    (fpm_to_tenv fpm) = (fpm_to_tenv (invalidate_conflict_ref_fpm (id, phl) am fpm)).
Admitted.


Lemma invalidate_conflict_ref_fpm_coherent_eq: forall phl id (fpm: fp_map) am mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (invalidate_conflict_ref_fpm (id, phl) am fpm) mp.
Admitted.   

Lemma invalidate_conflict_ref_fpm_check_path_is_dropped: forall phl id am (fpm: fp_map) ph,
    check_path_is_dropped fpm ph = OK true ->
    check_path_is_dropped (invalidate_conflict_ref_fpm (id, phl) am fpm) ph = OK true.
Admitted.

Hint Resolve 
  invalidate_conflict_ref_fpm_wt_place_unchanged 
  invalidate_conflict_ref_fpm_wt_footprint_unchanged
  invalidate_conflict_ref_fpm_coherent_unchanged
  invalidate_conflict_ref_fpm_wt_fpm_unchanged
  invalidate_conflict_ref_fpm_env_eq
  invalidate_conflict_ref_fpm_tenv_eq
  invalidate_conflict_ref_fpm_coherent_eq
  invalidate_conflict_ref_fpm_check_path_is_dropped
  invalidate_conflict_ref_fpm_fp_ref_wf_unchanged: invalidate_fp_ref.

Lemma kill_paths_ref_sem_wt_val: forall v (fp: footprint) vs mp,
    sem_wt_val ce fp v mp ->
    sem_wt_val ce (kill_paths_ref vs fp) v mp.
Admitted.


Lemma kill_paths_ref_coherent_fpm: forall (fpm: fp_map) vs mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (kill_paths_ref_fpm vs fpm) mp.
Admitted.

Hint Resolve 
  kill_paths_ref_sem_wt_val
  kill_paths_ref_coherent_fpm : kill_paths_ref.


Lemma eval_expr_match: forall (e: expr) vfp (fpm1 fpm2: fp_map) m MP1 FMP 
    (COH: coherent_fpm ce fpm1 MP1)
    (MPRED: m |= MP1 ** FMP)
    (WTEXPR: wt_expr fpm1 ce e)
    (WTFPM: wt_fpm ce fpm1)
    (REF_WF: fp_ref_loc_wf_fpm fpm1)
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
    set (fpm1' := (invalidate_conflict_ref_fpm p BorrowCheckDomain.Adeep fpm1)) in *.
    destr_path_of_place p.
    eapply invalidate_conflict_ref_fpm_coherent_unchanged in COH as COH1.
    exploit (@get_owner_path_for_owner ame); eauto. 
    eapply get_owner_loc_footprint_map_eq; eauto. intros GPH.
    exploit (get_owner_path_map_eval_place); eauto. eapply MPRED.
    1-4: eauto with invalidate_fp_ref. rewrite POP. eapply GPH.    
    intros (b1 & ofs1 & fp & A1 & A2).    
    unfold fpm1' in *.
    setoid_rewrite A1 in EQ. inv EQ.
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
    intros (mp5 & COH2 & MPIMP1).
    exists v, mp4, mp5.
    do 3 (try apply conj); eauto.
    + econstructor. econstructor.
      erewrite invalidate_conflict_ref_fpm_env_eq. eauto.
      eauto. 
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



Lemma clear_is_dropped_fp_map_coherent: forall (fpm1 fpm2: fp_map) ph mp1,
    check_path_is_dropped fpm1 ph = OK true ->
    clear_footprint_map ce ph fpm1 = OK fpm2 ->
    coherent_fpm ce fpm1 mp1 ->
    exists mp2, coherent_fpm ce fpm2 mp2 /\ massert_imp mp1 mp2.
Admitted.

(* Ltac simpl_getIM IM := *)
(*   generalize IM as IM1; intros; *)
(*   inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst; *)
(*   try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *. *)

Ltac unfold_eval_assign :=
  match goal with
  | [H : context G [eval_assign] |- _ ] =>
      unfold eval_assign in H; monadInv H;
      match goal with
      | [H1 : context G [before_write_place _ _ _ = OK (?a, ?b)] |- _ ] =>
          destruct a as ((?tgt_id & ?tgt_phl) & ?vs)
      end
  end.

Ltac unfold_before_write_place :=
  match goal with
  | [H : context G [before_write_place] |- _ ] =>
      unfold before_write_place in H; monadInv H;
      match goal with
      | [H1 : context G [check_path_is_dropped _ _ = OK ?b],
            H2: context [(if ?b then _ else _) = OK _]    
         |- _ ] =>              
          destruct b; try monadInv H2
      end
  end.


Lemma step_simulation: forall s1 t s2 s1',
    RustIRspec.step ge s1 t s2 ->
    match_states s1 s1' ->
    borrowck_inv s1 ->
    wt_state s1 ->
    exists s2', 
      plus RustIRsem.step tge s1' t s2' /\ match_states s2 s2' /\ borrowck_inv s2.
Proof.
  intros s1 t s2 s1' STEP MATCH BORINV WTST. 
  inv STEP; inv MATCH; inv BORINV; inv WTST.
  (* Sassign *)
  - inv WT1.
    unfold_eval_assign. inv EQ2.
    unfold_before_write_place.        
    destr_path_of_place p.
    (* evaluate expr *)
    exploit eval_expr_match. eauto. eapply MPRED. 
    (* wt_expr *) eauto.
    (* wt_fpm: we should add a new state invariant *) admit.
    eapply BOR_INV.
    eauto.
    intros (tv & mp1 & mp2 & TEVAL & WTVAL & COH1 & MPRED1).
    (* evaluate expr preserves borrow check invariant. We should write
    it in a separated lemma *)
    exploit (@eval_expr_preserve_borchk_inv ame); eauto.
    intros BORCK_INV1.  (* & WTFPM1 & WTFP1). *)
    (* shallow write preserves borrow check invariant *)
    exploit (@borrow_check_inv_shallow_write ame); eauto.
    (* econstructor. eauto. econstructor. *)
    intros BORCK_INV2.  (* & WTFP2 & WTFPM2). *)
    (* set footprint to the assginee preserves the invariant *)
    exploit (@borrow_check_inv_set_fp ame); eauto.
    eapply kill_paths_ref_fpm_preserve_is_dropped; eauto.
    eapply clear_footprint_map_is_dropped; eauto.
    intros BORCK_INV3. (* & WTFP3 & WTFPM3). *)
    (* derive the memory predicate before setting the footprint into
    fpm *)
    exploit invalidate_conflict_ref_fpm_check_path_is_dropped; eauto.
    intros ISDROP1.    
    exploit clear_is_dropped_fp_map_coherent. eauto. eapply EQ2.
    eauto with invalidate_fp_ref.
    intros (mp2' & COH2 & MPIMP1).
    exploit (kill_paths_ref_coherent_fpm x3 vs). eapply COH2. 
    intros COH3.
    (* derive the predicate for the value *)
    exploit kill_paths_ref_sem_wt_val; eauto. 
    instantiate (1 := vs). intros WTVAL1.
    (* evaluate the address of the assignee *)
    exploit (get_owner_path_map_eval_place p).
    eapply COH1. eapply MPRED1. 
    (* wt_fpm ce x0: we should prove a wt_footprint/wt_fpm
    preservation leamm *) admit.
    (* wt_place *) admit.
    eapply BORCK_INV1.
    rewrite POP. eapply EQ0.
    intros (b & ofs & pfp & GPLOC & EVALP).
    (** TODO: prove that invalidate_fp_ref, kill_paths_ref_fpm and
    clear_footprint_map in [ph] does not change the location of [ph] *)
    assert (GPLOC1: get_owner_loc_footprint_map  (tgt_id, tgt_phl)  (kill_paths_ref_fpm vs x3) = OK (b, ofs, clear_footprint_rec ce pfp)) by admit.
    assert (MPRED3: m |= mp2' ** mp1 ** FMP) by admit.
    (** Proved by type checking *)
    assert (BYVAL: exists chunk, access_mode (typeof_place p) = Ctypes.By_value chunk) by admit.
    destruct BYVAL as (chunk & BYVAL).    
    (* inv WTFP2. inv H4. *)
    (* assign_loc *)
    exploit (@get_owner_loc_footprint_map_wt ame); eauto.
    instantiate (1 := ce).
    (* wt_fpm: we should prove a wt_footprint/wt_fpm
    preservation leamm *) admit.
    intros (ty & WTPH1 & WTFP4 & AL).
    exploit (@assign_loc_by_value_coherent_fpm ame). eapply COH3.
    eapply WTVAL1. eauto.
    eapply GPLOC1. eauto. eauto. 
    (** lots of work need to be done to prove ty = typeof e = typeof p
    where '=' represent type_eq_except_origins because the
    get_owner_path_map p is performed on x0 instead of the fp_map
    after invalidation and kill_paths and clear_footprint. *)
    admit. instantiate (1 := chunk). admit.
    intros (m1 & fpm2 & mp3 & ASSIGN & SET1 & COH4 & MPRED4).
    rewrite ASS in SET1. inv SET1.
    (** All operations on fpm do not change the local env *)
    assert (ENVEQ1: fpm_to_env fpm1 = fpm_to_env x0) by admit.
    assert (ENVEQ2: fpm_to_env fpm1 = fpm_to_env fpm2) by admit.
    eexists. do 3 (try apply conj).
    + econstructor.      
      econstructor. rewrite ENVEQ1. eauto. eauto.
      (* sem_cast: We need to ignore it *)
      instantiate (1 := tv). admit.
      simpl.
      (** Also the problem of ty = typeof e = typeof p where '='
    represent type_eq_except_origins *)
      replace (typeof_place p) with ty by admit.
      eauto. eapply star_refl. auto.
    + rewrite ENVEQ2. 
      replace (Mem.support m) with (Mem.support m1) by admit.
      econstructor; eauto.
    + econstructor; eauto.
      eapply borrow_check_fpg_vals_inv_empty. eauto.
      
  - admit.
  - admit.
  (* Sdrop *)
  - inv WT1.
    destr_path_of_place p.
    unfold check_path_is_droppable in DEEP_INIT.
    monadInv DEEP_INIT.
    (* preserve borrow check invariant *)
    exploit get_owner_footprint_map_loc; eauto.
    intros (b & ofs & GLOC).
    exploit (@borrow_check_inv_move ame); eauto.
    instantiate (1 := nil).  admit.
    (* econstructor. instantiate (1 := typeof p). admit. (* wt_place *)
    implies wt_path *)
    intros BOR_INV1. (* & WTFP1 & WTFPM1). *)
    exploit (@borrow_check_inv_drop ame); eauto.
    instantiate (1 := O). simpl.
    intros BOR_INV2. (* & WTFP2 & WTFPM2). *)
    eapply borrow_check_fpg_vals_inv_empty in BOR_INV2.
    (* Use type information to do case analysis *)
    assert (WTFPM1: wt_fpm ce (invalidate_conflict_ref_fpm (pid, phl)
            BorrowCheckDomain.Adeep fpm1)) by admit.
    assert (DROP_TY: drop_type (typeof_place p) = true) by admit. (* It should be ensured by the syntatic type checking *)
    exploit (@get_owner_loc_footprint_map_wt ame); eauto.
    intros (pty & WTPH & WTFP & AL).
    replace pty with (typeof_place p) in * by admit. (* wt_path and wt_place properties *)
    destruct (typeof_place p) eqn: PTY; simpl in DROP_TY; try congruence.
    
    (* Tbox *)
    + inv WTFP; try congruence.
        (* fp_uninit is impossible. It should be ruled out by Drop
         elaboration *)
      (* memory predicate after deep access *)
      exploit (invalidate_conflict_ref_fpm_coherent_eq phl pid fpm1 BorrowCheckDomain.Adeep); eauto.
      intros COH1.
      (* eval_place *)
      exploit (get_owner_path_map_eval_place); eauto. eapply MPRED.
      1-4: eauto with invalidate_fp_ref. 
      eapply invalidate_conflict_ref_fpm_fp_ref_wf_unchanged. eapply BOR_INV.
      eapply get_owner_path_for_owner.
      eapply get_owner_loc_footprint_map_eq. rewrite POP. eapply GLOC.
      rewrite POP.
      intros (b1 & ofs1 & fp1 & A1 & A2).    
      rewrite GLOC in A1. inv A1.
      (* evaluate the address of dropped place *)
      exploit (@get_owner_loc_footprint_map_sem_wt_split ame); eauto.
      intros (mp1 & mp2 & B1 & B2).
      inv B1.
      (* memory predicate after drop: drop is like a move operation *)
      exploit (@get_owner_loc_footprint_map_clear_coherent); eauto.
      econstructor. eauto. reflexivity.
      intros (mp3 & COH2 & MPIMP).
      rewrite EQV in B2. 
      generalize MPRED as MPRED1. intros.
      rewrite B2 in MPRED.
      exploit load_rule. eapply MPRED. intros (?v & C1 & C2). subst.
      (* evaluate the free operation *)
      assert (FREE: exists m1, extcall_free_sem tge [Vptr b0 Ptrofs.zero] m E0 Vundef m1).
      { unfold box_pred in *.
        (* range_perm of fp *)
        exploit (@sem_wt_loc_range_perm ame). eapply WT. eauto.
        intros FP_RANGE. rewrite FP_RANGE in MPRED.
        replace (sizeof_footprint ce fp) with (sizeof ce t) in * by admit.
        (* load the size of the deallocated block *)
        exploit load_rule_neg. eapply MPRED. intros (?v & D1 & D2). subst.
        (** A bit tricky here: we use MPIMP and MPRED1 to prove the
        free operation because mp3 is the predicate after
        clear_footprint *)
        rewrite MPIMP in MPRED1.
        rewrite FP_RANGE in MPRED1.        
        (** free operation : TODO the free_rules only support positive
        location for now.  *)        
        assert (RANGE_PRED: m |= range b0 (- size_chunk Mptr) (sizeof ce t) ** mp3 ** FMP).
        admit.
        edestruct Mem.range_perm_free as (m1 & FREE).
        red. intros. eapply RANGE_PRED. eauto.
        exists m1. 
        econstructor. 
        rewrite Z.sub_0_l. eauto.
        all: rewrite Ptrofs.unsigned_repr.
        admit. (* sizeof positive *)
        admit. (* sizeof range *)
        rewrite Z.add_0_l. rewrite Z.sub_0_l. 
        eauto. 
        admit. (* sizeof range *) }
      destruct FREE as (m1 & FREE).  
      (* To prove this, we need a free_rule which supports negative
      location *)
      assert (MPRED2: m1 |= mp3 ** FMP) by admit.
      (** All operations on fpm do not change the local env *)
      assert (ENVEQ1: fpm_to_env fpm1 = fpm_to_env fpm3) by admit.
      eexists. do 3 (try apply conj).
      * econstructor.
        eapply step_drop_box. 
        erewrite invalidate_conflict_ref_fpm_env_eq.
        eauto. eauto.
        econstructor. reflexivity. simpl. rewrite Ptrofs.unsigned_repr.
        eauto. admit.           (* range proof *)
        eauto. eapply star_refl. auto.
      * rewrite ENVEQ1.
        replace (Mem.support m) with (Mem.support m1) by admit.
        econstructor; eauto.
      * econstructor; eauto.

    + 

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
