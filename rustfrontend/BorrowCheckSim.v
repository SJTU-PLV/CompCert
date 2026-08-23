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
Require Import BorrowCheck BorrowCheckInv.
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

(* Context {ame: adt_mem_env}. *)

(* Notation footprint := (@footprint ame). *)
(* Notation fp_map := (@fp_map ame). *)
(* Notation state_spec := (@RustIRspec.state ame). *)

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

(* Let wt_state := @wt_state ame prog se sg. *)
Let wt_state := RustIRspec.wt_state prog se sg.
Let borrowck_inv := @borrowck_inv prog se sg.

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
Inductive match_cont: RustIRspec.cont -> cont -> massert -> Prop :=
| match_Kstop:
    match_cont RustIRspec.Kstop Kstop STrue
| match_Kseq: forall s k tk MP
   (MCONT: match_cont k tk MP),
    match_cont (RustIRspec.Kseq s k) (Kseq s tk) MP
| match_Kloop: forall s k tk MP
   (MCONT: match_cont k tk MP),
    match_cont (RustIRspec.Kloop s k) (Kloop s tk) MP
| match_Kcall: forall k tk p MP f e
    (MSTK: match_stacks (RustIRspec.Kcall p f k) (Kcall (Some p) f e tk) MP),
    match_cont (RustIRspec.Kcall p f  k) (Kcall (Some p) f e tk) MP

with match_stacks : RustIRspec.cont -> cont -> massert -> Prop :=
| match_stacks_call: forall f k tk MP1 MP2 fpm fpm1 p
    (* We should set fp_emp to the inout parameters *)
    (* (FPM: clear_fpm_passed_ref_footprint fpm (map (fun '(id, (ph, _)) => ph) phl) = OK fpm1) *)
    (COH: coherent_fpm ge fpm1 MP1)
    (CONT: match_cont k tk MP2),
    match_stacks (RustIRspec.Kcall p f k) (Kcall (Some p) f fpm tk) (MP1 ** MP2)
.
    

Inductive match_states: RustIRspec.state -> state -> Prop :=
| match_regular_states: forall f fpm MP FMP m k tk s fidx
    (COHERENT: coherent_fpm ce fpm MP)
    (MCONT: match_cont k tk FMP)
    (MPRED: m |= MP ** FMP),
    match_states (RustIRspec.State f s k fpm fidx (Mem.support m)) (State f s tk fpm m)
| match_callstate: forall vf fd m fpl args k MP1 MP2 MP3 fpm tk fun_id fidx
    (* TODO: show that fun_id also points to this function *)
    (FUNC: Genv.find_funct ge vf = Some fd)    
    (* arguments are semantics well typed *)
    (WTVAL_LIST: sem_wt_val_list ce fpl args MP1)
    (INOUT_FPM: coherent_fpm ce fpm MP2)
    (* (ANORM: val_casted_list args tyargs) *)
    (MPRED: m |= MP1 ** MP2 ** MP3)
    (STK: match_stacks k tk MP3),
    (* also disjointness of fpl and fpf *)
    match_states (RustIRspec.Callstate fun_id fpl fpm fidx (Mem.support m) k) (Callstate vf args tk m)
| match_returnstate: forall m k vfp v MP1 MP2 MP3 tk fpm fidx
    (WTVAL: sem_wt_val ce vfp v MP1)
    (** inout memory locations are sem_wt_loc *)
    (INOUT_FPM: coherent_fpm ce fpm MP2)
    (MPRED: m |= MP1 ** MP2 ** MP3)    
    (STK: match_stacks k tk MP3),
    match_states (RustIRspec.Returnstate vfp fpm fidx (Mem.support m) k) (Returnstate v tk m).


(** Properties of evaluating place and expressions  *)

(* Notation get_owner_loc_footprint_map := (@get_owner_loc_footprint_map ame). *)

Ltac destr_get_fpm fpm id :=
  let GFP := fresh "GFP" in
  destruct (fpm ! id) as [(((?b & ?ofs) & ?ty) & ?fp)|] eqn: GFP.
  (* match goal with *)
  (* | [H : context G [fpm] |- _ ] => *)
  (*     (* setoid_rewrite PTree.gmap1 in H; *) *)
  (*     rewrite GFP in H; *)
  (*     simpl in H *)
  (* end. *)

Ltac destr_path_of_place p :=
  destruct (path_of_place p) as (?pid & ?phl) eqn: ?POP.


Ltac destr_find_field H :=
  destruct find_field as [((?lo & ?hi) & ?ffp)|] eqn: FIND in H; try congruence.

(* Graph properties of sv_map *)

Ltac inv_get_owner_path_app H ROOT :=
  match type of H with
  | get_owner_path ?fpm ?ph1 (?phl1 ++ ?phl2) ?fp ?aliases =
      OK (?ph3, ?views) =>
      let GET_ROOT := fresh "GET_ROOT" in
      assert (GET_ROOT: get_owner_footprint_map ph1 fpm = OK fp) by
        (unfold get_owner_footprint_map; simpl; rewrite ROOT; reflexivity);
      let GPH := fresh "GPH" in
      let GPH1 := fresh "GPH1" in
      let GVAL := fresh "GVAL" in
      let GPH2 := fresh "GPH2" in
      pose proof
        (get_owner_path_app_inv phl1 phl2 ph1 ph3 fp aliases views fpm
          GET_ROOT H) as GPH;
      destruct GPH as (?ph & ?vs & ?fp & GPH1 & GVAL & GPH2)
  end.

Ltac inv_get_owner_path_fpm H :=
  let GPH := fresh "GPH" in
  eapply get_owner_path_map_inv in H as GPH;
  destruct GPH as (?fp & ?G1 & ?G2).


Lemma get_owner_loc_footprint_get_owner_footprint : forall phl fp b ofs fp',
    get_owner_footprint phl fp = OK fp' ->
    exists b' ofs', get_owner_loc_footprint phl fp b ofs = OK (b', ofs', fp').
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros.
  - inv H. exists b, ofs. reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph vs];
      simpl in H; try congruence.
    + destruct (IH fp1 b1 0 fp' H) as (b' & ofs' & H1). exists b', ofs'. exact H1.
    + destruct (find_field fid1 fpl) as [[[base fofs] fp1]|] eqn:FIND;
        simpl in H; try congruence.
      destruct (IH fp1 b (ofs + fofs) fp' H) as (b' & ofs' & H1). exists b', ofs'. exact H1.
    + destruct (ident_eq fid1 fid2) eqn:EQ; simpl in H; try congruence.
      destruct (IH fp1 b (ofs + fofs) fp' H) as (b' & ofs' & H1). exists b', ofs'. exact H1.
Qed.


Lemma get_owner_footprint_map_loc : forall phl id (fpm: fp_map) fp
    (GET_PH: get_owner_footprint_map (id, phl) fpm = OK fp),
    exists b ofs,
      get_owner_loc_footprint_map (id, phl) fpm = OK (b, ofs, fp).
Proof using Type.
  intros phl id fpm fp GET_PH.
  unfold get_owner_footprint_map, get_owner_loc_footprint_map in *.
  simpl in *.
  destruct (fpm ! id) as [[[[b ofs] ty] fp0]|] eqn:FPM; simpl in *; try congruence.
  destruct (get_owner_loc_footprint_get_owner_footprint phl fp0 b ofs fp GET_PH)
    as (b' & ofs' & H1).
  exists b', ofs'. exact H1.
Qed.


Lemma get_owner_path_map_eval_place: forall (frame: frame_idx) (p: place) fpm vs ph m MP
    (COH: coherent_fpm ce fpm MP)
    (MPRED: m |= MP)
    (WT_FPM: wt_fpm ce fpm)
    (WTP: wt_place fpm ce p)
    (REF_WF: fp_ref_loc_wf_fpm fpm)
    (GET_PH: get_owner_path_map (enc_path frame p) fpm = OK (ph, vs)),
    exists b ofs fp,
      get_owner_loc_footprint_map ph fpm = OK (b, ofs, fp)
      /\ eval_place ce fpm m p b (Ptrofs.repr ofs).
Proof.
(* WIP proof body commented out: it was written against an older
   version of the helper lemmas (get_owner_path_map_inv,
   inv_get_owner_path_app) and references the removed [ame] context,
   so it no longer processes. Kept here for reference:
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
    inv_get_owner_path_app G2 G1.
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
    inv_get_owner_path_app G2 G1.
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
 *)
Admitted.

Section FRAME.

Variable frame: frame_idx.

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
    (EVAL: eval_pexpr frame fpm1 pe = OK (vfp, fpm2)),
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

(* What is the difference between this lemma and sem_wt_loc_split?
Note that this lemma only works for Emoveplace not. It does not
support Eplace. *)
Lemma deref_loc_sem_wt_val: forall (fp: footprint) b ofs mp ty m fpm
    (WTLOC: sem_wt_loc ce fp b ofs mp)
    (* For now we only support by_value dereference *)
    (BYVAL: access_by_value ty = true)
    (WTFP: wt_footprint ce fpm ty fp)
    (MPRED: m |= mp),
    exists v mp1 mp2,
      deref_loc ty m b (Ptrofs.repr ofs) v
      (* What if we do not move out the footprint? *)
      /\ sem_wt_loc ce (clear_footprint_rec ce fp) b ofs mp1
      /\ sem_wt_val ce fp v mp2
      /\ massert_imp mp (mp1 ** mp2).
Admitted.


(** General infrastructure for endomorphisms of [footprint] that
    preserve its structure.  Both [invalidate_conflict_ref ph ak am]
    and [kill_views_ref kill] are instances, which lets us prove the
    preservation of [get_owner_footprint], [get_owner_loc_footprint],
    [sizeof_footprint], [fp_is_dropped], [sem_wt_loc], [sem_wt_fp],
    [sem_wt_val], [wt_footprint], and [coherent_fpm] once and for
    all. *)

Definition struct_fp_map (f: footprint -> footprint) : Prop :=
  (forall sz al, f (fp_emp sz al) = fp_emp sz al)
  /\ (forall sz al, f (fp_uninit sz al) = fp_uninit sz al)
  /\ (forall chunk v, f (fp_scalar chunk v) = fp_scalar chunk v)
  /\ (forall b fp1, f (fp_box b fp1) = fp_box b (f fp1))
  /\ (forall id fpl,
         f (fp_struct id fpl) =
         fp_struct id (map (fun '(fid, (r, ffp)) => (fid, (r, f ffp))) fpl))
  /\ (forall id tag fid fofs fp1,
         f (fp_enum id tag fid fofs fp1) = fp_enum id tag fid fofs (f fp1))
  /\ (forall mut b ofs ph vs,
         (exists vs', f (fp_ref mut b ofs (Some ph) vs) = fp_ref mut b ofs (Some ph) vs')
         \/ (exists vs', f (fp_ref mut b ofs (Some ph) vs) = fp_ref mut b ofs None vs'))
  /\ (forall mut b ofs vs,
         exists vs', f (fp_ref mut b ofs None vs) = fp_ref mut b ofs None vs').

Lemma invalidate_conflict_ref_struct_fp_map: forall ph ak am,
    struct_fp_map (invalidate_conflict_ref ph ak am).
Proof using Type.
  intros ph ak am. unfold struct_fp_map.
  repeat split; intros; simpl; try reflexivity.
  - destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs).
    + right. eexists. reflexivity.
    + left. eexists. reflexivity.
  - destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs);
      eexists; reflexivity.
Qed.

Lemma kill_views_ref_struct_fp_map: forall kill,
    struct_fp_map (kill_views_ref kill).
Proof using Type.
  intros kill. unfold struct_fp_map.
  repeat split; intros; simpl; try reflexivity.
  - left. eexists. reflexivity.
  - eexists. reflexivity.
Qed.


Lemma find_field_map_ffp: forall (f: footprint -> footprint) fid
    (fpl: list (ident * ((Z * Z) * footprint))),
    find_field fid (map (fun '(id, (r, ffp)) => (id, (r, f ffp))) fpl) =
    option_map (fun '(r, ffp) => (r, f ffp)) (find_field fid fpl).
Proof using Type.
  intros f fid fpl.
  induction fpl as [|[id [r ffp]] fpl IH]; auto.
  simpl. rewrite ! find_field_cons.
  destruct (ident_eq fid id); simpl; auto.
Qed.


Lemma struct_fp_map_get_owner_footprint: forall f phl fp fp',
    struct_fp_map f ->
    get_owner_footprint phl fp = OK fp' ->
    get_owner_footprint phl (f fp) = OK (f fp').
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros.
  - inv H0. reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph0 vs];
      simpl in H0; try congruence.
    + pose proof H as SM'. destruct H as (_ & _ & _ & E4 & _ & _ & _ & _).
      rewrite E4. simpl. eapply IH; eauto.
    + pose proof H as SM'. destruct H as (_ & _ & _ & _ & E5 & _ & _ & _).
      rewrite E5. simpl. rewrite find_field_map_ffp.
      destruct (find_field fid1 fpl) as [[[base fofs] ffp]|] eqn:FIND;
        simpl in *; try congruence.
      eapply IH; eauto.
    + pose proof H as SM'. destruct H as (_ & _ & _ & _ & _ & E6 & _ & _).
      rewrite E6. simpl.
      destruct (ident_eq fid1 fid2); simpl in *; try congruence.
      eapply IH; eauto.
Qed.


Lemma struct_fp_map_get_owner_loc_footprint: forall f phl fp b ofs b' ofs' fp',
    struct_fp_map f ->
    get_owner_loc_footprint phl fp b ofs = OK (b', ofs', fp') ->
    get_owner_loc_footprint phl (f fp) b ofs = OK (b', ofs', f fp').
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros.
  - inv H0. reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph0 vs];
      simpl in H0; try congruence.
    + pose proof H as SM'. destruct H as (_ & _ & _ & E4 & _ & _ & _ & _).
      rewrite E4. simpl. eapply IH; eauto.
    + pose proof H as SM'. destruct H as (_ & _ & _ & _ & E5 & _ & _ & _).
      rewrite E5. simpl. rewrite find_field_map_ffp.
      destruct (find_field fid1 fpl) as [[[base fofs] ffp]|] eqn:FIND;
        simpl in *; try congruence.
      eapply IH; eauto.
    + pose proof H as SM'. destruct H as (_ & _ & _ & _ & _ & E6 & _ & _).
      rewrite E6. simpl.
      destruct (ident_eq fid1 fid2); simpl in *; try congruence.
      eapply IH; eauto.
Qed.


Lemma struct_fp_map_get_owner_footprint_map: forall f ps fpm fp,
    struct_fp_map f ->
    get_owner_footprint_map ps fpm = OK fp ->
    get_owner_footprint_map ps
      (PTree.map1 (fun '(b, ofs, ty, fp0) => (b, ofs, ty, f fp0)) fpm) = OK (f fp).
Proof using Type.
  intros f [id phl] fpm fp SM GET.
  unfold get_owner_footprint_map in *. simpl in *.
  rewrite PTree.gmap1 in *.
  destruct (fpm ! id) as [entry|] eqn:FPM; simpl in *; try congruence.
  destruct entry as [[[b ofs] ty] fp0]; simpl in *.
  eapply struct_fp_map_get_owner_footprint; eauto.
Qed.


Lemma struct_fp_map_get_owner_loc_footprint_map: forall f ps fpm b ofs fp,
    struct_fp_map f ->
    get_owner_loc_footprint_map ps fpm = OK (b, ofs, fp) ->
    get_owner_loc_footprint_map ps
      (PTree.map1 (fun '(b, ofs, ty, fp0) => (b, ofs, ty, f fp0)) fpm) = OK (b, ofs, f fp).
Proof using Type.
  intros f [id phl] fpm b ofs fp SM GET.
  unfold get_owner_loc_footprint_map in *. simpl in *.
  rewrite PTree.gmap1 in *.
  destruct (fpm ! id) as [entry|] eqn:FPM; simpl in *; try congruence.
  destruct entry as [[[b0 ofs0] ty] fp0]; simpl in *.
  eapply struct_fp_map_get_owner_loc_footprint; eauto.
Qed.


Lemma struct_fp_map_sizeof: forall f fp,
    struct_fp_map f ->
    sizeof_footprint ce (f fp) = sizeof_footprint ce fp.
Proof.
  intros f fp SM.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid fofs fp1 | mut b1 ofs1 ph0 vs] using strong_footprint_ind.
  - destruct SM as (E1 & _ & _ & _ & _ & _ & _ & _). rewrite E1. reflexivity.
  - destruct SM as (_ & E2 & _ & _ & _ & _ & _ & _). rewrite E2. reflexivity.
  - destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _). rewrite E3. reflexivity.
  - destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _). rewrite E4. simpl. reflexivity.
  - destruct SM as (_ & _ & _ & _ & E5 & _ & _ & _). rewrite E5. simpl. reflexivity.
  - destruct SM as (_ & _ & _ & _ & _ & E6 & _ & _). rewrite E6. simpl. reflexivity.
  - destruct ph0 as [ph1|].
    + destruct SM as (_ & _ & _ & _ & _ & _ & E7 & _).
      destruct (E7 mut b1 ofs1 ph1 vs) as [[vs' H1]|[vs' H1]]; rewrite H1; simpl; reflexivity.
    + destruct SM as (_ & _ & _ & _ & _ & _ & _ & E8).
      destruct (E8 mut b1 ofs1 vs) as (vs' & H1); rewrite H1; simpl; reflexivity.
Qed.


Lemma forallb_map_f: forall (A B: Type) (P: A -> bool) (g: B -> A) l,
    forallb P (map g l) = forallb (fun x => P (g x)) l.
Proof using Type.
  intros A B P g l. induction l as [|a l IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma forallb_In_ext: forall (A: Type) (P Q: A -> bool) l,
    (forall x, In x l -> P x = Q x) -> forallb P l = forallb Q l.
Proof using Type.
  intros A P Q l H. induction l as [|a l IH]; simpl; auto.
  assert (HA: P a = Q a) by (eapply H; left; reflexivity).
  rewrite HA. rewrite IH; [reflexivity | intros x IN; eapply H; right; exact IN].
Qed.

Lemma struct_fp_map_fp_is_dropped: forall f fp,
    struct_fp_map f ->
    fp_is_dropped (f fp) = fp_is_dropped fp.
Proof using Type.
  intros f fp SM.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind.
  - destruct SM as (E1 & _ & _ & _ & _ & _ & _ & _). rewrite E1. reflexivity.
  - destruct SM as (_ & E2 & _ & _ & _ & _ & _ & _). rewrite E2. reflexivity.
  - destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _). rewrite E3. reflexivity.
  - destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _). rewrite E4. simpl. reflexivity.
  - pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & E5 & _ & _ & _). rewrite E5. simpl.
    rewrite forallb_map_f. apply forallb_In_ext. intros x IN.
    destruct x as [fid' [r ffp']]. simpl.
    destruct r as [base' fofs']. eapply IHfields; eauto.
  - destruct SM as (_ & _ & _ & _ & _ & E6 & _ & _). rewrite E6. simpl.
    exact IHenum.
  - destruct ph0 as [ph1|].
    + destruct SM as (_ & _ & _ & _ & _ & _ & E7 & _).
      destruct (E7 mut b1 ofs1 ph1 vs) as [[vs' H1]|[vs' H1]]; rewrite H1; simpl; reflexivity.
    + destruct SM as (_ & _ & _ & _ & _ & _ & _ & E8).
      destruct (E8 mut b1 ofs1 vs) as (vs' & H1); rewrite H1; simpl; reflexivity.
Qed.


Lemma fields_loc_sep_struct_fp_map: forall f b ofs fpl mass,
    (forall fid r ffp b' ofs' mp',
       In (fid, (r, ffp)) fpl ->
       sem_wt_loc ce ffp b' ofs' mp' ->
       sem_wt_loc ce (f ffp) b' ofs' mp') ->
    fields_loc_sep b ofs (sem_wt_loc ce) fpl mass ->
    fields_loc_sep b ofs (sem_wt_loc ce)
      (map (fun '(fid, (r, ffp)) => (fid, (r, f ffp))) fpl) mass.
Proof.
  intros f b ofs fpl mass PRES H.
  induction H as [mass0 EQV | fid base fofs ffp l mass1 mass2 padmp mp IND IHIND FWT ALPERM EQV];
    simpl.
  - econstructor; eauto.
  - econstructor.
    + eapply IHIND. intros fid' r' ffp' b' ofs' mp' IN' HFFP'.
      eapply PRES. right. exact IN'. exact HFFP'.
    + eapply PRES. left. reflexivity. exact FWT.
    + exact ALPERM.
    + exact EQV.
Qed.


Lemma sem_wt_loc_struct_fp_map: forall f fp b ofs mp,
    struct_fp_map f ->
    sem_wt_loc ce fp b ofs mp ->
    sem_wt_loc ce (f fp) b ofs mp.
Proof.
  intros f fp b ofs mp. revert b ofs mp.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros b ofs mp SM H.
  - inv H. destruct SM as (E1 & _ & _ & _ & _ & _ & _ & _). rewrite E1. econstructor; eauto.
  - inv H. destruct SM as (_ & E2 & _ & _ & _ & _ & _ & _). rewrite E2. econstructor; eauto.
  - inv H. destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _). rewrite E3. econstructor; eauto.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _).
    rewrite E4. econstructor.
    + eapply IHbox; eauto.
    + assert (BOXPREQ: box_pred ce (f fp1) b1 nextmp = box_pred ce fp1 b1 nextmp).
      { unfold box_pred. rewrite (struct_fp_map_sizeof f fp1 SM'). reflexivity. }
      rewrite BOXPREQ. exact EQV.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & E5 & _ & _ & _).
    rewrite E5. econstructor.
    + eapply fields_loc_sep_struct_fp_map.
      * intros fid' r' ffp' b' ofs' mp' IN' HFFP'. destruct r' as [base' fofs'].
        eapply IHfields; eauto.
      * exact FWT.
    + reflexivity.
    + exact EQV.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & _ & E6 & _ & _).
    rewrite E6. econstructor.
    + reflexivity.
    + eapply IHenum. exact SM'. exact FWT.
    + reflexivity.
    + reflexivity.
    + rewrite (struct_fp_map_sizeof f fp1 SM'). exact EQV.
  - inv H. destruct SM as (_ & _ & _ & _ & _ & _ & E7 & E8).
    destruct ph0 as [ph1|].
    + destruct (E7 mut b1 ofs1 ph1 vs) as [[vs' H1]|[vs' H1]]; rewrite H1; econstructor; eauto.
    + destruct (E8 mut b1 ofs1 vs) as (vs' & H1); rewrite H1; econstructor; eauto.
Qed.


Lemma fields_fp_sep_struct_fp_map: forall f fpl mass,
    (forall fid r ffp mp, In (fid, (r, ffp)) fpl ->
       sem_wt_fp ce ffp mp -> sem_wt_fp ce (f ffp) mp)->
    fields_fp_sep (sem_wt_fp ce) fpl mass ->
    fields_fp_sep (sem_wt_fp ce)
      (map (fun '(fid, (r, ffp)) => (fid, (r, f ffp))) fpl) mass.
Proof.
  intros f fpl mass PRES H.
  induction H as [mass0 EQV | fid base fofs ffp l mass1 mass2 mp IND IHIND FWT EQV]; simpl.
  - econstructor; eauto.
  - econstructor.
    + eapply IHIND. intros fid' r' ffp' mp' IN' HFFP'.
      eapply PRES. right. exact IN'. exact HFFP'.
    + eapply PRES. left. reflexivity. exact FWT.
    + exact EQV.
Qed.


Lemma sem_wt_fp_struct_fp_map: forall f fp mp,
    struct_fp_map f ->
    sem_wt_fp ce fp mp ->
    sem_wt_fp ce (f fp) mp.
Proof.
  intros f fp mp. revert mp.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros mp SM H.
  - inv H. destruct SM as (E1 & _ & _ & _ & _ & _ & _ & _). rewrite E1. econstructor; eauto.
  - inv H. destruct SM as (_ & E2 & _ & _ & _ & _ & _ & _). rewrite E2. econstructor; eauto.
  - inv H. destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _). rewrite E3. econstructor; eauto.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _).
    rewrite E4. econstructor.
    + eapply sem_wt_loc_struct_fp_map; eauto.
    + assert (BOXPREQ: box_pred ce (f fp1) b1 nextmp = box_pred ce fp1 b1 nextmp).
      { unfold box_pred. rewrite (struct_fp_map_sizeof f fp1 SM'). reflexivity. }
      rewrite BOXPREQ. exact EQV.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & E5 & _ & _ & _).
    rewrite E5. econstructor.
    + eapply fields_fp_sep_struct_fp_map.
      * intros fid' r' ffp' IN' HFFP'. destruct r' as [base' fofs'].
        eapply IHfields; eauto.
      * exact FFP.
    + exact EQV.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & _ & E6 & _ & _).
    rewrite E6. econstructor; eauto.
  - inv H. destruct SM as (_ & _ & _ & _ & _ & _ & E7 & E8).
    destruct ph0 as [ph1|].
    + destruct (E7 mut b1 ofs1 ph1 vs) as [[vs' H1]|[vs' H1]]; rewrite H1; econstructor; eauto.
    + destruct (E8 mut b1 ofs1 vs) as (vs' & H1); rewrite H1; econstructor; eauto.
Qed.


Lemma sem_wt_val_struct_fp_map: forall f fp v mp,
    struct_fp_map f ->
    sem_wt_val ce fp v mp ->
    sem_wt_val ce (f fp) v mp.
Proof.
  intros f fp v mp. revert v mp.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid fofs fp1 | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros v0 mp SM H1; inv H1.
  - pose proof SM as SM'. destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _).
    rewrite E3. econstructor; eauto.
  - pose proof SM as SM'. destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _).
    rewrite E4. econstructor. rewrite <- E4. eapply sem_wt_fp_struct_fp_map; eauto.
  - pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & _ & _ & E7 & E8).
    destruct ph0 as [ph1|].
    + destruct (E7 mut b1 ofs1 ph1 vs) as [[vs' H1]|[vs' H1]];
        rewrite H1; inv MP; econstructor; econstructor; eauto.
    + destruct (E8 mut b1 ofs1 vs) as (vs' & H1);
        rewrite H1; inv MP; econstructor; econstructor; eauto.
Qed.


Lemma fp_match_field_struct_fp_map: forall f te co fpl members,
    (forall fid r ffp fty,
       In (fid, (r, ffp)) fpl ->
       wt_footprint ce te fty ffp ->
       wt_footprint ce te fty (f ffp)) ->
    Forall2 (fp_match_field ce co (wt_footprint ce te)) fpl members ->
    Forall2 (fp_match_field ce co (wt_footprint ce te))
      (map (fun '(fid, (r, ffp)) => (fid, (r, f ffp))) fpl) members.
Proof using ge.
  intros f te co fpl members PRES MATCH.
  induction MATCH; simpl.
  - constructor.
  - constructor.
    + inv H. econstructor.
      * exact FOFS.
      * eapply PRES. left. reflexivity. exact WTFP.
    + eapply IHMATCH. intros fid' r' ffp' fty' IN' WTFP'.
      eapply PRES. right. exact IN'. exact WTFP'.
Qed.


Lemma field_idents_struct_fp_map: forall (f: footprint -> footprint)
                                          (fpl: list (ident * ((Z * Z) * footprint))),
    field_idents (map (fun '(fid, (r, ffp)) => (fid, (r, f ffp))) fpl) =
    field_idents fpl.
Proof using Type.
  intros f fpl. unfold field_idents.
  induction fpl as [|[fid [r ffp]] fpl IH]; simpl; f_equal; auto.
Qed.


Lemma wt_footprint_struct_fp_map: forall f te ty fp,
    struct_fp_map f ->
    wt_footprint ce te ty fp ->
    wt_footprint ce te ty (f fp).
Proof.
  intros f te ty fp SM. revert ty.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros ty H.
  - inv H.
  - inv H. destruct SM as (_ & E2 & _ & _ & _ & _ & _ & _). rewrite E2. econstructor; eauto.
  - inv H. destruct SM as (_ & _ & E3 & _ & _ & _ & _ & _). rewrite E3. econstructor; eauto.
  - inv H. destruct SM as (_ & _ & _ & E4 & _ & _ & _ & _). rewrite E4. econstructor; eauto.
  - inv H. pose proof SM as SM'. destruct SM as (_ & _ & _ & _ & E5 & _ & _ & _). rewrite E5. econstructor.
    + exact CO. + exact STRUCT.
    + eapply fp_match_field_struct_fp_map.
      * intros fid' r' ffp' fty' IN' WTFP'. destruct r' as [base' fofs'].
        eapply IHfields; eauto.
      * exact MATCH.
    + rewrite field_idents_struct_fp_map. exact FLAT.
  - inv H. destruct SM as (_ & _ & _ & _ & _ & E6 & _ & _). rewrite E6.
    econstructor; try reflexivity; eauto.
  - inv H; destruct SM as (_ & _ & _ & _ & _ & _ & E7 & E8).
    + destruct (E7 mut b1 ofs1 ph vs) as [[vs' H1]|[vs' H1]];
        rewrite H1; econstructor; eauto.
    + destruct (E8 mut b1 ofs1 vs) as (vs' & H1);
        rewrite H1; econstructor.
Qed.


Lemma map_fst_map_snd_f: forall (A B: Type) (g: A -> B) (l: list (positive * A)),
    map fst (map (fun '(i, x) => (i, g x)) l) = map fst l.
Proof using Type.
  intros A B g l. induction l as [|[i x] l IH]; simpl; f_equal; auto.
Qed.

Lemma PTree_elements_map1: forall (A B: Type) (g: A -> B) (m: PTree.t A),
    PTree.elements (PTree.map1 g m) =
    map (fun '(i, x) => (i, g x)) (PTree.elements m).
Proof using Type.
  intros A B g [|m]; simpl; auto.
  assert (MAP:
    forall (tr: PTree.tree' A) i k,
      PTree.xelements' (PTree.map1' g tr) i
        (map (fun '(j, x) => (j, g x)) k) =
      map (fun '(j, x) => (j, g x)) (PTree.xelements' tr i k)).
  { intros tr. induction tr; intros; simpl.
    - apply IHtr.
    - reflexivity.
    - f_equal. apply IHtr.
    - apply IHtr.
    - rewrite IHtr2. apply IHtr1.
    - change ((PTree.prev i, g a) :: map (fun '(j, x) => (j, g x)) k)
        with (map (fun '(j, x) => (j, g x)) ((PTree.prev i, a) :: k)).
      apply IHtr.
    - rewrite IHtr2.
      change ((PTree.prev i, g a) ::
                map (fun '(j, x) => (j, g x))
                  (PTree.xelements' tr2 i~1 k))
        with (map (fun '(j, x) => (j, g x))
                ((PTree.prev i, a) :: PTree.xelements' tr2 i~1 k)).
      apply IHtr1. }
  specialize (MAP m xH nil). simpl in MAP. exact MAP.
Qed.


Lemma Forall_sep_coherent_var_struct_fp_map: forall f l mass,
    struct_fp_map f ->
    Forall_sep (coherent_var ce) l mass ->
    Forall_sep (coherent_var ce)
      (map (fun '(id, entry) =>
              (id, (fun '(b, ofs, ty, fp0) => (b, ofs, ty, f fp0)) entry)) l) mass.
Proof.
  intros f l mass SM H.
  induction H as [mass0 EQV | x l1 mass1 mass2 mass3 HEAD IH TAIL EQV]; simpl.
  - econstructor; eauto.
  - inv HEAD. econstructor.
    + econstructor.
      * reflexivity.
      * eapply sem_wt_loc_struct_fp_map; eauto.
    + exact TAIL.
    + exact EQV.
Qed.


Lemma coherent_fpm_struct_fp_map: forall f fpm mp,
    struct_fp_map f ->
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (PTree.map1 (fun '(b, ofs, ty, fp0) => (b, ofs, ty, f fp0)) fpm) mp.
Proof.
  intros f fpm mp SM COH.
  inv COH.
  econstructor.
  rewrite PTree_elements_map1.
  eapply Forall_sep_coherent_var_struct_fp_map; eauto.
Qed.


(** Specific traversal lemma for invalidate_conflict_ref, used by
    check_path_is_dropped preservation. *)

Lemma get_owner_footprint_invalidate_eq: forall phl ph ak am fp,
    get_owner_footprint phl (invalidate_conflict_ref ph ak am fp) =
    match get_owner_footprint phl fp with
    | OK fp' => OK (invalidate_conflict_ref ph ak am fp')
    | Error e => Error e
    end.
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros.
  - reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph0 vs];
      cbn [invalidate_conflict_ref get_owner_footprint];
      try reflexivity.
    + rewrite (IH ph ak am fp1). reflexivity.
    + rewrite find_field_invalidate_conflict_ref.
      destruct (find_field fid1 fpl) as [[[base fofs] ffp]|] eqn:FIND;
        cbn; try reflexivity.
      rewrite (IH ph ak am ffp). reflexivity.
    + destruct (ident_eq fid1 fid2); cbn; try reflexivity.
      rewrite (IH ph ak am fp1). reflexivity.
Qed.

Lemma get_owner_footprint_map_invalidate_eq: forall ph ak am ps fpm,
    get_owner_footprint_map ps (invalidate_conflict_ref_fpm ph ak am fpm) =
    match get_owner_footprint_map ps fpm with
    | OK fp => OK (invalidate_conflict_ref ph ak am fp)
    | Error e => Error e
    end.
Proof using Type.
  intros ph ak am [id phl] fpm.
  unfold get_owner_footprint_map, invalidate_conflict_ref_fpm. simpl.
  rewrite PTree.gmap1.
  destruct (fpm ! id) as [entry|]; simpl; auto.
  destruct entry as [[[b ofs] ty] fp0]; simpl.
  rewrite get_owner_footprint_invalidate_eq. reflexivity.
Qed.


(** Reverse preservation of mutable_path, reachability, and views
    adequacy/precision under invalidate_conflict_ref, used to prove
    fp_ref_loc_wf preservation. *)

Lemma mutable_path_footprint_after_invalidate_ref: forall phl fpm ak am ph fp b,
    mutable_path_footprint (invalidate_conflict_ref_fpm ph ak am fpm)
      phl (invalidate_conflict_ref ph ak am fp) = OK b ->
    mutable_path_footprint fpm phl fp = OK b.
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros fpm ak am ph fp b H.
  - inv H. reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph0 vs];
      simpl in H; try congruence.
    + eapply IH; eauto.
    + destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs) eqn:C;
        simpl in H; try congruence.
      destruct ph0 as [ph2|]; [| congruence].
      destruct mut.
      * destruct (get_owner_footprint_map ph2 (invalidate_conflict_ref_fpm ph ak am fpm))
          as [fp1|err] eqn:GET; simpl in H; try congruence.
        exploit get_owner_footprint_map_after_invalidate_ref; eauto.
        intros (fp2 & GET_ORIGINAL & INVALID).
        rewrite GET_ORIGINAL. simpl.
        rewrite <- INVALID in H. eapply IH; eauto.
      * inv H. reflexivity.
    + rewrite find_field_invalidate_conflict_ref in H.
      destruct (find_field fid1 fpl) as [[[base fofs] ffp]|] eqn:FIND;
        simpl in H; try congruence.
      eapply IH; eauto.
    + destruct (ident_eq fid1 fid2); simpl in H; try congruence.
      eapply IH; eauto.
Qed.


Lemma mutable_path_after_invalidate_ref: forall ph1 ph2 ak am fpm b,
    mutable_path ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK b ->
    mutable_path ph1 fpm = OK b.
Proof using Type.
  intros [id phl] ph2 ak am fpm b H.
  unfold mutable_path in *. simpl in *.
  unfold invalidate_conflict_ref_fpm in H.
  rewrite PTree.gmap1 in H.
  destruct (fpm ! id) as [entry|] eqn:FPM; simpl in H; try congruence.
  destruct entry as [[[b0 ofs] ty] fp0]; simpl in H.
  eapply mutable_path_footprint_after_invalidate_ref; eauto.
Qed.


Lemma reachable_from_dominators_after_invalidate_ref: forall ph2 ak am fpm ph1 tgt,
    reachable_from_dominators (invalidate_conflict_ref_fpm ph2 ak am fpm) ph1 tgt ->
    reachable_from_dominators fpm ph1 tgt.
Proof using Type.
  intros ph2 ak am fpm ph1 tgt H.
  inv H. econstructor; eauto.
  eapply get_owner_path_map_after_invalidate_ref; eauto.
Qed.


Lemma fp_ref_views_adequate_after_invalidate_ref: forall ph2 ak am fpm ph vs,
    fp_ref_views_adequate fpm ph vs ->
    fp_ref_views_adequate (invalidate_conflict_ref_fpm ph2 ak am fpm) ph vs.
Proof using Type.
  intros ph2 ak am fpm ph vs ADEQ.
  unfold fp_ref_views_adequate in *. intros ph1 REACH MUT.
  eapply ADEQ.
  - eapply reachable_from_dominators_after_invalidate_ref; eauto.
  - eapply mutable_path_after_invalidate_ref; eauto.
Qed.


Lemma mutable_path_footprint_invalidate_lockstep: forall phl fpm current aliases fp ph ak am tgt vs b,
    get_owner_path (invalidate_conflict_ref_fpm ph ak am fpm)
      current phl (invalidate_conflict_ref ph ak am fp) aliases = OK (tgt, vs) ->
    mutable_path_footprint fpm phl fp = OK b ->
    mutable_path_footprint (invalidate_conflict_ref_fpm ph ak am fpm)
      phl (invalidate_conflict_ref ph ak am fp) = OK b.
Proof using Type.
  induction phl as [|pj phl IH]; simpl; intros fpm current aliases fp ph ak am tgt vs b HGET HMUT.
  - inv HMUT. reflexivity.
  - destruct pj as [| fid1 | fid1];
      destruct fp as [esz eal | sz al | chunk v | b1 fp1 | id fpl | id tagz fid2 fofs fp1 | mut b2 ofs1 ph0 vs0];
      simpl in *; try congruence.
    + eapply IH; eauto.
    + destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs0) eqn:C;
        simpl in *; try congruence.
      destruct ph0 as [ph2|]; [| congruence].
      destruct mut.
      * destruct (get_owner_footprint_map ph2 (invalidate_conflict_ref_fpm ph ak am fpm))
          as [fp1|err] eqn:GET1; simpl in HGET; try congruence.
        destruct (get_owner_footprint_map ph2 fpm) as [fp2|err] eqn:GET2;
          simpl in HMUT; try congruence.
        exploit get_owner_footprint_map_after_invalidate_ref; eauto.
        intros (fp2' & GET_ORIGINAL & INVALID).
        rewrite GET2 in GET_ORIGINAL. inv GET_ORIGINAL.
        eapply IH; eauto.
      * inv HMUT. reflexivity.
    + rewrite find_field_invalidate_conflict_ref in HGET.
      destruct (find_field fid1 fpl) as [[[base fofs] ffp]|] eqn:FIND;
        simpl in *; try congruence.
      rewrite find_field_invalidate_conflict_ref, FIND. simpl.
      eapply IH; eauto.
    + destruct (ident_eq fid1 fid2); simpl in *; try congruence.
      eapply IH; eauto.
Qed.


Lemma mutable_path_after_invalidate_ref_cond: forall ph1 ph2 ak am fpm tgt vs b,
    get_owner_path_map ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK (tgt, vs) ->
    mutable_path ph1 fpm = OK b ->
    mutable_path ph1 (invalidate_conflict_ref_fpm ph2 ak am fpm) = OK b.
Proof using Type.
  intros [id phl] ph2 ak am fpm tgt vs b GET MUT.
  unfold mutable_path, get_owner_path_map in *. simpl in *.
  unfold invalidate_conflict_ref_fpm in *.
  rewrite PTree.gmap1 in *.
  destruct (fpm ! id) as [entry|] eqn:FPM; simpl in *; try congruence.
  destruct entry as [[[b0 ofs] ty] fp0]; simpl in *.
  eapply mutable_path_footprint_invalidate_lockstep; eauto.
Qed.


Lemma fp_ref_views_precise_after_invalidate_ref: forall ph2 ak am fpm ph vs,
    fp_ref_views_precise fpm ph vs ->
    fp_ref_views_precise (invalidate_conflict_ref_fpm ph2 ak am fpm) ph vs.
Proof using Type.
  intros ph2 ak am fpm ph vs PREC.
  unfold fp_ref_views_precise in *. intros ph1 tgt1 vs1 IN GET.
  destruct (PREC ph1 tgt1 vs1 IN) as (EQ1 & MUT1).
  - eapply get_owner_path_map_after_invalidate_ref; eauto.
  - split; auto.
    eapply mutable_path_after_invalidate_ref_cond; eauto.
Qed.


Lemma Forall_fp_ref_loc_wf_field_invalidate: forall ph ak am fpm fpl,
    (forall fid r ffp, In (fid, (r, ffp)) fpl ->
       fp_ref_loc_wf fpm ffp ->
       fp_ref_loc_wf (invalidate_conflict_ref_fpm ph ak am fpm)
                     (invalidate_conflict_ref ph ak am ffp)) ->
    Forall (fp_ref_loc_wf_field (fp_ref_loc_wf fpm)) fpl ->
    Forall (fp_ref_loc_wf_field (fp_ref_loc_wf (invalidate_conflict_ref_fpm ph ak am fpm)))
      (map (fun '(fid, (r, ffp)) => (fid, (r, invalidate_conflict_ref ph ak am ffp))) fpl).
Proof using Type.
  intros ph ak am fpm fpl PRES H.
  induction H as [| x l WF TAIL IH]; simpl.
  - constructor.
  - constructor.
    + inv WF. econstructor. eapply PRES. left. reflexivity. exact WF_FIELD.
    + eapply IH. intros fid' r' ffp' IN' HFFP'.
      eapply PRES. right. exact IN'. exact HFFP'.
Qed.


Lemma invalidate_conflict_ref_fp_ref_loc_wf: forall ph ak am fpm fp,
    fp_ref_loc_wf fpm fp ->
    fp_ref_loc_wf (invalidate_conflict_ref_fpm ph ak am fpm)
                  (invalidate_conflict_ref ph ak am fp).
Proof using Type.
  intros ph ak am fpm fp.
  induction fp as [esz eal | sz al | chunk v | b1 fp1 IHbox | id fpl IHfields | id tagz fid fofs fp1 IHenum | mut b1 ofs1 ph0 vs] using strong_footprint_ind;
    intros H.
  - inv H.
  - inv H. simpl. constructor.
  - inv H. simpl. constructor.
  - inv H.
  - inv H. simpl. constructor.
    eapply Forall_fp_ref_loc_wf_field_invalidate.
    * intros fid' r' ffp' IN' HFFP'. destruct r' as [base' fofs'].
      eapply IHfields; eauto.
    * exact MATCH.
  - inv H. simpl. constructor. eapply IHenum; eauto.
  - inv H; simpl.
    + destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs) eqn:C; simpl.
      * constructor.
      * eapply fp_ref_some_wf.
        -- eapply struct_fp_map_get_owner_loc_footprint_map.
           ++ eapply invalidate_conflict_ref_struct_fp_map.
           ++ exact GLOC.
        -- eapply fp_ref_views_adequate_after_invalidate_ref; eauto.
        -- eapply fp_ref_views_precise_after_invalidate_ref; eauto.
    + destruct (BorrowCheckDomain.conflict_access ak mut && conflict_view ph am vs) eqn:C; simpl; constructor.
Qed.


Lemma invalidate_conflict_ref_fpm_env_eq: forall (ph: path) (fpm: fp_map) ak am,
    (fpm_to_env fpm) = (fpm_to_env (invalidate_conflict_ref_fpm ph ak am fpm)).
Proof using Type.
  intros ph fpm ak am.
  unfold fpm_to_env, invalidate_conflict_ref_fpm.
  eapply PTree.extensionality. intros key.
  rewrite ! PTree.gmap_filter1. rewrite PTree.gmap1.
  destruct (fpm ! key) as [entry|]; simpl; auto.
  destruct entry as [[[b ofs] ty] fp0]; simpl; reflexivity.
Qed.

Lemma invalidate_conflict_ref_fpm_tenv_eq: forall (ph: path) (fpm: fp_map) ak am,
    (fpm_to_tenv fpm) = (fpm_to_tenv (invalidate_conflict_ref_fpm ph ak am fpm)).
Proof using Type.
  intros ph fpm ak am.
  unfold fpm_to_tenv, invalidate_conflict_ref_fpm.
  eapply PTree.extensionality. intros key.
  rewrite ! PTree.gmap1.
  destruct (fpm ! key) as [entry|]; simpl; auto.
  destruct entry as [[[b ofs] ty] fp0]; simpl; reflexivity.
Qed.


Lemma invalidate_conflict_ref_fpm_coherent_unchanged: forall (ph: path) (fpm: fp_map) ak am mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (invalidate_conflict_ref_fpm ph ak am fpm) mp.
Proof.
  intros. eapply coherent_fpm_struct_fp_map.
  - eapply invalidate_conflict_ref_struct_fp_map.
  - exact H.
Qed.

Lemma invalidate_conflict_ref_fpm_wt_fpm_unchanged: forall (ph: path) (fpm: fp_map) ak am,
    wt_fpm ce fpm ->
    wt_fpm ce (invalidate_conflict_ref_fpm ph ak am fpm).
Proof.
  intros ph fpm ak am WTFPM.
  unfold wt_fpm in *. intros id0 b ofs ty fp' GET'.
  unfold invalidate_conflict_ref_fpm in GET'.
  rewrite PTree.gmap1 in GET'.
  destruct (fpm ! id0) as [entry|] eqn:FPM; simpl in GET'; try congruence.
  destruct entry as [[[b0 ofs0] ty0] fp0]; simpl in GET'.
  inv GET'.
  rewrite <- (invalidate_conflict_ref_fpm_tenv_eq ph fpm ak am).
  eapply wt_footprint_struct_fp_map.
  - eapply invalidate_conflict_ref_struct_fp_map.
  - eapply WTFPM; eauto.
Qed.

Lemma invalidate_conflict_ref_fpm_fp_ref_wf_unchanged: forall (ph: path) (fpm: fp_map) ak am,
    fp_ref_loc_wf_fpm fpm ->
    fp_ref_loc_wf_fpm (invalidate_conflict_ref_fpm ph ak am fpm).
Proof.
  intros ph fpm ak am WF_FPM.
  unfold fp_ref_loc_wf_fpm in *. intros id0 b ofs ty fp' GET'.
  unfold invalidate_conflict_ref_fpm in GET'.
  rewrite PTree.gmap1 in GET'.
  destruct (fpm ! id0) as [entry|] eqn:FPM; simpl in GET'; try congruence.
  destruct entry as [[[b0 ofs0] ty0] fp0]; simpl in GET'.
  inv GET'.
  eapply invalidate_conflict_ref_fp_ref_loc_wf.
  eapply WF_FPM; eauto.
Qed.


Lemma invalidate_conflict_ref_fpm_wt_footprint_unchanged: forall (ph: path) (fpm: fp_map) ak am ty (fp: footprint),
    wt_footprint ce (fpm_to_tenv fpm) ty fp ->
    wt_footprint ce (fpm_to_tenv (invalidate_conflict_ref_fpm ph ak am fpm)) ty fp.
Proof using Type.
  intros ph fpm ak am ty fp H.
  rewrite (invalidate_conflict_ref_fpm_tenv_eq ph fpm ak am) in H.
  exact H.
Qed.


Lemma invalidate_conflict_ref_fpm_wt_place_unchanged: forall (ph: path) (fpm: fp_map) ak am p,
    wt_place fpm ce p ->
    wt_place (invalidate_conflict_ref_fpm ph ak am fpm) ce p.
Proof using Type.
  intros ph fpm ak am p H.
  change (wt_place (fpm_to_env fpm) ce p) in H.
  change (wt_place (fpm_to_env
    (invalidate_conflict_ref_fpm ph ak am fpm)) ce p).
  rewrite <- (invalidate_conflict_ref_fpm_env_eq ph fpm ak am).
  exact H.
Qed.


Lemma invalidate_conflict_ref_sem_wt_val_eq: forall ph (fp: footprint) v ak am mp,
    sem_wt_val ce fp v mp ->
    sem_wt_val ce (invalidate_conflict_ref ph ak am fp) v mp.
Proof.
  intros. eapply sem_wt_val_struct_fp_map.
  - eapply invalidate_conflict_ref_struct_fp_map.
  - exact H.
Qed.

Lemma invalidate_conflict_ref_fpm_coherent_eq: forall (ph: path) (fpm: fp_map) ak am mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (invalidate_conflict_ref_fpm ph ak am fpm) mp.
Proof using Type.
  intros. eapply invalidate_conflict_ref_fpm_coherent_unchanged; eauto.
Qed.

Lemma invalidate_conflict_ref_fpm_check_path_is_dropped: forall phl id ak am (fpm: fp_map) ph,
    check_path_is_dropped fpm ph = 
    check_path_is_dropped (invalidate_conflict_ref_fpm (id, phl) ak am fpm) ph.
Proof using Type.
  intros phl id ak am fpm [pid phl'].
  unfold check_path_is_dropped.
  destruct (get_owner_footprint_map (pid, phl') fpm) as [fp0|err] eqn:GET.
  - rewrite (get_owner_footprint_map_invalidate_eq (id, phl) ak am (pid, phl') fpm).
    rewrite GET. simpl.
    rewrite (struct_fp_map_fp_is_dropped (invalidate_conflict_ref (id, phl) ak am) fp0).
    + reflexivity.
    + apply invalidate_conflict_ref_struct_fp_map.
  - rewrite (get_owner_footprint_map_invalidate_eq (id, phl) ak am (pid, phl') fpm).
    rewrite GET. reflexivity.
Qed.

Lemma kill_paths_ref_sem_wt_val: forall v (fp: footprint) vs mp,
    sem_wt_val ce fp v mp ->
    sem_wt_val ce (kill_views_ref vs fp) v mp.
Proof.
  intros. eapply sem_wt_val_struct_fp_map.
  - apply kill_views_ref_struct_fp_map.
  - exact H.
Qed.


Lemma kill_paths_ref_coherent_fpm: forall (fpm: fp_map) vs mp,
    coherent_fpm ce fpm mp ->
    coherent_fpm ce (kill_views_ref_fpm vs fpm) mp.
Proof.
  intros. eapply coherent_fpm_struct_fp_map.
  - apply kill_views_ref_struct_fp_map.
  - exact H.
Qed.


End FRAME.

Hint Resolve 
  invalidate_conflict_ref_fpm_wt_place_unchanged 
  invalidate_conflict_ref_fpm_wt_footprint_unchanged
  invalidate_conflict_ref_fpm_coherent_unchanged
  invalidate_conflict_ref_fpm_wt_fpm_unchanged
  invalidate_conflict_ref_fpm_env_eq
  invalidate_conflict_ref_fpm_tenv_eq
  invalidate_conflict_ref_sem_wt_val_eq
  invalidate_conflict_ref_fpm_coherent_eq
  invalidate_conflict_ref_fpm_check_path_is_dropped
  invalidate_conflict_ref_fpm_fp_ref_wf_unchanged: invalidate_fp_ref.

Hint Resolve 
  kill_paths_ref_sem_wt_val
  kill_paths_ref_coherent_fpm : kill_paths_ref.

Lemma eval_expr_match_by_value frame: forall (e: expr) vfp (fpm1 fpm2: fp_map) m MP1 FMP 
    (COH: coherent_fpm ce fpm1 MP1)
    (MPRED: m |= MP1 ** FMP)
    (WTEXPR: wt_expr fpm1 ce e)
    (WTFPM: wt_fpm ce fpm1)
    (REF_WF: fp_ref_loc_wf_fpm fpm1)
    (EVAL: eval_expr frame ce fpm1 e = OK (vfp, fpm2))
    (BYVAL: access_by_value (typeof e) = true),
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
    set (fpm1' := (invalidate_conflict_ref_fpm
      (enc_path frame p) AWrite BorrowCheckDomain.Adeep fpm1)) in *.
    destr_path_of_place p.
    eapply invalidate_conflict_ref_fpm_coherent_unchanged in COH as COH1.
    exploit get_owner_path_for_owner; eauto. 
    eapply get_owner_loc_footprint_map_eq; eauto. intros GPH.
    exploit (get_owner_path_map_eval_place); eauto. eapply MPRED.
    1-4: eauto with invalidate_fp_ref. rewrite POP. eapply GPH.    
    intros (b1 & ofs1 & fp & A1 & A2).    
    unfold fpm1' in *.
    setoid_rewrite A1 in EQ. inv EQ.
    (* Because we need to read the contents in the location of p, we
    use this lemma. *)
    exploit get_owner_loc_footprint_map_sem_wt_split; eauto.
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

(* We only allow moving composite for now and do not allow copying
them in pure expression *)
Lemma eval_Emoveplace_by_copy frame: forall (e: expr) vfp (fpm1 fpm2: fp_map) m MP1 FMP 
    (COH: coherent_fpm ce fpm1 MP1)
    (MPRED: m |= MP1 ** FMP)
    (WTEXPR: wt_expr fpm1 ce e)
    (WTFPM: wt_fpm ce fpm1)
    (REF_WF: fp_ref_loc_wf_fpm fpm1)
    (EVAL: eval_expr frame ce fpm1 e = OK (vfp, fpm2))
    (BYCOPY: access_mode (typeof e) = Ctypes.By_copy), 
    exists b ofs mp1 mp2 mp3 mp4,
      Rustlightown.eval_expr ce fpm1 m tge e (Vptr b (Ptrofs.repr ofs))
      /\ sem_wt_fp ce vfp mp1
      /\ coherent_fpm ce fpm2 mp2
      /\ sem_wt_loc ce vfp b ofs mp4
      (* mp3 can be seen as the information we lost when we clear the
      footprint in the location of p *)
      /\ massert_imp (mp1 ** mp2 ** mp3) mp4
      /\ m |= mp1 ** mp2 ** mp3 ** FMP.
Proof.  
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
      | [H1 : context G [before_write_place _ _ _ _ = OK (?a, ?b)] |- _ ] =>
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


(* ===================================================================
   Per-step-case simulation lemmas.
   Each RustIRspec.step constructor is proved in its own lemma; the
   dispatcher step_simulation below just dispatches to them.
   =================================================================== *)

Lemma step_assign_simulation:
  forall f e (p: place) vfp fpm1 fpm2 fpm3 ph k sup fidx (s1': state),
    eval_assign ge fidx fpm1 p e = OK (ph, vfp, fpm2) ->
    set_footprint_map ph vfp fpm2 = OK fpm3 ->
    match_states (RustIRspec.State f (Sassign p e) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sassign p e) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sassign p e) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm3 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm3 fidx sup).
Proof.
  intros f e p vfp fpm1 fpm2 fpm3 ph k sup fidx s1' EVAL ASS MATCH BORINV WTST.
  inv MATCH; inv BORINV; inv WTST.
  inv WT1.
    unfold_eval_assign. inv EQ2.
    unfold_before_write_place.        
    destr_path_of_place p.
    (* evaluate expr *)
    exploit eval_expr_match_by_value. eauto. eapply MPRED. 
    (* wt_expr *) eapply WT3.
    (* wt_fpm: we should add a new state invariant *) admit.
    eapply BOR_INV.
    eauto.
    (** TODO: we need to consider that we may access e by copying its
    content from its location. *)
    admit.
    intros (tv & mp1 & mp2 & TEVAL & WTVAL & COH1 & MPRED1).
    (* evaluate expr preserves borrow check invariant. We should write
    it in a separated lemma *)
    exploit eval_expr_preserve_borchk_inv; eauto.
    intros BORCK_INV1.  (* & WTFPM1 & WTFP1). *)    
    (* shallow write preserves borrow check invariant *)
    exploit borrow_check_inv_shallow_write; eauto.
    (* econstructor. eauto. econstructor. *)
    intros BORCK_INV2.  (* & WTFP2 & WTFPM2). *)
    (* set footprint to the assginee preserves the invariant *)
    simpl in BORCK_INV2.
    exploit borrow_check_inv_set_fp; eauto.
    eapply kill_views_ref_fpm_preserve_is_dropped; eauto.
    eapply clear_footprint_map_is_dropped; eauto.
    (** Broken here: TODO *)
    intros BORCK_INV3. (* & WTFP3 & WTFPM3). *)
    (* derive the memory predicate before setting the footprint into
    fpm *)
    (* erewrite <-invalidate_conflict_ref_fpm_check_path_is_dropped in EQ1; eauto. *)
    (* intros ISDROP1.     *)
    exploit clear_is_dropped_fp_map_coherent. eauto. eapply EQ2.
    eapply invalidate_conflict_ref_fpm_coherent_eq. eauto.
    intros (mp2' & COH2 & MPIMP1).
    exploit (kill_paths_ref_coherent_fpm x3 vs). eapply COH2. 
    intros COH3.
    (* derive the predicate for the value *)
    exploit (invalidate_conflict_ref_sem_wt_val_eq (enc_path fidx (pid, phl)) x tv AWrite BorrowCheckDomain.Ashallow); eauto.
    intros WTVAL1.
    exploit kill_paths_ref_sem_wt_val; eauto. 
    instantiate (1 := vs). intros WTVAL2.
    (* evaluate the address of the assignee *)
    exploit (get_owner_path_map_eval_place fidx p).
    eapply COH1. eapply MPRED1. 
    (* wt_fpm ce x0: we should prove a wt_footprint/wt_fpm
    preservation leamm *) admit.
    (* wt_place *) admit.
    eapply BORCK_INV1.
    rewrite POP. 
    eapply get_owner_path_map_after_invalidate_ref. eapply EQ0.
    intros (b & ofs & pfp & GPLOC & EVALP).
    (** TODO: prove that invalidate_fp_ref, kill_views_ref_fpm and
    clear_footprint_map in [ph] does not change the location of [ph] *)
    assert (GPLOC1: get_owner_loc_footprint_map  (tgt_id, tgt_phl)  (kill_views_ref_fpm vs x3) = OK (b, ofs, clear_footprint_rec ce pfp)) by admit.
    assert (MPRED3: m |= mp2' ** mp1 ** FMP) by admit.
    (** FIXME: consider by_copy access *)
    assert (BYVAL: exists chunk, access_mode (typeof_place p) = Ctypes.By_value chunk) by admit.
    destruct BYVAL as (chunk & BYVAL).    
    (* inv WTFP2. inv H4. *)
    (* assign_loc *)
    exploit get_owner_loc_footprint_map_wt; eauto.
    instantiate (1 := ce).
    (* wt_fpm: we should prove a wt_footprint/wt_fpm
    preservation leamm *) admit.
    intros (ty & WTPH1 & WTFP4 & AL).
    exploit assign_loc_by_value_coherent_fpm. eauto. eauto. eapply COH3.
    eapply WTVAL2. eauto.
    eapply GPLOC1. eauto. eauto. 
    (** lots of work need to be done to prove ty = typeof e = typeof p
    where '=' represent type_eq_except_origins because the
    get_owner_path_map p is performed on x0 instead of the fp_map
    after invalidation and kill_paths and clear_footprint. *)
    admit. instantiate (1 := chunk). admit.
    admit. 
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
      (* eapply borrow_check_fpg_vals_inv_empty. eauto. *)
      admit.
Admitted.

Lemma step_assign_variant_simulation:
  forall f e (p: place) k fpm1 fpm2 fpm3 vfp co fid enum_id orgs ph fty fidx sup fofs tag (s1': state),
    eval_assign ge fidx fpm1 p e = OK (ph, vfp, fpm2) ->
    typeof_place p = Tvariant orgs enum_id ->
    ge.(genv_cenv) ! enum_id = Some co ->
    field_type fid co.(co_members) = OK fty ->
    field_tag fid co.(co_members) = Some tag ->
    variant_field_offset ge fid co.(co_members) = OK fofs ->
    set_footprint_map ph (fp_enum enum_id tag fid fofs vfp) fpm2 = OK fpm3 ->
    match_states (RustIRspec.State f (Sassign_variant p enum_id fid e) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sassign_variant p enum_id fid e) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sassign_variant p enum_id fid e) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm3 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm3 fidx sup).
Proof. Admitted.

Lemma step_box_simulation:
  forall f e (p: place) k ty fpm1 fpm2 fpm3 vfp ph fidx sup (s1': state),
    eval_assign ge fidx fpm1 p e = OK (ph, vfp, fpm2) ->
    typeof_place p = Tbox ty ->
    set_footprint_map ph (fp_box (Mem.fresh_block sup) vfp) fpm2 = OK fpm3 ->
    match_states (RustIRspec.State f (Sbox p e) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sbox p e) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sbox p e) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm3 fidx (Mem.sup_incr sup)) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm3 fidx (Mem.sup_incr sup)).
Proof. Admitted.

Lemma step_drop_simulation:
  forall fpm1 fpm2 fpm3 k f (p: place) fidx sup (s1': state),
    invalidate_conflict_ref_fpm (enc_path fidx p) AWrite BorrowCheckDomain.Adeep fpm1 = fpm2 ->
    check_path_is_droppable fpm2 (enc_path fidx p) = OK true ->
    clear_footprint_map ge (enc_path fidx p) fpm2 = OK fpm3 ->
    match_states (RustIRspec.State f (Sdrop p) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sdrop p) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sdrop p) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm3 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm3 fidx sup).
Proof.
  intros fpm1 fpm2 fpm3 k f p fidx sup s1' INVP DEEP_INIT DROP MATCH BORINV WTST.
  inv MATCH; inv BORINV; inv WTST.
  inv WT1.
    destr_path_of_place p.
    unfold check_path_is_droppable in DEEP_INIT.
    monadInv DEEP_INIT.
    (* preserve borrow check invariant *)
    exploit get_owner_footprint_map_loc; eauto.
    intros (b & ofs & GLOC).
    exploit borrow_check_inv_move; eauto.
    instantiate (1 := nil).  admit.
    (* econstructor. instantiate (1 := typeof p). admit. (* wt_place *)
    implies wt_path *)
    intros BOR_INV1. (* & WTFP1 & WTFPM1). *)
    exploit borrow_check_inv_drop; eauto.
    instantiate (1 := O). simpl.
    intros BOR_INV2. (* & WTFP2 & WTFPM2). *)
    (* eapply borrow_check_fpg_vals_inv_empty in BOR_INV2. *)
    (* Use type information to do case analysis *)
    assert (WTFPM1: wt_fpm ce (invalidate_conflict_ref_fpm (enc_path fidx (pid, phl))
            AWrite BorrowCheckDomain.Adeep fpm1)) by admit.
    assert (DROP_TY: drop_type (typeof_place p) = true) by admit. (* It should be ensured by the syntatic type checking *)
    exploit get_owner_loc_footprint_map_wt; eauto.
    intros (pty & WTPH & WTFP & AL).
    replace pty with (typeof_place p) in * by admit. (* wt_path and wt_place properties *)
    (* memory predicate after deep access *)
    exploit (invalidate_conflict_ref_fpm_coherent_eq (enc_path fidx (pid, phl)) fpm1 AWrite BorrowCheckDomain.Adeep); eauto.
    intros COH1.
    (* eval_place *)
    exploit (get_owner_path_map_eval_place); eauto. eapply MPRED.
    change (genv_cenv (globalenv se prog)) with ce in *.
    eapply invalidate_conflict_ref_fpm_wt_place_unchanged; eauto.
    eauto with invalidate_fp_ref.
    1-3: eauto with invalidate_fp_ref. 
    eapply invalidate_conflict_ref_fpm_fp_ref_wf_unchanged. eapply BOR_INV.
    eapply get_owner_path_for_owner.
    eapply get_owner_loc_footprint_map_eq. rewrite POP. eapply GLOC.
    rewrite POP.
    intros (b1 & ofs1 & fp1 & A1 & A2).    
    setoid_rewrite GLOC in A1. inv A1.
    destruct (typeof_place p) eqn: PTY; simpl in DROP_TY; try congruence.
    (* Tbox *)
    + inv WTFP; try congruence.
        (* fp_uninit is impossible. It should be ruled out by Drop
         elaboration *)
      (* specific to drop(Box): evaluate the address of dropped memory
      location *)
      exploit get_owner_loc_footprint_map_sem_wt_split; eauto.
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
      assert (FREE: exists m1, extcall_free_sem tge [Vptr b Ptrofs.zero] m E0 Vundef m1).
      { unfold box_pred in *.
        (* range_perm of fp *)
        exploit sem_wt_loc_range_perm.
        admit. admit. eapply WT. admit. eauto.
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
        assert (RANGE_PRED: m |= range b (- size_chunk Mptr) (sizeof ce t) ** mp3 ** FMP).
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
        admit.
    (* drop struct *)
    + admit.
    (* drop enum *)
    + admit.

Admitted.

Lemma step_storagelive_simulation:
  forall f k fidx fpm id sup (s1': state),
    match_states (RustIRspec.State f (Sstoragelive id) k fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sstoragelive id) k fpm fidx sup) ->
    wt_state (RustIRspec.State f (Sstoragelive id) k fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm fidx sup).
Proof. Admitted.

Lemma step_storagedead_simulation:
  forall f k fidx fpm1 fpm2 id sup (s1': state),
    check_path_is_dropped fpm1 (enc_path fidx (id, nil)) = OK true ->
    clear_footprint_map ge (enc_path fidx (id, nil)) fpm1 = OK fpm2 ->
    match_states (RustIRspec.State f (Sstoragedead id) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sstoragedead id) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sstoragedead id) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm2 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm2 fidx sup).
Proof. Admitted.

Lemma step_call_simulation:
  forall f ty al k tyargs fd cconv tyres p orgs org_rels fun_id fpm1 fpm2 args fidx sup (s1': state),
    classify_fun ty = fun_case_f tyargs tyres cconv ->
    ge.(genv_defmap) ! fun_id = Some (Gfun fd) ->
    type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv ->
    eval_exprlist fidx ge fpm1 al = OK (args, fpm2) ->
    function_not_drop_glue fd ->
    match_states (RustIRspec.State f (Scall p (Eglobal fun_id ty) al) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Scall p (Eglobal fun_id ty) al) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Scall p (Eglobal fun_id ty) al) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.Callstate fun_id args fpm2 fidx sup (RustIRspec.Kcall p f k)) s2'
      /\ borrowck_inv (RustIRspec.Callstate fun_id args fpm2 fidx sup (RustIRspec.Kcall p f k)).
Proof. Admitted.

Lemma step_internal_function_simulation:
  forall fun_id vargs k fpm1 fpm2 f fidx sup1 sup2 (s1': state),
    ge.(genv_defmap) ! fun_id = Some (Gfun (Internal f)) ->
    f.(fn_drop_glue) = None ->
    RustIRspec.function_entry ge f vargs fpm1 (fidx+1)%positive sup1 = OK (fpm2, sup2) ->
    match_states (RustIRspec.Callstate fun_id vargs fpm1 fidx sup1 k) s1' ->
    borrowck_inv (RustIRspec.Callstate fun_id vargs fpm1 fidx sup1 k) ->
    wt_state (RustIRspec.Callstate fun_id vargs fpm1 fidx sup1 k) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f f.(fn_body) k fpm2 (fidx+1)%positive sup2) s2'
      /\ borrowck_inv (RustIRspec.State f f.(fn_body) k fpm2 (fidx+1)%positive sup2).
Proof. Admitted.

Lemma step_return_1_simulation:
  forall p vfp vfp1 vfp2 fpm1 fpm2 fpm3 fpm4 fpm5 f (k ck: RustIRspec.cont) fidx out_params sup (s1': state),
    RustIRspec.call_cont k = Some ck ->
    eval_expr fidx ge fpm1 (Emoveplace p (typeof_place p)) = OK (vfp, fpm2) ->
    invalidate_conflict_ref_fpm_list (vars_to_paths fidx (f.(fn_vars) ++ f.(fn_params))) AWrite BorrowCheckDomain.Ashallow fpm2 = fpm3 ->
    kill_views_ref_fpm (vars_to_paths fidx (f.(fn_vars) ++ f.(fn_params))) fpm3 = fpm4 ->
    pop_stack fpm4 fidx (f.(fn_vars) ++ f.(fn_params)) = fpm5 ->
    kill_views_ref (vars_to_paths fidx (f.(fn_vars) ++ f.(fn_params))) vfp = vfp1 ->
    match_states (RustIRspec.State f (Sreturn p) k fpm1 fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sreturn p) k fpm1 fidx sup) ->
    wt_state (RustIRspec.State f (Sreturn p) k fpm1 fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.Returnstate vfp2 out_params (fidx-1)%positive sup ck) s2'
      /\ borrowck_inv (RustIRspec.Returnstate vfp2 out_params (fidx-1)%positive sup ck).
Proof. Admitted.

Lemma step_returnstate_simulation:
  forall p v v1 fpm1 fpm2 fpm3 f k ph fidx vs sup (s1': state),
    before_write_place ge fidx fpm1 p = OK (ph, vs, fpm2) ->
    set_footprint_map ph (kill_views_ref vs v1) fpm2 = OK fpm3 ->
    match_states (RustIRspec.Returnstate v fpm1 fidx sup (RustIRspec.Kcall p f k)) s1' ->
    borrowck_inv (RustIRspec.Returnstate v fpm1 fidx sup (RustIRspec.Kcall p f k)) ->
    wt_state (RustIRspec.Returnstate v fpm1 fidx sup (RustIRspec.Kcall p f k)) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm3 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm3 fidx sup).
Proof. Admitted.

Lemma step_seq_simulation:
  forall f s1 s2 k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f (Ssequence s1 s2) k fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Ssequence s1 s2) k fpm fidx sup) ->
    wt_state (RustIRspec.State f (Ssequence s1 s2) k fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f s1 (RustIRspec.Kseq s2 k) fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f s1 (RustIRspec.Kseq s2 k) fpm fidx sup).
Proof. Admitted.

Lemma step_skip_seq_simulation:
  forall f s k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f Sskip (RustIRspec.Kseq s k) fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f Sskip (RustIRspec.Kseq s k) fpm fidx sup) ->
    wt_state (RustIRspec.State f Sskip (RustIRspec.Kseq s k) fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f s k fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f s k fpm fidx sup).
Proof. Admitted.

Lemma step_continue_seq_simulation:
  forall f s k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f Scontinue (RustIRspec.Kseq s k) fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f Scontinue (RustIRspec.Kseq s k) fpm fidx sup) ->
    wt_state (RustIRspec.State f Scontinue (RustIRspec.Kseq s k) fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Scontinue k fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Scontinue k fpm fidx sup).
Proof. Admitted.

Lemma step_break_seq_simulation:
  forall f s k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f Sbreak (RustIRspec.Kseq s k) fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f Sbreak (RustIRspec.Kseq s k) fpm fidx sup) ->
    wt_state (RustIRspec.State f Sbreak (RustIRspec.Kseq s k) fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sbreak k fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sbreak k fpm fidx sup).
Proof. Admitted.

Lemma step_ifthenelse_simulation:
  forall f a s1 s2 k fpm fpm1 v1 b sup fidx (s1': state),
    eval_pexpr fidx fpm a = OK (fp_scalar Mint8unsigned v1, fpm1) ->
    bool_val v1 (typeof a) = Some b ->
    match_states (RustIRspec.State f (Sifthenelse (Epure a) s1 s2) k fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sifthenelse (Epure a) s1 s2) k fpm fidx sup) ->
    wt_state (RustIRspec.State f (Sifthenelse (Epure a) s1 s2) k fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f (if b then s1 else s2) k fpm1 fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f (if b then s1 else s2) k fpm1 fidx sup).
Proof. Admitted.

Lemma step_loop_simulation:
  forall f s k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f (Sloop s) k fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f (Sloop s) k fpm fidx sup) ->
    wt_state (RustIRspec.State f (Sloop s) k fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f s (RustIRspec.Kloop s k) fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f s (RustIRspec.Kloop s k) fpm fidx sup).
Proof. Admitted.

Lemma step_skip_or_continue_loop_simulation:
  forall f s k fpm fidx sup x (s1': state),
    x = Sskip \/ x = Scontinue ->
    match_states (RustIRspec.State f x (RustIRspec.Kloop s k) fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f x (RustIRspec.Kloop s k) fpm fidx sup) ->
    wt_state (RustIRspec.State f x (RustIRspec.Kloop s k) fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f s (RustIRspec.Kloop s k) fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f s (RustIRspec.Kloop s k) fpm fidx sup).
Proof. Admitted.

Lemma step_break_loop_simulation:
  forall f s k fpm fidx sup (s1': state),
    match_states (RustIRspec.State f Sbreak (RustIRspec.Kloop s k) fpm fidx sup) s1' ->
    borrowck_inv (RustIRspec.State f Sbreak (RustIRspec.Kloop s k) fpm fidx sup) ->
    wt_state (RustIRspec.State f Sbreak (RustIRspec.Kloop s k) fpm fidx sup) ->
    exists s2',
      plus RustIRsem.step tge s1' E0 s2'
      /\ match_states (RustIRspec.State f Sskip k fpm fidx sup) s2'
      /\ borrowck_inv (RustIRspec.State f Sskip k fpm fidx sup).
Proof. Admitted.

Lemma step_simulation: forall s1 t s2 s1',
    RustIRspec.step ge s1 t s2 ->
    match_states s1 s1' ->
    borrowck_inv s1 ->
    wt_state s1 ->
    exists s2', 
      plus RustIRsem.step tge s1' t s2' /\ match_states s2 s2' /\ borrowck_inv s2.
Proof.
  intros s1 t s2 s1' STEP MATCH BORINV WTST. 
  inv STEP.
  - eapply step_assign_simulation; eauto.
  - eapply step_assign_variant_simulation; eauto.
  - eapply step_box_simulation; eauto.
  - eapply step_drop_simulation; eauto.
  - eapply step_storagelive_simulation; eauto.
  - eapply step_storagedead_simulation; eauto.
  - eapply step_call_simulation; eauto.
  - eapply step_internal_function_simulation; eauto.
  - eapply step_return_1_simulation; eauto.
  - eapply step_returnstate_simulation; eauto.
  - eapply step_seq_simulation; eauto.
  - eapply step_skip_seq_simulation; eauto.
  - eapply step_continue_seq_simulation; eauto.
  - eapply step_break_seq_simulation; eauto.
  - eapply step_ifthenelse_simulation; eauto.
  - eapply step_loop_simulation; eauto.
  - eapply step_skip_or_continue_loop_simulation; eauto.
  - eapply step_break_loop_simulation; eauto.
Qed.


End BORROW_CHECK_SIM.


Notation li_rs_spec := li_rs_spec.

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

End ADT_ENV.
