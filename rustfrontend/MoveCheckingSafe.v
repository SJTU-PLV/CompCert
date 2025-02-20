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
Require Import MoveCheckingFootprint MoveCheckingDomain.
Require Import Wfsimpl.
(* use free_list related lemmas *)
Require SimplLocalsproof.

Import ListNotations.
Local Open Scope error_monad_scope.    

Inductive move_check_fundef_spec ce: fundef -> Prop :=
| move_check_funct: forall f
    (CKFUN: move_check_function ce f = OK tt),
    move_check_fundef_spec ce (Internal f)
| move_check_external: forall orgs rels tyl rty cc ef,
    ((exists name sg, ef = EF_external name sg) \/ ef = EF_malloc \/ ef = EF_free) ->
    move_check_fundef_spec ce (External orgs rels ef tyl rty cc).

(** Specification of move checking  *)
Record move_check_program_spec (p: program) :=
  { prog_comp_consistent: composite_env_consistent (prog_comp_env p);

    prog_comp_range: forall id co,
      (prog_comp_env p) ! id = Some co ->
      co_sizeof co <= Ptrofs.max_unsigned;

    prog_comp_length: forall id co,
      (prog_comp_env p) ! id = Some co ->
      list_length_z (co_members co) <= Int.max_unsigned;

    prog_comp_norepet: forall id co,
      (prog_comp_env p) ! id = Some co ->
      list_norepet (name_members (co_members co));

    prog_fundef: forall id fd,
      In (id, Gfun fd) p.(prog_defs) ->
      move_check_fundef_spec p.(prog_comp_env) fd;

    prog_well_typed: wt_program p;

  }.

Lemma move_check_function_wt: forall f ce,
    move_check_function ce f = OK tt ->
    wt_function ce f.
Proof. 
  intros. unfold move_check_function in H.
  monadInv H. destruct x1 as ((init & uninit) & universe).
  monadInv EQ2.
  econstructor. destruct x4.
  eapply type_check_stmt_sound; eauto.
Qed.  
  
Lemma move_check_program_meet_spec: forall p tp,
    move_check_program p = OK tp ->
    move_check_program_spec p.
Proof.
  intros p tp CHECK.
  unfold move_check_program in CHECK.
  monadInv CHECK. unfold check_composite_env in EQ.
  destruct PTree_Properties.for_all eqn: CE in EQ; try congruence.
  erewrite PTree_Properties.for_all_correct in CE.
  assert (CE1: forall id co, (prog_comp_env p) ! id = Some co ->
                        (co_sizeof co <= Ptrofs.max_unsigned
                        /\ list_length_z (co_members co) <= Int.max_unsigned
                         /\ list_norepet (name_members (co_members co)))).
  { intros. exploit CE; eauto.
    intros CK. unfold check_composite in CK.
    rewrite !andb_true_iff in CK.
    rewrite !Z.leb_le in CK.
    destruct CK as ((A1 & A2) & A3). repeat apply conj; auto.
    eapply proj_sumbool_true; eauto. }
  (* construct match_program_gen *)
  set (ce := prog_comp_env p) in *.
  rename x0 into tp.
  assert (MAT: match_program_gen (fun ctx f tf => move_check_fundef_spec ce f /\ wt_fundef ce f) eq p p tp).
  { eapply match_transform_partial_program2; eauto.
    - intros id f tf CK. unfold move_check_fundef in CK.
      destruct f.
      + destruct (move_check_function ce f) eqn: CK1; try congruence.
        destruct u. split.
        econstructor; eauto.
        econstructor.
        eapply move_check_function_wt; eauto.        
      + destruct e; try congruence; split; inv CK; econstructor; eauto.
    - intros. unfold transl_globvar in H. inv H. auto. }
  assert (SPEC: forall id fd, In (id, Gfun fd) p.(prog_defs) ->
                         move_check_fundef_spec p.(prog_comp_env) fd
                         /\ wt_fundef p.(prog_comp_env) fd).
  { destruct MAT as (MATCH & _). simpl in MATCH.
    revert MATCH. generalize (prog_defs p) (AST.prog_defs tp).
    induction 1; simpl; intros.
    contradiction.
    destruct a1.
    destruct H0; eauto. inv H0.
    inv H. destruct b1. simpl in *. subst. inv H1.
    destruct H2.
    split; auto. }    
  econstructor.
  - destruct p. simpl.
    eapply build_composite_env_consistent; eauto.
  - intros. eapply CE1; eauto.
  - intros. eapply CE1; eauto.
  - intros. eapply CE1; eauto.
  - intros. eapply SPEC; eauto.
  - econstructor. intros. eapply SPEC; eauto.
Qed.

Section MOVE_CHECK.

Variable prog: program.
Variable w: rs_own_world.
Variable se: Genv.symtbl.
Hypothesis VALIDSE: Genv.valid_for (erase_program prog) se.
Let L := semantics prog se.
Let ge := globalenv se prog.

(* composite environment *)
Let ce := ge.(genv_cenv).

Let AN : Type := (PMap.t IM.t * PMap.t IM.t * PathsMap.t).
                                                                  
Let match_stmt (ae: AN) body cfg s ts := match_stmt get_init_info ae (move_check_stmt ce) check_cond_expr body cfg s ts.

Definition mod_sg := match w with
                    | rsw sg _ _ _ => sg
                    end.

Let wt_state := wt_state prog se mod_sg.

(* split move_check_program_spec into the following hypotheses to simplify the proof *)
Hypothesis CONSISTENT: composite_env_consistent ce.

Hypothesis COMP_RANGE: forall id co, ce ! id = Some co -> co_sizeof co <= Ptrofs.max_unsigned.
Hypothesis COMP_LEN: forall id co, ce ! id = Some co -> list_length_z (co_members co) <= Int.max_unsigned.
Hypothesis COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co)).
Hypothesis FUN_CHECK:  forall id fd,
    In (id, Gfun fd) prog.(prog_defs) ->
    move_check_fundef_spec ce fd.

Hypothesis SG_COMP_ENV: (rs_sig_comp_env mod_sg = ce).
Hypothesis WTPROG: wt_program prog.

(** Properties of evaluation of place  *)

Lemma  co_alignof_pos: forall co,
    co_alignof co > 0.
Proof.
  intros.
  generalize (co_alignof_two_p co). intros (n & ALPOW).
  rewrite ALPOW. rewrite two_power_nat_equiv.
  generalize (Nat2Z.is_nonneg n). intros A.
  exploit Z.pow_pos_nonneg. instantiate (1:= 2). lia.
  eauto. lia.
Qed.


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

Lemma field_offset_in_max_range: forall ofs fofs co fty fid,
    field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = Struct ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.
  intros until fid; intros FOFS FTY R1 COMP STRUCT.
  generalize (Ptrofs.unsigned_range ofs). intros RAN1.
  generalize (sizeof_pos ce fty). intros SZGT.
  generalize (field_offset_in_range ce (co_members co) _ _ _ FOFS FTY).
  intros (DELR1 & DELR2). 
  (* not easy range proof *)
  assert (RAN2: Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned).
  {
    erewrite co_consistent_sizeof in *; eauto.
    rewrite STRUCT in *. simpl in *.
    generalize (align_le (sizeof_struct ce (co_members co)) (co_alignof co) (co_alignof_pos co)).
    intros. lia. }
  lia.
Qed.

Lemma variant_field_offset_in_max_range: forall ofs fofs co fty fid,
    variant_field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned ->
    composite_consistent ce co ->
    co_sv co = TaggedUnion ->
    0 <= fofs <= Ptrofs.max_unsigned
    /\ 0 <= Ptrofs.unsigned ofs + fofs <= Ptrofs.max_unsigned
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned.
Proof.  
  intros until fid; intros FOFS FTY R1 COMP ENUM.
  generalize (Ptrofs.unsigned_range ofs). intros RAN1.
  generalize (sizeof_pos ce fty). intros SZGT.
  generalize (variant_field_offset_in_range ce (co_members co) _ _ _ FOFS FTY).
  intros (DELR1 & DELR2). 
  (* not easy range proof *)
  assert (RAN2: Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.max_unsigned).
  {
    erewrite co_consistent_sizeof in *; eauto.
    rewrite ENUM in *. simpl in *.
    generalize (align_le (sizeof_variant ce (co_members co)) (co_alignof co) (co_alignof_pos co)).
    intros. lia. }
  lia.
Qed.


(* The locations evaluated by get_loc_footprint_map and eval_place are
the same. *)
Lemma eval_place_get_loc_footprint_map_equal: forall m le p fpm fp b1 ofs1 b2 ofs2 own
    (GFP: get_loc_footprint_map le (path_of_place p) fpm = Some (b1, ofs1, fp))
    (WT: wt_place le ce p)
    (WFENV: wf_env fpm ce m le)
    (EVAL: eval_place ce le m p b2 ofs2)
    (MM: mmatch fpm ce m le own)
    (DOM: dominators_is_init own p = true),
    b1 = b2
    /\ ofs1 = Ptrofs.unsigned ofs2
    (* It is used to strengthen this lemma *)
    /\ wt_footprint ce (typeof_place p) fp
    /\ ofs1 + sizeof ce (typeof_place p) <= Ptrofs.max_unsigned.
Proof.
  induction p; intros.
  - inv EVAL. simpl in GFP. rewrite H3 in GFP.
    destruct (fpm ! i) eqn: FP; try congruence. inv GFP.
    repeat apply conj; auto.
    simpl. exploit wf_env_footprint; eauto.
    intros (fp0 & A1 & A2). rewrite FP in A1. inv A1. auto.
    simpl. inv WT. eapply sizeof_in_range. auto.
  - inv EVAL. simpl in GFP. destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2).
    exploit IHp; eauto. inv WT. eauto.
    intros (A1 & A2 & A3 & A4). subst.
    simpl in G2. destruct fp3; try congruence.
    destruct (find_fields i fpl) eqn: FIND; try congruence. repeat destruct p0.
    inv G2. inv A3. rewrite H3 in H0. inv H0.
    exploit find_fields_some; eauto. intros (B1 & B2). subst.
    exploit WT2; eauto.
    intros (fty & C1 & C2 & C3).
    rewrite H6 in CO. inv CO.
    rewrite H7 in C2. inv C2.
    (* some range properties *)
    rewrite H3 in *. simpl in A4. rewrite H6 in A4.
    exploit field_offset_in_max_range; eauto.
    intros (R1 & R2 & R3).
    (* some rewrite *)
    inv WT. rewrite H3 in WT3. inv WT3.
    rewrite H6 in WT4. inv WT4.
    rewrite C1 in WT5. inv WT5. 
    repeat apply conj; auto.
    rewrite Ptrofs.add_unsigned; auto.
    (** range proof obligation *)
    rewrite !Ptrofs.unsigned_repr; auto.
    rewrite !Ptrofs.unsigned_repr; auto.        
  - inv EVAL. inv WT. destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2. inv H4; simpl in *; try congruence. inv H.
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
    destruct list_eq_dec in G2; try congruence.
    destruct ident_eq in G2; try congruence. inv G2.
    rewrite H3 in A3. inv A3.
    rewrite H4 in CO. inv CO.
    rewrite H9 in FOFS. inv FOFS.
    (* some range properties *)
    rewrite H3 in *. simpl in A4. rewrite H4 in A4.
    exploit variant_field_offset_in_max_range; eauto.
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
    rewrite Int.unsigned_repr in H8. rewrite H8 in TAG. inv TAG.
    simpl. auto.
    (* tag is in range *)
    generalize (list_nth_z_range _ _ TAG).
    generalize (COMP_LEN id co H4). lia.
    rewrite FTY in WT4. inv WT4.
    auto.
Qed.

Lemma field_offset_in_range_eq_gen: forall ofs fofs sz,
    0 <= fofs <= sz ->
    Ptrofs.unsigned ofs + sz <= Ptrofs.max_unsigned ->
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr fofs)) = Ptrofs.unsigned ofs + fofs.
Proof.
  intros.
  generalize (Ptrofs.unsigned_range ofs). intros R.
  erewrite Ptrofs.add_unsigned.
  rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr; auto.  
  lia.
  lia. lia.
Qed.

Lemma field_offset_in_range_eq: forall ofs fofs orgs id fid fty co,
    ce ! id = Some co ->
    co_sv co = Struct ->
    field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + sizeof ce (Tstruct orgs id) <= Ptrofs.max_unsigned ->
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr fofs)) = Ptrofs.unsigned ofs + fofs
    /\ Ptrofs.unsigned ofs <= Ptrofs.unsigned ofs + fofs
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.unsigned ofs + sizeof ce (Tstruct orgs id).
Proof.
  intros. 
  exploit field_offset_in_range_complete; eauto.
  intros (R1 & R2).
  generalize (Ptrofs.unsigned_range ofs). intros F4.
  generalize (COMP_RANGE id co H). intros R3.
  generalize (sizeof_pos ce fty). intros R4.
  simpl in *. rewrite H in *.
  repeat apply conj.
  eapply field_offset_in_range_eq_gen; eauto.
  lia. lia. lia.
Qed.

Lemma variant_field_offset_in_range_eq: forall ofs fofs orgs id fid fty co,
    ce ! id = Some co ->
    co_sv co = TaggedUnion ->
    variant_field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    Ptrofs.unsigned ofs + sizeof ce (Tvariant orgs id) <= Ptrofs.max_unsigned ->
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr fofs)) = Ptrofs.unsigned ofs + fofs
    /\ Ptrofs.unsigned ofs <= Ptrofs.unsigned ofs + fofs
    /\ Ptrofs.unsigned ofs + fofs + sizeof ce fty <= Ptrofs.unsigned ofs + sizeof ce (Tvariant orgs id)
    /\ 4 <= fofs.
Proof.
  intros. 
  exploit variant_field_offset_in_range_complete; eauto.
  intros (R1 & R2).
  generalize (Ptrofs.unsigned_range ofs). intros F4.
  generalize (COMP_RANGE id co H). intros R3.
  generalize (sizeof_pos ce fty). intros R4.
  simpl in *. rewrite H in *.
  repeat apply conj.
  eapply field_offset_in_range_eq_gen; eauto.
  lia. lia. lia. lia.
Qed.

  

(* This lemma is used to state that the location of a place is
unchanged if we the memory location in [bs] is unchanged. [bs] is the
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
        
(* The location from a not_shallow_prefix path must be in the
        footprint being gotten *)
Lemma get_loc_footprint_not_shallow_path: forall phl fp1 b1 ofs1 b2 ofs2 fp2,
    not_shallow_prefix_paths phl ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    In b2 (footprint_flat fp1).
Proof.
  induction phl; intros until fp2; intros SHA GFP; simpl in *.
  - inv SHA.
  - inv SHA.
    + destruct fp1; try congruence.
      exploit get_loc_footprint_in; eauto.
    + destruct a.
      * destruct fp1; try congruence.
        simpl. right. eauto.
      * destr_fp_field fp1 GFP.        
        exploit IHphl; eauto. intros.
        eapply in_flat_map; eauto.
      * destr_fp_enum fp1 ty.
        simpl in *. eauto.
Qed.                                               

(* if (own_env, fpm (or abstract memory), mem) satisfies mmatch, then
moving out the valid_owner of a place [p] preserves mmatch
properties. *)
Lemma mmatch_move_place_sound: forall p1 fpm1 fpm2 m le own
    (MM: mmatch fpm1 ce m le own)
    (WF: wf_own_env le ce own)
    (* This property ensure that the place to be moved out has shallow
    prefix (its location) in the universe. This property is ensured by
    must_movable *)
    (EX: Paths.Exists (fun p2 => is_shallow_prefix p1 p2 = true) (PathsMap.get (local_of_place p1) own.(own_universe)))
    (CLR: clear_footprint_map le (path_of_place p1) fpm1 = Some fpm2),
    mmatch fpm2 ce m le (move_place own p1).
Proof.
  intros. red. intros until fp.
  intros PFP INIT.
  (* set (p1:= (valid_owner p)) in *. *)
  rename p into p0.
  destruct (is_prefix p1 p0) eqn: PRE.
  (* impossible *)
  - unfold is_init, move_place, remove_place in INIT. simpl in INIT.
    eapply Paths.mem_2 in INIT.
    erewrite PathsMap.gsspec in INIT.
    destruct peq.
    * eapply Paths.filter_2 in INIT.
      rewrite PRE in INIT. simpl in INIT. congruence.
      red. solve_proper.
    * (* unfold p1 in *. *)
      (* rewrite valid_owner_same_local in n. *)
      erewrite <- (is_prefix_same_local p1 p0) in n.
      (* erewrite valid_owner_same_local in n. *)
      congruence.
      auto.      
  (* valid_owner p is not a prefix of p0 *)
  -  destruct (is_prefix p0 p1) eqn: PRE1.
    (* p0 is prefix of p1 (valid_owner p). clear p's footprint also
      affects the footprint of p0 *)
    * unfold clear_footprint_map in CLR.
      destruct (get_loc_footprint_map le (path_of_place p1) fpm1) eqn: GET1; try congruence.
      repeat destruct p.
      destruct (path_of_place p1) eqn: POP.
      exploit is_prefix_paths_app. eapply PRE1. rewrite POP.
      destruct (path_of_place p0) eqn: POP2. simpl.
      intros (A & (phl & B)). subst.
      (** set_footprint_map_app_inv is important TODO  *)
      exploit get_loc_footprint_map_app_inv. eapply GET1.
      intros (b2 & ofs2 & fp3 & A & B).
      exploit get_set_footprint_map_app_inv. eapply A. eauto.
      intros (fp4 & C & D).
      rewrite PFP in C. inv C.
      (* use mmatch *)
      exploit MM. erewrite POP2. eauto.
      eapply move_place_init_is_init. eauto.
      intros (BM & FULL).
      (** TODO: check that this property is necessary *)
      destruct EX as (p2 & IN & SPRE).
      assert (PRE01: is_prefix_strict p0 p1 = true).
      { eapply is_not_prefix_strict; auto. }
      assert (PRE02: is_prefix_strict p0 p2 = true).
      { eapply is_prefix_strict_trans_prefix. eauto.
        eapply is_shallow_prefix_is_prefix. eauto. }
      (* We need to say that p must not be shallow children of p0,
      otherwise moving out the valid owner of p would make p0
      partially owned. But p0 is owned from the premise of mmatch *)
      (** TODO: p0 must be not a shallow prefix of p1 because there is
      some shallow children of p1 in the universe which is guaranteed
      by the must_movable of p1 and some well-formedenss of universe
      (i.e., if p is in the universe, so p's shallow prefix is not in
      the universe) . So the extra paths [phl] must contain some
      ph_deref and updating fp3 to fp4 does not affect the bmatch in
      (b2, ofs2) because the update takes place in other block *)
      assert (NOT_SHALLOW: is_shallow_prefix p0 p1 = false).
      { destruct (is_shallow_prefix p0 p1) eqn: SHA; auto.
        exploit is_shallow_prefix_trans. eapply SHA. eauto.
        intros B1. rewrite <- B1.
        (* translation validation: p0 is strict prefix of p2, so p2
        must not be a shallow children of p0, otherwise they have
        overlapped memory location *)
        eapply wf_own_universe_shallow. eauto.
        erewrite in_universe_eq.
        eapply is_init_in_universe. eauto.
        eapply move_place_eq_universe. 
        unfold in_universe. eapply Paths.mem_1; auto.
        erewrite <- is_shallow_prefix_same_local. 2: eapply B1.
        (* erewrite <- valid_owner_same_local in IN. *)
        erewrite is_shallow_prefix_same_local. eauto.
        eauto. auto. }
      assert (NOT_SHALLOW_PHL: not_shallow_prefix_paths phl).
      { eapply path_of_not_shallow_prefix; eauto. }
      exploit bmatch_set_not_shallow_paths; eauto. intros BM1. split.
      auto.
      (** is_full is not possible because p2 is in the universe (add
        a premise in this lemma) *)      
      intros FULL1. unfold is_full, is_full_internal in FULL1.
      eapply Paths.for_all_2 in FULL1. exploit FULL1.
      erewrite is_prefix_same_local. 2: eapply PRE1.
      (* unfold p1. erewrite valid_owner_same_local.  *) eauto.
      intros NPRE.
      rewrite PRE02 in NPRE. simpl in NPRE. congruence.
      red. solve_proper.
    (* p0 is not prefix of p1 *)
    * unfold clear_footprint_map in CLR.
      destruct (get_loc_footprint_map le (path_of_place p1) fpm1) eqn: GET1; try congruence.
      repeat destruct p.      
      (* no relation between p0 and (valid_owner p), so two cases *)
      destruct (ident_eq (local_of_place p1) (local_of_place p0)).
     + exploit is_not_prefix_disjoint. eapply PRE. eapply PRE1.
       intros [A|B].
       -- do 2 erewrite <- local_of_paths_of_place in A. congruence.
       -- do 2 erewrite local_of_paths_of_place in e.
          destruct (path_of_place p1) eqn: C. destruct (path_of_place p0) eqn: D.
          simpl in e. subst.
          exploit get_set_disjoint_paths. eauto.
          eauto. instantiate (1:= le). intros E.
          cbn [snd] in *.
          rewrite PFP in E.
          (* use mmatch *)
          rewrite <- D in E.
          exploit MM. eauto.
          eapply move_place_init_is_init. eauto.
          intros (BM & WTLOC). auto.                  
     + destruct (path_of_place p1) eqn: B. destruct (path_of_place p0) eqn: C.       
       exploit get_set_different_local; eauto.
       replace (local_of_place p1) with i. eauto.
       erewrite local_of_paths_of_place. rewrite B. auto.
       replace (local_of_place p0) with i0.
       instantiate (1 := l0). instantiate (1 := le).
       intros D. rewrite PFP in D.
       2: { erewrite local_of_paths_of_place. rewrite C. auto. }
       (* use mmatch *)
       rewrite <- C in D.
       exploit MM. eauto.
       eapply move_place_init_is_init. eauto.
       intros (BM & WTLOC). auto.
Qed.       


    
(** dereferce a semantically well typed location produces well typed value *)
Lemma deref_sem_wt_loc_sound: forall m fp b ofs ty v               
    (WT: sem_wt_loc ce m fp b (Ptrofs.unsigned ofs))
    (VALID: Mem.valid_block m b)
    (* alignment *)
    (AL: (alignof ce ty | (Ptrofs.unsigned ofs)))
    (WTFP: wt_footprint ce ty fp)
    (DE: deref_loc ty m b ofs v)
    (PERM: Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof ce ty) Cur Readable),
    sem_wt_val ce m fp v.
Proof.
  intros. destruct ty; inv WTFP; inv WT; simpl in *; try inv MODE;
  inv DE; simpl in *; try congruence. 
  (* struct *)
  - econstructor; eauto. eapply sem_wt_struct; eauto. 
  (* enum *)
  - econstructor; eauto. eapply sem_wt_enum; eauto. 
Qed.


(* The location returned by get_loc_footprint is align with the type
of the footprint *)
Lemma get_loc_footprint_align: forall phl fp1 b1 ofs1 b2 ofs2 fp2 ty1 ty2,
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    wt_footprint ce ty1 fp1 ->
    wt_path ce ty1 phl ty2 ->
    (* ofs1 must be aligned first *)
    (alignof ce ty1 | ofs1) ->
    (alignof ce ty2 | ofs2).
Proof.
  intros phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros until ty2; intros GFP WTFP WTPH AL.
  - eapply length_zero_iff_nil in LEN. subst.
    simpl in *. inv GFP.
    eapply wt_path_nil_inv in WTPH. subst. auto.
  - exploit length_S_inv; eauto. 
    intros (phl' & ph & A1 & LEN1). subst.
    exploit get_loc_footprint_app_inv; eauto.
    intros (b3 & ofs3 & fp3 & G1 & G2). simpl in *.
    destruct ph.
    + destruct fp3; try congruence.
      inv G2. eapply Z.divide_0_r.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv G2.
      eapply wt_path_field_inv in WTPH as (id1 & orgs & co & A1 & A2 & A3 & A4).
      exploit get_wt_footprint_wt. eauto. eauto.
      eapply get_loc_footprint_eq. eauto. intros WTFP1.
      inv WTFP1.
      exploit find_fields_some; eauto. intros (B1 & B2). subst.
      exploit WT2; eauto.
      intros (fty & FTY & FOFS & WTFP2).
      rewrite A2 in CO. inv CO. rewrite A3 in FTY. inv FTY.
      exploit IHn; eauto. intros AL1.
      eapply Z.divide_add_r.
      (* show that the alignment of field type can be divided by the
      alignment of the struct *)      
      eapply Z.divide_trans; eauto.      
      simpl. rewrite A2.
      erewrite co_consistent_alignof; eauto.
      eapply field_alignof_divide_composite. eauto.
      (* show that the field offset is aligned *)            
      eapply field_offset_aligned; eauto.
    + destr_fp_enum fp3 ty.
      inv G2.
      eapply wt_path_downcast_inv in WTPH as (id1 & orgs1 & co & A1 & A2 & A3 & A4 & A5).
      inv A1.
      exploit get_wt_footprint_wt. eauto. eauto.
      eapply get_loc_footprint_eq. eauto. intros WTFP1.
      inv WTFP1.
      rewrite A3 in CO. inv CO. rewrite A4 in FTY. inv FTY.
      exploit IHn; eauto. intros AL1.
      eapply Z.divide_add_r.
      (* show that the alignment of field type can be divided by the
      alignment of the struct *)      
      eapply Z.divide_trans; eauto.      
      simpl. rewrite A3.
      erewrite co_consistent_alignof; eauto.
      eapply field_alignof_divide_composite. eauto.
      (* show that the field offset is aligned *)            
      eapply variant_field_offset_aligned; eauto.
Qed.
      
  
(* The location returned by get_loc_footprint is align with the type
of the footprint *)  
Lemma get_loc_footprint_map_align: forall le p fpm b ofs m fp,
    get_loc_footprint_map le (path_of_place p) fpm = Some (b, ofs, fp) ->
    wf_env fpm ce m le ->
    wt_place le ce p ->
    (alignof ce (typeof_place p) | ofs).
Proof.
  intros until fp. intros GFP WFENV WTP.      
  destruct (path_of_place p) eqn: POP.
  exploit wt_place_wt_local. eauto. rewrite local_of_paths_of_place. erewrite POP.
  simpl. intros (b0 & ty0 & LE).
  exploit wt_place_wt_path; eauto. intros WTPH.
  simpl in GFP. rewrite LE in GFP.
  destruct (fpm ! i) eqn: A; try congruence.
  exploit wf_env_footprint; eauto.
  intros (fp1 & A1 & A2). rewrite A in A1. inv A1.  
  eapply get_loc_footprint_align; eauto.
  eapply Z.divide_0_r.
Qed.

Lemma bmatch_scalar_type_sem_wt_loc: forall b ofs fp ty m,
    scalar_type ty = true ->
    bmatch ce m b ofs fp ->
    wt_footprint ce ty fp ->
    sem_wt_loc ce m fp b ofs
    /\ fp = fp_scalar ty.
Proof.
  destruct ty; intros; simpl in *; try congruence.
  all: inv H1; inv H0; split; econstructor; eauto.
Qed.

(* tedious proof *)
Lemma sem_wt_val_type_unop: forall uop ty1 ty2 m v1 v2,
    type_unop uop ty1 = OK ty2 ->
    Cop.sem_unary_operation uop v1 (to_ctype ty1) m = Some v2 ->
    sem_wt_val ce m (fp_scalar ty1) v1 ->
    sem_wt_val ce m (fp_scalar ty2) v2.
Proof.
  intros until v2. intros TY SEM WT1.
  destruct uop; simpl in TY; simpl in SEM.
  - unfold Cop.sem_notbool in SEM.
    assert (A: ty2 = Tint Ctypes.IBool Ctypes.Signed) by (destruct (classify_bool ty1); inv TY; auto). 
    assert (B: exists b, v2 = Val.of_bool b).
    { destruct (Cop.bool_val v1 (to_ctype ty1) m); inv SEM. exists (negb b); auto. }
    destruct B as [b B]. subst.
    destruct b. econstructor. econstructor.
  - unfold Cop.sem_notint in SEM; Ctyping.DestructCases; eauto with sem_ty.
    inv WT1. simpl in *. try congruence.
    inv WT1. simpl in *. try congruence.
    simpl in *. try congruence.
  (* neg *)
  - unfold Cop.sem_neg in SEM; DestructCases; eauto with sem_ty; try (inv WT1; simpl in *; try congruence; inv TY; econstructor).
  - unfold Cop.sem_absfloat in SEM; DestructCases; eauto with sem_ty; try (inv WT1; simpl in *; try congruence; inv TY; econstructor).
Qed.

(** Semantics well typedness preservation under binary operation
(which is mostly copied from Ctyping.v *)

Lemma sem_wt_val_sem_binarith: forall
  (sem_int: Ctypes.signedness -> int -> int -> option val)
  (sem_long: Ctypes.signedness -> int64 -> int64 -> option val)
  (sem_float: Floats.float -> Floats.float -> option val)
  (sem_single: Floats.float32 -> Floats.float32 -> option val)
  v1 ty1 v2 ty2 m v ty msg,
  (forall sg n1 n2,
   match sem_int sg n1 n2 with None | Some (Vint _)  => True | _ => False end) ->
  (forall sg n1 n2,
   match sem_long sg n1 n2 with None | Some (Vlong _)  => True | _ => False end) ->
  (forall n1 n2,
   match sem_float n1 n2 with None | Some (Vfloat _) => True | _ => False end) ->
  (forall n1 n2,
   match sem_single n1 n2 with None | Some (Vsingle _) => True | _ => False end) ->
  Cop.sem_binarith sem_int sem_long sem_float sem_single v1 (to_ctype ty1) v2 (to_ctype ty2) m = Some v ->
  binarith_type ty1 ty2 msg = OK ty ->
  sem_wt_val ce m (fp_scalar ty1) v1 ->
  sem_wt_val ce m (fp_scalar ty2) v2 ->
  sem_wt_val ce m (fp_scalar ty) v.
Proof with (try discriminate).
  intros. unfold Cop.sem_binarith in *.
  exploit binarith_type_to_ctype. eauto. intros BTY.
  unfold binarith_type in *.
  set (ty' := Cop.binarith_type (Cop.classify_binarith (to_ctype ty1) (to_ctype ty2))) in *.
  destruct (Cop.sem_cast v1 (to_ctype ty1) ty' m) as [v1'|] eqn:CAST1...
  destruct (Cop.sem_cast v2 (to_ctype ty2) ty' m) as [v2'|] eqn:CAST2...
  destruct (classify_binarith ty1 ty2) eqn: CLA; try congruence;
  erewrite classify_binarith_to_ctype in *; eauto; try congruence;
  simpl in *; inv H4;
  DestructCases.
  - specialize (H s i i0). rewrite H3 in H.
    destruct v; try contradiction. econstructor.
  - specialize (H0 s i i0). rewrite H3 in H0.
    destruct v; try contradiction. econstructor.
  - specialize (H1 f f0). rewrite H3 in H1.
    destruct v; try contradiction. econstructor.     
  - specialize (H2 f f0). rewrite H3 in H2.
    destruct v; try contradiction. econstructor.    
Qed.

Lemma sem_wt_val_sem_binarith_int: forall
  (sem_int: Ctypes.signedness -> int -> int -> option val)
  (sem_long: Ctypes.signedness -> int64 -> int64 -> option val)
  v1 ty1 v2 ty2 m v ty msg,
  (forall sg n1 n2,
   match sem_int sg n1 n2 with None | Some (Vint _)  => True | _ => False end) ->
  (forall sg n1 n2,
   match sem_long sg n1 n2 with None | Some (Vlong _)  => True | _ => False end) ->
  Cop.sem_binarith sem_int sem_long (fun n1 n2 => None) (fun n1 n2 => None) v1 (to_ctype ty1) v2 (to_ctype ty2) m = Some v ->
  binarith_int_type ty1 ty2 msg = OK ty ->
  sem_wt_val ce m (fp_scalar ty1) v1 ->
  sem_wt_val ce m (fp_scalar ty2) v2 ->
  sem_wt_val ce m (fp_scalar ty) v.
Proof.
  intros. eapply sem_wt_val_sem_binarith with (msg := msg); eauto.
  simpl; auto. simpl; auto.
  unfold binarith_int_type, binarith_type in *.
  destruct (classify_binarith ty1 ty2); congruence.
Qed.  

Lemma sem_wt_val_sem_shift:
  forall sem_int sem_long ty1 ty2 msg ty v1 v2 v m,
  shift_op_type ty1 ty2 msg = OK ty ->
  Cop.sem_shift sem_int sem_long v1 (to_ctype ty1) v2 (to_ctype ty2) = Some v ->
  sem_wt_val ce m (fp_scalar ty1) v1 ->
  sem_wt_val ce m (fp_scalar ty2) v2 ->
  sem_wt_val ce m (fp_scalar ty) v.
Proof.
  intros. unfold shift_op_type, Cop.sem_shift in *.
  destruct (classify_shift ty1 ty2) eqn: CLA; try congruence;
  erewrite classify_shift_to_ctype in *; eauto; try congruence;
  simpl in *; inv H0; inv H; DestructCases; econstructor.
Qed.

Lemma sem_wt_val_sem_cmp:
  forall ty1 ty2 msg ty c v1 v2 m v,
  comparison_type ty1 ty2 msg = OK ty ->
  Cop.sem_cmp c v1 (to_ctype ty1) v2 (to_ctype ty2) m = Some v ->
  sem_wt_val ce m (fp_scalar ty1) v1 ->
  sem_wt_val ce m (fp_scalar ty2) v2 ->
  sem_wt_val ce m (fp_scalar ty) v.
Proof with (try discriminate).
  unfold comparison_type, Cop.sem_cmp; intros.
  assert (X: forall b, sem_wt_val ce m (fp_scalar (Tint Ctypes.I32 Ctypes.Signed)) (Val.of_bool b)).
  {
    intros b; destruct b; constructor; exact I.
  }
  destruct (classify_binarith ty1 ty2) eqn: CLA; try congruence;
    erewrite classify_cmp_to_ctype in H0; eauto; try congruence; simpl in *.
  - unfold Cop.sem_binarith in H0.
    set (ty' := Cop.binarith_type (Cop.classify_binarith (to_ctype ty1) (to_ctype ty2))) in *.
    destruct (Cop.sem_cast v1 (to_ctype ty1) ty') as [v1'|]...
    destruct (Cop.sem_cast v2 (to_ctype ty2) ty') as [v2'|]...
    erewrite !classify_binarith_to_ctype in H0; eauto; try congruence; simpl in H0.
    inv H.
    DestructCases; auto.
  - unfold Cop.sem_binarith in H0.
    set (ty' := Cop.binarith_type (Cop.classify_binarith (to_ctype ty1) (to_ctype ty2))) in *.
    destruct (Cop.sem_cast v1 (to_ctype ty1) ty') as [v1'|]...
    destruct (Cop.sem_cast v2 (to_ctype ty2) ty') as [v2'|]...
    erewrite !classify_binarith_to_ctype in H0; eauto; try congruence; simpl in H0.
    inv H.
    DestructCases; auto. 
  - unfold Cop.sem_binarith in H0.
    set (ty' := Cop.binarith_type (Cop.classify_binarith (to_ctype ty1) (to_ctype ty2))) in *.
    destruct (Cop.sem_cast v1 (to_ctype ty1) ty') as [v1'|]...
    destruct (Cop.sem_cast v2 (to_ctype ty2) ty') as [v2'|]...
    erewrite !classify_binarith_to_ctype in H0; eauto; try congruence; simpl in H0.
    inv H.
    DestructCases; auto.
  - unfold Cop.sem_binarith in H0.
    set (ty' := Cop.binarith_type (Cop.classify_binarith (to_ctype ty1) (to_ctype ty2))) in *.
    destruct (Cop.sem_cast v1 (to_ctype ty1) ty') as [v1'|]...
    destruct (Cop.sem_cast v2 (to_ctype ty2) ty') as [v2'|]...
    erewrite !classify_binarith_to_ctype in H0; eauto; try congruence; simpl in H0.
    inv H.
    DestructCases; auto.
Qed.

(* tedious *)
Lemma sem_wt_val_type_binop: forall bop ty1 ty2 ty v1 v2 v m,
    type_binop bop ty1 ty2 = OK ty ->
    Cop.sem_binary_operation_rust bop v1 (to_ctype ty1) v2 (to_ctype ty2) m = Some v ->
    sem_wt_val ce m (fp_scalar ty1) v1 ->
    sem_wt_val ce m (fp_scalar ty2) v2 ->
    sem_wt_val ce m (fp_scalar ty) v.
Proof.
  intros until m. intros TY SEM WT1 WT2.
  destruct bop; simpl in *.
  - unfold Cop.sem_add_rust in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith; eauto; intros; exact I.
  - unfold Cop.sem_sub_rust in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith; eauto; intros; exact I.
  - unfold Cop.sem_mul in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith; eauto; intros; exact I.    
  - unfold Cop.sem_div in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith; eauto; intros.
    simpl; Ctyping.DestructMatch; auto.
    simpl; Ctyping.DestructMatch; auto.
    simpl; Ctyping.DestructMatch; auto.
    simpl; Ctyping.DestructMatch; auto.
  - unfold Cop.sem_mod in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith_int; eauto; intros.
    simpl; Ctyping.DestructMatch; auto.
    simpl; Ctyping.DestructMatch; auto.
  - unfold Cop.sem_and in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith_int; eauto; intros; exact I.
  - unfold Cop.sem_or in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith_int; eauto; intros; exact I.
  - unfold Cop.sem_xor in SEM; DestructCases.
    eapply sem_wt_val_sem_binarith_int; eauto; intros; exact I.
  - unfold Cop.sem_shl in SEM; DestructCases.
    eapply sem_wt_val_sem_shift; eauto.
  - unfold Cop.sem_shr in SEM; DestructCases.
    eapply sem_wt_val_sem_shift; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
  - eapply sem_wt_val_sem_cmp; eauto.
Qed.

    
(* The result of eval_expr is semantically well typed *)

(* The footprint must be fp_emp in pexpr *)
Lemma eval_pexpr_sem_wt: forall pe fpm m le own v init uninit universe
    (MM: mmatch fpm ce m le own)
    (EVAL: eval_pexpr ce le m ge pe v)
    (SOUND: sound_own own init uninit universe)
    (CHECK: move_check_pexpr init uninit universe pe = true)
    (WTPE: wt_pexpr le ce pe)
    (WFENV: wf_env fpm ce m le),
    sem_wt_val ce m (fp_scalar (typeof_pexpr pe)) v.
Proof.  
  induction pe; intros.
  - simpl. inv EVAL. econstructor.
  - simpl. inv EVAL. inv WTPE. econstructor. 
  - simpl. inv EVAL. inv WTPE. econstructor.
  - simpl. inv EVAL. inv WTPE. econstructor.
  - simpl. inv EVAL. inv WTPE. econstructor.
  - inv EVAL.
    simpl in CHECK. destruct (scalar_type t) eqn: TYP; try congruence.
    eapply andb_true_iff in CHECK as (DOM & INIT).
    eapply dominators_must_init_sound in DOM; eauto.
    inv WTPE.
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP & RAN & PERM & VALID).
    exploit get_loc_footprint_map_align; eauto. intros AL.
    (* get the footprint of valid owner *)
    exploit valid_owner_place_footprint; eauto.
    intros (fp' & ofs1 & fofs & G1 & G2 & G3).
    (* show that (b, ofs) is sem_wt_loc *)    
    exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM' & FULL').
    exploit valid_owner_bmatch; eauto. intros BM.
    (* scalar typed bmatch is sem_wt_loc *)
    exploit bmatch_scalar_type_sem_wt_loc; eauto. intros (WTLOC & FPEQ).
    subst.
    rewrite <- G3 in WTLOC.
    exploit deref_sem_wt_loc_sound; eauto.
    eapply Mem.range_perm_implies; eauto. constructor.
  - simpl. inv WTPE. inv EVAL.
    destruct Int.eq. econstructor. econstructor.
  (* reference: impossible *)
  - simpl in CHECK. congruence.
  - simpl. inv WTPE. simpl in CHECK. inv EVAL.
    exploit IHpe; eauto.
    intros WTVAL.
    eapply sem_wt_val_type_unop; eauto.
  - simpl. inv WTPE. simpl in CHECK. inv EVAL.
    eapply andb_true_iff in CHECK as (C1 & C2).
    exploit IHpe1; eauto. intros WTVAL1.
    exploit IHpe2; eauto. intros WTVAL2.
    eapply sem_wt_val_type_binop; eauto.
  - simpl in CHECK. congruence.
Qed.
    
  
(* THE value produced by eval_expr is semantics well-typed. We need to
update the abstract memory (split the footprint of the value from
fpm1) *)
Lemma eval_expr_sem_wt: forall fpm1 m le own1 own2 e v init uninit universe
    (MM: mmatch fpm1 ce m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_of_env le) (flat_fp_map fpm1))
    (EVAL: eval_expr ce le m ge e v)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_expr' ce init uninit universe e = true)
    (OWN: move_place_option own1 (moved_place e) = own2)
    (WFENV: wf_env fpm1 ce m le)
    (WT: wt_expr le ce e)
    (WFOWN: wf_own_env le ce own1),
  (** TODO: how to relate fp and fpm2 ? We should show that they are disjoint *)
  exists fp fpm2,
    sem_wt_val ce m fp v
    /\ wt_footprint ce (typeof e) fp
    (** If expr is pure expr, fp is fp_emp and not from any phs *)
    (* /\ get_footprint_map phs fpm1 = Some fp *)
    (* /\ clear_footprint_map ce phs fpm1 = Some fpm2 *)
    /\ mmatch fpm2 ce m le own2
    /\ wf_env fpm2 ce m le
    (* footprint disjointness *)
    /\ list_norepet (footprint_flat fp ++ flat_fp_map fpm2)
    (* we need to ensure that fp ∪ fpm2 = fpm1 to prove
    separation. Because we do not know how fpm2 is constructed (which
    is differnet in move place or pure expression), we use this
    list_equiv to relate fpm1 and fpm2 *)
    /\ list_equiv (footprint_flat fp ++ flat_fp_map fpm2) (flat_fp_map fpm1)
    (* it is satisfied trivially because we just move out a place *)
    /\ wf_own_env le ce own2.
Proof.
  intros. destruct e.
  (* Emoveplace *)
  - simpl in *. inv EVAL. inv WT. inv H2.
    destruct (place_eq p (valid_owner p)); subst.
    (* p is not downcast *)
    + eapply andb_true_iff in CHECK. destruct CHECK as (DONW & MOVABLE).
      eapply dominators_must_init_sound in DONW; eauto.
      exploit eval_place_sound; eauto.
      intros (pfp &  PFP & WTFP & RAN & PERM & VALID).
      (** TODO: wt_footprint implication *)
      (* location of p is sem_wt *)
      exploit movable_place_sem_wt; eauto.
      red. auto.
      intros WT_LOC. 
      (* deref sem_wt location *)
      exploit deref_sem_wt_loc_sound; eauto.
      (* prove that ofs is align with the size of p's type *)
      eapply get_loc_footprint_map_align; eauto.
      (* permission *)
      eapply Mem.range_perm_implies; eauto. constructor.
      intros WT_VAL.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place (valid_owner p)) fpm1 = Some fpm2).
      { unfold clear_footprint_map.
        rewrite <- e. erewrite PFP. destruct (path_of_place p) eqn: POP.        
        exploit get_set_footprint_map_exists. eauto. instantiate (1 := clear_footprint_rec pfp).
        intros (fpm2 & A1 & A2). exists fpm2. auto. }
      destruct A as (fpm2 & CLEAR).
      destruct (path_of_place p) eqn: POP.
      exists pfp, fpm2. repeat apply conj; auto.
      eapply (mmatch_move_place_sound (valid_owner p)); eauto.
      (** implication of must_movable  *)
      exploit must_movable_exists_shallow_prefix; eauto.
      intros (p2 & IN & A). exists p2. split.
      eapply sound_own_universe in IN.
      rewrite valid_owner_same_local. eauto.
      eauto.  eauto.
      (* wf_env *)
      rewrite <- e in *.
      rewrite POP in *.
      eapply wf_env_clear_footprint; eauto.
      (** footprint norepet  *)
      rewrite <- e in *. rewrite POP in *.
      unfold clear_footprint_map in CLEAR. rewrite PFP in CLEAR.
      exploit get_loc_footprint_map_norepet; eauto.
      intros (N1 & N2).
      exploit set_disjoint_footprint_norepet. 3: eauto. all: eauto.
      rewrite empty_footprint_flat. constructor.
      eapply empty_footprint_disjoint. intros N3.
      eapply list_norepet_app. repeat apply conj; auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint_map; eauto.
      eapply empty_footprint_disjoint.
      (** list_equiv  *)
      rewrite <- e in *. rewrite POP in *.
      eapply get_clear_footprint_map_equiv; eauto.
      (** wf_own_env  *)
      eapply wf_own_env_move_place; eauto.      
    (* p is downcast *)
    + do 2 rewrite andb_true_iff in CHECK. destruct CHECK as ((DOWN & INIT) & FULL).
      eapply dominators_must_init_sound in DOWN; eauto.
      exploit eval_place_sound; eauto.
      intros (fp1 & PFP & WTFP & RAN & PERM & VALID).
      exploit valid_owner_place_footprint; eauto.
      intros (fp2 & ofs1 & fofs1 & PFP1 & VOFS & OFSEQ).
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC).      
      exploit valid_owner_sem_wt_loc. eapply WTLOC.
      erewrite <- is_full_same; eauto. eapply sound_own_universe; eauto.
      eauto. intros WTLOC1.
      rewrite <- OFSEQ in WTLOC1.
      exploit deref_sem_wt_loc_sound; eauto.
      eapply get_loc_footprint_map_align; eauto.
      eapply Mem.range_perm_implies; eauto. constructor.
      intros WT_VAL.
      set (p1 := valid_owner p) in *.
      assert (A: exists fpm2, clear_footprint_map le (path_of_place p1) fpm1 = Some fpm2).
      { unfold clear_footprint_map.
        erewrite PFP1. destruct (path_of_place p1) eqn: POP.
        exploit get_set_footprint_map_exists. eauto.
        instantiate (1 := clear_footprint_rec fp2).
        intros (fpm2 & A1 & A2). exists fpm2. auto. }     
      destruct A as (fpm2 & CLEAR).
      destruct (path_of_place p1) eqn: POP.
      (* we have to prove the flat footprint of the valid_owner p is
      the same as p. Use the property of valid_owner_offset_footprint *)
      exploit valid_owner_footprint_flat_eq; eauto.
      intros FEQ.
      exists fp1, fpm2. repeat apply conj; auto.
      eapply (mmatch_move_place_sound (valid_owner p)); eauto.
      (* exists shallow prefix *)
      exists p1. split.      
      exploit is_init_in_universe. eapply must_init_sound. eauto. eauto.
      unfold in_universe. intros. eapply Paths.mem_2.
      unfold p1 in H. eauto.
      (* erewrite valid_owner_same_local in H. unfold p1. auto. *)
      eapply is_shallow_prefix_refl.
      fold p1.  rewrite POP. auto.
      (* wf_env *)
      eapply wf_env_clear_footprint; eauto.
      (** footprint norepet  *)
      rewrite FEQ.
      unfold clear_footprint_map in CLEAR. rewrite PFP1 in CLEAR.
      exploit get_loc_footprint_map_norepet; eauto.
      intros (N1 & N2).
      exploit set_disjoint_footprint_norepet. 3: eauto. all: eauto.
      rewrite empty_footprint_flat. constructor.
      eapply empty_footprint_disjoint. intros N3.
      eapply list_norepet_app. repeat apply conj; auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint_map; eauto.
      eapply empty_footprint_disjoint.
      (** list_equiv  *)
      rewrite FEQ.      
      eapply get_clear_footprint_map_equiv; eauto.
      (** wf_own_env  *)
      eapply wf_own_env_move_place; eauto.
  - exists (fp_scalar (typeof_pexpr p)), fpm1. simpl in *. subst.
    inv EVAL. inv WT.
    exploit eval_pexpr_sem_wt; eauto. intros VWT.
    repeat apply conj; auto.
    econstructor. eauto.
    red. split; intros; auto.
Qed.


(** IMPORTANT TODO: what if b is changed? *)
Lemma sem_wt_loc_unchanged_blocks: forall fp m1 m2 b ofs ce
    (WT: sem_wt_loc ce m1 fp b ofs)
    (UNC: Mem.unchanged_on (fun b1 _ => In b1 (footprint_flat fp) \/ b1 = b) m1 m2),
      sem_wt_loc ce m2 fp b ofs.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv WT.
  - inv WT.
    econstructor. eauto.
    eapply Mem.load_unchanged_on; eauto. intros. simpl. auto.
    inv WT0; econstructor; eauto.
  - inv WT. inv WT0.
    econstructor. eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    econstructor.
    eapply IHfp. eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto. auto.
  - inv WT. econstructor.
    intros. exploit FWT; eauto.
    intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    eapply H; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H1; auto.
    left. eapply in_flat_map. eauto.
  - inv WT. econstructor.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    eapply IHfp; eauto.
Qed.

Definition footprint_of_val (v: val) : list block :=
  match v with
  | Vptr b _ => b :: nil
  | _ => nil
  end.

Lemma sem_wt_val_unchanged_blocks: forall fp m1 m2 v ce
    (WT: sem_wt_val ce m1 fp v)
    (UNC: Mem.unchanged_on (fun b1 _ => In b1 (footprint_flat fp)
                                     \/ In b1 (footprint_of_val v)) m1 m2),
      sem_wt_val ce m2 fp v.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv WT.
  - inv WT; econstructor.
  - inv WT. 
    econstructor.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl.
    intros. destruct H; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto. auto.
  - inv WT. econstructor.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H0; auto.
    auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto. 
    simpl. auto.
    (* valid_block *)
    eapply Mem.unchanged_on_support; eauto.
  - inv WT. econstructor.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H; auto.
    auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.unchanged_on_support; eauto.
Qed.

Lemma sem_wt_val_list_unchanged_blocks: forall fpl vl m1 m2
    (WT: sem_wt_val_list ce m1 fpl vl)
    (UNC: Mem.unchanged_on (fun b1 _ => In b1 (flat_map footprint_flat fpl)
                                     \/ In b1 (flat_map footprint_of_val vl)) m1 m2),
      sem_wt_val_list ce m2 fpl vl.
Proof.
  induction 1; intros; simpl in *.
  econstructor.
  econstructor.
  eapply sem_wt_val_unchanged_blocks. eauto.
  eapply Mem.unchanged_on_implies; eauto. simpl.
  intros. rewrite !in_app. destruct H0; auto.
  eapply IHWT.
  eapply Mem.unchanged_on_implies; eauto. simpl.
  intros. rewrite !in_app. destruct H0; auto.
Qed.

Lemma sem_wt_val_valid_block: forall m v fp b ce
    (WTVAL: sem_wt_val ce m fp v)
    (IN: In b (footprint_of_val v)),
    Mem.valid_block m b.
Proof.
  intros. inv WTVAL; simpl in IN; try (inv IN; fail).
  - destruct IN; try contradiction. subst.
    eapply Mem.load_valid_access in SIZE.
    eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; eauto.
    constructor.
  - destruct IN; try contradiction. subst. auto.
  - destruct IN; try contradiction. subst. auto.
Qed.

Lemma sem_wt_val_list_valid_blocks: forall m vl fpl b
    (WTVAL: sem_wt_val_list ce m fpl vl)
    (IN: In b (flat_map footprint_of_val vl)),
    Mem.valid_block m b.
Proof.
  induction 1; intros; simpl in *.
  - contradiction.
  - eapply in_app in IN. destruct IN.
    + eapply sem_wt_val_valid_block; eauto.
    + eauto.
Qed.


(* A more general lemma of sem_wt_loc_unchanged_blocks but it require
wt_footprint premise: may be we can combine them into a single lemma?*)
Lemma sem_wt_loc_unchanged_loc: forall fp m1 m2 b ofs ty
    (WT: sem_wt_loc ce m1 fp b ofs)
    (WTFP: wt_footprint ce ty fp)
    (UNC: Mem.unchanged_on (fun b1 ofs1 => In b1 (footprint_flat fp) \/ (b1 = b /\ ofs <= ofs1 < ofs + sizeof ce ty)) m1 m2),
      sem_wt_loc ce m2 fp b ofs.
Proof.
    induction fp using strong_footprint_ind; intros.
  - inv WT.
  - inv WT. inv WTFP.
    econstructor. eauto.
    eapply Mem.load_unchanged_on; eauto. intros. simpl. right.
    erewrite <- sizeof_by_value; eauto.
    inv WT0; econstructor; eauto.
  - inv WT. inv WTFP. inv WT0.
    econstructor. eapply Mem.load_unchanged_on; eauto.
    simpl. auto.
    econstructor.
    eapply IHfp. eauto. eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H; auto. left. destruct H. auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto. auto.
  - inv WT. inv WTFP. econstructor.
    intros. exploit FWT; eauto.
    intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    exploit WT2; eauto. intros (fty & FTY & FOFS & WTFP1).
    eapply H; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H1; auto.
    left. eapply in_flat_map. eauto.
    destruct H1. subst. right. rewrite CO. split; auto.
    exploit field_offset_in_range_complete; eauto.
    lia.
  - inv WT. inv WTFP.
    exploit variant_field_offset_in_range_complete; eauto. intros R1.
    generalize (sizeof_pos ce fty). intros R2. 
    econstructor.
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros. rewrite CO. right.
    split; auto. lia.
    eapply IHfp; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl.
    intros. rewrite CO. destruct H. auto.
    right. destruct H. subst. split; auto. lia.
Qed.

    
Definition list_interval {A: Type} (l: list A) (lo: Z) (sz: Z) :=
  firstn (Z.to_nat sz) (skipn (Z.to_nat lo) l).

(* lo is the offset of the field and sz is the size of this field. hi
is the size of the composite *)
Definition in_range (lo sz hi: Z) : Prop :=
  0 <= lo /\ lo + sz <= hi.


(** Load the interval bytes of a list of bytes *)
Lemma loadbytes_interval: forall m b ofs sz ofs1 sz1 bytes,
    in_range ofs1 sz1 sz ->
    Mem.loadbytes m b ofs sz = Some bytes ->
    Mem.loadbytes m b (ofs + ofs1) sz1 = Some (list_interval bytes ofs1 sz1).
Proof.
  intros. red in H. destruct H.
  unfold list_interval.
  destruct (Z.le_decidable 0 sz1).
  - exploit Z.le_exists_sub. eapply H1.
    intros (n & A1 & A2). rewrite Z.add_comm in A1. subst.
    rewrite <- Z.add_assoc in H0.
    exploit Mem.loadbytes_split; eauto. lia. lia.
    intros (bytes1 & bytes2 & B1 & B2 & B3). subst.
    exploit Mem.loadbytes_split. eapply B2. lia. lia.
    intros (bytes3 & bytes4 & B4 & B5 & B6). subst.
    erewrite B4. f_equal.
    exploit Mem.loadbytes_length. eapply B1. intros LEN1.
    exploit Mem.loadbytes_length. eapply B4. intros LEN2.
    erewrite <- LEN1. erewrite <- LEN2.
    erewrite skipn_app. rewrite Nat.sub_diag. simpl.
    erewrite skipn_all. simpl.
    erewrite firstn_app. rewrite Nat.sub_diag. simpl.
    rewrite firstn_all. apply app_nil_end.    
  - erewrite Z_to_nat_neg. simpl.
    erewrite Mem.loadbytes_empty. auto.
    lia. lia.
Qed.


Lemma sem_wt_loc_unchanged_on_copy: forall fp m1 m2 ty b1 ofs1 b2 ofs2 bytes,
    sem_wt_loc ce m1 fp b1 ofs1 ->
    wt_footprint ce ty fp ->
    (alignof ce ty | ofs1) ->
    (alignof ce ty | ofs2) ->
    Mem.unchanged_on (fun b _ => In b (footprint_flat fp)) m1 m2 ->
    Mem.loadbytes m1 b1 ofs1 (sizeof ce ty) = Some bytes ->
    Mem.loadbytes m2 b2 ofs2 (sizeof ce ty) = Some bytes ->
    sem_wt_loc ce m2 fp b2 ofs2.
Proof.
  induction fp using strong_footprint_ind; intros until bytes; intros SEMWT WT AL1 AL2 UNC LOAD1 LOAD2.
  - inv SEMWT.
  - inv SEMWT. inv WT.
    erewrite <- sizeof_by_value in *; eauto.
    erewrite <- alignof_by_value in *; eauto.
    eapply Mem.loadbytes_load in LOAD1; eauto.
    eapply Mem.loadbytes_load in LOAD2; eauto.
    econstructor; eauto.
    rewrite LOAD in LOAD1. inv LOAD1.
    inv WT0; econstructor; auto.    
  - inv SEMWT. inv WT. inv WT0.
    replace (sizeof ce (Tbox ty0)) with (size_chunk Mptr) in * by auto.
    eapply Mem.loadbytes_load in LOAD1; eauto.
    eapply Mem.loadbytes_load in LOAD2; eauto.
    rewrite LOAD1 in LOAD. inv LOAD.    
    econstructor; eauto.
    rewrite H0. econstructor.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. destruct H; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. auto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. auto. auto.
  - inv SEMWT.
    inv WT. econstructor.
    intros until ffp. intros FIND.
    exploit FWT. eauto. intros WTLOC.
    exploit find_fields_some;eauto. intros (A & B).
    exploit WT2; eauto. intros (fty & C & D & E).
    eapply H; eauto.
    (* align *)
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. simpl. rewrite CO.
    (** align of composite is dividable by the alignment of each member *)
    erewrite co_consistent_alignof; eauto.
    eapply field_alignof_divide_composite; eauto.
    (** the field offset is dividable by the alignment of each field *)
    eapply field_offset_aligned; eauto.
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. simpl. rewrite CO.
    (** align of composite is dividable by the alignment of each member *)
    erewrite co_consistent_alignof; eauto.
    eapply field_alignof_divide_composite; eauto.
    (** the field offset is dividable by the alignment of each field *)
    eapply field_offset_aligned; eauto.
    (* unchanged *)
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. 
    eapply in_flat_map. eauto.
    (* loadbytes *)
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tstruct orgs id)).
    (* in_range *)
    red. simpl. rewrite CO. exploit field_offset_in_range_complete; eauto.    
    eauto.
    (* loadbytes *)
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tstruct orgs id)).
    (* in_range *)
    red. simpl. rewrite CO. eapply field_offset_in_range_complete; eauto.
    eauto.
  - inv SEMWT.
    inv WT. simpl in *. rewrite CO in *.
    (** IMPORTANT TODO: the shape of sizeof variant (4 + ...), to get
    the bytes of the tag *)
    econstructor.
    exploit Mem.load_loadbytes; eauto. intros (tagbytes & LTAG & DEC). simpl in LTAG.   
    erewrite co_consistent_sizeof in *; eauto. rewrite ENUM in *. simpl in *.
    generalize (sizeof_variant_ge4 ce (co_members co)). intros GE4.
    assert (GE: 4 <= (align (sizeof_variant ce (co_members co)) (co_alignof co))).
    { generalize (co_alignof_pos co). intros POS.
      generalize (align_le (sizeof_variant ce (co_members co)) (co_alignof co) POS). 
      lia. }                                     
    exploit Z.le_exists_sub. eapply GE.
    intros (n1 & A1 & A2). rewrite Z.add_comm in A1. rewrite A1 in *.
    exploit Mem.loadbytes_split. eapply LOAD1. lia. lia. 
    intros (tagbytes1 & bytes1 & B1 & B2 & B3). subst.
    rewrite LTAG in B1. inv B1.
    exploit Mem.loadbytes_split. eapply LOAD2. lia. lia.
    intros (tagbytes2 & bytes2 & B4 & B5 & B6). subst.
    exploit Mem.loadbytes_length. eapply LTAG. intros L1.
    exploit Mem.loadbytes_length. eapply B4. intros L2.
    exploit list_append_injective_l; eauto. intuition.
    intros (C1 & C2). subst.
    erewrite DEC.
    eapply Mem.loadbytes_load. auto.    
    (* 4 | ofs2 *)
    eapply Z.divide_trans; eauto.
    erewrite co_consistent_alignof; eauto. rewrite ENUM in *.
    eapply tag_align_divide_composite.
    (* end of loading the tag *)
    eapply IHfp; eauto.
    (* align *)
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. 
    (** align of composite is dividable by the alignment of each member *)
    erewrite co_consistent_alignof; eauto.
    eapply field_alignof_divide_composite; eauto.
    (** the field offset is dividable by the alignment of each field *)
    eapply variant_field_offset_aligned; eauto.
    eapply Z.divide_add_r.
    eapply Z.divide_trans; eauto. 
    (** align of composite is dividable by the alignment of each member *)
    erewrite co_consistent_alignof; eauto.
    eapply field_alignof_divide_composite; eauto.
    (** the field offset is dividable by the alignment of each field *)
    eapply variant_field_offset_aligned; eauto.
    (* loadbytes *)
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tvariant orgs id)).
    (* in_range *)
    red. simpl. rewrite CO. exploit variant_field_offset_in_range_complete; eauto.
    lia.
    simpl. rewrite CO. eauto.
    (* loadbytes *)
    eapply loadbytes_interval. instantiate (1 := sizeof ce (Tvariant orgs id)).
    (* in_range *)
    red. simpl. rewrite CO. exploit variant_field_offset_in_range_complete; eauto.
    lia.
    simpl. rewrite CO. eauto.
Qed.

Lemma load_result_int: forall chunk n sz si,
    Cop.cast_int_int sz si n = n ->
    access_mode (Tint sz si) = Ctypes.By_value chunk ->
    Val.load_result chunk (Vint n) = Vint n.
Proof.
  intros until si; intros H0 H.
  simpl in H.
  destruct sz; destruct si; inv H; simpl;
    try (simpl in H0; rewrite H0; auto).
  auto. auto.
  simpl in H0. destruct (Int.eq n Int.zero).
  subst. simpl. auto.
  subst. simpl. auto.
  simpl in H0. destruct (Int.eq n Int.zero).
  subst. simpl. auto.
  subst. simpl. auto.
Qed.

(* Assigning a semantics well typed value to a location makes this
location semantics well-typed. The difficult part is the align and
composite. *)
Lemma assign_loc_sem_wt: forall fp ty m1 b ofs v m2
    (* We may require that the location is aligned (note that the
    location is calculated from l-value) *)                           
    (AS: assign_loc ce ty m1 b ofs v m2)
    (AL: (alignof ce ty | (Ptrofs.unsigned ofs)))
    (* The value stored in the memory must be casted *)
    (CAST: RustOp.val_casted v ty)
    (WT: sem_wt_val ce m1 fp v)
    (WTFP: wt_footprint ce ty fp)
    (* the assignment does not affect the footprint *)
    (IN: ~ In b (footprint_flat fp)),
    sem_wt_loc ce m2 fp b (Ptrofs.unsigned ofs).
Proof.
  (* no need to induciton on fp *)
  destruct fp; intros.
  - inv WT.
  - inv WT.
    + inv AS. 
      inv WTFP. simpl in H. inv H.
      eapply sem_wt_base; eauto.
      simpl. eauto.
      eapply Mem.load_store_same. eauto.
      simpl. econstructor.
    + inv AS.
      inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl.
      erewrite load_result_int; eauto.
      econstructor. inv CAST. auto.
    (* single *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv CAST. inv H.
      econstructor.
    (* float *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv CAST. inv H.
      econstructor.
    (* long *)
    + inv AS. inv WTFP.
      eapply sem_wt_base; eauto.
      eapply Mem.load_store_same. eauto.
      simpl in H. inv H. simpl.
      econstructor.      
  - inv WTFP. inv WT.
    inv AS; simpl in *; try congruence.
    eapply Decidable.not_or in IN. destruct IN as (IN1 & IN2).
    assert (UNC: Mem.unchanged_on (fun b _ => b <> b0) m1 m2).
    { eapply Mem.store_unchanged_on; eauto. }
    inv H.
    econstructor. 
    eapply Mem.load_store_same. eauto.
    exploit sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto. intros. simpl.
    destruct H.
    intro. apply IN2. subst. auto.
    subst. auto.
    intros WTLOC1.
    replace (Val.load_result Mptr (Vptr b Ptrofs.zero)) with (Vptr b Ptrofs.zero) by auto.
    econstructor; eauto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    eapply Mem.perm_valid_block; eauto.
    eapply Mem.load_unchanged_on; eauto.
  - inv AS. inv WTFP. simpl in *. try congruence.
    inv WT.
    eapply sem_wt_loc_unchanged_on_copy; eauto.
    (* alignment *)
    inv WTFP. eauto.
    (* unchanged *)
    eapply Mem.storebytes_unchanged_on; eauto.    
    eapply Mem.loadbytes_length in H4.
    eapply Mem.loadbytes_storebytes_same in H5.
    replace (sizeof ce ty) with (Z.of_nat (length bytes)).
    auto.
    rewrite H4. erewrite Z_to_nat_max.
    generalize (sizeof_pos ce ty). lia.    
  - inv AS. inv WTFP. simpl in *. try congruence.
    inv WT.
    eapply sem_wt_loc_unchanged_on_copy; eauto.
    (* alignment *)
    inv WTFP. eauto.
    (* unchanged *)
    eapply Mem.storebytes_unchanged_on; eauto.    
    eapply Mem.loadbytes_length in H4.
    eapply Mem.loadbytes_storebytes_same in H5.
    replace (sizeof ce ty) with (Z.of_nat (length bytes)).
    auto.
    rewrite H4. erewrite Z_to_nat_max.
    generalize (sizeof_pos ce ty). lia.
Qed.

Lemma assign_loc_unchanged_on: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    Mem.unchanged_on (fun b1 ofs1 => ~ (b1 = b /\ Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + sizeof ce ty)) m1 m2.
Proof.
  intros until v. intros AS.
  inv AS.
  - eapply Mem.store_unchanged_on; eauto.
    intros. intro. eapply H2. split; auto.
    erewrite <- sizeof_by_value; eauto.
  - exploit Mem.loadbytes_length. eauto.
    intros LEN.
    eapply Mem.storebytes_unchanged_on; eauto.
    intros. intro. eapply H7. split; auto.
    rewrite LEN in H6.
    erewrite Z_to_nat_max in H6.
    generalize (sizeof_pos ce0 ty). intros.
    erewrite Z.max_l in H6. eauto. lia.
Qed.

    
(* assignment does not change the permission of all the memory location *)
Lemma assign_loc_perm_unchanged: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    (forall b ofs k p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p).
Proof.
  intros until v. intros AS. inv AS.
  - intros. split; intros.
    eapply Mem.perm_store_1; eauto.
    eapply Mem.perm_store_2; eauto.
  - intros. split; intros.
    eapply Mem.perm_storebytes_1; eauto.
    eapply Mem.perm_storebytes_2; eauto.
Qed.

Lemma assign_loc_sup_unchanged: forall ce ty m1 m2 b ofs v,
    assign_loc ce ty m1 b ofs v m2 ->
    Mem.support m1 = Mem.support m2.
Proof.
  intros until v. intros AS. inv AS.
  - eapply Mem.support_storev; eauto.
  - erewrite <- Mem.support_storebytes; eauto.
Qed.

(* It collects the blocks pointed by the box pointer in the footprint. It does not collect *)
Fixpoint blocks_of_fp_box (fp: footprint) : list (block * Z) :=
  match fp with
  | fp_box b sz _ => (b, sz) :: nil
  | fp_struct _ fpl =>
      flat_map (fun '(fid, fofs, ffp) => blocks_of_fp_box ffp) fpl
  | fp_enum _ _ _ _ _ ffp =>
      blocks_of_fp_box ffp
  | _ => nil
  end.

(* The memory location of the size record in the allocated blocks *)
Definition loc_of_size_record (bs: list block) :=
  fun b ofs => In b bs /\ (- size_chunk Mptr) <= ofs < 0.

Definition loc_of_size_record_fp (fp: footprint) :=
  loc_of_size_record (map fst (blocks_of_fp_box fp)).

(* The permissions of all blocks in bs are unchanged *)
Definition blocks_perm_unchanged (bs: list (block * Z)) (m1 m2: mem) : Prop :=
  forall b sz ofs k p,
    In (b, sz) bs -> 0 <= ofs < sz ->
    (* To avoid prove all blocks in the footprint are valid, we just
    need m1 implies m2 *)
    Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.

Definition blocks_perm_unchanged_fp (fp: footprint) (m1 m2: mem) : Prop :=
  blocks_perm_unchanged (blocks_of_fp_box fp) m1 m2.


Lemma loc_of_size_record_fp_subfield: forall fp fpl b ofs fid fofs id,
    loc_of_size_record_fp fp b ofs ->
    In (fid, fofs, fp) fpl ->           
    loc_of_size_record_fp (fp_struct id fpl) b ofs.
Proof.
  intros. red. red.
  repeat red in H. destruct H. split; auto.
  eapply in_map_iff in H.
  destruct H as ((b1 & sz) & A & IN). simpl in A. subst.
  eapply in_map_iff.
  exists (b, sz). split. auto.
  simpl. eapply in_flat_map. 
  exists (fid, fofs, fp). eauto.
Qed.

Lemma blocks_perm_unchanged_fp_subfield: forall fp fpl m1 m2 fid fofs id,
    blocks_perm_unchanged_fp (fp_struct id fpl) m1 m2 ->
    In (fid, fofs, fp) fpl ->
    blocks_perm_unchanged_fp fp m1 m2.
Proof.
  intros. red. red. intros.
  do 2 red in H. eapply H; eauto.
  simpl. eapply in_flat_map.
  exists (fid, fofs, fp). eauto.
Qed.

(* The permission of (-size Mptr, sz) (i.e., the size of allocation)
is unchanged if the size record is unchanged_on and the permission of
the block body is also unchanged *)
Lemma size_record_and_perm_unchanged: forall fp m1 m2 b sz,
    Mem.unchanged_on (fun b1 ofs1 => loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    blocks_perm_unchanged_fp fp m1 m2 ->
    In (b, sz) (blocks_of_fp_box fp) ->
    forall k p,
      (** FIXME: if we just prove this direction, we do not need to
      prove that all the blocks in fp are valid blocks (which is used
      in unchanged_on_perm). This proof may require lots of
      effort... *)
      Mem.range_perm m1 b (- size_chunk Mptr) sz k p ->
      Mem.range_perm m2 b (- size_chunk Mptr) sz k p.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 sz1 UNC PERM IN; simpl in *; try contradiction.
  - destruct IN; try contradiction.
    inv H.
    do 2 red in PERM. intros. 
    red. intros.
    (* two cases: ofs < 0 and ofs >= 0 *)
    destruct (Z.lt_decidable ofs 0).      
    + erewrite <- Mem.unchanged_on_perm. eauto. eauto.
      simpl. red. red. simpl. split; eauto.
      lia.
      (** b1 in m1 is valid  *)
      eapply Mem.perm_valid_block. eauto.
    + eapply PERM. simpl. eauto.
      lia. eauto.
  - intros k p RPERM. red. intros ofs RANGE.
    (* (b1, sz1) is in one of the field box *)
    eapply in_flat_map in IN as (((fid & fofs) & ffp) & A1 & A2). subst.
    (* use I.H. *)
    eapply H. eauto.
    (* unchanged_on *)
    eapply Mem.unchanged_on_implies; eauto. simpl.
    intros. eapply loc_of_size_record_fp_subfield; eauto.
    (* perm unchanged *)
    eapply blocks_perm_unchanged_fp_subfield; eauto.
    eauto. auto. auto.
  - intros k p RPERM. red. intros.
    eapply IHfp.
    eapply Mem.unchanged_on_implies; eauto.
    red in PERM. simpl in PERM. red. eauto.
    eauto. auto. auto.
Qed.

        
(* bmatch remians valid if we only changes the location outside the
block b and the box blocks pointed by the the shallow footprint of
fp *)
Lemma bmatch_unchanged_on_block: forall fp m1 m2 b ofs,
    bmatch ce m1 b ofs fp ->
    (* The memory block [b] and the location of the size record are
    unchanged *)
    Mem.unchanged_on (fun b1 ofs1 => b1 = b \/ loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    (* We require that the permission of the box blocks pointed by the
    shallow part of fp is unchanged *)
    blocks_perm_unchanged_fp fp m1 m2 ->
    bmatch ce m2 b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 ofs1 BM UNC PERM.
  - inv BM.
  - inv BM. econstructor; eauto.
    eapply Mem.load_unchanged_on. eauto. simpl. auto. eauto.
    inv WT; econstructor. 
  (* fp_box *)
  - inv BM. econstructor.
    eapply Mem.load_unchanged_on; eauto. simpl. auto.
    (* the size loaded in m2 is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. right. red. simpl. 
    red. split. econstructor; auto. lia.
    (* permission is unchanged *)
    eapply size_record_and_perm_unchanged.
    eapply Mem.unchanged_on_implies; eauto. simpl. eauto.
    auto. simpl. auto. auto. auto.
  - inv BM. econstructor. intros fid fofs ffp FIND.
    exploit FMATCH; eauto. intros BM1.
    exploit find_fields_some; eauto.
    intros (A1 & A2).
    eapply H. eauto. eauto.
    (* unchanged_on *)
    eapply Mem.unchanged_on_implies. eauto.
    simpl. intros. destruct H0; subst; auto.
    right. eapply loc_of_size_record_fp_subfield; eauto.
    (* perm unchanged *)
    eapply blocks_perm_unchanged_fp_subfield; eauto.
  - inv BM. econstructor.
    (* prove the tag is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl. auto.
    (* prove bmatch *)
    eapply IHfp. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    red. red in PERM. eauto.
Qed.


(* A finded grained version of bmatch_unchanged_on. *)
Lemma bmatch_unchanged_on_loc: forall fp m1 m2 b ofs ty,
    bmatch ce m1 b ofs fp ->
    wt_footprint ce ty fp ->
    Mem.unchanged_on (fun b1 ofs1 => (b1 = b /\ (ofs <= ofs1 < ofs + sizeof ce ty)) \/ loc_of_size_record_fp fp b1 ofs1) m1 m2 ->
    (* We require that the permission of the box blocks pointed by the
    shallow part of fp is unchanged *)
    blocks_perm_unchanged_fp fp m1 m2 ->
    bmatch ce m2 b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros m1 m2 b1 ofs1 ty1 BM WTFP UNC PERM.
  - inv BM.
  - inv BM. inv WTFP.
    econstructor; eauto.
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. left. split; auto.
    erewrite <- sizeof_by_value; eauto.
    inv WT; econstructor; eauto.
  (* fp_box *)
  - inv BM. inv WTFP. econstructor.
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. left. split; auto.
    (* the size loaded in m2 is unchanged *)
    eapply Mem.load_unchanged_on; eauto. simpl.
    intros. right. red. simpl. 
    red. split. econstructor; auto. lia.
    (* permission is unchanged *)
    eapply size_record_and_perm_unchanged.
    eapply Mem.unchanged_on_implies; eauto. simpl. eauto.
    auto. simpl. auto. auto. auto.
  - inv BM. inv WTFP.
    econstructor. intros fid fofs ffp FIND.
    exploit FMATCH; eauto. intros BM1.
    exploit find_fields_some; eauto.    
    intros (A1 & A2).
    exploit WT2; eauto. intros (fty & FTY & FOFS & WTFP1).
    eapply H. eauto. eauto. eauto.
    (* unchanged_on *)
    + eapply Mem.unchanged_on_implies. eauto.
      simpl. intros. destruct H0.
      * destruct H0. subst. left. split; auto. rewrite CO.
        exploit field_offset_in_range_complete; eauto.
        lia.
      * right. eapply loc_of_size_record_fp_subfield; eauto.
    + (* perm unchanged *)
      eapply blocks_perm_unchanged_fp_subfield; eauto.
  - inv BM. inv WTFP.
    exploit variant_field_offset_in_range_complete; eauto. intros RAN.
    econstructor.    
     (* prove the tag is unchanged *)
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros. left. split; auto.
    rewrite CO.
    generalize (sizeof_pos ce fty). lia.
    (* prove bmatch *)
    eapply IHfp. eauto. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H.
    + destruct H. subst. left. split; auto.
      rewrite CO. lia.
    + right.
      red. red in PERM. eauto.
    + eauto.
Qed.

(* The footprint located in the shallow path of the footprint
satisfying bmatch still satisfies bmatch *)
Lemma get_loc_footprint_bmatch: forall phl b1 ofs1 b2 ofs2 fp1 fp2 m
    (BM: bmatch ce m b1 ofs1 fp1)
    (SHA: ~ not_shallow_prefix_paths phl)
    (GFP: get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2)),
    bmatch ce m b2 ofs2 fp2.
Proof.
  induction phl; intros; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + exfalso. eapply SHA. econstructor. auto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence. repeat destruct p.
      inv BM.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit FMATCH; eauto. intros BM1.
      eapply IHphl; eauto.
      intro. eapply SHA. eapply in_cons. eauto.
    + destr_fp_enum fp1 ty.
      inv BM. eapply IHphl; eauto.
      intro. eapply SHA. eapply in_cons. eauto.
Qed.

(* The footprint located in the path of the footprint satisfying
sem_wt_loc still satisfies sem_wt_loc *)
Lemma get_loc_footprint_sem_wt_loc: forall phl b1 ofs1 b2 ofs2 fp1 fp2 m
    (BM: sem_wt_loc ce m fp1 b1 ofs1)
    (GFP: get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2)),
    sem_wt_loc ce m fp2 b2 ofs2.
Proof.
  induction phl; intros; simpl in *.
  - inv GFP. auto.
  - destruct a.
    + destruct fp1; try congruence.
      inv BM. inv WT. eapply IHphl; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence. repeat destruct p.
      inv BM.
      exploit find_fields_some; eauto. intros (A1 & A2). subst.
      exploit FWT; eauto.
    + destr_fp_enum fp1 ty.
      inv BM. eapply IHphl; eauto.
Qed.

      
(* The box blocks of the footprint of shallow path are subset *)
Lemma get_footprint_shallow_path_incl: forall phl fp1 fp2,
    get_footprint phl fp1 = Some fp2 ->
    ~ not_shallow_prefix_paths phl ->
    incl (blocks_of_fp_box fp2) (blocks_of_fp_box fp1).
Proof.
  induction phl; intros until fp2; intros GFP NSHA; simpl in *.
  - inv GFP. eapply incl_refl.
  - destruct a.
    + destruct fp1; try congruence.
      unfold not_shallow_prefix_paths in NSHA. simpl in NSHA.
      eapply Decidable.not_or in NSHA. destruct NSHA. congruence.
    + destr_fp_field fp1 GFP.
      unfold not_shallow_prefix_paths in NSHA. simpl in NSHA.
      eapply Decidable.not_or in NSHA. destruct NSHA.
      red. intros.
      exploit IHphl; eauto. intros.
      simpl. eapply in_flat_map; eauto.
    + destr_fp_enum fp1 ty. simpl in *.
      unfold not_shallow_prefix_paths in NSHA. simpl in NSHA.
      eapply Decidable.not_or in NSHA. destruct NSHA.
      red. intros. eapply IHphl; eauto.
Qed.      

Lemma blocks_perm_unchanged_fp_incl: forall fp1 fp2 m1 m2,
    incl (blocks_of_fp_box fp2) (blocks_of_fp_box fp1) ->
    blocks_perm_unchanged_fp fp1 m1 m2 ->
    blocks_perm_unchanged_fp fp2 m1 m2.
Proof.
  intros. red. red. intros.
  eapply H0; eauto.
Qed.

(* If we only update the contents of the memory, the permission is
unchanged *)
Lemma blocks_perm_unchanged_normal: forall m1 m2 fp,
    (forall b ofs k p, Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p) ->
    blocks_perm_unchanged_fp fp m1 m2.
Proof.
  intros. red. red. intros. eapply H. eauto.
Qed.


(* The location computed by get_loc_footprint is not in size
    record (i.e., (-size Mptr, 0) *)
Lemma get_loc_footprint_pos: forall phl fp1 b1 ofs1 b2 ofs2 fp2 ce ty,
    ofs1 >= 0 ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    wt_footprint ce ty fp1 ->
    ofs2 >= 0.
Proof.
  induction phl; intros; simpl in *. inv H0. auto.
  destruct a.
  - destruct fp1; try congruence.
    inv H1. eapply IHphl. 2: eauto. lia. eauto.
  - destr_fp_field fp1 H0.
    inv H1. exploit WT2; eauto.
    intros (fty & FTY & FOFS & WTFP).
    exploit field_offset_in_range; eauto. intros (A1 & A2).
    eapply IHphl. 2: eauto. lia. eauto.
  - destr_fp_enum fp1 ty0.
    inv H1.
    exploit variant_field_offset_in_range; eauto. intros (A1 & A2).
    eapply IHphl. 2: eauto. lia. eauto.
Qed.
    
Lemma get_loc_footprint_map_pos: forall phl id b ofs fp fpm e m ce,
    get_loc_footprint_map e (id, phl) fpm = Some (b, ofs, fp) ->
    wf_env fpm ce m e ->
    ofs >= 0.
Proof.
  intros. simpl in *.
  destruct (e!id) eqn: A; try congruence. destruct p.
  destruct (fpm ! id) eqn: B; try congruence.
  exploit wf_env_footprint; eauto.
  intros (fp1 & A1 & A2). rewrite B in A1. inv A1.
  eapply get_loc_footprint_pos; eauto.
  lia. 
Qed.

(* The memory is only changed in (b1, ofs1), the changed location is
sem_wt. The memory is still bmatch *)
Lemma bmatch_set_subpath_wt_val: forall phl fp1 fp2 vfp m1 m2 b ofs b1 ofs1 ty1 vty pfp
    (BM: bmatch ce m1 b ofs fp1)    
    (* It is used to ensure that the changed location is not size
    record. Restrict ofs instead of ofs1 here is because we need to
    strengthen the I.H. More generally, there are some locations in
    the memory should be protected. They must be not modified by the
    semantics. In our setting, these locations are the location of
    size record allocated by malloc *)
    (GT: ofs >= 0)
    (* Move this comment to sem_wt_loc_set_wt_val. Only changes the
    location which is updated with vfp. To use I.H., we need to relax
    this condition to that the memory not in the vfp and not in (b1,
    ofs1) is unchanged instead of just not in (b1, ofs1)*)
    (UNC: Mem.unchanged_on (fun b2 ofs2 => ~ (b2 = b1 /\ (ofs1 <= ofs2 < ofs1 + sizeof ce vty))) m1 m2)
    (* The permission of the box blocks is unchanged *)
    (PERMUNC: blocks_perm_unchanged_fp fp1 m1 m2)
    (* we just need (b1, ofs1) to be bmatch to strengthen the I.H. *)
    (WTLOC: bmatch ce m2 b1 ofs1 vfp)
    (* pfp is useless in this proof *)
    (GFP: get_loc_footprint phl fp1 b ofs = Some (b1, ofs1, pfp))
    (SFP: set_footprint phl vfp fp1 = Some fp2)
    (WTFP1: wt_footprint ce ty1 fp1)
    (* relate ty1 and vty *)
    (WTPATH: wt_path ce ty1 phl vty)
    (* separation of fp *)
    (NOREP: list_norepet (footprint_flat fp1))
    (DIS: ~ In b (footprint_flat fp1)),
    bmatch ce m2 b ofs fp2.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. inv SFP. auto.
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    exploit set_footprint_app_inv. eauto.
    intros (fp3' & vfp' & B1 & B2 & B3).
    (* relate fp3 and fp3' *)
    exploit get_loc_footprint_eq. eapply A1. intros B1'.
    rewrite B1 in B1'. inv B1'.
    (* show that ofs1 >= 0 *)
    assert (GT1: ofs1 >= 0).
    { eapply get_loc_footprint_pos; eauto. }
    destruct ph; simpl in *.
    + destruct fp3; try congruence. inv A2. inv B2.
      (* key proof: phl' ++ [ph_deref] is not shallow path, so if
      bmatch m2 b ofs fp1 then bmatch m2 b ofs fp2
      (bmatch_set_not_shallow_paths) *)
      (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
      exploit get_footprint_incl. eauto. simpl. left; eauto.
      intros IN.
      assert (BNE: b1 <> b).
      { intro. eapply DIS. subst. auto. }
      (* To use bmatch_unchanged_on_block: we also need to prove that
      the size record and the permission of the box blocks are
      unchanged *)
      exploit bmatch_unchanged_on_block. eapply BM.
      eapply Mem.unchanged_on_implies. eauto. intros. simpl.
      destruct H. subst. intro. eapply BNE. intuition.      
      intro. destruct H1. subst. do 2 red in H. lia.
      (* perm unchanged *)
      auto.
      intros BM1.
      (* use bmatch_set_not_shallow_paths *)
      eapply bmatch_set_not_shallow_paths. eauto.
      eapply SFP. eapply in_app. right. econstructor. auto.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv B2. inv A2.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      (* Get the type *)
      eapply wt_path_field_inv in WTPATH as (sid & orgs & co & WTPATH & CO & FTY & STR).
      assert (WTFP:  wt_footprint ce (Tstruct orgs sid) (fp_struct id fpl)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* get the field_offset of i *)
      rewrite CO in CO0. inv CO0.
      exploit WT1. eapply FTY. intros (ffpi & fofsi & E1 & E2 & E3).
      rewrite FIND in E1. inv E1.
      (* show that fofsi >= 0 *)
      exploit field_offset_in_range. eauto. eauto. intros (R1 & R2).      
      (* key proof: discuss phl is shallow path or not. If yes, prove
      bmatch m2 (fp_struct id (set_field i vfp fpl)) and then use
      I.H. *)
      destruct (in_dec path_eq ph_deref phl').
      (* phl' is not shallow path. The proof is mostly the same as in ph_deref *)
      * (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
        exploit (get_loc_footprint_not_shallow_path phl'). auto.
        eapply A1. intros IN.        
        assert (BNE: b1 <> b).
        { intro. eapply DIS. subst. auto. }
        exploit bmatch_unchanged_on_block. eapply BM.
        eapply Mem.unchanged_on_implies. eauto. intros. simpl.
        destruct H. subst. intuition.
        intro. destruct H1. subst.
        do 2 red in H. destruct H. lia.
        auto.
        intros BM1.
        (* use bmatch_set_not_shallow_paths *)
        eapply bmatch_set_not_shallow_paths. eauto.
        eapply SFP. eapply in_app. left. auto.
      (* phl' is shallow path. First prove b1 = b and bmatch m1
      (fp_struct id fpl) (note that this can only be proved if phl' is
      shallow path). Then prove bmatch m2 (fp_struct (set_field i vfp
      fpl)). Finally use I.H. to prove bmatch m2 fp2 *)
      * exploit get_loc_footprint_bmatch. eapply BM. 1-2: eauto.
        intros BM1.
        assert (BM2: bmatch ce m2 b1 ofs2 (fp_struct id (set_field i vfp fpl))).
        { inv BM1. econstructor.
          intros fid fofs ffp FIND1.
          destruct (ident_eq fid i); subst.
          (* fid = i: use WTLOC to prove *)
          - exploit find_fields_same_footprint. eauto. intro. subst.
            (* prove fofs = z *)
            exploit find_fields_same_offset. eauto. intros (vfp1 & F).
            rewrite FIND in F. inv F. auto.
          (* fid <> i *)
          - exploit find_fields_same_offset; eauto.
            intros (vfp1 & FIND2).
            exploit FMATCH. eauto. intros BM3.
            exploit find_fields_set_spec. eauto.
            erewrite FIND1. intros D. inv D.
            destruct peq; try congruence.
            (* use bmatch_unchanged_on and BM3. Show that (ofs2 +
            fofs) has no overlap with the field i *)            
            (* get the type of vfp1 (the type of fid) *)
            exploit WT2. eapply FIND2. intros (fty & FTY1 & FOFS & WTVFP1).
            eapply bmatch_unchanged_on_loc; eauto.
            (* show unchanged_on i.e., (ofs2 + fofs) not in [(ofs2 +
            z), (ofs2 + z + size vty) *)
            eapply Mem.unchanged_on_implies. eauto.
            simpl. intros. destruct H.
            destruct H. subst. intro. destruct H.
            exploit field_offset_no_overlap_simplified.
            5: eauto. 1-4: eauto.
            intros [A|B]. lia. lia.
            (* loc_of_size_record_fp *)
            intro. destruct H1. subst. do 2 red in H. destruct H. lia.
            (* perm unchanged: we need to show that (blocks_of_fp_box
            vfp1) ⊆ (blocks_of_fp_box fp1) because phl is shallow
            prefix path *)
            red.
            exploit find_fields_some. eapply FIND2. intros (F1 & F2).
            eapply blocks_perm_unchanged_fp_subfield; eauto.
            eapply blocks_perm_unchanged_fp_incl; eauto.
            eapply get_footprint_shallow_path_incl.
            eapply get_loc_footprint_eq. eauto. auto. }
        (* prove by I.H. *)
        eapply IHn. eauto. eauto. eapply GT.
        2: eauto.
        2: eapply BM2. all: eauto.
        (* prove (ofs2+z) is in the range of the struct, i.e., [ofs2,
        ofs2+sizeof struct sid) *)
        eapply Mem.unchanged_on_implies; eauto.
        intros. simpl. intro. eapply H. destruct H1.
        split; auto. subst. clear H.
        (* show that z >= 0 *)
        exploit field_offset_in_range_complete; eauto.
        simpl. rewrite CO. lia.
    (* enum case: the proof strategy is similar to struct *)
    + destruct fp3; try congruence.
      destruct ty; try congruence.
      destruct ident_eq; try congruence.
      destruct list_eq_dec; try congruence.
      destruct ident_eq; try congruence.
      inv A2. inv B2.
      (* key proof: discuss phl is shallow path or not. If yes, prove
      bmatch m2 (fp_struct id (set_field i vfp fpl)) and then use
      I.H. *)
      destruct (in_dec path_eq ph_deref phl').
      (* phl' is not shallow path. The proof is mostly the same as in ph_deref *)
      * (* first show b1 <> b which is used to prove bmatch m2 b ofs fp1 *)
        exploit (get_loc_footprint_not_shallow_path phl'). auto.
        eapply A1. intros IN.        
        assert (BNE: b1 <> b).
        { intro. eapply DIS. subst. auto. }
        exploit bmatch_unchanged_on_block. eapply BM.
        eapply Mem.unchanged_on_implies. eauto. intros. simpl.
        destruct H. subst. intuition.
        intro. destruct H1. subst.
        do 2 red in H. destruct H. lia.
        auto.
        intros BM1.
        (* use bmatch_set_not_shallow_paths *)
        eapply bmatch_set_not_shallow_paths. eauto.
        eapply SFP. eapply in_app. left. auto.
      * exploit get_loc_footprint_bmatch. eapply BM. 1-2: eauto.
        intros BM1.
        eapply wt_path_downcast_inv in WTPATH as (id1 & orgs1 & co & EQTY & WTPATH & CO & FTY & ENUM ). symmetry in EQTY. inv EQTY.
        assert (WTFP:  wt_footprint ce (Tvariant orgs id) (fp_enum id orgs tag fid0 ofs0 pfp)).
        { eapply get_wt_footprint_wt; eauto. }
        inv WTFP.
        (* some rewrite *)
        rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
        assert (BM2: bmatch ce m2 b1 ofs2 (fp_enum id orgs tag fid0 ofs0 vfp)).
        { inv BM1. econstructor; eauto.
          (* prove that the location of the tag is unchanged *)
          eapply Mem.load_unchanged_on; eauto.
          simpl. intros. intro. destruct H0.
          exploit variant_field_offset_in_range; eauto. lia. }
        (* prove by I.H. *)
        eapply IHn. eauto. eauto. eauto.
        2: eauto.
        2: eapply BM2. all: eauto.        
        eapply Mem.unchanged_on_implies; eauto.
        intros. simpl. intro. destruct H1. subst. eapply H. 
        split; auto. clear H.                
        exploit variant_field_offset_in_range_complete; eauto.
        simpl. rewrite CO. lia.
Qed.


            
(* The location in (b, ofs) or in the footprint fp *)
Definition loc_in_footprint (b: block) (ofs sz: Z) (fp: footprint) :=
  fun b1 ofs1 =>
    (b1 = b /\ ofs <= ofs1 < ofs + sz) \/
      In b1 (footprint_flat fp).

(* The location out of (P1 and P2) is unchanged and the permission in
P1 is unchanged, if P1 and P2 are disjoint, then the permission in P1
or outside (P1 and P2) is unchanged. Here P1 is "in the range of (b, ofs) to (b, ofs + sz)" and P2 is "in the footprint fp" *)
Lemma perm_unchanged_in_loc: forall b ofs sz m1 m2 fp,
    Mem.unchanged_on (fun b1 ofs1 => ~ loc_in_footprint b ofs sz fp b1 ofs1) m1 m2 ->
    ~ In b (footprint_flat fp) ->
    (forall ofs2 k p,
        ofs <= ofs2 < ofs + sz ->
        Mem.perm m1 b ofs2 k p ->
        Mem.perm m2 b ofs2 k p) ->
    (* permission in b is unchanged *)
    (forall ofs2 k p,
        Mem.perm m1 b ofs2 k p ->
        Mem.perm m2 b ofs2 k p).
Proof.
  intros. 
  destruct (Z.le_decidable ofs ofs2).
  - destruct (Z.lt_decidable ofs2 (ofs + sz)).
    + eapply H1. lia. auto.
    + erewrite <- Mem.unchanged_on_perm; eauto.
      simpl. intro. red in H5.
      destruct H5. lia.
      congruence.
      eapply Mem.perm_valid_block; eauto.
  - erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. intro. red in H4. destruct H4.
    lia. congruence.
    eapply Mem.perm_valid_block; eauto.
Qed.


Lemma loc_in_footprint_subfield: forall b ofs co fty fofs fid ffp b1 ofs1 id fpl ce,
    co_sv co = Struct ->
    composite_consistent ce co ->
    field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    In (fid, fofs, ffp) fpl ->
    loc_in_footprint b (ofs + fofs) (sizeof ce fty) ffp b1 ofs1 ->
    loc_in_footprint b ofs (co_sizeof co) (fp_struct id fpl) b1 ofs1.
Proof.
  intros. red. red in H4.
  destruct H4.
  - destruct H4. subst. left.
    exploit field_offset_in_range_complete; eauto.
    lia.
  - right. simpl. eapply in_flat_map. eauto.
Qed.


(* sem_wt_loc version of bmatch_set_subpath_wt_val. It says that if
the modified location of the memory is sem_wt_loc, then the memory m2
also satisfies sem_wt_loc *)
Lemma set_wt_loc_set_subpath_wt_val: forall phl fp1 fp2 vfp m1 m2 b ofs b1 ofs1 ty1 vty pfp
    (WTLOC1: sem_wt_loc ce m1 fp1 b ofs)
    (* only changes the location which is updated with vfp. We should
    relax this condition to that the blocks in vfp can be "changed"
    when updating m1 to m2 because we do not care about their contents
    in m1 *)
    (UNC: Mem.unchanged_on (fun b2 ofs2 => ~ loc_in_footprint b1 ofs1 (sizeof ce vty) vfp b2 ofs2) m1 m2)
    (* We require that the permission in the range of (b1 ,ofs1) is
    unchanged, otherwise the (b1,ofs1) can be freed and breaks
    sem_wt_loc *)
    (PERMUNC: forall k p ofs2,
        ofs1 <= ofs2 < ofs1 + sizeof ce vty ->
        Mem.perm m1 b1 ofs2 k p ->
        Mem.perm m2 b1 ofs2 k p)
    (WTLOC2: sem_wt_loc ce m2 vfp b1 ofs1)
    (GFP: get_loc_footprint phl fp1 b ofs = Some (b1, ofs1, pfp))
    (SFP: set_footprint phl vfp fp1 = Some fp2)
    (WTFP1: wt_footprint ce ty1 fp1)
    (* relate ty1 and vty *)
    (WTPATH: wt_path ce ty1 phl vty)
    (* separation of fp *)
    (NOREP: list_norepet (footprint_flat fp1))
    (DIS1: ~ In b (footprint_flat fp1))
    (* The footprint to be set is disjoint with fp1 to make sure that
    fp2 is non-cyclic. If we expand vfp, we need to shrink fp1 !!!! So
    we should relax this premise to that we do not consider the blocks
    in pfp ! *)
    (* (DIS2: list_disjoint (b :: (footprint_flat fp1)) (footprint_flat vfp)) *)
    (DIS2: forall x y, In x (footprint_flat fp1) ->
                  ~ In x (footprint_flat pfp) ->
                  In y (footprint_flat vfp) ->
                  x <> y)
    (DIS3: ~ In b1 (footprint_flat vfp))
    (DIS4: ~ In b (footprint_flat vfp)),
    sem_wt_loc ce m2 fp2 b ofs.
Proof.
  intro phl. cut (exists n, length phl = n); eauto. intros (n & LEN).
  generalize dependent phl.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv GFP. inv SFP. auto.
  - eapply length_S_inv in LEN. destruct LEN as (phl' & ph & APP & LEN).
    subst.
    exploit get_loc_footprint_app_inv. eauto.
    intros (b2 & ofs2 & fp3 & A1 & A2).
    exploit set_footprint_app_inv. eauto.
    intros (fp3' & vfp' & B1 & B2 & B3).
    (* relate fp3 and fp3' *)
    exploit get_loc_footprint_eq. eapply A1. intros B1'.
    rewrite B1 in B1'. inv B1'.
    destruct ph; simpl in *.
    + destruct fp3; try congruence. inv A2. inv B2.
      (* prove that (b2, ofs2) is sem_wt_loc in m1 *)
      exploit sem_wt_subpath. eapply WTLOC1. eauto.
      intros WTLOC3. inv WTLOC3. inv WT.
      (* show that b1 <> b2 *)
      exploit get_loc_footprint_norepet. eauto. eapply A1. eauto.
      intros (N1 & N2). simpl in N2. eapply Decidable.not_or in N2.
      destruct N2 as (N3 & N4). 
      (* get the type vty *)
      eapply wt_path_deref_inv in WTPATH.
      destruct WTPATH as (ty1' & WTPATH & TYDEF).
      eapply type_deref_some in TYDEF. subst.
      (* prove that sz = (sizeof ce vty) *)
      exploit get_wt_footprint_wt. eapply WTPATH. eauto. eauto.
      intros WTFP2. inv WTFP2.
      (* prove that (b2, ofs2) is sem_wt_loc in m2 *)            
      assert (WTLOC3: sem_wt_loc ce m2 (fp_box b1 (sizeof ce vty) vfp) b2 ofs2).
      { econstructor.
        eapply Mem.load_unchanged_on; eauto. simpl. intros.
        unfold loc_in_footprint. intro. destruct H0.
        destruct H0. subst. intuition.
        exploit get_loc_footprint_in. eapply A1. intros IN. inv IN.
        congruence.
        eapply DIS2; eauto.
        (* sem_wt_val *)
        econstructor. eauto.
        (* perm *)
        red. intros.
        eapply perm_unchanged_in_loc. eauto. eauto. eauto. eauto.
        (* load the size record *)
        eapply Mem.load_unchanged_on; eauto.
        simpl. intros. intro. red in H0. destruct H0. lia.
        congruence. lia. }
      eapply IHn. eauto. eapply WTLOC1.
      3: eapply WTLOC3.
      (* unchanged_on *)
      instantiate (1 := (Tbox vty)).
      eapply Mem.unchanged_on_implies. eauto. simpl. intros. intro. eapply H.
      red in H1. destruct H1. destruct H1. subst. right. simpl. auto.
      red. right. simpl. auto.
      (* permission unchanged *)
      intros. erewrite <- Mem.unchanged_on_perm; eauto. 
      simpl. intro. red in H1. destruct H1. destruct H1. subst.
      auto.
      exploit get_loc_footprint_in. eapply A1. intros IN.
      inv IN. congruence.
      eapply DIS2; eauto. 
      eapply Mem.perm_valid_block. eauto.
      all: eauto.
      (* disjointness *)
      simpl. intros. destruct H1. subst.
      intro. apply H0. auto.
      eapply DIS2; eauto.
      (* DIS3 *)
      simpl. intro. destruct H. congruence.
      exploit get_loc_footprint_in. eapply A1. intros IN. inv IN. congruence.
      eapply DIS2; eauto.
      (* DIS4 *)
      simpl. intro. destruct H; auto. subst.
      exploit get_loc_footprint_incl. eapply A1. instantiate (1 := b).
      simpl. auto. intros. congruence.
    + destruct fp3; try congruence.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p. inv B2. inv A2.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      (* Get the type *)
      eapply wt_path_field_inv in WTPATH as (sid & orgs & co & WTPATH & CO & FTY & STR).
      assert (WTFP:  wt_footprint ce (Tstruct orgs sid) (fp_struct id fpl)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* get the field_offset of i *)
      rewrite CO in CO0. inv CO0.
      exploit WT1. eapply FTY. intros (ffpi & fofsi & E1 & E2 & E3).
      rewrite FIND in E1. inv E1.
      exploit find_fields_some. eapply FIND. intros (F1 & F2).
      exploit get_loc_footprint_norepet. eauto. eapply A1. eauto.
      intros (NOREP2 & NIN). simpl in NOREP2.
      assert (WTLOC3: sem_wt_loc ce m2 (fp_struct id (set_field i vfp fpl)) b1 ofs2).
      { econstructor. intros fid fofs ffp FIND1.
        destruct (ident_eq fid i); subst.
        (* fid = i: use WTLOC2 to prove *)
       - exploit find_fields_same_footprint. eauto. intro. subst.
         (* prove fofs = z *)
         exploit find_fields_same_offset. eauto. intros (vfp1 & F).
         rewrite FIND in F. inv F. auto.
       - exploit find_fields_same_offset; eauto.
         intros (vfp1 & FIND2).
         exploit find_fields_set_spec. eauto. erewrite FIND1.
         destruct peq; try congruence. intros. inv H.
         exploit WT2. eapply FIND2. intros (fty & FTY1 & FOFS & WTVFP1).
         exploit get_loc_footprint_sem_wt_loc. eapply WTLOC1. eauto.
         intros WTLOC1'. inv WTLOC1'.
         exploit FWT. eapply FIND2.
         intros WTLOC3.
         eapply sem_wt_loc_unchanged_loc. eauto. eauto.
         (* unchanged_on *)
         eapply Mem.unchanged_on_implies. eauto.
         simpl. intros. destruct H.
         (* block in vfp1 must be not in vfp and (b1, ofs2+fofsi) to (b1, ofs2+fofsi) *)
         + intro. red in H1.           
           exploit find_fields_some. eapply FIND2. intros (IN1 & IN2).
           destruct H1.
           * destruct H1. subst.             
             apply NIN. simpl.             
             eapply in_flat_map. exists (fid, fofs, vfp1). split; auto.
           (* The footprint of two different subfields are disjoint *)
           * destruct (in_dec eq_block b0 (footprint_flat ffpi)).
             (* To use DIS2, we need to discuss b0 is in ffpi or not *)
             -- exploit find_fields_some. eapply FIND. intros (IN3 & IN4).
                eapply footprint_norepet_fields_disjoint. eauto.
                eapply IN2. eapply IN4. auto. eauto. eauto. auto.
             -- exploit get_loc_footprint_incl. eapply A1.
                (* show that b0 in fp1 *)
                instantiate (1 := b0). simpl.
                eapply in_flat_map. exists (fid, fofs, vfp1). split; auto.
                intros IN5.
                eapply DIS2; eauto.
         + destruct H. subst.
           intro. red in H. destruct H.
           * destruct H.
             (* prove by the disjointness of two different fields in the struct *)
             exploit field_offset_no_overlap_simplified.
             eapply E2. eauto.
             eapply FOFS. eauto. auto. lia.
           * congruence. }
      (* prove by I.H. *)
      eapply IHn. eauto. eauto.
      3: eapply WTLOC3.
      instantiate (1 := Tstruct orgs id).
      (* unchanged on *)
      eapply Mem.unchanged_on_implies; eauto. simpl. rewrite CO.
      intros. intro. eapply H. clear H.
      eapply loc_in_footprint_subfield; eauto.
      exploit find_fields_some. eapply find_fields_set_spec with (fid2:=i); eauto.
      destruct peq; try congruence. intros (K1 & K2). eauto.
      (* permission unchanged *)
      intros. eapply perm_unchanged_in_loc; eauto.
      all: eauto.
      (* DIS2: discuss y in vfp or not *)
      intros. destruct (in_dec eq_block y (footprint_flat vfp)).
      eapply DIS2; eauto. intro. eapply H0.
      simpl. eapply in_flat_map. exists (i, fofsi, ffpi). eauto.
      (* These code used in DIS3 and DIS4, how to generalize it? *)
      assert (IN1: In y (footprint_flat (fp_struct id fpl))).
      { simpl. simpl in H1. eapply in_flat_map in H1.
        destruct H1 as (((fid & fofs) & ffp) & IN2 & IN3).
        exploit find_fields_split; eauto. intros (l1 & l2 & G1 & G2). subst.
        erewrite set_fields_split in IN2; eauto.
        eapply in_app in IN2. rewrite flat_map_app. simpl.
        rewrite !in_app.
        destruct IN2.
        - left. eapply in_flat_map; eauto.
        - inv H1.
          + inv H2. contradiction.
          + right. right. eapply in_flat_map; eauto. }
      intro. subst. contradiction.
      (* DIS3 *)
      intro. simpl in H. eapply in_flat_map in H.
      destruct H as (((fid & fofs) & ffp) & IN2 & IN3).
      eapply NIN. simpl.
      { exploit find_fields_split; eauto. intros (l1 & l2 & G1 & G2). subst.
        erewrite set_fields_split in IN2; eauto.
        eapply in_app in IN2. rewrite flat_map_app. simpl.
        rewrite !in_app.
        destruct IN2.
        - left. eapply in_flat_map; eauto.
        - inv H.
          + inv H0. contradiction.
          + right. right. eapply in_flat_map; eauto. }
      (* DIS4 *)
      intro. simpl in H. eapply in_flat_map in H.
      destruct H as (((fid & fofs) & ffp) & IN2 & IN3).
      eapply DIS1.
      eapply get_loc_footprint_incl. eauto. simpl.
      { exploit find_fields_split; eauto. intros (l1 & l2 & G1 & G2). subst.
        erewrite set_fields_split in IN2; eauto.
        eapply in_app in IN2. rewrite flat_map_app. simpl.
        rewrite !in_app.
        destruct IN2.
        - left. eapply in_flat_map; eauto.
        - inv H.
          + inv H0. contradiction.
          + right. right. eapply in_flat_map; eauto. }
    + destr_fp_enum fp3 ty. 
      inv A2. inv B2.
      exploit get_loc_footprint_sem_wt_loc. eapply WTLOC1. eapply A1.
      intros WTLOC1'. inv WTLOC1'.
      eapply wt_path_downcast_inv in WTPATH as (id1 & orgs1 & co & EQTY & WTPATH & CO & FTY & ENUM ). symmetry in EQTY. inv EQTY.
      assert (WTFP:  wt_footprint ce (Tvariant orgs id) (fp_enum id orgs tag fid0 ofs0 pfp)).
      { eapply get_wt_footprint_wt; eauto. }
      inv WTFP.
      (* some rewrite *)
      rewrite CO in CO0. inv CO0. rewrite FTY in FTY0. inv FTY0.
      assert (WTLOC3: sem_wt_loc ce m2 (fp_enum id orgs tag fid0 ofs0 vfp) b1 ofs2).
      { econstructor.
        (* load tag *)
        eapply Mem.load_unchanged_on. eauto.
        simpl. intros. intro. red in H0.
        destruct H0. destruct H0.
        exploit variant_field_offset_in_range_complete; eauto. lia.
        congruence.
        auto. auto. }
      eapply IHn. eauto. eauto.
      3: eapply WTLOC3.
      instantiate (1 := Tvariant orgs id).
      (* unchanged on *)
      simpl. rewrite CO. eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. intro. eapply H.
      red. red in H1. simpl. destruct H1; auto.
      left. destruct H1. subst. split; auto.
      exploit variant_field_offset_in_range_complete; eauto. lia.
      (* perm unchanged *)
      intros. eapply perm_unchanged_in_loc; eauto.
      all: eauto.
Qed.

Lemma init_place_full_unchanged: forall own p p1,
    is_full (own_universe own) p = is_full (own_universe (init_place own p1)) p.
Proof.
  intros. unfold is_full, init_place. simpl. auto.
Qed.

Lemma list_disjoint_app_r {A: Type}: forall (l1 l2 l3: list A),
    list_disjoint l1 (l2 ++ l3) ->
    list_disjoint l1 l2 /\ list_disjoint l1 l3.
Proof.
  intros. red in H. split.
  red. intros. eapply H; auto. eapply in_app; eauto.
  red. intros. eapply H; auto. eapply in_app; eauto.
Qed.

Lemma list_disjoint_app_l {A: Type}: forall (l1 l2 l3: list A),
    list_disjoint (l1 ++ l2) l3 ->
    list_disjoint l1 l3 /\ list_disjoint l2 l3.
Proof.
  intros. eapply list_disjoint_sym in H.
  eapply list_disjoint_app_r in H. destruct H.
  split; apply list_disjoint_sym; auto.
Qed.

(* Because we have normal assignment and enum assignment, to reuse the
proof, we write this assign_loc_sound_gen lemma. It uses UNC1, UNC2
and WTLOC to replace the assign_loc premise to simulate the actual
assignment process. This generalization can handle both normal
assginment and enum assignment. *)
Lemma assign_loc_sound_gen: forall fpm1 m1 m2 own1 own2 b ofs p vfp pfp e ty
    (MM: mmatch fpm1 ce m1 e own1)
    (TY: ty = typeof_place p)    
    (* (AS: assign_loc ce ty m1 b ofs v m2) *)
    (UNC1: Mem.unchanged_on (fun b1 ofs1 => ~ (b1 = b /\ Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + sizeof ce ty)) m1 m2)
    (UNC2: forall b1 ofs1 k p, Mem.perm m1 b1 ofs1 k p <-> Mem.perm m2 b1 ofs1 k p)
    (WTLOC: sem_wt_loc ce m2 vfp b (Ptrofs.unsigned ofs))
    (* (AL: (alignof ce ty | Ptrofs.unsigned ofs)) *)
    (* (CAST: val_casted v ty) *)
    (NOREPVFP: list_norepet (footprint_flat vfp))
    (* (WT: sem_wt_val ce m1 vfp v) *)
    (WFENV: wf_env fpm1 ce m1 e)
    (WTFP: wt_footprint ce ty vfp)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm1 = Some (b, (Ptrofs.unsigned ofs), pfp))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (NOREP: list_norepet (footprint_of_env e ++ (flat_fp_map fpm1)))
    (* vfp and fpm1 are disjoint so that their combination is separated *)
    (DIS1: list_disjoint (footprint_flat vfp) (footprint_of_env e ++ (flat_fp_map fpm1)))
    (WFOWN: wf_own_env e ce own1),
  exists fpm2, set_footprint_map (path_of_place p) vfp fpm1 = Some fpm2
          /\ mmatch fpm2 ce m2 e own2
          /\ list_norepet (footprint_of_env e ++ (flat_fp_map fpm2))
          /\ wf_env fpm2 ce m2 e.
Proof.
  intros. destruct (path_of_place p) eqn: POP.
  exploit get_set_footprint_map_exists; eauto.
  instantiate (1 := vfp).
  intros (fpm2 & A & B). exists fpm2. split. auto.
  eapply list_norepet_app in NOREP.
  destruct NOREP as (NOREP1 & NOREP1' & DIS2).
  eapply list_disjoint_app_r in DIS1. destruct DIS1 as (DIS3 & DIS4).  
  assert (NOREP2: list_norepet (flat_fp_map fpm2)).
  { eapply set_disjoint_footprint_norepet. eauto. eauto. eauto.
    eapply list_disjoint_sym. auto. }
  assert (DIS5: list_disjoint (footprint_of_env e) (flat_fp_map fpm2)).
  { red. intros.
    eapply set_footprint_map_incl in H0; eauto. destruct H0; eauto.
    intro. subst. eapply DIS3; eauto. }
  assert (NOREP3: list_norepet ((footprint_of_env e) ++ (flat_fp_map fpm2))).
  { eapply list_norepet_app; eauto. }
  (* set wt_footprint remains wf_env *)
  assert (WFENV2: wf_env fpm2 ce m2 e).
  {  (**  how to show that set a wt footprint remains wt: use the fact
  that p is well-typed?? *)
    eapply wf_env_perm_unchanged. eauto.
    eapply Mem.unchanged_on_support; eauto.
    eapply wf_env_set_wt_footprint. eauto. erewrite <- TY.
    eauto. auto. rewrite POP. auto. }
  (* show that (b, ofs) does not locate in size record *)
  assert (NSZREC: forall b1 ofs1 fp1, loc_of_size_record_fp fp1 b1 ofs1 ->
                                 ~ (b1 = b /\ Ptrofs.unsigned ofs <= ofs1 < Ptrofs.unsigned ofs + sizeof ce ty)).
  { intros. intro. destruct H0. subst.
    do 2 red in H. destruct H.
    generalize (Ptrofs.unsigned_range ofs). lia. }
  repeat apply conj; auto.
  (* mmatch *)
  - red. intros until fp.
    intros GFP INIT.
    unfold own_transfer_assign in CKAS.
    destruct (is_prefix p p0) eqn: PRE.
    (**  Case 1: p0 is children of p1: we need to prove that the
    value/location of p0 is sem_wt *)
    + exploit is_prefix_paths_app; eauto.
      rewrite POP. simpl.
      destruct (path_of_place p0) eqn: POP0. simpl.
      intros (P1 & (phl & P2)). subst.
      (* show that fp is subpath of vfp and (b0, ofs0) is sem_wt_loc
      which requires that (b1,ofs) is sem_wt_loc. *)
      exploit get_loc_footprint_map_app_inv; eauto.
      intros (b1 & ofs1 & fp1 & D & E). rewrite B in D. inv D.
      (* prove that assign_loc assigns a sem_wt_val then the location
      is sem_wt_loc *)
      (* exploit assign_loc_sem_wt; eauto.       *)
      (** b1 is not in fp1. Use B to show that location and its
      footprint are disjoint *)
      (* exploit get_loc_footprint_map_norepet. eapply NOREP2. eapply B. eauto. eauto. *)
      (* intuition.       *)
      (* intros WTLOC. *)
      exploit sem_wt_subpath; eauto.
      intros WTLOC1.
      (* sem_wt_loc implies bmatch *)
      exploit sem_wt_loc_implies_bmatch; eauto.
    (** Case 2: p0 is not children of p1 *)
    + assert (INIT1: is_init own1 p0 = true).
      { subst. destruct (is_init own1 p0) eqn: I; auto.
        exploit init_irrelavent_place_still_not_owned; eauto. }
      destruct (is_prefix p0 p) eqn: PRE1.
      (* p0 is prefix of p. It is possible that p0 is a shallow prefix
      of p !!! It is the situation where overriding a field of an
      initialized struct ! *)
      * exploit is_prefix_paths_app; eauto.
        destruct (path_of_place p0) eqn: POP2.
        rewrite POP. simpl. intros (? & (phl & P1)). subst.
        exploit get_loc_footprint_map_app_inv. eapply PFP.
        intros (b2 & ofs2 & fp3 & A1 & A2). 
        exploit get_set_footprint_map_app_inv. eapply A1. eauto.
        intros (fp4 & G1 & G2).
        rewrite GFP in G1. inv G1.
        exploit MM. erewrite POP2. eauto. eauto.
        intros (BM1 & FULL1).
        exploit wf_own_wt_place. eauto.
        eapply is_init_in_universe. eapply INIT1. intros WTP0.
        assert (WTPH: wt_path ce (typeof_place p0) phl (typeof_place p)).
        { exploit wt_place_wt_local. eapply WTP.
          intros (b1 & ty1 & ETY). rewrite local_of_paths_of_place in ETY.
          rewrite POP in ETY. simpl in ETY.          
          eapply wt_path_app.          
          eapply wt_place_wt_path; eauto.
          eapply wt_place_wt_path; eauto. }
        exploit get_loc_footprint_map_norepet. eapply NOREP1'. eapply A1. eauto.
        intros (N1 & NOTIN).
        split.
        (** task1: prove bmatch m2 b2 ofs2 fp4 using bmatch_set_subpath_wt_val *)
        eapply bmatch_set_subpath_wt_val. eauto.
        eapply get_loc_footprint_map_pos; eauto.        
        eauto.
        (* blocks_perm_unchanged_fp: the assignment does not change
        permission of memory *)
        eapply blocks_perm_unchanged_normal. eauto.
        eapply sem_wt_loc_implies_bmatch. eauto. eauto. auto.
        (* wt_footprint *)
        instantiate (1 := typeof_place p0).
        eapply get_wt_place_footprint_wt. eapply WFENV. auto.
        rewrite POP2. eauto.
        (* wt_path *)
        eauto.
        (* list_norepet *)
        auto. auto.
        (** Task2: prove sem_wt_loc of (b2,ofs2) *)
        (* full -> sem_wt_loc *)
        intros FULL2.
        (* exploit assign_loc_sem_wt; eauto. *)
        (* b is not in vfp *)
        (* exploit get_loc_footprint_map_norepet. eapply NOREP2. eapply B. eauto. *)
        (* intuition. *)
        (* intros WTLOC. *)
        assert (FULL3: is_full (own_universe own1) p0 = true).
        { erewrite init_place_full_unchanged. eauto. }
        exploit FULL1. auto.
        intros WTLOC1.
        eapply set_wt_loc_set_subpath_wt_val; eauto.
        (* unchanged_on *)
        eapply Mem.unchanged_on_implies.
        eauto. simpl. intros.
        intro. eapply H. destruct H1. subst. red. left; auto.
        (* perm unchanged *) 
        intros. erewrite <- UNC2; eauto.
        (* wt_footprint *)
        eapply get_wt_place_footprint_wt. eapply WFENV. auto.
        rewrite POP2. eauto.
        (* disjointness of fp3 and vfp *)
        intros. eapply list_disjoint_sym in DIS4.
        eapply DIS4; auto.
        eapply get_loc_footprint_map_incl; eauto.
        (* b not in vfp *)
        exploit get_loc_footprint_map_norepet. eapply NOREP2.
        eapply B. auto. intuition.
        (* b2 not in vfp: proved by DIS3 and DIS4 *)
        exploit get_loc_footprint_map_in_range. eapply A1. intros IN.
        eapply in_app in IN. destruct IN.
        intro. eapply DIS3; eauto.
        intro. eapply DIS4; eauto.
      (** Case 3: p0 is not a prefix of p, so p0 and p are disjoint place *)
      * exploit is_not_prefix_disjoint; eauto.
        destruct (path_of_place p0) eqn: POP2. rewrite POP. simpl.
        destruct (ident_eq i0 i); subst.
        intros [P1|P2]; try congruence.
        (** DIFFICULT: two locals are equal but their paths are disjoint *)
        --   (** How to know p0 is well-typed or not? *)
          erewrite <- get_set_disjoint_paths in GFP; eauto.
          (* bmatch m1 b0 ofs0 fp *)
          exploit MM. erewrite POP2. eauto. auto.
          intros (BM0 & FULL0).
          (* pfp is well-typed *)
          exploit get_wt_place_footprint_wt. eapply WFENV. eauto.
          erewrite POP. eauto. intros WTPFP.
          (** prove that (b, ofs) and (b0, ofs0) are disjoint *)
          unfold get_loc_footprint_map in PFP, GFP.
          destruct (e!i) eqn: E1; try congruence. destruct p1.
          destruct (fpm1 ! i) eqn: E2; try congruence.
          (* prove fp is wt_footprint *)
          exploit wf_env_footprint. eapply WFENV. eauto. intros (fp1 & E3 & E4).
          rewrite E2 in E3. inv E3.          
          exploit get_wt_footprint_exists_wt.
          eauto. eapply get_loc_footprint_eq; eauto.
          intros (ty1 & E5 & E6).
          exploit get_loc_footprint_disjoint_paths. eauto. eapply paths_disjoint_sym; eauto. 
          instantiate (1 := fp1). eapply norepet_flat_fp_map_element; eauto.
          4: eapply PFP. 4: eapply GFP.
          eauto. eapply wt_place_wt_path; eauto. eauto.
          3: { eapply paths_disjoint_sym. auto. }
          (* b1 is not in fp1 *)
          intro. eapply DIS2. eapply in_footprint_of_env; eauto.
          eapply in_footprint_flat_fp_map; eauto. auto.
          (** Two cases *)
          destruct (eq_block b b0). subst.
          (* Case1: b = b0 *)
          ++ intros ([C1|[C2|C3]] & I1 & I2 & I3); try congruence.
             ** split.
                eapply bmatch_unchanged_on_loc; eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eauto.
                (** sem_wt_loc *)
                intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC1.
                eapply sem_wt_loc_unchanged_loc. eauto. eauto.                
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl.
                destruct H0.
                (** prove b must be not in fp *)
                intro. destruct H2. subst.
                congruence.
                lia.
             (* The same as above *)
             ** split.
                eapply bmatch_unchanged_on_loc; eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eauto.
                (** sem_wt_loc *)
                intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC1.
                eapply sem_wt_loc_unchanged_loc. eauto.
                eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl.
                destruct H0.
                (** prove b must be not in fp *)
                intro. destruct H2. subst.
                congruence.
                lia.
          (* Case2: b <> b0 *)
          ++ intros (N & I1 & I2 & I3). clear N. split.
             ** eapply bmatch_unchanged_on_block. eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. destruct H; try lia.
                eapply NSZREC. eauto.
                eapply blocks_perm_unchanged_normal.
                eauto.
             (** sem_wt_loc  *)
             ** intros. exploit FULL0.
                erewrite init_place_full_unchanged. eauto.
                intros WTLOC1.
                eapply sem_wt_loc_unchanged_blocks. eauto.
                eapply Mem.unchanged_on_implies. eauto.
                intros. simpl. intro. destruct H2. subst.
                destruct H0; try congruence.
                (** prove b must be not in fp: use the fact that
                "disjoint locations have disjoint footprints" *)                
        -- exploit get_loc_footprint_map_different_local. eapply NOREP3.
           2: eapply B. eauto. eauto. intros (N1 & N2 & N3).
           intros. clear H.
           erewrite <- get_set_different_local in GFP; eauto. 
           exploit MM. erewrite POP2. eauto. auto.           
           intros (BM1 & FULL1).
           split.
           eapply bmatch_unchanged_on_block. eauto.
           eapply Mem.unchanged_on_implies. eauto.
           intros. simpl. destruct H; try lia.
           eapply NSZREC. eauto.
           eapply blocks_perm_unchanged_normal.
           eauto.
           (** sem_wt_loc *)
           intros FULL2.
           subst.
           erewrite <- init_place_full_unchanged in FULL2.
           exploit FULL1; eauto. intros WTLOC2.
           eapply sem_wt_loc_unchanged_blocks. eauto.
           eapply Mem.unchanged_on_implies. eauto. intros. simpl.
           destruct H; auto.
           (* b1 is in the fp: show that b must not be in the fp *)
           intro. destruct H1; subst. congruence.
           subst. intro. destruct H. subst. congruence.
Qed.


(** Important Lemma: we need to say that the footprint inside a struct
is also disjoint !!! *)
(* Consider assign to a variant? *)
Lemma assign_loc_sound: forall fpm1 m1 m2 own1 own2 b ofs v p vfp pfp e ty
    (MM: mmatch fpm1 ce m1 e own1)
    (TY: ty = typeof_place p)
    (AS: assign_loc ce ty m1 b ofs v m2)
    (AL: (alignof ce ty | Ptrofs.unsigned ofs))
    (CAST: val_casted v ty)
    (NOREPVFP: list_norepet (footprint_flat vfp))
    (WT: sem_wt_val ce m1 vfp v)
    (WFENV: wf_env fpm1 ce m1 e)
    (WTFP: wt_footprint ce ty vfp)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm1 = Some (b, (Ptrofs.unsigned ofs), pfp))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (NOREP: list_norepet (footprint_of_env e ++ (flat_fp_map fpm1)))
    (* vfp and fpm1 are disjoint so that their combination is separated *)
    (DIS1: list_disjoint (footprint_flat vfp) (footprint_of_env e ++ (flat_fp_map fpm1)))
    (WFOWN: wf_own_env e ce own1),
  exists fpm2, set_footprint_map (path_of_place p) vfp fpm1 = Some fpm2
          /\ mmatch fpm2 ce m2 e own2
          /\ list_norepet (footprint_of_env e ++ (flat_fp_map fpm2))
          /\ wf_env fpm2 ce m2 e.
Proof.
  intros. eapply assign_loc_sound_gen; eauto.
  eapply assign_loc_unchanged_on; eauto.
  eapply assign_loc_perm_unchanged; eauto.
  eapply assign_loc_sem_wt; eauto.
  destruct (path_of_place p) eqn: POP.
  exploit get_loc_footprint_map_in_range; eauto.
  intros IN. intro. eapply DIS1; eauto.
Qed.

Lemma sizeof_variant_ge4_complete: forall ce co,
    composite_consistent ce co ->
    co_sv co = TaggedUnion ->
    4 <= co_sizeof co.
Proof.
  intros. erewrite co_consistent_sizeof; eauto.
  rewrite H0. simpl.
  generalize (co_alignof_pos co). intros A1.
  generalize (align_le (sizeof_variant ce0 (co_members co)) (co_alignof co) A1).
  intros.
 generalize (sizeof_variant_ge4 ce0 (co_members co)). lia.
Qed.

Lemma variant_field_offset_aligned_add: forall ofs fofs id orgs co fid fty,
    ce ! id = Some co ->
    co_sv co = TaggedUnion ->
    variant_field_offset ce fid (co_members co) = OK fofs ->
    field_type fid (co_members co) = OK fty ->
    (alignof ce (Tvariant orgs id) | ofs) ->
    (alignof ce fty | ofs + fofs).
Proof.
  intros.
  eapply Z.divide_add_r.
  eapply Z.divide_trans; eauto.
  simpl. rewrite H.
  erewrite co_consistent_alignof; eauto. 
  eapply field_alignof_divide_composite; eauto.
  eapply variant_field_offset_aligned; eauto.
Qed.

(* Enum assignment preserves the invariant *)
Lemma assign_loc_variant_sound: forall fpm1 m1 m2 m3 own1 own2 b ofs v p vfp pfp e ty id fty fid fofs orgs co tag
    (MM: mmatch fpm1 ce m1 e own1)
    (TY: ty = typeof_place p)
    (PTY: typeof_place p = Tvariant orgs id)
    (CO: ce ! id = Some co)
    (ENUM: co.(co_sv) = TaggedUnion)
    (AS: assign_loc ce fty m1 b (Ptrofs.add ofs (Ptrofs.repr fofs)) v m2)
    (STAG: Mem.storev Mint32 m2 (Vptr b ofs) (Vint (Int.repr tag)) = Some m3)
    (FOFS: variant_field_offset ce fid (co_members co) = OK fofs)
    (FTY: field_type fid (co_members co) = OK fty)
    (FTAG: field_tag fid co.(co_members) = Some tag)
    (AL: (alignof ce ty | Ptrofs.unsigned ofs))
    (RANGE: Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.max_unsigned)
    (CAST: val_casted v fty)
    (NOREPVFP: list_norepet (footprint_flat vfp))
    (WT: sem_wt_val ce m1 vfp v)
    (WFENV: wf_env fpm1 ce m1 e)
    (WTFP: wt_footprint ce fty vfp)
    (* The path of this place and the path of the footprint fo p (which is not used) *)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm1 = Some (b, (Ptrofs.unsigned ofs), pfp))
    (* ownership transfer *)
    (CKAS: own_transfer_assign own1 p = own2)
    (WTP: wt_place (env_to_tenv e) ce p)
    (NOREP: list_norepet (footprint_of_env e ++ (flat_fp_map fpm1)))
    (* vfp and fpm1 are disjoint so that their combination is separated *)
    (DIS1: list_disjoint (footprint_flat vfp) (footprint_of_env e ++ (flat_fp_map fpm1)))
    (WFOWN: wf_own_env e ce own1),
  (* The footprint to be set must be fp_enum *)
  exists fpm2, set_footprint_map (path_of_place p) (fp_enum id orgs tag fid fofs vfp) fpm1 = Some fpm2
          /\ mmatch fpm2 ce m3 e own2
          /\ list_norepet (footprint_of_env e ++ (flat_fp_map fpm2))
          /\ wf_env fpm2 ce m3 e.
Proof.
  intros.
  assert (WTFP1: wt_footprint ce ty (fp_enum id orgs tag fid fofs vfp)).
  { subst. rewrite PTY.
    exploit field_type_implies_field_tag; eauto.
    intros (tag1 & A1 & A2). rewrite FTAG in A1. inv A1.
    econstructor; eauto. }
  exploit variant_field_offset_in_range_complete; eauto.
  intros (F1 & F2).
  assert (SZEQ: sizeof ce (typeof_place p) = co_sizeof co).
  { rewrite PTY. simpl. rewrite CO. auto. }
  assert (OFSEQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr fofs)) =
                   Ptrofs.unsigned ofs + fofs).
  { generalize (sizeof_pos ce fty). intros F3.
    generalize (Ptrofs.unsigned_range ofs). intros F4.
    subst. rewrite SZEQ in *.
    erewrite Ptrofs.add_unsigned.
    rewrite Ptrofs.unsigned_repr. 1-2: rewrite Ptrofs.unsigned_repr; auto.
    lia. lia. lia. }
  assert (NIN: ~ In b (footprint_flat vfp)).
  { destruct (path_of_place p) eqn: POP.
    exploit get_loc_footprint_map_in_range; eauto.
    intros IN. intro. eapply DIS1; eauto. }
  eapply assign_loc_sound_gen; eauto.
  (* unchanged_on *)
  eapply Mem.unchanged_on_trans.
  eapply Mem.unchanged_on_implies.
  eapply assign_loc_unchanged_on; eauto. simpl.
  intros. intro. eapply H. destruct H1; subst. clear H.
  split; auto.
  rewrite OFSEQ in *. rewrite SZEQ. lia.  
  eapply Mem.store_unchanged_on; eauto.
  intros. intro. eapply H0.
  split; auto.      
  subst. rewrite PTY. simpl. rewrite CO.
  simpl in H.
  exploit CONSISTENT; eauto. intros.
  generalize (sizeof_variant_ge4_complete ce co H1 ENUM); eauto. lia.
  (* permission unchanged *)
  intros. split.
  intros. eapply Mem.perm_store_1. eauto.
  erewrite <- assign_loc_perm_unchanged; eauto.
  intros. eapply assign_loc_perm_unchanged; eauto.
  eapply Mem.perm_store_2; eauto. 
  (* sem_wt_loc *)
  econstructor.
  erewrite Mem.load_store_same; eauto.
  auto.
  eapply sem_wt_loc_unchanged_loc; eauto.  
  rewrite <- OFSEQ.
  eapply assign_loc_sem_wt; eauto.
  (* alingment *)  
  rewrite OFSEQ.
  eapply variant_field_offset_aligned_add; eauto.
  rewrite <- PTY. rewrite <- TY. auto.
  (* unchanged on location *)
  eapply Mem.store_unchanged_on; eauto.
  simpl. intros. intro. destruct H0. congruence.
  destruct H0.
  exploit variant_field_offset_in_range_complete; eauto. lia.
Qed.  
  
  
Lemma sem_cast_sem_wt: forall m fp v1 v2 ty1 ty2,
    sem_wt_val ce m fp v1 ->
    wt_footprint ce ty1 fp ->
    RustOp.sem_cast v1 ty1 ty2 = Some v2 ->
    (* The scalar type in the footprint may be changed *)
    exists fp', sem_wt_val ce m fp' v2
           /\ wt_footprint ce ty2 fp'
           /\ footprint_flat fp = footprint_flat fp'.
Proof.
  destruct ty1; intros until ty2; intros WTVAL WTFP CAST; inv WTFP; inv WTVAL;
    destruct ty2; (unfold sem_cast in CAST; simpl in CAST; DestructCases); try congruence.
  all: try (eexists; repeat apply conj; econstructor;eauto).
  inv WTLOC.
  econstructor; eauto.
Qed.

Lemma sem_cast_sem_wt_exists: forall m fp v1 ty,
    sem_wt_val ce m fp v1 ->
    wt_footprint ce ty fp ->
    exists v2, sem_cast v1 ty ty = Some v2.
Proof.
  intros until ty. intros WTVAL WTFP.
  destruct ty; DestructCases; inv WTFP; inv WTVAL; simpl in *; try congruence; try (eexists; reflexivity).
  - eexists. unfold sem_cast. simpl.
    destruct i; eauto.
  - unfold sem_cast. simpl.
    rewrite dec_eq_true. eexists. reflexivity.
  - unfold sem_cast. simpl.
    rewrite dec_eq_true. eexists. reflexivity.
  - unfold sem_cast. simpl.
    rewrite dec_eq_true. eexists. reflexivity.
Qed.

Lemma sem_cast_val_footprint_unchanged: forall v1 v2 ty1 ty2,
    sem_cast v1 ty1 ty2 = Some v2 ->
    footprint_of_val v1 = footprint_of_val v2.
Proof.
  destruct ty1; intros until ty2; intros CAST;
    destruct ty2; (unfold sem_cast in CAST; simpl in CAST; DestructCases); try congruence;
    simpl; auto.
Qed.

(* The evaluation of a list of expression produces a list of footprint and a list of values which are sem_wt_val *)
Lemma eval_exprlist_sem_wt: forall al vl tyl fpm1 m le own1 own2 init uninit init1 uninit1 universe
    (MM: mmatch fpm1 ce m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_of_env le) (flat_fp_map fpm1))
    (EVAL: eval_exprlist ce le m ge al tyl vl)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_exprlist ce init uninit universe al = Some (init1, uninit1))
    (OWN: move_place_list own1 (moved_place_list al) = own2)
    (WFENV: wf_env fpm1 ce m le)
    (WT: wt_exprlist le ce al)
    (WFOWN: wf_own_env le ce own1),
  exists fpl fpm2,
    sem_wt_val_list ce m fpl vl
    /\ wt_footprint_list ce (type_list_of_typelist tyl) fpl
    /\ mmatch fpm2 ce m le own2
    /\ wf_env fpm2 ce m le
    (* footprint disjointness *)
    /\ list_norepet (flat_map footprint_flat fpl ++ flat_fp_map fpm2)
    /\ list_equiv (flat_map footprint_flat fpl ++ flat_fp_map fpm2) (flat_fp_map fpm1)
    (* it is satisfied trivially because we just move out a place *)
    /\ wf_own_env le ce own2
    /\ val_casted_list vl tyl.
Proof.
  induction al; intros.
  - inv EVAL. simpl in *.
    exists nil, fpm1.
    repeat apply conj; auto.
    econstructor. econstructor.
    simpl. red. intros. reflexivity.
    econstructor.
  - inv EVAL. inv WT.
    simpl in CHECK.
    destruct (move_check_expr ce init uninit universe) eqn: MOVE1; try congruence.
    destruct p as (init2, uninit2).
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce init uninit universe a) eqn: MOVECKE; try congruence.
    (* construct sem_wt_val for v2 *)
    exploit eval_expr_sem_wt; eauto.
    intros (fp2 & fpm2 & WTVAL1 & WTFP1 & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp2' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own1 (moved_place a)) init2 uninit2 universe).
    { destruct (moved_place a) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    (* show fpm2 is norepet *)
    generalize NOREP1 as NOREP2. intros.
    eapply list_norepet_app in NOREP2 as (N1 & N2 & N3).
    assert (DIS1: list_disjoint (footprint_of_env le) (flat_fp_map fpm2)).
    { red. intros.
      eapply DIS. eauto.
      eapply EQUIV1. eapply in_app; auto. }
    exploit IHal; eauto.
    intros (fpl & fpm3 & WTVAL3 & WTFP3 & MM2 & WFENV2 & NOREP2 & EQUIV2 & WFOWN2 & CAST).
    exists (fp2' :: fpl), fpm3.
    repeat apply conj; auto.
    + econstructor; eauto.
    + econstructor; eauto.
    + simpl. destruct (moved_place a); auto.
    + simpl. rewrite <- app_assoc.
      eapply list_norepet_app.
      repeat apply conj; auto.
      red. intros. eapply N3; auto.
      eapply EQUIV2. auto.
    + simpl. red. intros.
      split; intros.
      eapply EQUIV1. rewrite !in_app in H.
      repeat destruct H; try (eapply in_app; eauto).
      right. eapply EQUIV2. eapply in_app; auto.
      right. eapply EQUIV2. eapply in_app; auto.
      rewrite !in_app. eapply EQUIV1 in H.
      rewrite !in_app in H.
      destruct H; auto.
      eapply EQUIV2 in H.  rewrite !in_app in H. destruct H; auto.
    + simpl. destruct (moved_place a); auto.
    + econstructor; eauto.
      eapply cast_val_is_casted; eauto.               
Qed.

(** Soundness of function_entry  *)


Lemma analyze_collect_func_inv: forall f cfg entry ce init uninit universe,
    analyze ce f cfg entry = OK (init, uninit, universe) ->
    collect_func ce f = OK universe.
Proof.
  intros. unfold analyze in H.
  destruct (collect_func ce0 f) eqn: A; simpl in H; try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer t true f cfg) entry
          (IM.State
             (add_place_list t (places_of_locals (fn_params f))
                (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) t)))); try congruence.
  destruct (DS.fixpoint cfg successors_instr (transfer t false f cfg) entry
          (IM.State
             (remove_place_list (places_of_locals (fn_params f))
                (add_place_list t (places_of_locals (fn_params f ++ fn_vars f))
                   (PTree.map (fun (_ : positive) (_ : LPaths.t) => Paths.empty) t))))); try congruence.
  destruct (IM.lub t0 !! entry t1 !! entry); try congruence.
  destruct PathsMap.beq; try congruence.
Qed.


Lemma alloc_variables_wf_env: forall l e1 e2 fpm1 m1 m2 ce
    (WFENV: wf_env fpm1 ce m1 e1)
    (ALLOC: alloc_variables ce e1 m1 l e2 m2)
    (NOREP: list_norepet (var_names l))
    (* (NIN: (forall id ty, In (id, ty) l -> fpm1 ! id = None)) *)
    (NOCY: forall id ty, In (id, ty) l -> check_cyclic_struct ce ty = true)
    (VALIDTYS: forall id ty, In (id, ty) l -> valid_type ty = true),
    wf_env (init_footprint_map ce l fpm1) ce m2 e2.
Proof.
  induction l; intros.
  - inv ALLOC. simpl. eauto.
  - inv ALLOC. simpl in *.
    eapply IHl. 2: eauto.
    (* wf_env *)
    econstructor; intros.
    rewrite PTree.gsspec in *. destruct peq. inv H.
    eexists. split; eauto.
    eapply type_to_empty_footprint_wt. eapply NOCY. eauto.
    eapply wf_env_footprint; eauto.
    rewrite PTree.gsspec in *. destruct peq. inv H.
    split.
    red. intros. eapply Mem.perm_alloc_2; eauto.
    eapply Mem.valid_new_block; eauto.
    exploit wf_env_freeable. eapply WFENV. eauto.
    intros (PERM & VAL).
    split.
    red. intros. erewrite <- Mem.unchanged_on_perm. eauto.
    eapply Mem.alloc_unchanged_on with (P:= fun _ _ => True); eauto. simpl. auto. auto.
    eapply Mem.valid_block_alloc; eauto.
    (* NOREP *)
    inv NOREP. auto.
    (* check_cyclic_struct  *)
    intros. eapply NOCY; eauto.
    (* valid_type *)
    intros. eapply VALIDTYS; eauto.
Qed.
   
Lemma alloc_variables_norepet: forall l e1 e2 m1 m2 ce
    (ALLOC: alloc_variables ce e1 m1 l e2 m2)
    (VALID: forall id b ty, e1 ! id = Some (b, ty) -> Mem.valid_block m1 b)
    (* (NIN: forall id ty, In (id, ty) l -> e1 ! id = None) *)
    (NOREP: list_norepet (footprint_of_env e1)),
    list_norepet (footprint_of_env e2)
    /\ (forall id b ty, e2 ! id = Some (b, ty) ->                  
                  ~ Mem.valid_block m1 b \/ e1 ! id = Some (b, ty)).
Proof.
  induction l; intros.
  - inv ALLOC. split; eauto.
  - inv ALLOC. exploit IHl. eauto.
    (* VALID *)
    intros. rewrite PTree.gsspec in H.
    destruct peq. inv H. eapply Mem.valid_new_block; eauto.
    eapply Mem.valid_block_alloc. eauto. eauto.
    (* NOREP *)
    eapply set_env_footprint_norepet; eauto.
    intro. exploit in_footprint_of_env_inv; eauto.
    intros (id1 & ty1 & A). eapply VALID in A.
    eapply Mem.fresh_block_alloc; eauto.
    intros (NOREP1 & NV). split; auto.
    intros. exploit NV; eauto.
    intros [A1|A2].
    left. intro. eapply A1. eapply Mem.valid_block_alloc; eauto.
    rewrite PTree.gsspec in A2.
    destruct peq. inv A2. left.
    eapply Mem.fresh_block_alloc; eauto.
    auto.
Qed.

Lemma alloc_variables_unchanged_on: forall l e1 e2 m1 m2 ce P
    (ALLOC: alloc_variables ce e1 m1 l e2 m2),
    Mem.unchanged_on P m1 m2.
Proof.
  induction l; intros.
  inv ALLOC. eapply Mem.unchanged_on_refl.
  inv ALLOC. eapply Mem.unchanged_on_trans.
  eapply Mem.alloc_unchanged_on; eauto.
  eauto.
Qed.

Lemma mmatch_no_init_place: forall own m fpm le,
    (forall p, is_init own p = false) ->
    mmatch fpm ce m le own.
Proof.
  intros.
  red. intros. congruence.
Qed.

Lemma wf_env_empty: forall fpm ce m,
    wf_env fpm ce m empty_env.
Proof.
  intros. constructor; intros; rewrite PTree.gempty in H; try congruence.
Qed.

  
Lemma bind_parameters_sound: forall pl vl fpl fpm1 m1 m2 own1 own2 le
   (MM: mmatch fpm1 ce m1 le own1)
   (BIND: bind_parameters ce le m1 pl vl m2)
   (CAST: val_casted_list vl (type_of_params pl))
   (NOREP1: list_norepet (flat_map footprint_flat fpl))
   (WTVAL: sem_wt_val_list ce m1 fpl vl)
   (WTFPL: wt_footprint_list ge (type_list_of_typelist (type_of_params pl)) fpl)
   (INIT: init_place_list own1 (places_of_locals pl) = own2)
   (NOREP2: list_norepet (footprint_of_env le ++ flat_fp_map fpm1))
   (EMPFP: forall id ty, In (id, ty) pl -> exists fp, fpm1 ! id = Some fp)
   (VALIDTYS: forall id ty, In (id, ty) pl -> valid_type ty = true)
   (DIS1: list_disjoint (flat_map footprint_flat fpl) (footprint_of_env le ++ flat_fp_map fpm1))
   (* we need to consider the footprints in vl are disjoint with the allocated blocks *)
   (DIS2: list_disjoint (footprint_of_env le) (flat_map footprint_of_val vl))
   (WFOWN: wf_own_env le ce own1)
   (WFENV: wf_env fpm1 ce m1 le),
  exists fpm2,
    mmatch fpm2 ce m2 le own2
    /\ list_norepet (footprint_of_env le ++ flat_fp_map fpm2)
    /\ wf_env fpm2 ce m2 le
    /\ incl (flat_fp_map fpm2) (flat_map footprint_flat fpl ++ flat_fp_map fpm1)
    /\ wf_own_env le ce own2.
Proof.
  induction pl; intros.
  - inv BIND. inv CAST. inv WTVAL. inv WTFPL. simpl.
    exists fpm1. repeat apply conj; auto.
    apply incl_refl.
  - inv BIND. inv CAST. inv WTVAL. inv WTFPL.
    exploit EMPFP. simpl. left. eauto. intros (fp & A1).
    exploit assign_loc_sound. eauto. instantiate (1 := Plocal id ty). eauto.
    eauto. eapply Z.divide_0_r. auto.
    instantiate (1 := a1). simpl in NOREP1. eapply list_norepet_append_left; eauto.
    auto. auto. auto.
    simpl. rewrite H1. rewrite A1. eauto.
    eauto. econstructor. unfold env_to_tenv. erewrite PTree.gmap1. rewrite H1. auto.
    eapply VALIDTYS; eauto. simpl. eauto.
    auto. simpl in DIS1. eapply list_disjoint_app_l in DIS1.
    destruct DIS1. auto.
    auto.
    intros (fpm2 & SFP & MM2 & NOREP3 & WFENV2).
    simpl in NOREP1.
    intros. simpl in SFP. rewrite A1 in SFP. inv SFP.
    exploit IHpl. eapply MM2. eauto. auto. eapply list_norepet_append_right; eauto.
    (* sem_wt_val_list in m0 *)
    eapply sem_wt_val_list_unchanged_blocks. eauto.
    eapply Mem.unchanged_on_implies.
    eapply assign_loc_unchanged_on. eauto.
    simpl. intros. intro. destruct H2. subst.
    destruct H.
    eapply DIS1. simpl. eapply in_app; eauto.
    eapply in_app. left. eapply in_footprint_of_env; eauto. reflexivity.
    eapply DIS2. eapply in_footprint_of_env; eauto. simpl.
    eapply in_app; eauto. reflexivity.
    (* wt_footprint_list *)
    auto. eauto. auto.
    (* EMPFP *)    
    intros. rewrite PTree.gsspec.
    destruct peq; subst. eauto. eapply EMPFP. simpl. eauto.
    (* valid_type *)
    intros. eapply VALIDTYS. eapply in_cons. eauto.
    (* DIS1 *)
    simpl in DIS1. red. intros.
    intro. subst. rewrite in_app in H0.
    destruct H0. eapply DIS1. eapply in_app; eauto.
    eapply in_app; eauto. reflexivity.
    eapply in_flat_map in H0.
    destruct H0 as ((id1 & fp1) & IN1 & IN2).
    eapply PTree.elements_complete in IN1. rewrite PTree.gsspec in IN1.
    destruct peq in IN1; subst. inv IN1. simpl in IN2.
    eapply list_norepet_app in NOREP1 as (N1 & N2 & N3).
    eapply N3; eauto.
    eapply DIS1. eapply in_app; eauto. eapply in_app. right.
    eapply in_flat_map. exists (id1, fp1). split; eauto.
    eapply PTree.elements_correct; eauto. reflexivity.
    (* DIS2 *)
    simpl in DIS2. eapply list_disjoint_app_r. eauto.
    (* wf_own_env *)
    assert (WTP: wt_place le ce (Plocal id ty)).
    { econstructor. unfold env_to_tenv. rewrite PTree.gmap1.
      rewrite H1. eauto. eapply VALIDTYS. simpl. eauto. }
    eapply wf_own_env_init_place. auto. auto. auto.
    (* wf_env *)
    auto.
    intros (fpm3 & MM3 & NOREP4 & WFENV3 & INCL2 & WFOWN2).
    exists fpm3. repeat apply conj; auto.
    (* incl *)
    simpl. red. intros. eapply INCL2 in H.
    rewrite in_app in H. rewrite !in_app.
    destruct H; auto.
    eapply in_flat_map in H.
    destruct H as ((id1 & fp1) & IN1 & IN2).
    eapply PTree.elements_complete in IN1. rewrite PTree.gsspec in IN1.
    destruct peq in IN1; subst. inv IN1. simpl in IN2.
    auto. right. 
    eapply in_flat_map. exists (id1, fp1). split; eauto.
    eapply PTree.elements_correct; eauto.    
Qed.

Lemma bind_parameters_unchanged_on: forall pl vl m1 m2 le ce,
    bind_parameters ce le m1 pl vl m2 ->
    Mem.unchanged_on (fun b _ => ~ In b (footprint_of_env le)) m1 m2.
Proof.
  induction 1; intros; simpl.
  eapply Mem.unchanged_on_refl.
  eapply Mem.unchanged_on_trans; eauto.
  eapply Mem.unchanged_on_implies.
  eapply assign_loc_unchanged_on; eauto. simpl.
  intros. intro. apply H2. destruct H4. subst.
  eapply in_footprint_of_env; eauto.
Qed.

Lemma type_of_params_eq_var_type: forall l,
    type_list_of_typelist (type_of_params l) = var_types l.
Proof.
  induction l; simpl; auto.
  destruct a. simpl. f_equal. auto.
Qed.


Lemma list_equiv_nil_r {A: Type}: forall (l: list A),
    list_equiv l nil ->
    l = nil.
Proof.
  intros. destruct l. auto. red in H.
  generalize (H a). intros (A1 & A2).
  exfalso. eapply A1. simpl. auto.
Qed.

Lemma function_entry_sound: forall f vl fpl m1 le m2 own1 own2 
   (ENTRY: function_entry ge f vl m1 le m2)
   (OWN1: init_own_env ge f = OK own1)
   (OWN2: init_place_list own1 (places_of_locals (fn_params f)) = own2)
   (WTVAL: sem_wt_val_list ge m1 fpl vl)
   (WTFPL: wt_footprint_list ge (var_types f.(fn_params)) fpl)
   (CAST: val_casted_list vl (type_of_params f.(fn_params)))
   (INCL: Mem.sup_include (flat_map footprint_flat fpl) (Mem.support m1))
   (NOREP: list_norepet (flat_map footprint_flat fpl))
   (* used to prove wf_own_env for own1 *)
   (CHECK: move_check_function ge f = OK tt),
   (* prove disjointness between le and fpm *)
  exists fpm,
    mmatch fpm ge m2 le own2
    /\ wf_env fpm ge m2 le
    /\ wf_own_env le ce own2
    /\ list_norepet (footprint_of_env le ++ flat_fp_map fpm)
    (* used to prove that fpm is separated from the footprint of
    function frames *)
    /\ (forall b, In b (footprint_of_env le) ->
            ~ Mem.valid_block m1 b)
    /\ (forall b, In b (flat_fp_map fpm) ->
            In b (flat_map footprint_flat fpl))
    (* used to prove sound_cont *)
    /\ (forall P, Mem.unchanged_on P m1 m2).
Proof.
  intros.
  unfold move_check_function in CHECK.
  monadInv CHECK.
  destruct x1 as ((initMap & uninitMap) & universe). monadInv EQ2.
  (* try to destruct init_own_env *)
  unfold init_own_env in OWN1.
  destruct (collect_func ge f) eqn: COL; simpl in OWN1; try congruence.
  set (empty:= (PTree.map
                   (fun (_ : positive) (_ : LPaths.t) => Paths.empty)
                   t)) in *.
  set (uninit := (add_place_list t
                (places_of_locals (fn_params f ++ fn_vars f)) empty)) in *.
  generalize OWN1. clear OWN1.
  set (flag := check_own_env_consistency empty empty uninit t).
  generalize (eq_refl flag).
  generalize flag at 1 3.
  intros flag0 E. destruct flag0; try congruence.
  intros. 
  exploit analyze_collect_func_inv; eauto. intros COL1.
  rewrite COL in COL1. inv COL1.
  inv ENTRY.
  assert (WFOWN1: wf_own_env le ge own1).
  { inv OWN1. eapply check_universe_wf_own_env.
    destruct x1.
    rewrite bind_vars_app in EQ0.
    replace (PTree.empty type) with (env_to_tenv (PTree.empty (block * type))) in EQ0 by auto.
    erewrite alloc_variables_bind_vars_eq in EQ0.
    2: eauto. eapply EQ0.
    intros id paths EMP. unfold empty in EMP. erewrite PTree.gmap in EMP.
    destruct (universe ! id) eqn: G; simpl in EMP; try congruence.
    inv EMP. eapply Paths.empty_1. }
  assert (MM1: mmatch (init_footprint_map ce (fn_params f ++ fn_vars f) (PTree.empty footprint)) ce m0 le own1).
  { eapply mmatch_no_init_place.
    intros. inv OWN1.
    unfold is_init. simpl.
    unfold empty. unfold PathsMap.get.
    rewrite PTree.gmap. destruct (universe ! (local_of_place p)); simpl.
    auto. auto. }
  set (fpm1 := (init_footprint_map ce (fn_params f ++ fn_vars f) (PTree.empty footprint))) in *.
  assert (WFENV1: wf_env fpm1 ce m0 le).
  { eapply alloc_variables_wf_env. 2: eauto.
    eapply wf_env_empty. unfold var_names. rewrite map_app.
    eauto.
    (* intros. eapply PTree.gempty.     *)
    unfold check_cyclic_struct_res in EQ2. destruct forallb eqn: CYC in EQ2; try congruence.
    intros. erewrite forallb_forall in CYC. eapply CYC. eapply in_map_iff.
    exists (id, ty). eauto.
    unfold check_valid_types in EQ3. destruct forallb eqn: VAL in EQ3; try congruence.
    intros. erewrite forallb_forall in VAL. eapply VAL. eapply in_map_iff.
    exists (id, ty). eauto.  }
  assert (WTVAL1: sem_wt_val_list ge m0 fpl vl).
  { eapply sem_wt_val_list_unchanged_blocks. eauto.
    eapply alloc_variables_unchanged_on; eauto. }
  exploit alloc_variables_norepet; eauto.
  intros. rewrite PTree.gempty in H2. inv H2.
  econstructor.
  intros (NOREPLE & NVALID).
  assert (NVALID1: forall id b ty, le!id = Some (b, ty) -> ~ Mem.valid_block m1 b).
  { intros. exploit NVALID; eauto.
    intros [A1|A2]. auto. rewrite PTree.gempty in A2. inv A2. }    
  (* show that fpm1 is empty *)
  generalize (init_footprint_map_flat (fn_params f ++ fn_vars f) (PTree.empty footprint)).
  intros EQUIV.
  replace (flat_fp_map (PTree.empty footprint)) with (@nil block) in EQUIV by auto.
  exploit @list_equiv_nil_r; eauto. intros NIL. fold fpm1 in NIL.    
  exploit bind_parameters_sound. eapply MM1. eauto. eauto.
  eapply NOREP. eauto.
  erewrite type_of_params_eq_var_type. eauto.
  eauto.
  (* norepet *)
  unfold fpm1.
  erewrite NIL. rewrite app_nil_r. auto.
  intros.  
  exploit (init_footprint_map_flat_element (fn_params f ++ fn_vars f)).
  eapply in_app; eauto.
  intros (fp & A1 & A2). exists fp. eauto.
  (* valid_type *)
  unfold check_valid_types in EQ3. destruct forallb eqn: VAL in EQ3; try congruence.
  intros. erewrite forallb_forall in VAL. eapply VAL. eapply in_map_iff.
  exists (id, ty). split; auto. eapply in_app; auto.  
  (* disjoint *)
  unfold fpm1.
  rewrite NIL. rewrite app_nil_r.
  red. intros. intro. subst.
  exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & LE).
  eapply NVALID1; eauto. eapply INCL; eauto.
  (* disjointness between le and vl *)
  red. intros. intro. subst.
  exploit in_footprint_of_env_inv. eauto. intros (id & ty & IN1).
  eapply NVALID1; eauto.
  eapply sem_wt_val_list_valid_blocks; eauto.
  auto. auto.
  intros (fpm2 & MM2 & NOREP3 & WFENV2 & INCL1 & WFOWN2).
  exists fpm2.
  repeat apply conj; eauto.
  (* not valid *)
  intros. 
  exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & LE).
  eapply NVALID1. eauto.
  (* fpm2 is included in fpl *)
  intros. eapply INCL1 in H2.
  rewrite in_app in H2. destruct H2; auto.
  unfold fpm1 in H2.
  rewrite NIL in H2. inv H2.
  (* unchanged_on m1 m2 *)
  intros.
  exploit alloc_variables_unchanged_on; eauto. instantiate (1 := P).
  intros UNC1.
  exploit bind_parameters_unchanged_on; eauto. intros UNC2.
  intros. econstructor.
  eapply Mem.sup_include_trans.
  eapply Mem.unchanged_on_support; eauto.
  eapply Mem.unchanged_on_support; eauto.
  (* permission *)
  intros. split; intros.
  erewrite <- Mem.unchanged_on_perm.
  erewrite <- Mem.unchanged_on_perm. eauto. eauto. exact H2. auto.  
  eauto.  simpl. intro.
  exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & IN1).          
  eapply NVALID1; eauto.
  eapply Mem.unchanged_on_support; eauto.
  erewrite Mem.unchanged_on_perm.
  erewrite Mem.unchanged_on_perm. eauto. eauto.
  simpl. intro.
  exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & IN1).          
  eapply NVALID1; eauto. eapply Mem.unchanged_on_support; eauto. eauto.  
  exact H2. auto.  
  (* contents *)
  intros. eapply Mem.perm_valid_block in H3 as VAL.
  erewrite Mem.unchanged_on_contents.
  2: eapply UNC2.
  eapply Mem.unchanged_on_contents; eauto.
  simpl. intro.
  exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & IN1).          
  eapply NVALID1; eauto.
  erewrite <- Mem.unchanged_on_perm; eauto. 
Qed.

(** Function return *)

Lemma find_funct_move_check: forall vf fd,
    Genv.find_funct ge vf = Some fd ->
    move_check_fundef_spec ge fd.
Proof.
  intros. simpl in H.  eapply Genv.find_funct_prop; eauto.
  intros. eapply FUN_CHECK. eauto.
Qed.

Lemma footprint_of_not_composite_val: forall ty v fp m,
    sem_wt_val ce m fp v ->
    wt_footprint ce ty fp ->
    not_composite ty = true ->
    incl (footprint_of_val v) (footprint_flat fp).
Proof.
  induction 1; simpl; intros; try (apply incl_refl).
  - red. intros. inv H1. simpl; auto. inv H2.
  - inv H. simpl in *. congruence.
  - inv H. simpl in *. congruence.
Qed.

Lemma free_list_unchanged_on :
  forall l m m' P,
  Mem.free_list m l = Some m' ->
  (forall b z1 z2, In (b,z1,z2) l -> ~ P b) ->
  Mem.unchanged_on (fun b _ => P b) m m'.
Proof.
  induction l; simpl; intros.
  - inv H. eapply Mem.unchanged_on_refl.
  - destruct a. destruct p. destruct (Mem.free m b z0 z) eqn: FREE; try congruence.
    eapply Mem.unchanged_on_trans. 2: eapply IHl; eauto.
    eapply Mem.free_unchanged_on; eauto.
Qed.

Lemma footprint_blocks_of_env_eq: forall le,
    footprint_of_env le = map (fun '(b, _, _) => b) (blocks_of_env ce le).
Proof.
  intros. unfold footprint_of_env, blocks_of_env.
  rewrite map_map.  apply map_ext.
  intros (id & (b & ty)). auto.
Qed.

Lemma rsw_acc_sg_eq: forall sg fp m Hm,
    rsw_acc w (rsw sg fp m Hm) ->
    mod_sg = sg.
Proof.
  intros. unfold mod_sg. destruct w. inv H. auto.
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

(* Invariant of deref_loc_rec_footprint *)

(* This definition is about the invariant of the drop_member_state
used in the evaluation of Dropstate (i.e., the evaluation of the drop
glue). It says that the drop_member_state has the footprint fp if the
composite resides in the end of the box chain is sem_wt_loc w.r.t the
footprint obtained by recusively derefercing fp
(deref_loc_rec_footprint). deref_loc_rec_footprint also checks the
validity (e.g., Freeable) of the memory locaiton it dereferences. *)
Inductive drop_member_footprint (m: mem) (co: composite) (b: block) (ofs: Z) (fp: footprint) : option drop_member_state -> Prop :=
| drop_member_fp_none:
  (* We do not care fp is fp_emp or not. We just drop it from the fpf_drop *)
    drop_member_footprint m co b ofs fp None
| drop_member_fp_comp: forall fid fofs fty tyl b1 ofs1 fp1 compty
    (* (STRUCT: co.(co_sv) = Struct) *)
    (FOFS: match co.(co_sv) with
           | Struct =>
               field_offset ce fid co.(co_members)
           | TaggedUnion =>
               variant_field_offset ce fid co.(co_members)
           end = OK fofs)
    (* maybe unused *)
    (FTY: field_type fid co.(co_members) = OK fty)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 compty fp1)
    (* (b1, ofs1) is sem_wt_loc *)
    (WTLOC: sem_wt_loc ce m fp1 b1 ofs1)
    (* used to guarantee that fp is well founded (e.g., no repeated field names) *)
    (WTFFP: wt_footprint ce fty fp)
    (WTFP: wt_footprint ce compty fp1),
    drop_member_footprint m co b ofs fp (Some (drop_member_comp fid fty compty tyl))
(* | drop_member_fp_comp_enum: forall fid fofs fty tyl b1 ofs1 fp1 compty *)
(*     (ENUM: co.(co_sv) = TaggedUnion) *)
(*     (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs) *)
(*     (FTY: field_type fid co.(co_members) = OK fty)         *)
(*     (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 compty fp1) *)
(*     (* (b1, ofs1) is sem_wt_loc *) *)
(*     (WTLOC: sem_wt_loc ce m fp1 b1 ofs1) *)
(*     (WTFP: wt_footprint ce compty fp1), *)
(*     drop_member_footprint m co b ofs fp (Some (drop_member_comp fid fty compty tyl)) *)
| drop_member_fp_box: forall fid fofs fty tyl b1 ofs1 ty fp1
    (* (STRUCT: co.(co_sv) = Struct) *)
    (* reduce the size of proof *)
    (FOFS: match co.(co_sv) with
           | Struct =>
               field_offset ce fid co.(co_members)
           | TaggedUnion =>
               variant_field_offset ce fid co.(co_members)
           end = OK fofs)
    (FTY: field_type fid co.(co_members) = OK fty)    
    (* used to guarantee that fp is well founded (e.g., no repeated field names) *)
    (* (WTFFP: wt_footprint ce fty fp)     *)
    (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 ty fp1),
    drop_member_footprint m co b ofs fp (Some (drop_member_box fid fty tyl))
(* | drop_member_fp_box_enum: forall fid fofs fty tyl b1 ofs1 ty fp1 *)
(*     (ENUM: co.(co_sv) = TaggedUnion) *)
(*     (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs) *)
(*     (FTY: field_type fid co.(co_members) = OK fty)        *)
(*     (FFP: deref_loc_rec_footprint m b (ofs + fofs) fty fp tyl b1 ofs1 ty fp1), *)
(*     drop_member_footprint m co b ofs fp (Some (drop_member_box fid fty tyl)) *)
.

Lemma deref_loc_rec_footprint_app: forall l1 l2 b1 ofs1 ty1 fp1 b2 ofs2 ty2 fp2 b0 ty0 fp0 ofs0 m,
    deref_loc_rec_footprint m b1 ofs1 ty1 fp1 l1 b2 ofs2 ty2 fp2 ->
    deref_loc_rec_footprint m b0 ofs0 ty0 fp0 l2 b1 ofs1 ty1 fp1 ->
    deref_loc_rec_footprint m b0 ofs0 ty0 fp0 (l1 ++ l2) b2 ofs2 ty2 fp2.
Proof.
  induction l1; intros.
  - inv H. simpl. auto.
  - inv H. simpl. econstructor; eauto.
Qed.
    
Lemma sound_drop_glue_children_types: forall fty fp ty tys b ofs m
   (WTFP: wt_footprint ce fty fp)
   (WTLOC: sem_wt_loc ce m fp b ofs)
   (CHILD: drop_glue_children_types fty = ty :: tys),
  exists b1 ofs1 fp1,
    deref_loc_rec_footprint m b ofs fty fp tys b1 ofs1 ty fp1
    /\ sem_wt_loc ce m fp1 b1 ofs1
    /\ wt_footprint ce ty fp1.
Proof.
  induction fty; simpl in *; try congruence; intros.
  - eapply app_not_nil in CHILD.
    destruct CHILD as [(A1 & A2 & A3)| (l1' & A2 & A3)]; subst.
    + exists b, ofs, fp. repeat apply conj; auto.
      econstructor.
    + inv WTFP. inv WTLOC.
      simpl in WF. congruence.
      inv WTLOC. inv WT0.
      exploit IHfty; eauto.
      intros (b1 & ofs1 & fp1 & C1 & C2 & C3).
      exists b1, ofs1, fp1. repeat apply conj; auto.
      eapply deref_loc_rec_footprint_app; eauto.
      econstructor. econstructor.
      all: eauto. 
  - inv CHILD.
    exists b, ofs, fp. repeat apply conj; auto.
    econstructor.
  - inv CHILD.
    exists b, ofs, fp. repeat apply conj; auto.
    econstructor.
Qed.

Lemma sound_type_to_drop_member_state: forall fid fty fofs fp m b ofs co
    (WTFP: wt_footprint ce fty fp)
    (WTLOC: sem_wt_loc ce m fp b (ofs + fofs))
    (FOFS: match co_sv co with
           | Struct =>
               field_offset ce fid (co_members co) = OK fofs
           | TaggedUnion =>
               variant_field_offset ce fid (co_members co) = OK fofs
           end)
    (FTY: field_type fid (co_members co) = OK fty),
    drop_member_footprint m co b ofs fp (type_to_drop_member_state ge fid fty).
Proof.
  intros. unfold type_to_drop_member_state.
  destruct (own_type ge fty); try constructor.
  destruct (drop_glue_children_types fty) eqn: TYS.
  econstructor.
  exploit drop_glue_children_types_wf; eauto.
  intros (A1 & A2).
  destruct A1 as [ (orgs & i & ?)|[(orgs & i & ?) | (ty' & ?)] ]; subst.
  - destruct ((genv_dropm ge) ! i) eqn: DM.
    2: constructor.
    exploit sound_drop_glue_children_types; eauto.
    intros (b1 & ofs1 & fp1 & DEREF & WTLOC1 & WTFP1).
    eapply drop_member_fp_comp; eauto.
    destruct (co_sv co); auto.
  - destruct ((genv_dropm ge) ! i) eqn: DM.
    2: constructor.
    exploit sound_drop_glue_children_types; eauto.
    intros (b1 & ofs1 & fp1 & DEREF & WTLOC1 & WTFP1). 
    eapply drop_member_fp_comp; eauto.
    destruct (co_sv co); auto.
  - destruct (co_sv co) eqn: COSV.
    + exploit sound_drop_glue_children_types; eauto.
      intros (b1 & ofs1 & fp1 & DEREF & WTLOC1 & WTFP1).
      inv WTFP1. inv WTLOC1.
      simpl in WF. congruence.
      inv WTLOC1. inv WT0.
      eapply drop_member_fp_box; eauto.
      erewrite COSV. eauto.
      econstructor; eauto. 
    + exploit sound_drop_glue_children_types; eauto.
      intros (b1 & ofs1 & fp1 & DEREF & WTLOC1 & WTFP1).
      inv WTFP1. inv WTLOC1.
      simpl in WF. congruence.
      inv WTLOC1. inv WT0.
      eapply drop_member_fp_box; eauto.
      erewrite COSV. eauto.
      econstructor; eauto. 
Qed.

Fixpoint typeof_cont_call (ttop: type) (k: cont) : type :=
  match k with
  | Kcall p _ _ _ _ =>
      typeof_place p
  | Kstop => ttop
  | Kseq _ k
  | Kloop _ k
  (* impossible? *)
  | Kdropplace _ _ _ _ _ k
  | Kdropcall _ _ _ _ k => typeof_cont_call ttop k
  end.


(** Some thoughts about how to define sound_drop_place_state  *)
(** How to prove eval_place can get the footprint of p in
step_dropplace? We cannot use eval_place_sound because we cannot prove
that p's dominators are init. We can use the fact that the footprint
map is unchanged during step_dropplace. So we can prove that when
entering drop_fully_owned, the footprint of the split place can be
obtained (by get_loc_footprint_progress). Invariant of
drop_place_state must contain that we can use the extra paths of p to
get the footprint of p from the footprint of the (split place's
footprint), and show that this footprint is mmatch (sem_wt if it is
composite). How to prove that the locations evaluated by eval_place
and get_loc_footprint are the same? We need some eval_place_prefix
lemma to split eval_place to eval_prefix and eval_sufix, but how to
prove the result of eval_prefix is unchanged if we drop a place?? Can
we prove mmatch (yes, by mmatch_unchanged_on) when we move out some
footprint outside the footprint map and then use eval_place_sound to
show that the result of eval_prefix is unchanged? *)

(** How to prove the eval_place in step_dropplace has no memory error? *)

(* This relation says that for some root place (split place) residing
in (b,ofs) whose footprint is rfp, we can evaluate the places list and
get the place and its location (along with its type and footprint) of
the pointee of this list. So if this list is empty, the pointee is
just the root place itselt; if this list is not empty, the list must
have some given shape, and the location is evaluated by dereferencing
the location of the result of the remaining list. Some invariant, the
return place is the dereference of the head of the list or the root place *)
Inductive sound_split_fully_own_place (m: mem) (r: place) (b: block) (ofs: Z) (rfp: footprint) : list place -> place -> block -> Z -> type -> footprint -> Prop :=
| sound_split_nil:
  sound_split_fully_own_place m r b ofs rfp nil r b ofs (typeof_place r) rfp
| sound_split_cons: forall b1 ofs1 ty b2 sz fp2 l p1 
    (SOUND: sound_split_fully_own_place m r b ofs rfp l p1 b1 ofs1 (Tbox ty) (fp_box b2 sz fp2))
    (TYSZ: sz = sizeof ce ty)
    (* Properties of bmatch *)
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b2 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (PERM: Mem.range_perm m b2 (- size_chunk Mptr) sz Cur Freeable)
    (* avoid overflow *)
    (RANGE: 0 < sz <= Ptrofs.max_unsigned),
    sound_split_fully_own_place m r b ofs rfp (p1 :: l) (Pderef p1 ty) b2 0 ty fp2  
.

(* This relation is the invariant of the drop_place_state. In
particular, when there is a composite to be dropped, we should say
that the location "computed" by sound_split_fully_own_place is
semantically well-typed. The root place (and its location and its
footprint because we need to maintain some separation property of its
footprint and the other) is internal in this invariant because we do
not want to expose them in sound_cont (i.e., internal in
sound_cont). rfp is the footprint of this state *)
Inductive sound_drop_place_state (e: env) (m: mem) (fpm: fp_map) (own: own_env) : footprint -> option drop_place_state -> Prop :=
| sound_drop_place_state_none: sound_drop_place_state e m fpm own fp_emp None
| sound_drop_place_state_comp: forall r b ofs p l b1 ofs1 fp1 empfp rfp    (* Note that the footprint of r has been moved out (but we cannot
    ensure that its footprint is fp_emp because it may be a struct! *)
    (PFP: get_loc_footprint_map e (path_of_place r) fpm = Some (b, ofs, empfp))
    (NOREP: list_norepet (footprint_flat rfp))
    (* used to prove get_loc_footprint_map is equal to eval_place r) *)
    (DOM: dominators_is_init own r = true)
    (SPLIT: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 (typeof_place p) fp1)
    (WTLOC: sem_wt_loc ce m fp1 b1 ofs1)
    (WTP: wt_place e ce r)
    (WTFP: wt_footprint ce (typeof_place p) fp1),
    sound_drop_place_state e m fpm own rfp (Some (drop_fully_owned_comp p l))
| sound_drop_place_state_box: forall r b ofs l b1 ofs1 ty1 empfp p rfp fp
    (PFP: get_loc_footprint_map e (path_of_place r) fpm = Some (b, ofs, empfp))
    (NOREP: list_norepet (footprint_flat rfp))
    (DOM: dominators_is_init own r = true)
    (* The footprint of p must be empty to make rfp minimum so that we
    can prove no memory leak. But it make the sound_dropplace proof
    very difficult as we need to track the status of the footprint in
    the sound_dropplace *)
    (SPLIT: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp)
    (WTP: wt_place e ce r),
    sound_drop_place_state e m fpm own rfp (Some (drop_fully_owned_box l)).


Lemma sound_split_fully_own_place_type_inv: forall m r b ofs rfp l p b1 ofs1 ty1 fp1,
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    typeof_place p = ty1.
Proof.
  destruct l; intros.
  - inv H. auto.
  - inv H. simpl. auto.
Qed.

Lemma sound_split_fully_own_place_footprint_get: forall l m r b ofs rfp p b1 ofs1 ty1 fp1
    (SOUND: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1),
    get_loc_footprint (repeat ph_deref (length l)) rfp b ofs = Some (b1, ofs1, fp1).
Proof.
  induction l; intros.
  - inv SOUND. simpl. auto.
  - inv SOUND. exploit IHl; eauto.
    intros A.
    cbn [length]. cbn [repeat].
    erewrite repeat_cons.
    eapply get_loc_footprint_app; eauto.
Qed.


(* we also require that the produced footprint is norepet *)
Lemma sound_split_fully_own_place_footprint_norepet: forall m r b ofs rfp l p b1 ofs1 ty1 fp1,
    list_norepet (footprint_flat rfp) ->
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    ~ In b (footprint_flat rfp) ->
    (* incl (footprint_flat fp1) (footprint_flat rfp) *)
    (* /\ In b1 (footprint_flat rfp) *)
    list_norepet (footprint_flat fp1)
    /\  ~ In b1 (footprint_flat fp1).
Proof.  
  intros.
  exploit sound_split_fully_own_place_footprint_get; eauto.
  intros GFP.
  exploit get_loc_footprint_norepet; eauto.
Qed.

Lemma sound_split_fully_own_place_footprint_in: forall m r b ofs rfp l p b1 ofs1 ty1 fp1,
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    In b1 (b :: footprint_flat rfp).
Proof.
  intros.
  exploit sound_split_fully_own_place_footprint_get; eauto.
  intros GFP.
  exploit get_loc_footprint_in; eauto.
Qed.

(* sound_split_fully_own_place remains satisfied if the changed blocks
are inside the fp1. It is mostly the same as
deref_loc_rec_footprint_unchanged *)
Lemma sound_split_fully_own_place_unchanged: forall m1 m2 r b ofs rfp l p b1 ofs1 ty1 fp1
    (NOREP: list_norepet (footprint_flat rfp))
    (SOUND: sound_split_fully_own_place m1 r b ofs rfp l p b1 ofs1 ty1 fp1)
    (NIN: ~ In b (footprint_flat rfp))
    (* block in fp1 can be changed *)
    (UNC: Mem.unchanged_on (fun b2 _ =>  ~ In b2 (footprint_flat fp1)) m1 m2),
    sound_split_fully_own_place m2 r b ofs rfp l p b1 ofs1 ty1 fp1.
Proof.
  induction l; intros.
  - inv SOUND. econstructor.
  - inv SOUND.
    exploit sound_split_fully_own_place_footprint_norepet; eauto.
    intros (NOREP1 & NIN1).
    exploit sound_split_fully_own_place_footprint_get; eauto.
    intros GFP.
    (* generalize (get_loc_footprint_incl _ _ _ _ _ _ _ GFP). intros INCL. *)
    econstructor; eauto.
    eapply IHl; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros.
    simpl. intro. eapply H. simpl. auto.
    (* load value *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. intro. eapply NIN1. simpl. auto.    
    (* load size of block *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl.
    simpl in NOREP1. inv NOREP1. auto.
    (* range_perm *)
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl.
    simpl in NOREP1. inv NOREP1. auto.
    (* valid_block *)
    eapply Mem.perm_valid_block; eauto.
Qed.

(* This frame rule is used in updating the memory outside rfp and b
(i.e., sound_cont_unchanged) *)
Lemma sound_split_fully_own_place_unchanged1: forall m1 m2 r b ofs rfp l p b1 ofs1 ty1 fp1
    (SOUND: sound_split_fully_own_place m1 r b ofs rfp l p b1 ofs1 ty1 fp1)
    (UNC: Mem.unchanged_on (fun b2 _ =>  b2 = b \/ In b2 (footprint_flat rfp)) m1 m2),
    sound_split_fully_own_place m2 r b ofs rfp l p b1 ofs1 ty1 fp1.
Proof.
  induction l; intros.
  - inv SOUND. econstructor.
  - inv SOUND.
    exploit sound_split_fully_own_place_footprint_in; eauto. intros IN.
    exploit sound_split_fully_own_place_footprint_get; eauto. intros GFP.
    econstructor; eauto.
    (* load value *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. inv IN; auto.
    (* load size of block *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl.
    right. eapply get_loc_footprint_incl; eauto.
    simpl. auto.
    (* range_perm *)
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl.
    right. eapply get_loc_footprint_incl; eauto.
    simpl. auto.
    (* valid_block *)
    eapply Mem.perm_valid_block; eauto.
Qed.

Lemma sound_split_fully_own_place_eval_place: forall l m r b ofs rfp p b1 ofs1 ty1 fp1 b2 ofs2 e
  (SOUND: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1)
  (EVAL: eval_place ce e m p b2 ofs2),
  exists b3 ofs3,
    eval_place ce e m r b3 ofs3
    /\ ((b3, Ptrofs.unsigned ofs3) = (b, ofs) -> (b1, ofs1) = (b2, Ptrofs.unsigned ofs2)).
Proof.
  induction l; intros.
  - inv SOUND. exists b2, ofs2.
    eauto.
  - inv SOUND. inv EVAL.
    exploit sound_split_fully_own_place_type_inv; eauto. intros TY.
    rewrite TY in *.
    inv H4; simpl in *; try congruence. inv H.
    exploit IHl; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exists b3, ofs3. split; auto.
    intros. inv H. exploit A2. auto.
    intros. inv H.
    rewrite LOAD in H0. inv H0.
    auto.
Qed.    

Lemma sound_split_fully_own_place_range: forall l m r b ofs rfp p b1 ofs1 ty1 fp1,
    sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1 ->
    ofs + sizeof ce (typeof_place r) <= Ptrofs.max_unsigned ->
    ofs1 + sizeof ce ty1 <= Ptrofs.max_unsigned.
Proof.
  destruct l; intros.
  - inv H. lia.    
  - inv H. lia.
Qed.

Lemma sound_split_fully_own_place_set: forall l m r b ofs rfp p b1 ofs1 ty1 fp1 fp2
    (SOUND: sound_split_fully_own_place m r b ofs rfp l p b1 ofs1 ty1 fp1),
  exists rfp1,
    get_footprint (repeat ph_deref (length l)) rfp = Some fp1
    /\ set_footprint (repeat ph_deref (length l)) fp2 rfp = Some rfp1
    /\ sound_split_fully_own_place m r b ofs rfp1 l p b1 ofs1 ty1 fp2.
Proof.
  induction l; intros.
  - inv SOUND. simpl. eexists. repeat apply conj; eauto.
    econstructor.
  - inv SOUND. exploit IHl; eauto.
    instantiate (1 := fp_box b1 (sizeof ce ty1) fp2).    
    intros (rfp1 & A & B & C).
    cbn [length]. cbn [repeat].
    erewrite repeat_cons.
    exists rfp1. repeat apply conj.
    + eapply get_footprint_app; eauto.
    + eapply set_footprint_app; eauto.
      simpl. auto.
    + econstructor; eauto.
Qed.

(* similar to sound_split_fully_own_place_set *)
Lemma deref_loc_rec_footprint_set: forall tys m ty b ofs rfp b1 ofs1 ty1 fp1 fp2
    (SOUND: deref_loc_rec_footprint m b ofs ty rfp tys b1 ofs1 ty1 fp1),
  exists rfp1,
    get_footprint (repeat ph_deref (length tys)) rfp = Some fp1
    /\ set_footprint (repeat ph_deref (length tys)) fp2 rfp = Some rfp1
    /\ deref_loc_rec_footprint m b ofs ty rfp1 tys b1 ofs1 ty1 fp2.
Proof.
  induction tys; intros.
  - inv SOUND. simpl. eexists. repeat apply conj; eauto.
    econstructor.
  - inv SOUND. exploit IHtys; eauto.
    instantiate (1 := fp_box b1 (sizeof ce ty1) fp2).    
    intros (rfp1 & A & B & C).
    cbn [length]. cbn [repeat].
    erewrite repeat_cons.
    exists rfp1. repeat apply conj.
    + eapply get_footprint_app; eauto.
    + eapply set_footprint_app; eauto.
      simpl. auto.
    + econstructor; eauto.
Qed.

Lemma deref_loc_rec_footprint_get: forall tys m ty b ofs rfp b1 ofs1 ty1 fp1
    (SOUND: deref_loc_rec_footprint m b ofs ty rfp tys b1 ofs1 ty1 fp1),
    get_loc_footprint (repeat ph_deref (length tys)) rfp b ofs = Some (b1, ofs1, fp1).
Proof.
  induction tys; intros.
  - inv SOUND. simpl. auto.
  - inv SOUND. exploit IHtys; eauto.
    intros A.
    cbn [length]. cbn [repeat].
    erewrite repeat_cons.
    eapply get_loc_footprint_app; eauto.
Qed.

Lemma deref_loc_rec_footprint_norepet: forall tys m ty b ofs b1 ofs1 ty1 fp fp1
    (DEF: deref_loc_rec_footprint m b ofs ty fp tys b1 ofs1 ty1 fp1)
    (NIN: ~ In b (footprint_flat fp))
    (NOREP: list_norepet (footprint_flat fp)),
    list_norepet (footprint_flat fp1) /\ ~ In b1 (footprint_flat fp1).
Proof.
  intros.
  exploit deref_loc_rec_footprint_get; eauto.
  intros GFP.
  exploit get_loc_footprint_norepet; eauto.
Qed.

Lemma deref_loc_rec_footprint_in: forall tys m ty b ofs b1 ofs1 ty1 fp fp1
    (DEF: deref_loc_rec_footprint m b ofs ty fp tys b1 ofs1 ty1 fp1),
    In b1 (b :: footprint_flat fp).
Proof.
  intros.
  exploit deref_loc_rec_footprint_get; eauto.
  intros GFP.
  exploit get_loc_footprint_in; eauto.
Qed.

Lemma deref_loc_rec_footprint_app_inv: forall l1 l2 b2 ofs2 ty2 fp2 b0 ty0 fp0 ofs0 m,
    deref_loc_rec_footprint m b0 ofs0 ty0 fp0 (l1 ++ l2) b2 ofs2 ty2 fp2 ->
    exists b1 ofs1 ty1 fp1,
      deref_loc_rec_footprint m b1 ofs1 ty1 fp1 l1 b2 ofs2 ty2 fp2
      /\ deref_loc_rec_footprint m b0 ofs0 ty0 fp0 l2 b1 ofs1 ty1 fp1.
Proof.
  induction l1; intros.
  - simpl in H. exists b2, ofs2, ty2, fp2.
    split. econstructor. auto.
  - simpl in H. inv H.
    exploit IHl1; eauto.
    intros (b3 & ofs2 & ty1 & fp1 & A1 & A2).
    do 4 eexists. split.
    econstructor; eauto. auto.
Qed.

Lemma deref_loc_rec_footprint_range: forall tys m ty b ofs rfp b1 ofs1 ty1 fp1,
    deref_loc_rec_footprint m b ofs ty rfp tys b1 ofs1 ty1 fp1 ->
    ofs + sizeof ce ty <= Ptrofs.max_unsigned ->
    ofs1 + sizeof ce ty1 <= Ptrofs.max_unsigned.
Proof.
  destruct tys; intros.
  - inv H. lia.    
  - inv H. lia.
Qed.

Lemma deref_loc_rec_footprint_pos: forall tys m ty b ofs rfp b1 ofs1 ty1 fp1,
    deref_loc_rec_footprint m b ofs ty rfp tys b1 ofs1 ty1 fp1 ->
    0 <= ofs ->
    0 <= ofs1.
Proof.
  destruct tys; intros.
  - inv H. lia.    
  - inv H. lia.
Qed.


(* Used in proving sound_cont which is different from
deref_loc_rec_footprint_unchanged which is used to prove the situation
that we are freeing the blocks in fp1 *)
Lemma deref_loc_rec_footprint_unchanged1: forall m1 m2 b ofs rfp l b1 ofs1 ty1 fp1 ty
    (DEF: deref_loc_rec_footprint m1 b ofs ty rfp l b1 ofs1 ty1 fp1)
    (UNC: Mem.unchanged_on (fun b2 _ =>  b2 = b \/ In b2 (footprint_flat rfp)) m1 m2),
    deref_loc_rec_footprint m2 b ofs ty rfp l b1 ofs1 ty1 fp1.
Proof.
  induction l; intros.
  - inv DEF. econstructor.
  - inv DEF.
    exploit deref_loc_rec_footprint_in; eauto. intros IN.
    exploit deref_loc_rec_footprint_get; eauto. intros GFP.
    econstructor; eauto.
    (* load value *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl. inv IN; auto.
    (* load size of block *)
    eapply Mem.load_unchanged_on; eauto.
    intros. simpl.
    right. eapply get_loc_footprint_incl; eauto.
    simpl. auto.
    (* range_perm *)
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl.
    right. eapply get_loc_footprint_incl; eauto.
    simpl. auto.
    (* valid_block *)
    eapply Mem.perm_valid_block; eauto.
Qed.


(* soundness of continuation: the execution of current function cannot
modify the footprint maintained by the continuation *)

Inductive sound_cont : AN -> statement -> rustcfg -> cont -> node -> option node -> option node -> node -> mem -> fp_frame -> Prop :=
| sound_Kstop: forall an body cfg nret m
    (RET: cfg ! nret = Some Iend),
    sound_cont an body cfg Kstop nret None None nret m fpf_emp
| sound_Kseq: forall an body cfg s ts k pc next cont brk nret m fpf
    (MSTMT: match_stmt an body cfg s ts pc next cont brk nret)
    (MCONT: sound_cont an body cfg k next cont brk nret m fpf),
    sound_cont an body cfg (Kseq s k) pc cont brk nret m fpf
| sound_Kloop: forall an body cfg s ts k body_start loop_jump_node exit_loop nret contn brk m fpf
    (START: cfg ! loop_jump_node = Some (Inop body_start))
    (MSTMT: match_stmt an body cfg s ts body_start loop_jump_node (Some loop_jump_node) (Some exit_loop) nret)
    (MCONT: sound_cont an body cfg k exit_loop contn brk nret m fpf),
    sound_cont an body cfg (Kloop s k)loop_jump_node (Some loop_jump_node) (Some exit_loop) nret m fpf
| sound_Kcall: forall an body cfg k nret f e own p m fpf
    (MSTK: sound_stacks (Kcall p f e own k) m fpf)
    (RET: cfg ! nret = Some Iend)
    (WFOWN: wf_own_env e ce own),
    sound_cont an body cfg (Kcall p f e own k) nret None None nret m fpf
| sound_Kdropplace: forall f st ps nret cfg pc cont brk k own1 own2 e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit rfp (* rfpty *)
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc cont brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (WFNEV: wf_env fpm ce m e)
    (** VERY DIFFICULT: Invariant of drop_place_state *)
    (SDP: sound_drop_place_state e m fpm own1 rfp st)
    (SEP: list_norepet (flat_fp_frame (fpf_dropplace e fpm rfp fpf)))
    (MOVESPLIT: move_split_places own1 ps = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst ps))
    (* all places in drops are wt_place *)
    (WTPS: Forall (fun p => wt_place e ge p) (map fst ps))
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env e ce own1)
    (FULL: (forall p full, In (p, full) ps -> is_full (own_universe own1) p = full))
    (* (WTRFP: wt_footprint ce rfpty rfp) *),
    sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg (Kdropplace f st ps e own1 k) pc cont brk nret m (fpf_dropplace e fpm rfp fpf)
| sound_Kdropcall: forall an body cfg k pc cont brk nret fpf st co fp ofs b membs fpl id m
    (CO: ce ! id = Some co)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned)
    (** Do we need some separation properties? *)
    (SOUND: sound_cont an body cfg k pc cont brk nret m fpf)
    (INFRM: In b (flat_fp_frame fpf))
    (CONTDIS: ~ In b (footprint_flat fp ++ flat_map footprint_flat fpl)),
    sound_cont an body cfg (Kdropcall id (Vptr b ofs) st membs k) pc cont brk nret m (fpf_drop fp fpl fpf)

with sound_stacks : cont -> mem -> fp_frame -> Prop :=
| sound_stacks_stop: forall m,
    sound_stacks Kstop m fpf_emp
| sound_stacks_call: forall f nret cfg pc contn brk k own1 own2 p e m maybeInit maybeUninit universe entry fpm fpf mayinit mayuninit
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))   
    (MCONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k pc contn brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (WFENV: wf_env fpm ce m e)
    (* we need to maintain this invariant for p's evaluation when
    function return *)
    (DOM: dominators_is_init own1 p = true)
    (* own2 is built after the function call *)
    (AFTER: own2 = init_place own1 p)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env e ce own1),
    sound_stacks (Kcall p f e own1 k) m (fpf_func e fpm fpf).
    

(** TODO: add syntactic well typedness in the sound_state and
sound_cont *)
Inductive sound_state: state -> Prop :=
| sound_regular_state: forall f cfg entry maybeInit maybeUninit universe s ts pc next cont brk nret k e own m fpm fpf flat_fp sg mayinit mayuninit Hm
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (STMT: match_stmt (maybeInit, maybeUninit, universe) f.(fn_body) cfg s ts pc next cont brk nret)
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (IM: get_IM_state maybeInit!!pc maybeUninit!!pc (Some (mayinit, mayuninit)))
    (OWN: sound_own own mayinit mayuninit universe)
    (MM: mmatch fpm ce m e own)
    (FLAT: flat_fp = flat_fp_frame (fpf_func e fpm fpf))
    (* footprint is separated *)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (* we need to maintain the well-formed invariant of own_env *)
    (WFENV: wf_env fpm ce m e)
    (* invariant of the own_env *)
    (WFOWN: wf_own_env e ce own),
    sound_state (State f s k e own m)
| sound_dropplace: forall f cfg entry maybeInit maybeUninit universe next cont brk nret st drops k e own1 own2 m fpm fpf flat_fp sg mayinit mayuninit rfp Hm
    (AN: analyze ce f cfg entry = OK (maybeInit, maybeUninit, universe))
    (CONT: sound_cont (maybeInit, maybeUninit, universe) f.(fn_body) cfg k next cont brk nret m fpf)
    (MM: mmatch fpm ce m e own1)
    (FLAT: flat_fp = flat_fp_frame (fpf_dropplace e fpm rfp fpf))
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (* every place in the drop_fully_owned state is owned: this may be
    wrong because it does not consider own is changing *)
    (SDP: sound_drop_place_state e m fpm own1 rfp st)
    (* big step update of the own_env *)
    (MOVESPLIT: move_split_places own1 drops = own2)
    (* ordered property of the split places used to prove sound_state after the dropplace *)
    (ORDERED: move_ordered_split_places_spec own1 (map fst drops))
    (* fullspec is used to maintain the invariant between is_full and the full flags *)
    (FULLSPEC: forall p full,  In (p, full) drops -> is_full (own_universe own1) p = full)
    (* all places in drops are wt_place *)
    (WTPS: Forall (fun p => wt_place e ge p) (map fst drops))
    (WF: wf_env fpm ce m e)
    (* We just want to make rfp well structured (e.g., field names are
    norepet and the size of blocks are in range) *)
    (* (WTRFP: wt_footprint ce rfpty rfp)  *)
    (IM: get_IM_state maybeInit!!next maybeUninit!!next (Some (mayinit, mayuninit)))
    (* Why sound_own own2 here not own1? because the analysis result is about the next node *)
    (OWN: sound_own own2 mayinit mayuninit universe)
    (WFOWN: wf_own_env e ce own1),
    (* no need to maintain borrow check domain in dropplace? But how
    to record the pc and next statement? *)
    sound_state (Dropplace f st drops k e own1 m)
| sound_dropstate: forall an body cfg next cont brk nret id co fp fpl b ofs st m membs k fpf flat_fp sg Hm
    (CO: ce ! id = Some co)
    (* The key is how to prove semantics well typed can derive the
    following two properties *)
    (DROPMEMB: drop_member_footprint m co b (Ptrofs.unsigned ofs) fp st)
    (* all the remaining members are semantically well typed *)
    (MEMBFP: list_forall2 (member_footprint m co b (Ptrofs.unsigned ofs)) fpl membs)
    (CONT: sound_cont an body cfg k next cont brk nret m fpf)
    (FLAT: flat_fp = flat_fp_frame (fpf_drop fp fpl fpf))
    (NOREP: list_norepet flat_fp)
    (* The location of the composite to be dropped is not in the
    current footprint ! Note that it may resides in fpf! *)
    (DIS: ~ In b (footprint_flat fp ++ flat_map footprint_flat fpl))
    (* b is in fpf to make sure that changing the memory outside
    flat_fp does not change b *)
    (INFRM: In b (flat_fp_frame fpf))
    (ACC: rsw_acc w (rsw sg flat_fp m Hm))
    (RANGE: Ptrofs.unsigned ofs + co_sizeof co <= Ptrofs.max_unsigned),
    sound_state (Dropstate id (Vptr b ofs) st membs k m)
| sound_callstate: forall vf fd orgs org_rels tyargs tyres cconv m fpl args fpf k flat_fp sg Hm
    (FUNC: Genv.find_funct ge vf = Some fd)
    (FUNTY: type_of_fundef fd = Tfunction orgs org_rels tyargs tyres cconv)
    (* arguments are semantics well typed *)
    (WTVAL: list_forall2 (sem_wt_val ce m) fpl args)
    (* Used in assign_loc_sound in function entry proof *)
    (ANORM: val_casted_list args tyargs)
    (WTFP: list_forall2 (wt_footprint ce) (type_list_of_typelist tyargs) fpl)
    (STK: sound_stacks k m fpf)
    (FLAT: flat_fp = flat_fp_frame fpf ++ flat_map footprint_flat fpl)
    (* also disjointness of fpl and fpf *)
    (NOREP: list_norepet flat_fp)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm)),
    sound_state (Callstate vf args k m)
| sound_returnstate: forall sg fpf flat_fp m k retty rfp v Hm    
    (* For now, all function must have return type *)
    (RETY: typeof_cont_call (rs_sig_res sg) k = retty)
    (WTVAL: sem_wt_val ce m rfp v)
    (CAST: val_casted v retty)
    (WTFP: wt_footprint ce retty rfp)
    (FLAT: flat_fp = footprint_flat rfp ++ flat_fp_frame fpf)
    (SEP: list_norepet flat_fp)
    (STK: sound_stacks k m fpf)
    (ACC: rsw_acc w (rsw sg flat_fp m Hm)),
    sound_state (Returnstate v k m)
.

Lemma blocks_of_fp_box_incl: forall b fp,
    In b (map fst (blocks_of_fp_box fp)) ->
    In b (footprint_flat fp).
Proof.
  induction fp using strong_footprint_ind; try (simpl; congruence).
  - simpl. intros. destruct H; try congruence.
    auto. contradiction.
  - simpl. intros.
    eapply in_map_iff in H0 as ((b1 & ofs) & A1 & A2). 
    simpl in A1. subst.
    eapply in_flat_map in A2.
    destruct A2 as (((id1 & ofs1) & fpl1) & B1 & B2).
    exploit H; eauto.
    eapply in_map_iff. exists (b, ofs). eauto.
    intros IN1. eapply in_flat_map; eauto.
  - simpl. auto.
Qed.

Lemma mmatch_unchanged: forall m1 m2 fpm e own,
    mmatch fpm ce m1 e own ->
    Mem.unchanged_on (fun b _ => In b (footprint_of_env e ++ flat_fp_map fpm)) m1 m2 ->
    mmatch fpm ce m2 e own.
Proof.
  intros. red. intros.
  exploit H; eauto.
  intros (BM & FULL).
  destruct (path_of_place p) eqn: POP.
  split.
  - eapply bmatch_unchanged_on_block; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H3. subst.
    eapply get_loc_footprint_map_in_range; eauto.
    do 2 red in H3.  destruct H3.
    eapply in_app. right.
    eapply get_loc_footprint_map_incl. eauto.
    eapply blocks_of_fp_box_incl; eauto.
    (* blocks_perm_unchanged_fp *)
    red. red.
    intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl.
    eapply in_app. right.
    eapply get_loc_footprint_map_incl. eauto.
    eapply blocks_of_fp_box_incl; eauto.
    eapply in_map_iff. exists (b0, sz). eauto.
    eapply Mem.perm_valid_block; eauto.
  - intros. exploit FULL. eauto.
    intros WT.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. 
    destruct H4; subst.
    rewrite in_app. right.
    eapply get_loc_footprint_map_incl; eauto.
    eapply get_loc_footprint_map_in_range; eauto.
Qed.

Lemma sound_drop_place_state_unchanged: forall e m1 m2 fpm own rfp ps,
    sound_drop_place_state e m1 fpm own rfp ps ->
    Mem.unchanged_on (fun b _ => In b (footprint_of_env e ++ flat_fp_map fpm ++ footprint_flat rfp)) m1 m2 ->
    sound_drop_place_state e m2 fpm own rfp ps.
Proof.
  intros until ps. intros A B.
  inv A.
  econstructor.  
  - destruct (path_of_place r) eqn: POP.
    econstructor; eauto. rewrite POP. eauto.
    eapply sound_split_fully_own_place_unchanged1; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl. intros.
    rewrite !in_app.
    exploit get_loc_footprint_map_in_range; eauto. intros IN.
    rewrite in_app in IN.
    destruct H; subst. destruct IN; auto. auto.
    (* sem_wt_loc *)
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. 
    rewrite !in_app.
    exploit sound_split_fully_own_place_footprint_in; eauto.
    intros IN.    
    exploit sound_split_fully_own_place_footprint_get; eauto.
    intros GFP.
    destruct H; subst.
    right. right. eapply get_loc_footprint_incl; eauto.
    inv IN; auto.
    exploit get_loc_footprint_map_in_range; eauto. intros IN.
    erewrite in_app in IN. destruct IN; auto.
  - destruct (path_of_place r) eqn: POP.
    econstructor; eauto.  rewrite POP. eauto.
    eapply sound_split_fully_own_place_unchanged1; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl. intros.
    rewrite !in_app.
    exploit get_loc_footprint_map_in_range; eauto. intros IN.
    rewrite in_app in IN.
    destruct H; subst. destruct IN; auto. auto.
Qed.

Lemma drop_member_footprint_unchanged: forall m1 m2 co b ofs fp st,
    drop_member_footprint m1 co b ofs fp st ->
    Mem.unchanged_on (fun b' _ => b' = b \/ In b' (footprint_flat fp)) m1 m2 ->
    drop_member_footprint m2 co b ofs fp st.
Proof.
  intros until st. intros A B.
  inv A. econstructor.
  - econstructor; eauto.
    eapply deref_loc_rec_footprint_unchanged1; eauto.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    exploit deref_loc_rec_footprint_get; eauto.
    intros GFP.
    exploit get_loc_footprint_in; eauto. intros IN.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. destruct H; subst; auto.
    inv IN; auto. right. eapply get_loc_footprint_incl; eauto.
    right. eapply get_loc_footprint_incl; eauto.
    inv IN; auto.
  - econstructor; eauto.
    eapply deref_loc_rec_footprint_unchanged1; eauto.
Qed.

Lemma member_footprint_unchanged: forall fpl membs m1 m2 co b ofs,
    list_forall2 (member_footprint m1 co b ofs) fpl membs ->
    Mem.unchanged_on (fun b' _ => b' = b \/ In b' (flat_map footprint_flat fpl)) m1 m2 ->
    list_forall2 (member_footprint m2 co b ofs) fpl membs.
Proof.
  induction 1; intros UNC.
  - econstructor.
  - exploit IHlist_forall2; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros.
    destruct H1; auto.
    right. eapply in_app; eauto.
    intros. econstructor; eauto.
    inv H. econstructor; eauto.
    eapply sem_wt_loc_unchanged_blocks; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros.
    destruct H; auto.
    right. eapply in_app; auto.
Qed.

(* (* sound_cont is preserved if its footprint is unchanged *) *)

(* Similar to non-interference properties? *)
Lemma sound_cont_unchanged: forall m1 m2 k fpf an body cfg next cont brk nret
  (SOUND: sound_cont an body cfg k next cont brk nret m1 fpf)
  (UNC: Mem.unchanged_on (fun b _ => In b (flat_fp_frame fpf)) m1 m2),
    sound_cont an body cfg k next cont brk nret m2 fpf.
Proof.
  induction k; intros; inv SOUND; try (econstructor; eauto; fail).
  - econstructor; eauto. inv MSTK.
    econstructor; eauto.
    eapply IHk; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. eapply in_app. right. eapply in_app; auto.
    (* mmatch unchanged *)
    eapply mmatch_unchanged. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite app_assoc. eapply in_app. auto.
    (* wf_env *)
    eapply wf_env_unchanged. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply in_app. auto.
  - econstructor; eauto.
    eapply IHk; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite !app_assoc. eapply in_app. auto.
    eapply mmatch_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite app_assoc. eapply in_app. auto.
    (* wf_env *)
    eapply wf_env_unchanged. eauto.
    eapply Mem.unchanged_on_implies; eauto.
    intros. simpl. eapply in_app. auto.
    (* sound_drop_place_state unchanged *)
    eapply sound_drop_place_state_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. erewrite app_assoc with (n:= flat_fp_frame fpf0).
    erewrite app_assoc. eapply in_app; auto.
  - econstructor; eauto.
    eapply drop_member_footprint_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite !in_app. destruct H; subst; auto.
    eapply member_footprint_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite !in_app. destruct H; subst; auto.
    eapply IHk; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. rewrite !in_app. auto.
Qed.

Lemma sound_stacks_unchanged_on: forall k m1 m2 fpf
    (SOUND: sound_stacks k m1 fpf)
    (UNC: Mem.unchanged_on (fun b _ => In b (flat_fp_frame fpf)) m1 m2),
    sound_stacks k m2 fpf.
Proof.
  induction k; intros; try (inv SOUND; econstructor; eauto).
  eapply sound_cont_unchanged; eauto.
  eapply Mem.unchanged_on_implies; eauto. simpl.
  intros. rewrite !in_app. auto.
  eapply mmatch_unchanged; eauto.
  eapply Mem.unchanged_on_implies; eauto. simpl.
  intros. rewrite app_assoc. rewrite in_app. auto.
  eapply wf_env_unchanged. eauto.
  eapply Mem.unchanged_on_implies; eauto.
  intros. simpl. eapply in_app. auto.
Qed.

  
Lemma call_cont_sound: forall k ck maybeInit maybeUninit universe body cfg next cont brk nret m fpf
    (CONT: sound_cont (maybeInit, maybeUninit, universe) body cfg k next cont brk nret m fpf)
    (CC: call_cont k = Some ck),
    sound_stacks ck m fpf.
Proof.
  induction k; intros; simpl; inv CC; inv CONT; eauto; econstructor.
Qed.
  

Lemma valid_owner_same: forall p,
    (forall (ty : type) (fid : ident), ~ In (ph_downcast ty fid) (snd (path_of_place p))) ->
    valid_owner p = p.
Proof.
  induction p; intros; simpl in *; auto.
  destruct (path_of_place p). simpl in H.
  generalize (H (typeof_place p) i).
  intros. exfalso. eapply H0.
  eapply in_app. right. simpl. auto.
Qed.

Lemma sound_split_fully_own_place_app: forall l1 l2 m p1 p2 p3 b1 b2 b3 ofs1 ofs2 ofs3 fp1 fp2 fp3 ty2 ty3,
    sound_split_fully_own_place m p1 b1 ofs1 fp1 l1 p2 b2 ofs2 ty2 fp2 ->
    sound_split_fully_own_place m p2 b2 ofs2 fp2 l2 p3 b3 ofs3 ty3 fp3 ->
    sound_split_fully_own_place m p1 b1 ofs1 fp1 (l2++l1) p3 b3 ofs3 ty3 fp3.
Proof.
  induction l2; intros.
  - exploit sound_split_fully_own_place_type_inv. eapply H. intros. subst.
    inv H0. simpl.   auto.
  - inv H0. exploit sound_split_fully_own_place_type_inv. eapply H. intros. subst.
    simpl. econstructor.
    eapply IHl2; eauto. all: eauto.
Qed.

(* Used to prove gen_drop_place_state_sound. We only consider non-empty list. *)
Lemma split_fully_own_place_sound: forall ty p m b ofs fp p0 l
    (PTY: typeof_place p = ty)
    (SPLIT: split_fully_own_place p ty = p0 :: l)
    (WTLOC: sem_wt_loc ce m fp b ofs)
    (WTFP: wt_footprint ce (typeof_place p) fp),
    exists b1 ofs1 fp1,
      sound_split_fully_own_place m p b ofs fp l p0 b1 ofs1 (typeof_place p0) fp1
      /\ sem_wt_loc ce m fp1 b1 ofs1
      /\ wt_footprint ce (typeof_place p0) fp1.
Proof.
  induction ty; intros; simpl in *; try congruence.
  - destruct l.
    + eapply app_eq_unit in SPLIT. destruct SPLIT as [[A1 A2]|[B1 B2]]; try congruence.
      inv A2.
      exists b, ofs, fp. repeat apply conj; auto.
      econstructor.
    + destruct (split_fully_own_place (Pderef p ty) ty) eqn: SPLIT1; simpl in SPLIT; try congruence.
      inv SPLIT.
      (* get fp *)
      rewrite PTY in WTFP. inv WTFP. inv WTLOC. simpl in WF. congruence.
      inv WTLOC. inv WT0.
      exploit IHty. 2: eauto. simpl. auto.
      eapply WTLOC. simpl. auto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      exists b1, ofs1, fp1. repeat apply conj; auto.
      eapply sound_split_fully_own_place_app.
      econstructor. erewrite <- PTY. econstructor.
      all: auto. 
  - destruct l0; try congruence. inv SPLIT.
    exists b, ofs, fp. repeat apply conj; auto.
      econstructor.
  - destruct l0; try congruence. inv SPLIT.
    exists b, ofs, fp. repeat apply conj; auto.
    econstructor.
Qed.

  
Lemma split_fully_own_place_cons_type: forall ty p p1 l,
    typeof_place p = ty ->
    split_fully_own_place p ty = p1 :: l ->
    (exists orgs id, typeof_place p1 = Tstruct orgs id)
    \/ (exists orgs id, typeof_place p1 = Tvariant orgs id)
    \/ (exists ty, typeof_place p1 = Tbox ty).
Proof.
  induction ty; intros; simpl in *; try congruence.
  - destruct l.
    + eapply app_eq_unit in H0. destruct H0 as [[A1 A2]|[B1 B2]]; try congruence.
      inv A2. eauto.
    + destruct (split_fully_own_place (Pderef p ty) ty) eqn: SPLIT1; simpl in H0; try congruence.
      inv H0.
      eapply IHty. instantiate (1 := Pderef p ty). auto. eauto.
  - inv H0. eauto.
  - inv H0. eauto.
Qed.
    
Lemma gen_drop_place_state_sound: forall p own fp b ofs m empfp fpm (le: env),
    wt_place le ce p ->
    dominators_is_init own p = true ->
    sem_wt_loc ce m fp b ofs ->
    wt_footprint ce (typeof_place p) fp ->
    get_loc_footprint_map le (path_of_place p) fpm = Some (b, ofs, empfp) ->
    list_norepet (footprint_flat fp) ->
    sound_drop_place_state le m fpm own fp (Some (gen_drop_place_state p)).
Proof.
  intros until le; intros WTP DOM WTLOC WTFP GFP NOREP; unfold gen_drop_place_state.
  destruct (split_fully_own_place p (typeof_place p)) eqn: SPLIT.
  - econstructor; eauto.
    econstructor.
  - exploit split_fully_own_place_cons_type; eauto.
    intros. destruct H as [A|B]. 2: destruct B.
    + destruct A as (orgs & id & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      econstructor; eauto.
    + destruct H as (orgs & id & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      econstructor; eauto.
    + destruct H as (ty & TYP1).
      rewrite TYP1.
      exploit split_fully_own_place_sound. 2: eauto. 1-3: eauto.
      intros (b1 & ofs1 & fp1 & A1 & A2 & A3).
      rewrite TYP1 in *.
      inv A3. inv A2. simpl in WF. congruence.
      inv A2. inv WT0.
      econstructor; eauto.
      econstructor; eauto.
Qed.
          
(* Extract useful properties if only the fpm is changed *)
Lemma list_norepet3_fpm_changed {A: Type} : forall (le fpm fpf: list A),
    list_norepet (le ++ fpm ++ fpf) ->
    list_norepet (le ++ fpf)
    /\ list_norepet fpm 
    /\ list_disjoint (le ++ fpf) fpm
    (* used in get_loc_footprint_norepet *)
    /\ list_disjoint le fpm
    (* the separation of stack and heap *)
    /\ list_norepet (le ++ fpm)
    (* used to prove that block changed in le ++ fpm must be not in
    fpf, which is used to prove sound_cont *)
    /\ list_disjoint (le ++ fpm) fpf.
Proof.
  intros until fpf. intros N1.
  generalize N1 as N2. intros.
  eapply list_norepet_append_commut2 in N1.
  rewrite app_assoc in N1. eapply list_norepet_app in N1 as (N3 & N4 & N5).
  rewrite app_assoc in N2. eapply list_norepet_app in N2 as (A1 & A2 & A3).
  repeat apply conj; auto.
  eapply list_norepet_app in A1 as (B1 & B2 & B3). auto.
Qed.

Definition flat_fp_struct (fpl: list (ident * Z * footprint)) :=
  map (fun '(_, _, fp) => fp) fpl.

Lemma field_type_skip_prefix: forall ms1 ms2 id,
    ~ In id (name_members ms1) ->
    field_type id (ms1 ++ ms2) = field_type id ms2.
Proof.
  induction ms1; simpl in *; try congruence; intros.
  eapply Decidable.not_or in H. destruct H.
  destruct ident_eq; try congruence.
  eauto.
Qed.

  
Lemma name_members_app: forall ms1 ms2,
    name_members (ms1 ++ ms2) = name_members ms1 ++ name_members ms2.
Proof.
  unfold name_members. eapply map_app.
Qed.

Lemma sem_wt_member_footprint: forall co fpl ms b ofs m
   (STR: co_sv co = Struct)
   (INCL: exists ms', ms' ++ ms = (co_members co))
   (NOREP: list_norepet (name_members (co_members co)))
   (* (WT1: forall (fid : ident) (fty : type), *)
   (*     field_type fid ms = OK fty -> *)
   (*     exists (ffp : footprint) (fofs : Z), *)
   (*       find_fields fid fpl = Some (fid, fofs, ffp) /\ *)
   (*         field_offset ce fid (co_members co) = OK fofs /\ wt_footprint ce fty ffp) *)
   (WT2: forall (fid : ident) (fofs : Z) (ffp : footprint),
       find_fields fid fpl = Some (fid, fofs, ffp) ->
       exists fty : type,
         field_type fid (co_members co) = OK fty /\
           field_offset ce fid (co_members co) = OK fofs /\ wt_footprint ce fty ffp)
    (FWT : forall (fid : ident) (fofs : Z) (ffp : footprint),
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        sem_wt_loc ce m ffp b (ofs + fofs))
    (FLAT: name_footprints fpl = name_members ms),
    list_forall2 (member_footprint m co b ofs) (flat_fp_struct fpl) ms.
Proof.
  induction fpl; simpl in *; intros.
  destruct ms; simpl in FLAT; inv FLAT. econstructor.
  destruct a. destruct p. destruct ms; simpl in FLAT; inv FLAT.
  destruct m0. simpl in *.
  destruct INCL as (ms' & A1). rewrite <- A1 in *.
  generalize NOREP as NOREP1. intros.
  rewrite name_members_app in NOREP.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3).
  exploit (WT2 id z f).
  simpl. destruct ident_eq; try congruence; auto.
  intros (fty & A2 & A3 & A4). 
  econstructor.
  econstructor; eauto. rewrite <- A1. eauto.
  rewrite <- A1. erewrite field_type_skip_prefix. simpl. destruct ident_eq; try congruence.
  intro. eapply N3; eauto. simpl. auto.
  eapply FWT with (fid := id). destruct ident_eq; try congruence; auto.
  erewrite field_type_skip_prefix in A2. simpl in A2. destruct ident_eq in A2; try congruence.
  intro. eapply N3; eauto. simpl. auto.
  eapply IHfpl; eauto. 
  exists (ms' ++ [Member_plain id t]). erewrite <- app_assoc. simpl. auto.  
  (* WT2 *)
  intros. eapply WT2.
  (* we need to show that fid must not be equal to id otherwise B1 is
  a contradiction because id is not in fpl due to H1 and NOREP *)  
  destruct ident_eq; subst.
  exploit find_fields_some; eauto. intros (B1 & B2).
  inv N2. rewrite <- H1 in H3.
  exfalso. eapply H3. eapply in_map_iff.
  exists (id, fofs, ffp). eauto.
  auto.
  (* FWT *)
  intros. eapply FWT with (fid := fid).
  destruct ident_eq; subst.
  exploit find_fields_some; eauto. intros (B1 & B2).
  inv N2. rewrite <- H1 in H3.
  exfalso. eapply H3. eapply in_map_iff.
  exists (id, fofs, ffp). eauto. auto.
Qed.  


Lemma list_equiv_norepet1 {A: Type}: forall (l1 l2 l3 l4: list A),
    list_norepet (l1 ++ l2) ->
    list_equiv (l1 ++ l2) l3 ->
    list_norepet (l4 ++ l3) ->
    list_norepet (l4 ++ l1)
    /\ list_norepet (l4 ++ l2)
    /\ list_disjoint l1 (l4 ++ l2).
Proof.
  intros. eapply list_norepet_app in H as (A1 & A2 & A3).
  eapply list_norepet_app in H1 as (B1 & B2 & B3).
  repeat apply conj.
  - eapply list_norepet_app.
    repeat apply conj; auto.
    red. intros. eapply B3. auto.
    eapply H0. eapply in_app; auto. 
  - eapply list_norepet_app.
    repeat apply conj; auto.
    red. intros. eapply B3. auto.
    eapply H0. eapply in_app; auto.
  - red. intros. eapply in_app in H1. destruct H1.
    + eapply list_disjoint_sym in B3. eapply B3; auto.
      eapply H0. eapply in_app; auto.
    + eapply A3; auto.
Qed.

Lemma list_equiv_norepet2 {A: Type}: forall (l1 l2 l3 l4: list A),
    list_norepet (l1 ++ l2) ->
    list_equiv (l3 ++ l4) l2 ->
    list_norepet (l3 ++ l4) ->
    list_norepet (l1 ++ l3 ++ l4).
Proof.
  intros until l4. intros A1 A2 A3.
  eapply list_norepet_app.
  eapply list_norepet_app in A1 as (N1 & N2 & N3).
  repeat apply conj; auto.
  red. intros.
  eapply A2 in H0. eauto.
Qed.

(* The footprint constructed by extracting fp from l2 is still
norepet *)
Lemma dropplace_to_dropstate_footprint_norepet: forall (l0 l1 l2 l3 l2' fp: flat_footprint)

    (EQUIV: list_equiv (fp ++ l2') l2)
    (NOREP: list_norepet (l0 ++ l1 ++ l2 ++ l3))
    (NOREP1: list_norepet (fp ++ l2')),
    list_norepet (fp ++ l0 ++ l1 ++ l2' ++ l3).
Proof.
  intros.
  eapply list_norepet_append_commut.
  rewrite !app_assoc.
  rewrite <- (app_assoc _ _ fp).
  rewrite <- (app_assoc _ l2' _).
  rewrite app_assoc in NOREP.        
  eapply list_norepet_append_commut2.
  rewrite <- !app_assoc.
  do 2 rewrite app_assoc.
  eapply list_norepet_append_commut2 in NOREP.
  rewrite app_assoc in NOREP.
  eapply list_equiv_norepet2; eauto.
Qed.

Lemma dropstate_to_dropstate_footprint_norepet: forall (l1 l2 l3 l1' fp: flat_footprint)
    (EQUIV: list_equiv (fp ++ l1') l1)
    (NOREP: list_norepet (l1 ++ l2 ++ l3))
    (NOREP1: list_norepet (fp ++ l1')),
    list_norepet (fp ++ l1' ++ l2 ++ l3).
Proof.
  intros.
  rewrite app_assoc.
  eapply list_norepet_append_commut.
  eapply list_equiv_norepet2.
  eapply list_norepet_append_commut. eauto.
  auto. auto.
Qed.


Lemma state_to_callstate_footprint_norepet: forall (l1 l2 l3 fpl l2': flat_footprint)
    (EQUIV: list_equiv (fpl ++ l2') l2)
    (NOREP: list_norepet (l1 ++ l2 ++ l3))
    (NOREP1: list_norepet (l2' ++ fpl)),
    list_norepet (l1 ++ l2' ++ l3 ++ fpl).
Proof.
  intros.
  eapply list_norepet_append_commut2.
  eapply list_norepet_append_commut2 in NOREP.
  rewrite <- app_assoc, app_assoc. rewrite app_assoc in NOREP.
  eapply list_norepet_app in NOREP as (N1 & N2 & N3).
  eapply list_norepet_app.
  repeat apply conj; auto.
  eapply list_norepet_append_commut. eauto.
  red. intros. eapply N3; eauto.
  eapply EQUIV. auto.
Qed.


Lemma footprint_flat_fp_struct_eq: forall id fpl,
    footprint_flat (fp_struct id fpl) = flat_map footprint_flat (flat_fp_struct fpl).
Proof.
  induction fpl; simpl; intros; auto.
  destruct a. destruct p.
  f_equal. eapply IHfpl.
Qed.



Lemma deref_loc_rec_footprint_eq: forall tys m b ofs fty fp b1 ofs1 ty1 fp1 b2 ofs2,
    deref_loc_rec_footprint m b (Ptrofs.unsigned ofs) fty fp tys b1 ofs1 ty1 fp1 ->
    deref_loc_rec m b ofs tys (Vptr b2 ofs2) ->
    b1 = b2 /\ ofs1 = Ptrofs.unsigned ofs2.
Proof.
  induction tys; intros.
  - inv H0. inv H. auto.
  - inv H0. inv H. exploit IHtys; eauto.
    intros (A1 & A2). subst.
    inv H5. simpl in H0. simpl in H. inv H. rewrite LOAD in H0. inv H0.
    auto.
    simpl in H0; congruence.
    simpl in H0; congruence.
Qed.

Lemma deref_loc_rec_app: forall l1 l2 b1 b2 b3 ofs1 ofs2 ofs3 m,
    deref_loc_rec m b1 ofs1 l2 (Vptr b2 ofs2) ->
    deref_loc_rec m b2 ofs2 l1 (Vptr b3 ofs3) ->
    deref_loc_rec m b1 ofs1 (l1 ++ l2) (Vptr b3 ofs3).
Proof.
  induction l1; intros.
  - inv H0. simpl. auto.
  - inv H0. econstructor; eauto.
Qed.

(* If the footprint not in fp1 is unchanged,
deref_loc_rec_footprint remains valid *)
Lemma deref_loc_rec_footprint_unchanged: forall l m1 m2 b ofs  ty fp b1 ofs1 ty1 fp1
    (DEF: deref_loc_rec_footprint m1 b ofs ty fp l b1 ofs1 ty1 fp1)
    (UNC: Mem.unchanged_on (fun b' _ => ~ In b' (footprint_flat fp1)) m1 m2)
    (NIN: ~ In b (footprint_flat fp))
    (NOREP: list_norepet (footprint_flat fp)),
    deref_loc_rec_footprint m2 b ofs ty fp l b1 ofs1 ty1 fp1.
Proof.
  induction l; intros.
  - inv DEF. econstructor.
  - inv DEF.
    exploit deref_loc_rec_footprint_get; eauto. intros GFP.
    exploit get_loc_footprint_norepet; eauto. intros (N1 & N2).
    (* exploit get_loc_footprint_in; eauto. intros IN. *)
    exploit IHl; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro. eapply H. auto.
    intros DEF1.
    econstructor; eauto.
    (* load *)
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros.
    intro. eapply N2. simpl. eauto.
    (* load size record *)
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros.
    simpl in N1. inv N1. eauto.
    (* range_perm *)
    red. intros. eapply Mem.perm_unchanged_on; eauto.
    simpl.
    simpl in N1. inv N1. eauto.
Qed.

(* We need to prove that freeing the blocks in l1 does not change the
address computing of deref_loc_rec *)
Lemma drop_box_rec_app: forall l1 l2 b1 ofs1 b2 ofs2 m1 m2 m3 b3 ofs3 ty ty1 fp fp1
    (DFP: deref_loc_rec_footprint m1 b2 (Ptrofs.unsigned ofs2) ty fp l1 b3 ofs3 ty1 fp1)
    (NIN: ~ In b2 (footprint_flat fp))
    (* freeing the blocks of l1 does not change the result of
    deref_loc_rec in l2 *)
    (NOREP: list_norepet (footprint_flat fp))
    (UNC: forall m1', Mem.unchanged_on (fun b' _ => ~ In b' (footprint_flat fp)) m1 m1' ->
                 deref_loc_rec m1' b1 ofs1 l2 (Vptr b2 ofs2)) 
    (DLOC: deref_loc_rec m1 b1 ofs1 l2 (Vptr b2 ofs2))      
    (DROP1: drop_box_rec ge b2 ofs2 m1 l1 m2)
    (DROP2: drop_box_rec ge b1 ofs1 m2 l2 m3),
    drop_box_rec ge b1 ofs1 m1 (l1 ++ l2) m3.
Proof.
  induction l1; intros.
  - inv DROP1. simpl. auto.
  - replace (a::l1) with ((a::nil) ++ l1) in DFP by auto.
    exploit deref_loc_rec_footprint_app_inv. eauto.
    intros (b4 & ofs4 & ty2 & fp2 & A1 & A2).
    inv A1. inv DEREF.
    (* remove b3 from (fp_box b3 ...) *)
    exploit deref_loc_rec_footprint_set; eauto.
    instantiate (1 := clear_footprint_rec (fp_box b3 (sizeof ce ty1) fp1)).
    intros (rfp1 & B1 & B2 & B3).
    (* show rfp1 is norepet *)
    assert (NOREP1: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      simpl. econstructor. simpl. red. intros. inv H0. }
    inv DROP1. inv H2; simpl in *; try congruence. inv H.
    econstructor.
    eapply deref_loc_rec_app; eauto.
    econstructor; eauto. simpl. auto.
    eauto.
    (* show that the result of A2 and B3 are the same address *)
    exploit deref_loc_rec_footprint_eq; eauto. intros (C1 & C2). subst.
    rewrite LOAD in H0. inv H0.
    (* show fp = rfp1 + b5 *)
    generalize (get_clear_footprint_equiv _ _ _ _  B1 B2); eauto.
    intros EQUIV.
    exploit get_footprint_norepet. eapply NOREP. eauto.
    simpl. intros NOREP2. inv NOREP2.
    (* apply I.H. *)
    eapply IHl1.
    (* deref_loc_rec_footprint: we need to show that b2 not in fp *)
    eapply deref_loc_rec_footprint_unchanged. eapply A2.
    inv H4.
    eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply H0. simpl. auto.
    (* not in *)
    all: eauto.
    (* intro. eapply H0. eapply EQUIV. *)
    (* eapply in_app. simpl. eauto. *)
    (* unchanged *)
    inv H4.
    intros. eapply UNC.
    eapply Mem.unchanged_on_trans.
    eapply Mem.free_unchanged_on; eauto.
    (* show b5 in fp *)
    intros. intro. eapply H4. eapply EQUIV.
    eapply in_app. simpl. eauto.
    eapply Mem.unchanged_on_implies; eauto. 
    (* deref_loc_rec in m0 *)
    eapply UNC. inv H4.
    eapply Mem.free_unchanged_on. eauto.
    intros.
    intro. eapply H0.
    eapply EQUIV.
    eapply in_app. simpl. eauto. 
Qed.


(* We prove that deref_loc_rec_footprint can make drop_box_rec a total function *)
Lemma drop_box_rec_progress_and_unchanged: forall tys b ofs m1 fp ty b1 ofs1 ty1 fp1
    (* norepet is to make sure that DEREF can hold if we free a block in m1 *)
    (NOREP: list_norepet (footprint_flat fp))
    (* we need to consider b = b1 in induction case *)
    (NIN: ~ In b (footprint_flat fp))
    (DEREF: deref_loc_rec_footprint m1 b (Ptrofs.unsigned ofs) ty fp tys b1 ofs1 ty1 fp1),
    (* We do not care fp1 is changed or not  *)
    exists m2,
      drop_box_rec ge b ofs m1 tys m2
      /\ Mem.unchanged_on (fun b1 _ => ~ In b1 (footprint_flat fp)) m1 m2.
Proof.
  intro. cut (exists n, length tys = n); eauto. intros (n & LEN).
  generalize dependent tys.
  induction n; intros.
  - eapply length_zero_iff_nil in LEN. subst. simpl in *.
    inv DEREF. exists m1. split.
    econstructor.
    eapply Mem.unchanged_on_refl.
  - eapply length_S_inv in LEN. destruct LEN as (tys' & ty' & APP & LEN).
    subst.
    exploit deref_loc_rec_footprint_app_inv; eauto.
    intros (b2 & ofs2 & ty2 & fp2 & A1 & A2). inv A2. inv DEREF0.
    replace 0 with (Ptrofs.unsigned Ptrofs.zero) in A1 by auto.
    simpl in NOREP. inv NOREP.
    exploit IHn. eauto. 
    3: eapply A1. auto.
    auto.
    intros (m2 & DROP & UNC1).
    (* show that we can free b2 in m2 *)
    exploit Mem.load_unchanged_on. eapply UNC1.
    2: eapply SIZE. auto. intros SIZE1.
    assert (PERM1: Mem.range_perm m2 b2 (- size_chunk Mptr) (sizeof ce ty2) Cur Freeable).
    { red. intros. erewrite<- Mem.unchanged_on_perm. eapply PERM. auto.
      eauto. auto.
      eapply Mem.perm_valid_block; eauto. }
    assert (FREE1: {m2'| Mem.free m2 b2 (-size_chunk Mptr) (sizeof ce ty2) = Some m2'}).
    { eapply Mem.range_perm_free; eauto. }
    destruct FREE1 as (m2' & FREE1).
    assert (FREE2: extcall_free_sem ge [Vptr b2 Ptrofs.zero] m2 E0 Vundef m2').
    { econstructor; eauto.
      rewrite Ptrofs.unsigned_repr; lia.
      rewrite <- FREE1. f_equal.
      rewrite Ptrofs.unsigned_zero. simpl.
      rewrite Ptrofs.unsigned_repr; lia. }
    exists m2'. split.
    eapply drop_box_rec_app; eauto.
    (* unchanged_on *)
    intros. econstructor; eauto. econstructor.
    econstructor. simpl. eauto.
    simpl. eapply Mem.load_unchanged_on; eauto.
    simpl. intros. simpl in NIN. intro. eapply NIN. auto.
    (* deref_loc_rec *)
    econstructor; eauto. econstructor.
    econstructor; simpl; eauto.
    (* drop_box_rec *)
    econstructor;eauto.
    econstructor. econstructor; simpl; eauto.
    eapply Mem.load_unchanged_on; eauto.
    simpl. intros.
    simpl in NIN. intro. eapply NIN. auto.
    econstructor.
    (* unchanged_on *)
    simpl. eapply Mem.unchanged_on_trans.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro. eapply H. auto.
    eapply Mem.free_unchanged_on; eauto.
Qed.


Lemma rsw_acc_shrink: forall m1 m2 sg fp1 fp2 Hm1,
    incl fp2 fp1 ->
    Mem.unchanged_on (fun b _ => ~ In b fp1) m1 m2 ->
    exists Hm2, rsw_acc (rsw sg fp1 m1 Hm1) (rsw sg fp2 m2 Hm2).
Proof.
  intros.
  assert (Hm2: Mem.sup_include fp2 (Mem.support m2)).
  { eapply Mem.sup_include_trans. eapply H.
    eapply Mem.sup_include_trans. eapply Hm1.
    eapply Mem.unchanged_on_support; eauto. }
  exists Hm2. econstructor. auto.
  eapply flat_footprint_separated_shrink; eauto.
Qed.


Lemma field_offset_in_range_add: forall fofs fty ofs co,
    co_sizeof co <= Ptrofs.max_unsigned ->
    (0 <= fofs /\ fofs + sizeof ge fty <= co_sizeof co) ->
    (Ptrofs.unsigned ofs) + co_sizeof co <= Ptrofs.max_unsigned ->
    Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr fofs)) = Ptrofs.unsigned ofs + fofs.
Proof.
  intros until co. intros COSZ R OFS.
  destruct R as (R1 & R2).
  generalize (sizeof_pos ge fty). intros R3.
  rewrite Ptrofs.add_unsigned.
  rewrite !Ptrofs.unsigned_repr. auto.
  lia.
  rewrite Ptrofs.unsigned_repr.
  generalize (Ptrofs.unsigned_range ofs).
  lia. lia.
Qed.  


Lemma step_dropstate_sound: forall s1 t s2,
    sound_state s1 ->
    step_drop ge s1 t s2 ->
    sound_state s2.
Proof.
  intros s1 t s2 SOUND (* WTST *) STEP.
  inv STEP.
  (* step_dropstate_init *)
  - inv SOUND. inv DROPMEMB.
    inv MEMBFP. inv H2.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp (a1 :: al) fpf)) m Hm)
                           (rsw sg (flat_fp_frame (fpf_drop a1 al fpf)) m Hm1)).
    { eapply rsw_acc_shrink. simpl.
      eapply incl_appr. rewrite <- app_assoc. eapply incl_refl.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropstate; eauto.
    eapply sound_type_to_drop_member_state; eauto.
    rewrite STRUCT. auto.
    (* norepet *)
    simpl in NOREP. simpl.
    rewrite <- app_assoc in NOREP.
    eapply list_norepet_append_right. eauto.
    (* disjoint *)
    intro. eapply DIS. simpl in H. simpl.
    eapply in_app. eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    (* wt_state*)
  (* step_dropstate_struct *)
  - inv SOUND.
    inv DROPMEMB.
    (* prove that (Ptrofs.unsigned ofs1 + fofs0) is in the range *)
    unfold ce in *.
    rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty <= co_sizeof co).
    { destruct (co_sv co) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit variant_field_offset_in_range_complete; eauto. lia. }
    exploit field_offset_in_range_add. eapply COMP_RANGE. eapply CO1. all: eauto. 
    intros OFSEQ.
    rewrite <- OFSEQ in FFP.
    exploit deref_loc_rec_footprint_eq; eauto. intros (E1 & E2). subst.
    (* construct the footprint list for the members to be dropped *)
    inv WTFP; inv WTLOC. simpl in WF. congruence.
    exploit sem_wt_member_footprint; eauto.
    exists nil. auto. intros MEMWT.
    (* show that (fp_struct id2 fpl0) is norepet and cb not in fpl0 *)
    assert (NOREP1: list_norepet (footprint_flat fp)).
    { simpl in NOREP. eapply list_norepet_append_left. eauto. }
    exploit deref_loc_rec_footprint_norepet; eauto. 
    intro. eapply DIS. eapply in_app; eauto. intros (N1 & N2).
    (* show that cb is in (b1::fp) *)
    exploit deref_loc_rec_footprint_in; eauto. intros IN.
    (* remove (fp_struct id2 fpl0) from fp *)
    generalize FFP as FFP1. intros.
    eapply deref_loc_rec_footprint_set with (fp2 := clear_footprint_rec (fp_struct id2 fpl0)) in FFP1.
    destruct FFP1 as (rfp1 & GFP1 & SFP1 & FFP2).
    (* some rewrites *)
    rewrite CO2 in CO. inv CO.
    (* norepet *)
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      rewrite empty_footprint_flat. econstructor.
      eapply empty_footprint_disjoint. }
    assert (EQUIV1: list_equiv (footprint_flat (fp_struct id2 fpl0) ++ footprint_flat rfp1)
                      (footprint_flat fp)).
    { eapply get_clear_footprint_equiv; eauto. }
    assert (NOREP3: list_norepet
                      (flat_fp_frame (fpf_drop fp_emp (flat_fp_struct fpl0) (fpf_drop rfp1 fpl fpf)))).
    { simpl. simpl in NOREP.
      erewrite <- (footprint_flat_fp_struct_eq id2); eauto.
      eapply dropstate_to_dropstate_footprint_norepet; eauto.
      eapply list_norepet_app. repeat apply conj.
      eapply get_footprint_norepet. eapply NOREP1. eauto.
      auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint; eauto.
      rewrite empty_footprint_flat. red. intros. inv H0. }
    (* range *)
    assert (R5: Ptrofs.unsigned cofs + co_sizeof co0 <= Ptrofs.max_unsigned).
    { specialize (deref_loc_rec_footprint_range _ _ _ _ _ _ _ _ _ _ FFP2).
      rewrite OFSEQ. simpl. unfold ce. rewrite CO2. intros. eapply H.
      lia. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp fpl fpf)) m Hm)
                     (rsw sg (flat_fp_frame (fpf_drop fp_emp (flat_fp_struct fpl0) (fpf_drop rfp1 fpl fpf))) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros.
      erewrite !in_app in H.
      erewrite !in_app.
      destruct H. left. eapply EQUIV1.
      erewrite <- (footprint_flat_fp_struct_eq id2 fpl0) in H. eapply in_app; auto.
      repeat destruct H; auto. left. eapply EQUIV1. eapply in_app; auto.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).    
    eapply sound_dropstate with (fp:= fp_emp) (fpf:= (fpf_drop rfp1 fpl fpf)) (fpl:= (flat_fp_struct fpl0)); eauto.
    econstructor.
    (* sound_cont *)
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- OFSEQ. eauto.
    intro. eapply DIS. eapply in_app_iff in H. eapply in_app.
    destruct H; auto. left.
    eapply EQUIV1. eapply in_app; auto.
    (* disjoint *)
    simpl. erewrite <- footprint_flat_fp_struct_eq. eauto.
    (* cb in (fpf_drop rfp1 fpl fpf) *)
    simpl. erewrite !in_app. inv IN; auto.
    eapply EQUIV1 in H. eapply in_app in H. destruct H; try congruence. auto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    
  (* step_dropstate_enum *)
  - inv SOUND.
    inv DROPMEMB.
    (* prove that (Ptrofs.unsigned ofs1 + fofs0) is in the range *)
    unfold ce in *.
    rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty1 <= co_sizeof co).
    { destruct (co_sv co) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit (variant_field_offset_in_range_complete ge co); eauto. lia. }
    destruct R as (R1 & R2).
    generalize (sizeof_pos ge fty1). intros R3.
    generalize (COMP_RANGE id1 co CO1). intros R4.
    rewrite Ptrofs.add_unsigned in DEREF.
    rewrite Ptrofs.unsigned_repr in DEREF. 2: lia.
    (* show that deref_loc_rec and deref_loc_rec_footprint return the same address *)
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs1 + fofs0)) = (Ptrofs.unsigned ofs1 + fofs0)).
    { erewrite Ptrofs.unsigned_repr. auto.
      generalize (Ptrofs.unsigned_range ofs1). lia. }
    rewrite <- OFSEQ in FFP.
    exploit deref_loc_rec_footprint_eq; eauto. intros (E1 & E2). subst.
    (* show that fp1 is fp_enum *)
    inv WTFP; inv WTLOC. simpl in MODE. congruence.
    (* show that (fp_struct id2 fpl0) is norepet and cb not in fpl0 *)
    assert (NOREP1: list_norepet (footprint_flat fp)).
    { simpl in NOREP. eapply list_norepet_append_left. eauto. }
    exploit deref_loc_rec_footprint_norepet; eauto. 
    intro. eapply DIS. eapply in_app; eauto. intros (N1 & N2).
    (* show that cb is in (b1::fp) *)
    exploit deref_loc_rec_footprint_in; eauto. intros IN.
    (* remove (fp_enum id2 orgs tagz fid fofs fp0) from rfp *)
    generalize FFP as FFP1. intros.
    eapply deref_loc_rec_footprint_set with (fp2 := clear_footprint_rec (fp_enum id2 orgs tagz fid fofs fp0)) in FFP1.
    destruct FFP1 as (rfp1 & GFP1 & SFP1 & FFP2).
    (* some rewrites *)
    rewrite CO2 in CO. inv CO.
    (* norepet *)
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      rewrite empty_footprint_flat. econstructor.
      eapply empty_footprint_disjoint. }
    assert (EQUIV1: list_equiv (footprint_flat (fp_enum id2 orgs tagz fid fofs fp0) ++ footprint_flat rfp1)
                      (footprint_flat fp)).
    { eapply get_clear_footprint_equiv; eauto. }
    assert (NOREP3: list_norepet
                      (flat_fp_frame (fpf_drop fp0 nil (fpf_drop rfp1 fpl fpf)))).
    { simpl. simpl in NOREP.
      eapply dropstate_to_dropstate_footprint_norepet; eauto.
      eapply list_norepet_app. repeat apply conj.
      exploit get_footprint_norepet. eapply NOREP1. eauto. simpl. auto.
      auto.
      eapply list_disjoint_sym.
      red. intros.
      eapply get_set_disjoint_footprint; eauto. 
      simpl. red. intros. inv H2. }            
    (* range *)
    assert (R5: Ptrofs.unsigned cofs + co_sizeof co0 <= Ptrofs.max_unsigned).
    { specialize (deref_loc_rec_footprint_range _ _ _ _ _ _ _ _ _ _ FFP2).
      rewrite OFSEQ. simpl. unfold ce. rewrite CO2. intros. eapply H.
      lia. }
    (* show that fp satisfies drop_member_footprint *)
    exploit sound_type_to_drop_member_state; eauto. rewrite ENUM0. eauto.
    intros MEMFP.
    (* show tag = tagz and then fid2 = fid *)
    simpl in TAG. rewrite TAG in TAG1. inv TAG1. 
    eauto. rewrite Int.unsigned_repr in MEMB. rewrite MEMB in TAG0. inv TAG0.
    (* show that tag is in range *)
    2: { generalize (list_nth_z_range _ _ TAG0).
         generalize (COMP_LEN id2 co0 CO2). lia. }
    assert (RACC: exists Hm1,
               rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp fpl fpf)) m Hm)
                 (rsw sg (flat_fp_frame (fpf_drop fp0 nil (fpf_drop rfp1 fpl fpf))) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros.
      erewrite !in_app in H.
      erewrite !in_app.
      destruct H. left. eapply EQUIV1.
      eapply in_app; auto.
      repeat destruct H; auto. left. eapply EQUIV1. eapply in_app; auto.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropstate with (fp:= fp0) (fpf:= (fpf_drop rfp1 fpl fpf)) (fpl:= nil); eauto.
    econstructor.
    (* sound_cont *)
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- OFSEQ. eauto.
    intro. eapply DIS. eapply in_app_iff in H. eapply in_app.
    destruct H; auto. left.
    eapply EQUIV1. eapply in_app; auto.
    (* disjoint *) 
    simpl. rewrite app_nil_r. simpl in N2. auto.
    (* show cb is in (fpf_drop rfp1 fpl fpf) *)
    simpl. rewrite !in_app. inv IN; auto.
    eapply EQUIV1 in H. eapply in_app in H.
    destruct H; try congruence. auto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
  (* step_dropstate_box *)
  - inv SOUND.
    inv DROPMEMB.
    (* prove that (Ptrofs.unsigned ofs + fofs0) is in the range *)
    unfold ce in *.
    rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty <= co_sizeof co0).
    { destruct (co_sv co0) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit (variant_field_offset_in_range_complete ge co0); eauto. lia. }
    destruct R as (R1 & R2).
    generalize (sizeof_pos ge fty). intros R3.
    generalize (COMP_RANGE id co0 CO1). intros R4.
    rewrite Ptrofs.add_unsigned in DROPB.
    rewrite Ptrofs.unsigned_repr in DROPB. 2: lia.    
    assert (OFSEQ: Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned ofs + fofs0)) = (Ptrofs.unsigned ofs + fofs0)).
    { erewrite Ptrofs.unsigned_repr. auto.
      generalize (Ptrofs.unsigned_range ofs). lia. }
    (* show that fp and fpl are disjoint *)
    generalize NOREP as NOREP1. intros.
    simpl in NOREP1. eapply list_norepet_app in NOREP1 as (N1 & N2 & N3).
    assert (DIS1: list_disjoint (footprint_flat fp) (flat_map footprint_flat fpl)).
    { red. intros. eapply N3; eauto.
      eapply in_app; auto. }
    (* show drop_box_rec must succeed *)
    rewrite <- OFSEQ in FFP.
    exploit drop_box_rec_progress_and_unchanged; eauto.
    simpl in NOREP. eapply list_norepet_app in NOREP. intuition.
    intros (m2 & DROP & UNC).
    exploit drop_box_rec_det. eapply DROPB. eapply DROP. intros. subst.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp fpl fpf)) m Hm)
                           (rsw sg (flat_map footprint_flat fpl ++ flat_fp_frame fpf) m2 Hm1)).
    { eapply rsw_acc_shrink.
      simpl. eapply incl_appr. eapply incl_refl.
      eapply Mem.unchanged_on_implies; eauto. simpl.
      intros. intro. eapply H. eapply in_app; auto. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropstate with (fp:= fp_emp) (fpl:= fpl) (fpf:= fpf); eauto.
    econstructor. 
    (* member_footprint *)
    eapply member_footprint_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto. simpl. intros.
    destruct H. subst.
    intro. eapply DIS. eapply in_app; auto.
    intro. eapply DIS1; eauto.
    (* sound_cont *)
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.    
    intros. simpl. intro.
    eapply N3; eauto. eapply in_app; auto.
    (* disjoint *)
    simpl. intro. eapply DIS. eapply in_app; auto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
  (* step_dropstate_return1 *)
  - inv SOUND. inv DROPMEMB. inv MEMBFP.
    inv CONT.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp nil (fpf_dropplace e fpm rfp fpf0))) m Hm) (rsw sg (flat_fp_frame (fpf_dropplace e fpm rfp fpf0)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. eapply incl_appr. eapply incl_refl.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    econstructor; eauto. 
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
  (* step_dropstate_return2 *)
  - inv SOUND. inv CONT. inv MEMBFP.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_drop fp nil (fpf_drop fp0 fpl0 fpf0))) m Hm) (rsw sg (flat_fp_frame (fpf_drop fp0 fpl0 fpf0)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. eapply incl_appr. eapply incl_refl.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    econstructor; eauto.
    simpl in *. eapply list_norepet_append_right; eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
Qed.
    
Lemma step_dropplace_sound: forall s1 t s2,
    sound_state s1 ->
    step_dropplace ge s1 t s2 ->
    sound_state s2.
Proof.
  intros s1 t s2 SOUND STEP.
  inv STEP.
  (* step_dropplace_init1 *)
  - inv SOUND. inv ORDERED. inv WTPS.
    simpl in *. rewrite NOTOWN in *.
    econstructor; eauto.
  (* step_dropplace_init2 *)
  - inv SOUND. inv ORDERED.
    inv WTPS. rename H1 into WTP. rename H2 into WTPS.
    simpl in *. rewrite OWN in *.
    (* compute the new footprint map: it require some well-formed
    properties of own_env *)
    exploit get_loc_footprint_map_progress. eauto. eauto.
    (* wt_place *)
    instantiate (1 := p). auto.
    (* dominators_is_init *)
    eapply wf_own_dominators; eauto.
    (* place p does not contain downcast *)
    intros. eapply wf_own_no_downcast. eauto.
    eapply is_init_in_universe. eauto.    
    intros (b & ofs & fp & GFP & WTFP).
    (* remove fp from fpm *)
    destruct (path_of_place p) eqn: POP.
    exploit get_set_footprint_map_exists. eauto.
    instantiate (1 := clear_footprint_rec fp). intros (fpm1 & CLR & GFP1).
    (* p has no downcast *)
    assert (forall ty fid, ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. eapply wf_own_no_downcast. eauto. eapply is_init_in_universe. auto. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_dropplace le fpm rfp fpf)) m Hm) (rsw sg (flat_fp_frame (fpf_dropplace le fpm1 fp fpf)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros. 
      rewrite !in_app_iff.
      rewrite !in_app_iff in H0. repeat destruct H0; auto.
      right. left.
      exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
      rewrite empty_footprint_flat in B. inv B.
      right. left.
      eapply get_loc_footprint_map_incl; eauto.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).      
    inv SDP.
    (* destruct the norepet *)
    simpl in NOREP.
    eapply list_norepet3_fpm_changed in NOREP.
    destruct NOREP as (A1 & A2 & A3 & A4 & A5).    
    eapply sound_dropplace with (fpm:=fpm1) (rfp:=fp); eauto.
    (* mmatch: use mmatch_move_place_sound *)
    erewrite <- (valid_owner_same p).
    eapply mmatch_move_place_sound. eauto.
    all: try erewrite valid_owner_same; eauto.
    exists p. split.
    eapply Paths.mem_2. eapply is_init_in_universe. auto.
    apply is_shallow_prefix_refl.
    unfold clear_footprint_map. rewrite POP. rewrite GFP. auto.
    (* norepet of the footprint frame *)
    simpl.
    erewrite (app_assoc (flat_fp_map fpm1)).
    eapply list_norepet_append_commut2.
    rewrite app_assoc.
    eapply list_norepet_app. repeat apply conj; auto.
    eapply list_norepet_app. repeat apply conj.
    eapply set_disjoint_footprint_norepet. 3: eauto. all: eauto.
    erewrite empty_footprint_flat. constructor.
    erewrite empty_footprint_flat. red. intros. inv H1.
    eapply get_loc_footprint_map_norepet; eauto.
    eapply get_set_disjoint_footprint_map; eauto.
    erewrite empty_footprint_flat. red. intros. inv H1.
    red. intros. eapply A3; auto.
    eapply in_app in H1. destruct H1.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    erewrite empty_footprint_flat in B. inv B.
    eapply get_loc_footprint_map_incl; eauto.        
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    (* prove sound_drop_place_state, but first we
    test if sound_drop_place_state is enough or not *)
    exploit MM. erewrite POP. eauto. auto.
    intros (BM & FULL).
    (* prove that full is true then p is_full *)
    destruct full.
    exploit FULL. eapply FULLSPEC. auto. intros WTLOC.
    (* soundness of gen_drop_place_state *)
    exploit move_place_dominator_still_init. eapply wf_own_dominators; eauto.
    intros DOM1. (* inv WTST. inv WT1. *)
    eapply gen_drop_place_state_sound; eauto.
    rewrite POP. eauto.
    eapply get_loc_footprint_map_norepet; eauto.
    (* case2 *)
    { exploit FULLSPEC. left. eauto.
      intros F.
      (* p's type must be Box type *)
      exploit wf_own_type. eauto.
      eapply is_init_in_universe. eauto. auto.
      intros (ty & B3).
      (* how do we know the type of p? How can we ensure that the *)
      (*         footprint of p is fp_emp? *)
      erewrite B3 in *.  inv WTFP;  try congruence.
      inv BM. inv BM.
      eapply sound_drop_place_state_box with (r:=p). erewrite POP.
      eauto.
      (* norepet *)
      eapply get_loc_footprint_map_norepet; eauto.
      (* dominator is init *)
      eapply move_place_dominator_still_init.
      eapply wf_own_dominators; eauto.
      (* sound_split_fully_own_place *)
      econstructor. erewrite <- B3. eapply sound_split_nil; eauto.
      all: eauto. }
    (* wf_env *)
    eapply wf_env_set_wt_footprint with (fp:= clear_footprint_rec fp). eauto.
    eapply wt_footprint_clear. eauto. 
    eapply wf_own_wt_place. eauto. eapply is_init_in_universe. auto.
    rewrite POP. auto.
    (* wf_own_env *)
    eapply wf_own_env_move_place. auto.
  (* step_dropplace_scalar: mostly the same as step_dropplace_init2
  because p is init and the type of p does not affect the proof of
  sound_state *)
  - inv SOUND. inv SDP. simpl in *. rewrite OWN in *.
    inv WTPS. rename H1 into WTP. rename H2 into WTPS.
    (* compute the new footprint map: it require some well-formed
    properties of own_env *)
    exploit get_loc_footprint_map_progress. eauto. eauto.
    (* wt_place *)
    instantiate (1 := p). auto.
    (* dominators_is_init *)
    eapply wf_own_dominators; eauto.
    (* place p does not contain downcast *)
    intros. eapply wf_own_no_downcast. eauto.
    eapply is_init_in_universe. eauto.    
    intros (b & ofs & fp & GFP & WTFP).
    (* remove fp from fpm *)
    destruct (path_of_place p) eqn: POP.
    exploit get_set_footprint_map_exists. eauto.
    instantiate (1 := clear_footprint_rec fp). intros (fpm1 & CLR & GFP1).
    (* p has no downcast *)
    assert (forall ty fid, ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. eapply wf_own_no_downcast. eauto. eapply is_init_in_universe. auto. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (footprint_of_env le ++ flat_fp_map fpm ++ flat_fp_frame fpf) m Hm)  (rsw sg (flat_fp_frame (fpf_dropplace le fpm1 fp_emp fpf)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros. 
      rewrite !in_app_iff.
      rewrite !in_app_iff in H0. repeat destruct H0; auto.
      right. left.
      exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
      rewrite empty_footprint_flat in B. inv B.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropplace with (fpm:=fpm1) (rfp:=fp_emp); eauto.
    (* mmatch: use mmatch_move_place_sound *)
    erewrite <- (valid_owner_same p).
    eapply mmatch_move_place_sound. eauto.
    all: try erewrite valid_owner_same; eauto.
    exists p. split.
    eapply Paths.mem_2. eapply is_init_in_universe. auto.
    apply is_shallow_prefix_refl.
    unfold clear_footprint_map. rewrite POP. rewrite GFP. auto.
    (* norepet of the footprint frame *)
    simpl.
    eapply list_norepet_append_commut2.
    eapply list_norepet_append_commut2 in NOREP.
    rewrite app_assoc in *.
    eapply list_norepet_app in NOREP. destruct NOREP as (A1 & A2 & A3).
    eapply list_norepet_app. repeat apply conj; auto.
    eapply set_disjoint_footprint_norepet. 3: eauto. all: eauto. 
    rewrite empty_footprint_flat. constructor.
    erewrite empty_footprint_flat. red. intros. inv H1.
    red. intros. eapply A3; auto.
    exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
    erewrite empty_footprint_flat in B. inv B.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    (* sound_drop_place_state *)
    econstructor.
    (* move_ordered_split_places_spec *)
    inv ORDERED. rewrite OWN in *. auto.
    (* wf_env *)
    eapply wf_env_set_wt_footprint with (fp:= clear_footprint_rec fp). eauto.
    eapply wt_footprint_clear. eauto. 
    eapply wf_own_wt_place. eauto. eapply is_init_in_universe. auto.
    rewrite POP. auto.   
    (* wf_own_env *)
    eapply wf_own_env_move_place. auto.
  (* step_dropplace_box *)
  - inv SOUND. inv SDP. inv SPLIT.
    (* To prove the (b,ofs) is equal to (b2,ofs2) so that (b', ofs')
    is equal to (b1, 0). But we first need to show that eval_place r
    is (b0, ofs0). It is possible because eval_place p has been
    successful *)
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & EVALR & A).
    (* the locations of get_loc_footprint_map and eval_place are the
    same. Do we need to prove that all the dominators of r is init to
    utilize mmatch? *)
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A. auto. intros A2. inv A2.
    (* prove (b',ofs') = (b1,0) *)
    inv PVAL; simpl in *; try congruence. inv H.
    rewrite LOAD in H0. inv H0.
    (* use sound_split_fully_own_place_unchanged,  m -> m' only changes b' *)
    inv FREE.
    (* we need to show that b3 is not in rfp to use sound_split_fully_own_place_unchanged *)
    assert (NIN: ~ In b3 (footprint_flat rfp)).
    { destruct (path_of_place r) eqn: POP.
      exploit get_loc_footprint_map_in_range; eauto. intros IN1.
      rewrite app_assoc in NOREP.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3).
      intro. eapply N3. eauto. eapply in_app; eauto. auto. }      
    exploit sound_split_fully_own_place_unchanged. 2: eapply SOUND.
    auto. auto.    
    eapply Mem.free_unchanged_on. eauto.
    intros. intro. destruct H0. simpl. auto.
    intros SOUND1.
    (* sound_split_fully_own still holds after removing the final footprint of rfp *)
    exploit sound_split_fully_own_place_set; eauto.
    instantiate (1 := fp_emp). intros (rfp1 & G1 & G2 & G3).
    (* b' is not in (fpm ++ fpf). It is used to prove sound_cont and mmatch *)
    generalize NOREP as NOREP1. intros.
    erewrite app_assoc in NOREP.
    eapply list_norepet_append_commut2 in NOREP.
    erewrite app_assoc in NOREP.
    eapply list_norepet_app in NOREP.
    destruct NOREP as (N1 & N2 & N3).
    assert (NOTIN: ~ In b' (footprint_of_env le ++ flat_fp_map fpm ++ flat_fp_frame fpf)).
    { intro. erewrite !in_app in H. repeat destruct H.
      eapply N3. erewrite! in_app. eauto.
      eapply get_footprint_incl; eauto. simpl. eauto. auto.
      eapply N3. erewrite! in_app. eauto.
      eapply get_footprint_incl; eauto. simpl. eauto. auto.
      eapply N3. eapply in_app. right. eauto.
      eapply get_footprint_incl; eauto. simpl. eauto. auto. }
    (* norepet of rfp1 *)
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      simpl. econstructor.
      simpl. red. intros. inv H0. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_dropplace le fpm rfp fpf)) m Hm) (rsw sg (flat_fp_frame (fpf_dropplace le fpm rfp1 fpf)) m' Hm1)).
    { eapply rsw_acc_shrink. simpl.
      red. intros. 
      erewrite !in_app. erewrite !in_app in H.
      repeat destruct H; auto.
      right. right. left.
      eapply set_footprint_incl in H; eauto. destruct H; auto.
      simpl in H. contradiction.
      eapply Mem.free_unchanged_on; eauto. intros.
      intro. eapply H0. eapply in_app_iff. right.
      eapply in_app_iff. right. eapply in_app_iff. left.
      eapply get_footprint_incl; eauto. simpl. eauto. }
    destruct RACC as (Hm1 & RACC).
    (* prove sound_dropplace *)
    eapply sound_dropplace with (rfp := rfp1); eauto.
    (* sound_cont *)
    eapply sound_cont_unchanged; eauto.
    eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply NOTIN. erewrite !in_app; auto.
    (* mmatch *)
    eapply mmatch_unchanged; eauto.
    eapply Mem.free_unchanged_on; eauto. intros.
    intro. eapply NOTIN. rewrite app_assoc. eapply in_app; auto.
    (* norepet *)
    simpl.
    erewrite app_assoc.
    eapply list_norepet_append_commut2.
    erewrite app_assoc.
    eapply list_norepet_app. repeat apply conj; eauto.
    red. intros. eapply N3. auto.
    exploit set_footprint_incl; eauto. intros [?|?]; auto. simpl in H3.
    contradiction.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    (* sound_drop_place_state *)
    econstructor; eauto.
    (* wf_env *)
    eapply wf_env_unchanged. eauto.
    eapply Mem.free_unchanged_on. eauto.
    intros. intro. eapply NOTIN.
    eapply in_app; auto.
  (* step_dropplace_struct *)
  - inv SOUND. inv SDP. 
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & EVALR & A).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A. auto. intros A2. inv A2.
    generalize (sound_split_fully_own_place_range _ _ _ _ _ _ _ _ _ _ _ SPLIT B4).
    intros RAN1.
    (* construct the footprint list for the members to be dropped *)
    rewrite PTY in *. inv WTFP; inv WTLOC. simpl in WF0. congruence.
    exploit sem_wt_member_footprint; eauto.
    exists nil. auto. intros MEMWT.
    (* show that (fp_struct id fpl) is norepet and b not in fpl *)
    assert (NIN: ~ In b3 (footprint_flat rfp)).
    { destruct (path_of_place r) eqn: POP.
      exploit get_loc_footprint_map_in_range; eauto. intros IN1.
      simpl in NOREP.
      rewrite app_assoc in NOREP.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3).
      intro. eapply N3. eauto. eapply in_app; eauto. auto. }
    exploit sound_split_fully_own_place_footprint_norepet; eauto. 
    intros (N1 & N2).
    (* show that b is in (b3::rfp) *)
    exploit sound_split_fully_own_place_footprint_in. eauto.
    intros IN1.
    (* show b3 s in (le ++ fpm) *)
    assert (IN2: In b3 (footprint_of_env le ++ flat_fp_map fpm)).
    { destruct (path_of_place r) eqn: POP.
      eapply get_loc_footprint_map_in_range; eauto. }
    (* remove (fp_struct id fpl) from rfp *)
    generalize SPLIT as SPLIT1. intros.
    eapply sound_split_fully_own_place_set with (fp2 := clear_footprint_rec (fp_struct id fpl)) in SPLIT1.
    destruct SPLIT1 as (rfp1 & GFP1 & SFP1 & SPLIT1).
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      rewrite empty_footprint_flat. econstructor.
      eapply empty_footprint_disjoint. }
    assert (EQUIV1: list_equiv (footprint_flat (fp_struct id fpl) ++ footprint_flat rfp1) (footprint_flat rfp)).
    { eapply get_clear_footprint_equiv; eauto. }
    (** Question: how to simplify the algebric reasoning of this
    norepet property *)
    assert (NOREP3: list_norepet
                      (flat_fp_frame (fpf_drop fp_emp (flat_fp_struct fpl) (fpf_dropplace le fpm rfp1 fpf)))).
    { simpl. simpl in NOREP.
      erewrite <- (footprint_flat_fp_struct_eq id); eauto.
      eapply dropplace_to_dropstate_footprint_norepet; eauto.
      eapply list_norepet_app. repeat apply conj.
      eapply get_footprint_norepet. eapply NOREP0. eauto.
      auto.
      eapply list_disjoint_sym.
      eapply get_set_disjoint_footprint; eauto.
      rewrite empty_footprint_flat. red. intros. inv H0. }
    (* used in sound_cont *)
    assert (NOREP4: list_norepet (flat_fp_frame (fpf_dropplace le fpm rfp1 fpf))).
    { simpl. simpl in NOREP3. eapply list_norepet_app in NOREP3. intuition. }
    (* some rewrites *)
    simpl in RAN1. rewrite CO in RAN1.
    unfold ce in CO.
    rewrite SCO in CO. inv CO.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_dropplace le fpm rfp fpf)) m Hm)
                           (rsw sg (flat_fp_frame (fpf_drop fp_emp (flat_fp_struct fpl) (fpf_dropplace le fpm rfp1 fpf))) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. erewrite <- (footprint_flat_fp_struct_eq id); eauto.
      red. intros.
      erewrite !in_app in H.
      erewrite !in_app.
      destruct H. right. right. left. eapply EQUIV1. eapply in_app; eauto.
      repeat destruct H; auto. right. right. left. eapply EQUIV1. eapply in_app; eauto.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropstate with (fp:= fp_emp) (fpf:= (fpf_dropplace le fpm rfp1 fpf)); eauto.
    econstructor.
    (* sound_cont *)
    econstructor; eauto.   
    (* easy: sound_drop_place_state *)
    econstructor; eauto.
    (* disjoint *)
    simpl. erewrite <- footprint_flat_fp_struct_eq; eauto.
    (* prove b in (fpf_dropplace le fpm rfp1 fpf) *)
    simpl. rewrite !in_app. erewrite !in_app in IN2.
    inv IN1. destruct IN2; auto.
    eapply EQUIV1 in H. erewrite !in_app in H. destruct H; try congruence; auto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
  (* step_dropplace_enum *)
  - inv SOUND. inv SDP. 
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & EVALR & A).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A. auto. intros A2. inv A2.
    (* show that fp1 is fp_enum *)
    erewrite PTY in *. inv WTFP; inv WTLOC. simpl in WF0. congruence.
    generalize (sound_split_fully_own_place_range _ _ _ _ _ _ _ _ _ _ _ SPLIT B4).
    intros RAN1. simpl in RAN1. rewrite CO in RAN1.
    (* some rewrites *)
    unfold ce in CO.
    rewrite SCO in CO. inv CO.
    simpl in TAG. rewrite TAG in TAG1. inv TAG1.
    rewrite Int.unsigned_repr in MEMB.
    (* show that tag is in range *)
    2: { generalize (list_nth_z_range _ _ TAG0).
         generalize (COMP_LEN id co0 SCO). lia. }
    rewrite MEMB in TAG0. inv TAG0.
    (* show drop_member_footprint *)
    exploit sound_type_to_drop_member_state; eauto.
    erewrite COENUM. eauto. intros DROPMEMB.
    (* show that fp is norepet and b not in fpl *)
    assert (NIN: ~ In b3 (footprint_flat rfp)).
    { destruct (path_of_place r) eqn: POP.
      exploit get_loc_footprint_map_in_range; eauto. intros IN1.
      simpl in NOREP.
      rewrite app_assoc in NOREP.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3).
      intro. eapply N3. eauto. eapply in_app; eauto. auto. }
    exploit sound_split_fully_own_place_footprint_norepet; eauto. 
    intros (N1 & N2).
    (* remove (fp_enum id orgs tagz fid0 fofs fp) from rfp *)
    generalize SPLIT as SPLIT1. intros.
    eapply sound_split_fully_own_place_set with (fp2 := clear_footprint_rec (fp_enum id orgs tagz fid0 fofs fp )) in SPLIT1.
    destruct SPLIT1 as (rfp1 & GFP1 & SFP1 & SPLIT1).
    simpl in SPLIT1.
    (* show that b is in (b3::rfp) *)
    exploit sound_split_fully_own_place_footprint_in. eauto.
    intros IN1.
    (* show b3 s in (le ++ fpm) *)
    assert (IN2: In b3 (footprint_of_env le ++ flat_fp_map fpm)).
    { destruct (path_of_place r) eqn: POP.
      eapply get_loc_footprint_map_in_range; eauto. }
    assert (NOREP2: list_norepet (footprint_flat rfp1)).
    { eapply set_footprint_norepet; eauto.
      rewrite empty_footprint_flat. econstructor.
      eapply empty_footprint_disjoint. }
    assert (EQUIV1: list_equiv (footprint_flat (fp_enum id orgs tagz fid0 fofs fp) ++ footprint_flat rfp1) (footprint_flat rfp)).
    { eapply get_clear_footprint_equiv; eauto. }
    simpl in *.
    assert (NOREP3: list_norepet
                      (flat_fp_frame (fpf_drop fp nil (fpf_dropplace le fpm rfp1 fpf)))).
    { simpl. simpl in NOREP.
      eapply dropplace_to_dropstate_footprint_norepet; eauto.
      eapply list_norepet_app. repeat apply conj.
      exploit get_footprint_norepet. eapply NOREP0. eauto. simpl. auto.
      auto.
      eapply list_disjoint_sym.
      red. intros.
      eapply get_set_disjoint_footprint; eauto. 
      simpl. red. intros. inv H2. }
    assert (NOREP4: list_norepet (flat_fp_frame (fpf_dropplace le fpm rfp1 fpf))).
    { simpl. simpl in NOREP3. eapply list_norepet_app in NOREP3. intuition. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_dropplace le fpm rfp fpf)) m Hm) (rsw sg (flat_fp_frame (fpf_drop fp nil (fpf_dropplace le fpm rfp1 fpf))) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros.
      erewrite !in_app in H.
      erewrite !in_app.
      destruct H. right. right. left. eapply EQUIV1. eapply in_app; eauto.
      repeat destruct H; auto. right. right. left. eapply EQUIV1. eapply in_app; eauto.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropstate with (fp := fp) (fpl:= nil); eauto.
    econstructor.
    (* sound_cont *)
    eapply sound_Kdropplace with (rfp:= rfp1); eauto.
    (* sound_drop_place_state *)
    eapply sound_drop_place_state_box; eauto.
    (* disjoint *)
    simpl. rewrite app_nil_r. auto.
    (* prove b in (fpf_dropplace le fpm rfp1 fpf) *)
    simpl. rewrite !in_app. erewrite !in_app in IN2.
    destruct IN1. subst. destruct IN2; auto. auto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
  - inv SOUND. inv SDP. inv SPLIT.
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_dropplace le fpm fp fpf)) m Hm)
                           (rsw sg (flat_fp_frame (fpf_dropplace le fpm fp_emp fpf)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl.
      eapply incl_app_app. eapply incl_refl.
      eapply incl_app_app. eapply incl_refl.
      eapply incl_appr. eapply incl_refl.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropplace with (rfp:= fp_emp); eauto.
    (* norepet *)
    simpl. simpl in NOREP.
    rewrite app_assoc in NOREP.
    eapply list_norepet_append_commut2 in NOREP.
    rewrite app_assoc in NOREP.
    eapply list_norepet_app in NOREP as (N1 & N2 & N3).
    rewrite <- app_assoc in N1. auto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    econstructor.
  - inv SOUND. inv SDP.
    econstructor; eauto.
    econstructor.
Qed.
    
(* To prove the norepet of footprint frame when only the footprint
    map is changed *)
Lemma fp_frame_norepet_internal: forall le fpm1 fpm2 fpf,
    list_norepet (flat_fp_frame (fpf_func le fpm1 fpf)) ->
    incl (flat_fp_map fpm2) (flat_fp_map fpm1) ->
    list_norepet (flat_fp_map fpm2) ->
    list_norepet (flat_fp_frame (fpf_func le fpm2 fpf)).
Proof.
  intros until fpf. intros A1 A2 A3.
  simpl in *. apply list_norepet_append_commut2.
  apply list_norepet_append_commut2 in A1.
  rewrite app_assoc in *.
  apply list_norepet_app in A1. destruct A1 as (N1 & N2 & N3).
  apply list_norepet_app. repeat apply conj; auto.
  red. intros. intro. subst. eapply N3. eauto.
  eapply A2. eauto. auto.
Qed.


(* Some frame update of rsw_acc *)
Lemma rsw_acc_app: forall l l1 l2 m1 m2 sg Hm1 Hm2 Hm1',
    rsw_acc (rsw sg l1 m1 Hm1) (rsw sg l2 m2 Hm2) ->
    exists Hm2', rsw_acc (rsw sg (l1 ++ l) m1 Hm1') (rsw sg (l2 ++ l) m2 Hm2').
Proof.
  intros. inv H.
  assert (INC: Mem.sup_include (l2 ++ l) (Mem.support m2)).
  { red. intros. eapply in_app in H.
    destruct H. eapply Hm'0. auto.
    eapply Mem.unchanged_on_support. eauto.
    eapply Hm1'. eapply in_app. auto. }
  exists INC.
  econstructor.
  eapply Mem.unchanged_on_implies; eauto.
  intros. simpl. intro. eapply H. eapply in_app; eauto.
  red. intros. intro. eapply SEP; eauto.
  intro. eapply H. eapply in_app; eauto.
  eapply in_app in H0. destruct H0; auto.
  exfalso. eapply H. eapply in_app; auto.
Qed.

  
(* More generally, rsw_acc is preserved under permuation of the
      footprint *)

Ltac simpl_getIM IM :=
  generalize IM as IM1; intros;
  inversion IM1 as [? | ? | ? ? GETINIT GETUNINIT]; subst;
  try rewrite <- GETINIT in *; try rewrite <- GETUNINIT in *.

(* sound state and syntactic well-typed state is preserved in one
step *)
Lemma step_sound: forall s1 t s2,
    sound_state s1 ->
    wt_state s1 ->
    Step L s1 t s2 ->
    sound_state s2 /\ wt_state s2.
Proof.
  intros s1 t s2 SOUND WTST STEP. simpl in STEP.
  split.
  2: { eapply wt_state_step_preservation; eauto. }
  inv STEP.
  (* assign sound *)
  - inv SOUND. inv STMT. simpl in TR.    
    simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own1 (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    eapply dominators_must_init_sound in MOVE2; eauto.
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM).
    exploit (@list_equiv_norepet1 block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit cast_val_is_casted; eauto. intros CASTED.
    exploit assign_loc_sound; eauto.
    eapply list_norepet_append_left; eauto.
    intros (fpm3 & SFP & MM3 & NOREP3 & WFENV3).        
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    instantiate (1 := (init_place (move_place_option own1 (moved_place e)) p)).
    exploit move_option_place_sound. eapply OWN.
    instantiate (1 := (moved_place e)). intros SOUND1.
    exploit init_place_sound; eauto.
    intros (mayinit3 & mayuninit3 & A & B).      
    (* end of construct *)
    (* sound_state *)
    (* key proof: figure out which location the changed block resides
    in. The changed block is in the stack or in the footprint map
    (maybe we can prove this using get_loc_footprint_map_in_range *)
    assert (RAN: In b (footprint_of_env le ++ flat_fp_map fpm2)).
    { destruct (path_of_place p) eqn: POP. 
      eapply get_loc_footprint_map_in_range. eapply GFP. }
    assert (RAN1: In b (footprint_of_env le ++ flat_fp_map fpm)).
    { eapply in_app in RAN. apply in_app. destruct RAN; auto.
      right. eapply EQUIV1. eapply in_app; eauto. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m1 Hm)
                           (rsw sg (flat_fp_frame (fpf_func le fpm3 fpf)) m2 Hm1)).
    { destruct (path_of_place p) eqn: POP.
      eapply rsw_acc_shrink.      
      simpl. red. intros. rewrite !in_app in H3; rewrite !in_app; repeat destruct H3; auto.
      eapply set_footprint_map_incl in H3; eauto. destruct H3; eauto.
      right. left. eapply EQUIV1. eapply in_app; eauto.
      right. left. eapply EQUIV1. eapply in_app; eauto.
      exploit assign_loc_unchanged_on; eauto.
      intros UNC1. eapply Mem.unchanged_on_implies. eauto.
      simpl. intros. intro. destruct H5. subst.
      apply H3. rewrite app_assoc. eapply in_app. auto. }
    destruct RACC as (Hm1 & RACC).      
    econstructor; eauto.
    econstructor.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    (* to prove sound_cont: unchanged on the footprint of the frames
    of the function *)
    exploit assign_loc_unchanged_on; eauto.
    intros UNC1. eapply Mem.unchanged_on_implies. eauto.
    simpl. intros. intro. destruct H5. subst.
    (* show that block in le++fpm is not in fpf *)
    eapply DIS1. eauto. eauto. auto. 
    (* end of the proof of sound_cont *)
    (* norepet *)
    eapply fp_frame_norepet_internal. eauto.
    destruct (path_of_place p) eqn: POP.
    red. intros. eapply set_footprint_map_incl in H3; eauto.
    eapply EQUIV1. eapply in_app. intuition.
    eapply list_norepet_app. eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans. eauto. eauto.
    (* wf_own_env preservation (write it in another lemma) *)
    eapply wf_own_env_init_place. auto. auto.
    destruct (moved_place e); simpl.
    eapply wf_own_env_move_place. eauto. eauto.
  (* assign_variant sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own1 (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    eapply dominators_must_init_sound in MOVE2; eauto.
    exploit eval_place_sound. eapply PADDR1. all: eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM).
    exploit (@list_equiv_norepet1 block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit cast_val_is_casted; eauto. intros CASTED.
    replace (genv_cenv (globalenv se prog)) with ce in * by auto.
    rewrite CO in WT4. inv WT4.
    (* show that the address of p after assigning the enum body is unchanged *)
    assert (PADDREQ: eval_place (globalenv se prog) le m2 p b ofs).
    { exploit variant_field_offset_in_range_eq; eauto.
      rewrite <- TYP. eauto. intros (OFSEQ & R1 & R2 & R3).
      exploit eval_place_footprint_unchanged.
      2: eapply PADDR1. eauto. eauto. auto.
      all: eauto.
      intros (bs & UNC & NBS & INCL & DIS).
      eapply UNC; eauto.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on. eauto.
      simpl. intros.
      destruct H.
      intro. destruct H1. subst. eapply DIS; eauto.
      simpl. auto.
      destruct H; subst. intro. destruct H. eapply H1.
      rewrite OFSEQ in *. rewrite TYP. lia.      
    }
    exploit eval_place_det. eapply PADDR2. eauto. intros (E1 & E2). subst.
    exploit assign_loc_variant_sound; eauto.
    instantiate (1 := fp'). eapply list_norepet_append_right; eauto.
    instantiate (3 := pfp).
    (* exploit cannot handle lemma with too much premises *)
    intros TMP. exploit TMP; eauto. clear TMP.
    intros (fpm3 & SFP & MM3 & NOREP3 & WFENV3).
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    instantiate (1 := (init_place (move_place_option own1 (moved_place e)) p)).
    exploit move_option_place_sound. eapply OWN. 
    instantiate (1 := (moved_place e)). intros SOUND1.
    exploit init_place_sound; eauto.
    intros (mayinit3 & mayuninit3 & A & B).
    (* end of construct *)
    (* sound_state *)
    (* key proof: figure out which location the changed block resides
    in. The changed block is in the stack or in the footprint map
    (maybe we can prove this using get_loc_footprint_map_in_range *)
    assert (RAN: In b (footprint_of_env le ++ flat_fp_map fpm2)).
    { destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_in_range; eauto. }
    assert (RAN1: In b (footprint_of_env le ++ flat_fp_map fpm)).
    { eapply in_app in RAN. apply in_app. destruct RAN; auto.
      right. eapply EQUIV1. eapply in_app; eauto. }
    (* The enum assignment only changes b1 *)
    assert (UNC: Mem.unchanged_on (fun b' _ => b' <> b) m1 m3).
    { eapply Mem.unchanged_on_trans.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto. simpl. intros.
      intro. eapply H. destruct H1. auto.
      eapply Mem.store_unchanged_on; eauto. }
        assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m1 Hm)
                           (rsw sg (flat_fp_frame (fpf_func le fpm3 fpf)) m3 Hm1)).
    { destruct (path_of_place p) eqn: POP.
      eapply rsw_acc_shrink.      
      simpl. red. intros. rewrite !in_app in H; rewrite !in_app; repeat destruct H; auto.
      eapply set_footprint_map_incl in H; eauto. destruct H; eauto.
      right. left. eapply EQUIV1. eapply in_app; eauto.
      right. left. eapply EQUIV1. eapply in_app; eauto.
      eapply Mem.unchanged_on_implies. eauto.
      simpl. intros. intro. subst. eapply H.
      rewrite app_assoc. eapply in_app. auto. }
    destruct RACC as (Hm1 & RACC).      
    econstructor; eauto.
    econstructor.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro. subst.
    (* show that block in le++fpm is not in fpf *)
    eapply DIS1. eauto. eauto. auto.
    (* end of the proof of sound_cont *)
    (* norepet *)
    eapply fp_frame_norepet_internal. eauto.
    destruct (path_of_place p) eqn: POP.
    red. intros. eapply set_footprint_map_incl in SFP; eauto.
    eapply EQUIV1. eapply in_app. intuition.
    eapply list_norepet_app. eauto.
    (* accessibility *)
    eapply rsw_acc_trans. eauto. eauto.
    (* wf_own_env preservation (write it in another lemma) *)
    eapply wf_own_env_init_place. auto. auto.
    destruct (moved_place e); simpl.
    eapply wf_own_env_move_place. eauto. eauto.
    
  (* step_box sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    unfold move_check_expr in MOVE1.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    inv TR.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    (* show that b is not in (flat_fp_frame (fpf_func le fpm fpf)) *)
    assert (BNIN: ~ In b (flat_fp_frame (fpf_func le fpm fpf))).
    { intro. eapply Mem.fresh_block_alloc; eauto. eapply Hm. auto. }    
    (* show that m1 -> m3 unchanges the blocks in le and fpm *)
    assert (UNC1: Mem.unchanged_on (fun b' _ => In b' (flat_fp_frame (fpf_func le fpm fpf))) m1 m3).
    { simpl. eapply Mem.unchanged_on_trans.
      eapply Mem.alloc_unchanged_on. eauto.
      eapply Mem.store_unchanged_on; eauto. }
    assert (UNC2: Mem.unchanged_on (fun b' _ => In b' (flat_fp_frame (fpf_func le fpm fpf))) m3 m4).
    { eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto. simpl. intros. intro.
      destruct H9. subst. eapply BNIN. eauto. }
    assert (MM1: mmatch fpm ce m3 le own1).
    { eapply mmatch_unchanged. eapply MM.
      eapply Mem.unchanged_on_implies. eapply UNC1. simpl. intros.
      rewrite app_assoc. eapply in_app; auto. }
    assert (WFENV1: wf_env fpm ce m3 le).
    { eapply wf_env_unchanged. eauto.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. eapply in_app; auto. }
    (* show v is sem_wt_val *)
    exploit eval_expr_sem_wt. eapply MM1. all: eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM2 & WFENV2 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    exploit cast_val_is_casted; eauto. intros CASTED.
    (* show (b,0) is sem_wt_loc in m4 *)
    exploit assign_loc_sem_wt. eapply H4. eapply Z.divide_0_r.
    all: eauto. intro.
    eapply BNIN. simpl. rewrite !in_app.
    right. left. eapply EQUIV1. eapply in_app; auto.
    intros WTLOC1.
    (* show Vptr(b, 0) is sem_wt_val in m4 *)
    assert (WTVAL1: sem_wt_val ce m4 (fp_box b (sizeof (globalenv se prog) (typeof e)) fp') (Vptr b Ptrofs.zero)).
    { econstructor. auto.
      (* range_perm *)
      red. intros.
      erewrite <- assign_loc_perm_unchanged. 2: eauto.
      eapply Mem.perm_store_1. eauto.
      eapply Mem.perm_alloc_2; eauto.
      (* load the size record *)
      eapply Mem.load_unchanged_on.
      eapply assign_loc_unchanged_on. eauto.
      simpl. intros. intro. destruct H8.
      generalize (size_chunk_pos Mptr).
      generalize (sizeof_pos (prog_comp_env prog) ty). intros.
      rewrite Ptrofs.unsigned_zero in *. lia.
      (* load store same *)
      erewrite Mem.load_store_same; eauto.
      f_equal.
      (* size checking: do it in syntactic type checking *)
      auto. }
    (* show m4 is sound in the new own_env *)
    assert (MM3: mmatch fpm2 ce m4 le (move_place_option own1 (moved_place e))).
    { eapply mmatch_unchanged. eapply MM2.
      eapply Mem.unchanged_on_implies. eapply UNC2. simpl. intros.
      rewrite !in_app in H7. rewrite !in_app.
      destruct H7; auto. right. left. eapply EQUIV1. eapply in_app; auto. }
    assert (WFENV3: wf_env fpm2 ce m4 le).
    { eapply wf_env_unchanged. eapply WFENV2.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. eapply in_app; auto. }
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own1 (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    (* eval_place_sound *)
    eapply dominators_must_init_sound in MOVE2; eauto.
    exploit eval_place_sound; eauto. 
    intros (pfp & GFP & WTFP3 & PRAN & PERM).
    (* assign the box pointer to p *)
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
     exploit (@list_equiv_norepet1 block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit assign_loc_sound; eauto.
    rewrite H. econstructor.
    simpl. econstructor.
    (* b not in fp' *)
    intro. eapply BNIN. simpl. rewrite !in_app.
    right. left. eapply EQUIV1. eapply in_app; auto.
    eapply list_norepet_append_left; eauto.
    (* wt_footprint *)
    rewrite H. replace (genv_cenv (globalenv se prog)) with ce by auto.
    rewrite H in WT4. inv WT4.
    replace (genv_cenv (globalenv se prog)) with ce in SZEQ by auto.
    rewrite <- SZEQ. econstructor; eauto.
    (* disjointness *)
    simpl. eapply list_disjoint_cons_l. eauto.
    intro. eapply BNIN. simpl. rewrite !in_app. rewrite in_app in H7.
    destruct H7; auto.
    right. left. eapply EQUIV1. eapply in_app; auto.
    intros (fpm3 & SFP & MM4 & NOREP3 & WFENV4).
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    instantiate (1 := (init_place (move_place_option own1 (moved_place e)) p)).
    exploit move_option_place_sound. eapply OWN.
    instantiate (1 := (moved_place e)). intros SOUND1.
    exploit init_place_sound; eauto.
    intros (mayinit3 & mayuninit3 & A & B). 
    (* end of construct *)
    assert (RAN: In pb (footprint_of_env le ++ flat_fp_map fpm2)).
    { destruct (path_of_place p) eqn: POP. 
      eapply get_loc_footprint_map_in_range. eapply GFP. }
    assert (RAN1: In pb (footprint_of_env le ++ flat_fp_map fpm)).
    { eapply in_app in RAN. apply in_app. destruct RAN; auto.
      right. eapply EQUIV1. eapply in_app; eauto. }
    assert (Hm1: Mem.sup_include (flat_fp_frame (fpf_func le fpm3 fpf)) (Mem.support m5)).
    { erewrite <- assign_loc_sup_unchanged. 2: eauto.
      erewrite <- assign_loc_sup_unchanged. 2: eauto.
      erewrite Mem.support_store. 2: eauto.
      simpl.
      erewrite Mem.support_alloc. 2: eauto.
      red. intros.
      eapply Mem.sup_incr_in.
      red in H7. rewrite !in_app in H7.
      repeat destruct H7.
      - right. eapply Hm. simpl. eapply in_app. auto.
      - destruct (path_of_place p) eqn: POP.
        exploit set_footprint_map_incl; eauto. intros [E1 | E2].
        + right. eapply Hm. simpl. eapply in_app. right.
          eapply in_app. left. eapply EQUIV1. eapply in_app; auto.
        + simpl in E2. destruct E2; subst.
          * left. eapply Mem.alloc_result. eauto.
          * right. eapply Hm. simpl. eapply in_app. right.
            eapply in_app. left. eapply EQUIV1. eapply in_app; auto.
      - right. eapply Hm. simpl. eapply in_app. right.
        eapply in_app. auto. }
    assert (UNC3: Mem.unchanged_on (fun b0 _ => b0 <> b) m2 m4).
    { eapply Mem.unchanged_on_trans.
      eapply Mem.store_unchanged_on. eauto. congruence.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on. eauto. simpl.
      intros. intro. eapply H7. destruct H9. auto. }
    assert (UNC4: Mem.unchanged_on (fun b0 _ => ~ In b0 (flat_fp_frame (fpf_func le fpm fpf))) m1 m4).
    { simpl. econstructor.
      (* sup_include *)
      eapply Mem.sup_include_trans.
      eapply Mem.sup_include_incr. erewrite <- Mem.support_alloc.
      2: eauto.
      erewrite <- Mem.support_store. 2: eauto.
      erewrite assign_loc_sup_unchanged. 2: eauto.
      eapply Mem.sup_include_refl.
      (* permission unchanged *)
      intros. split; intros.
      erewrite <- assign_loc_perm_unchanged. 2: eauto.
      eapply Mem.perm_store_1. eauto.
      eapply Mem.perm_alloc_1. eauto. auto.
      erewrite <- assign_loc_perm_unchanged in H9. 2: eauto.
      eapply Mem.perm_store_2 in H9. 2: eauto.
      eapply Mem.perm_alloc_4; eauto. intro. subst.
      eapply Mem.fresh_block_alloc. eauto. auto.
      (* contents unchanged *)
      intros.
      etransitivity. eapply Mem.unchanged_on_contents.
      eapply UNC3. simpl. intro. subst. eapply Mem.fresh_block_alloc. eauto.
      eapply Mem.perm_valid_block. eauto.
      eapply Mem.perm_alloc_1; eauto. 
      eapply Mem.unchanged_on_contents.
      eapply Mem.alloc_unchanged_on with (P := fun _ _ => True). eauto. simpl. auto.
      auto. }      
    assert (RACC: rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m1 Hm)
                    (rsw sg (flat_fp_frame (fpf_func le fpm3 fpf)) m5 Hm1)).
    { econstructor.
      (* unchanged on *)
      eapply Mem.unchanged_on_trans. eauto.      
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto. simpl. intros.
      intro. eapply H7. destruct H9. subst.
      rewrite app_assoc. eapply in_app; eauto.
      (* flat_footprint_separated *)
      simpl. red. intros.
      rewrite !in_app in H8. intro. eapply H7.
      rewrite !in_app. repeat destruct H8; auto.
      destruct (path_of_place p) eqn: POP.
      exploit set_footprint_map_incl; eauto. intros [E1 | E2].
      - right. left. eapply EQUIV1. eapply in_app. auto.
      - simpl in E2. destruct E2; subst.
        + exfalso. eapply Mem.fresh_block_alloc; eauto.
        + right. left. eapply EQUIV1. eapply in_app. auto. }
    econstructor; eauto.
    econstructor.
    (* sound_cont: show the unchanged m1 m2 *)
    instantiate (1 := fpf).
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_trans.
    eapply Mem.unchanged_on_implies. eapply UNC1. simpl. intros.
    rewrite !in_app. auto.
    eapply Mem.unchanged_on_trans.
    eapply Mem.unchanged_on_implies. eapply UNC2. simpl. intros.
    rewrite !in_app. auto. 
    eapply Mem.unchanged_on_implies; eauto.
    eapply assign_loc_unchanged_on. eauto. 
    simpl. intros. intro. destruct H9. subst.
    (* show that block in le++fpm is not in fpf *)
    eapply DIS1. eauto. eauto. auto.
    (* end of the proof of sound_cont *)
    (* norepet *)
    simpl. eapply list_norepet_append_commut2. rewrite app_assoc.
    eapply list_norepet_append_commut2 in NOREP'. rewrite app_assoc in NOREP'.
    eapply list_norepet_app in NOREP' as (F1 & F2 & F3).
    eapply list_norepet_app. repeat apply conj; auto.
    eapply list_norepet_append_right. eauto.
    red. intros.
    destruct (path_of_place p) eqn: POP.
    exploit set_footprint_map_incl; eauto. intros [E1 | E2].
    eapply N3. eauto.
    eapply EQUIV1. eapply in_app; auto.
    simpl in E2. destruct E2; subst.
    intro. subst. eapply BNIN. simpl. eapply in_app_commut.
    rewrite app_assoc. eapply in_app; auto.
    eapply N3. eauto.
    eapply EQUIV1. eapply in_app; auto.
    (* accessibility *)
    eapply rsw_acc_trans. eauto. eauto.
    (* wf_own_env preservation (write it in another lemma) *)
    eapply wf_own_env_init_place. auto. auto.
    destruct (moved_place e); simpl.
    eapply wf_own_env_move_place. eauto. eauto.
    
  (** NOTEASY: step_to_dropplace sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    (** TODO: Properties about own_env (make it a lemma) *)
    exploit split_drop_place_meet_spec; eauto.
    intros SPLIT_SPEC.
    (* make ORDER_SPEC a lemma *)
    assert (ORDER_SPEC: move_ordered_split_places_spec own (map fst drops)).
    { eapply ordered_and_complete_split_places_meet_spec.
      (* Complete *)
      intros. left.
      assert (PRE: is_prefix p a = true).
      { eapply is_prefix_trans. eapply split_sound; eauto. auto. }
      eapply split_complete. eauto.
      erewrite is_prefix_same_local. eauto.
      auto. auto.
      eapply split_ordered; eauto. }
    (* construct sound_own and get_IM *)
    exploit analyze_succ. 1-3: eauto. rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
    simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    instantiate (1 := (move_split_places own drops)).    
    eapply sound_own_after_drop; eauto.    
    intros (mayinit3 & mayuninit3 & A & B).
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m Hm)
                           (rsw sg (flat_fp_frame (fpf_dropplace le fpm fp_emp fpf)) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. apply incl_refl.
      eapply Mem.unchanged_on_refl. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_dropplace with (rfp:= fp_emp).
    eauto. eauto. eauto. eauto.
    simpl. eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto. 
    (* sound_drop_place_state *)
    econstructor.
    eauto.
    eauto.
    (* full *)
    intros. unfold is_full.
    erewrite <- is_prefix_same_local.
    eapply split_correct_full; eauto.
    eapply split_sound; eauto. eapply in_map_iff. exists (p0, full). eauto.
    (* all drops are wt_place *)
    eapply Forall_forall. intros.
    eapply wf_own_wt_place. eauto.
    exploit split_sound. eauto. eauto. intros (IN1 & PRE).
    unfold in_universe. erewrite <- is_prefix_same_local.
    eapply Paths.mem_1; eauto. auto.
    (* wf_env *)
    auto.
    eauto. auto. auto.
    
  (* step_in_dropplace sound *)
  - eapply step_dropplace_sound; eauto.
  (* step_dropstate sound *)
  - eapply step_dropstate_sound; eauto.
  (* step_storagelive sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    exploit analyze_succ. 1-3: eauto. rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
    simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    eauto. intros (mayinit3 & mayuninit3 & A & B).
    econstructor; eauto. econstructor.
    
  (* step_storagedead sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    exploit analyze_succ. 1-3: eauto. rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
    simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    eauto. intros (mayinit3 & mayuninit3 & A & B).
    econstructor; eauto. econstructor.
    
  (* step_call sound *)
  - inv SOUND. inv STMT. simpl in TR.
    simpl_getIM IM.
    destruct (move_check_exprlist ce mayinit mayuninit universe al) eqn: MOVE1; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    exploit eval_exprlist_sem_wt; eauto.
    intros (vfpl & fpm2 & WTVALS & WTFPS & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1 & CASTL).
    (** sound_own after moving the place in the expression *)
    exploit move_place_list_sound. eauto.
    instantiate (1 := (moved_place_list al)).
    exploit move_check_exprlist_result. eauto. intros (R1 & R2). subst.
    intros SOWN1.
    exploit init_place_sound; eauto. instantiate (1 := p).
    intros SOWN2.
    (* construct get_IM and sound_own *)
    exploit analyze_succ. 1-3: eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. econstructor.
    simpl. auto.   
    unfold transfer. rewrite <- GETINIT. rewrite SEL. rewrite STMT0. eauto.
    unfold transfer. rewrite <- GETUNINIT. rewrite SEL. rewrite STMT0. eauto.
    eauto.
    intros (mayinit3 & mayuninit3 & A & B).      
    (* end of construct *)
    (* prove that p is dominator owned in (move_place_list own1 (moved_place_list al)) *)
    assert (DOM: dominators_is_init (move_place_list own1 (moved_place_list al)) p = true).
    { eapply dominators_must_init_sound; eauto. }
    (* sound_state *)
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m Hm)
                           (rsw sg ((flat_fp_frame (fpf_func le fpm2 fpf)) ++ flat_map footprint_flat vfpl) m Hm1)).
    { eapply rsw_acc_shrink.
      simpl. red. intros b IN. 
      rewrite !in_app in IN. rewrite !in_app.
      repeat destruct IN; auto.
      do 2 (destruct H4; auto).
      right. left. eapply EQUIV1. eapply in_app; auto.
      right. left. eapply EQUIV1. eapply in_app; auto.
      eapply Mem.unchanged_on_refl. }            
    destruct RACC as (Hm1 & RACC).
    eapply sound_callstate with (fpf:= fpf_func le fpm2 fpf); eauto.    
    econstructor; eauto.
    (* norepet *)
    simpl. rewrite <- !app_assoc.
    eapply state_to_callstate_footprint_norepet; eauto.
    eapply list_norepet_append_commut; auto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
    
  (* step_internal_function *)
  - inv SOUND.
    exploit find_funct_move_check. eapply FIND. intros SPEC. 
    inv SPEC. simpl in FUNC.
    simpl in FIND. rewrite FIND in FUNC. inv FUNC.
    simpl in FUNTY. unfold type_of_function in FUNTY. inv FUNTY.
    (* construct footprint map after function entry *)
    exploit function_entry_sound. eauto. eauto. eauto.
    eauto. rewrite type_of_params_eq_var_type in WTFP. auto.
    auto. eapply Mem.sup_include_trans. 2: eauto.
    red. intros. eapply in_app; eauto.
    eapply list_norepet_append_right; eauto.
    auto.
    intros (fpm1 & MM1 & WFENV1 & WFOWN1 & NOREP1 & NVALID & INCL1 & UNC1).
    assert (NOREP2: list_norepet (flat_fp_frame (fpf_func e fpm1 fpf))).
    { simpl. rewrite app_assoc.
      eapply list_norepet_app. repeat apply conj; auto.
      eapply list_norepet_append_left; eauto.
      red. intros. intro. subst.
      rewrite in_app in H. destruct H; eauto.
      eapply NVALID in H. apply H.
      eapply Hm. eapply in_app; eauto.
      eapply list_norepet_app in NOREP as (N1 & N2 & N3). eapply N3; eauto. }
    (** construct analyze, match_stmt and sound_own which are the same
    as ElaborateDropProof *)
    unfold move_check_function in CKFUN. monadInv CKFUN.
    destruct x1 as ((init & uninit) & universe). monadInv EQ2.
    exploit (@transl_on_cfg_meet_spec AN); eauto. 
    intros (nret & MSTMT & RET).
    (* own_env in function entry is sound *)
    exploit sound_function_entry. simpl. eapply EQ1. 
    eauto. eauto. eauto. intros (einit & euninit & GIM & OWNENTRY).
    (** end of construction *)        
    assert (Hm1: Mem.sup_include (flat_fp_frame (fpf_func e fpm1 fpf)) (Mem.support m')).
    { simpl. red. intros.
      unfold sup_In in H. erewrite !in_app in H.
      repeat destruct H.
      exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & IN1).
      eapply wf_env_freeable; eauto.
      eapply Mem.unchanged_on_support with (P:= fun _ _ => True). eauto.
      eapply Hm. eapply in_app; eauto.
      eapply Mem.unchanged_on_support with (P:= fun _ _ => True). eauto.
      eapply Hm. eapply in_app; eauto. }
    assert (RACC: rsw_acc (rsw sg (flat_fp_frame fpf ++ flat_map footprint_flat fpl) m Hm)  (rsw sg (flat_fp_frame (fpf_func e fpm1 fpf)) m' Hm1)).
    { econstructor.
      eapply UNC1.      
      red. intros. simpl in H0. rewrite !in_app in H0.
      destruct H0.
      exploit in_footprint_of_env_inv; eauto.
      destruct H0. intro. eapply H. eapply in_app; eauto.
      intro. eapply H. eapply in_app; auto. }
    eapply sound_regular_state; eauto.
    (* sound_cont *)
    inv STK.
    econstructor; eauto.
    econstructor; eauto. econstructor; eauto.
    eapply sound_cont_unchanged; eauto.
    eapply mmatch_unchanged; eauto.
    eapply wf_env_unchanged; eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
    
  (** step_external_function: we cannot prove that the builtin
  external functions defined by CompCert satisfy the rely-guarantee
  property of rsw_acc because some of them use Vundef as return value
  which is not supported in sem_wt_val. But we observe that the memory
  relation of rsw_acc may be satisfied by external_call_mem_inject if
  we instantiate the source and target memorys with the same memory
  and injection function with the (flat_inj footprint_of_args). The
  return footprint can be constructed by (filter j (support m_res)). *)
  - inv SOUND.
    exploit find_funct_move_check. eapply FIND.
    intros SPEC. inv SPEC.
    destruct NORMAL.
    destruct H1; [|destruct H1; try congruence].
    destruct H1 as (name1 & sg1 & A). subst. inv H.    
  (* step_return_1 *)
  - inv SOUND. inv STMT. unfold move_check_stmt in TR.
    unfold get_init_info in TR.
    simpl_getIM IM.
    set (e:= (if scalar_type (typeof_place p)
            then Epure (Eplace p (typeof_place p))
            else Emoveplace p (typeof_place p))) in *.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    (* eval_expr *)
    assert (EVAL1: eval_expr (globalenv se prog) le m1 (globalenv se prog) e v).
    { unfold e. destruct (scalar_type (typeof_place p)); auto.
      inv EVAL. inv H0. econstructor. econstructor; eauto. }
    assert (WTE: wt_expr le ce e).
    { unfold e. destruct (scalar_type (typeof_place p)) eqn: PTY; econstructor; auto.
      econstructor. auto. }
    assert (TYEQ: typeof e = typeof_place p).
    { unfold e. destruct (scalar_type (typeof_place p)) eqn: PTY; auto. }
    exploit eval_expr_sem_wt; eauto.
    intros (fp & fpm1 & WTVAL1 & WTFP1 & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    rewrite <- TYEQ in *.
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    exploit cast_val_is_casted; eauto. intros CASTED.
    (* show that v(v1) does not contain footprint in le *)
    pose proof (footprint_of_not_composite_val _ _ _ _ WTVAL1 WTFP1 WT3) as INCL1.
    erewrite sem_cast_val_footprint_unchanged in INCL1; eauto.
    rewrite FPEQ in INCL1.
    assert (DISVAL: list_disjoint (footprint_of_val v1) (footprint_of_env le)).
    { red. intros. intro. subst.
      eapply N3. eapply in_app; eauto.
      eapply EQUIV1. eapply in_app. left. eapply INCL1. eauto. reflexivity. }
    (* free stack blocks unchanged on *)
    assert (UNC1: Mem.unchanged_on (fun b _ => ~ In b (footprint_of_env le)) m1 m2).
    { eapply free_list_unchanged_on. eauto.
      intros. intro. eapply H0.
      rewrite footprint_blocks_of_env_eq.
      eapply in_map_iff. exists (b, z1, z2). eauto. }
    (* show that v1 is sem_wt in m2 *)
    exploit sem_wt_val_unchanged_blocks. eapply WTVAL2.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro.
    eapply N4. eauto. eapply EQUIV1.
    eapply in_app. left. destruct H; eauto. reflexivity.
    intros WTVAL2'.    
    (* prove that ck is wt_call_cont *)
    assert (WTCC: wt_call_cont prog se mod_sg ck f.(fn_return)).
    { eapply call_cont_wt_call_cont; eauto. }
    assert (TYCC: typeof_cont_call (rs_sig_res sg) ck = f.(fn_return)).
    { replace sg with mod_sg.
      eapply wt_call_cont_type_eq; eauto.
      eapply rsw_acc_sg_eq; eauto. }
    assert (RACC: exists Hm1, rsw_acc (rsw sg (flat_fp_frame (fpf_func le fpm fpf)) m1 Hm)
                           (rsw sg (footprint_flat fp' ++ flat_fp_frame fpf) m2 Hm1)).
    { eapply rsw_acc_shrink.
      simpl. rewrite app_assoc. eapply incl_app_app.
      eapply incl_appr. red. intros. eapply EQUIV1. eapply in_app; auto.
      eapply incl_refl.
      simpl. eapply Mem.unchanged_on_implies; eauto.
      simpl. intros.  intro. eapply H. rewrite !in_app; auto. }
    destruct RACC as (Hm1 & RACC).
    eapply sound_returnstate with (fpf := fpf); eauto.
    (* norepet *)
    eapply list_norepet_app. repeat apply conj.
    eapply list_norepet_append_left; eauto.
    eapply list_norepet_append_right; eauto.
    red. intros. intro. subst. eapply N3.
    eapply in_app; eauto. eapply EQUIV1. eapply in_app; eauto. reflexivity.
    (* sound_stacks *)    
    eapply call_cont_sound; eauto.
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro. eapply DIS1. eapply in_app; eauto. eauto.
    reflexivity.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
    
  (* step_returnstate *)
  - inv SOUND. simpl in *. inv STK.
    (* inversion of wt_state *)
    inv WTST. inv WT1.
    (* destruct norepet *)
    eapply list_norepet_app in SEP as (N1 & N2 & N3). simpl in N2, N3.
    generalize N2 as N2'. intros.
    eapply list_norepet3_fpm_changed in N2 as (N4 & N5 & N6 & N7 & N8 & DIS1).
    rewrite app_assoc in N3.
    eapply list_disjoint_app_r in N3 as (N3 & N3').
    (* evaluate the place *)
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP1 & PRAN & PERM & VALIDB).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.        
    (* assign *)
    exploit assign_loc_sound; eauto.
    intros (fpm1 & SFP & MM1 & NOREP1 & WFENV1).
    assert (RACC: exists Hm1, rsw_acc (rsw sg (footprint_flat rfp ++ flat_fp_frame (fpf_func e fpm fpf0)) m1 Hm) (rsw sg (flat_fp_frame (fpf_func e fpm1 fpf0)) m2 Hm1)).
    { destruct (path_of_place p) eqn: POP.
      eapply rsw_acc_shrink. simpl.
      red. intros. rewrite !in_app in H2. rewrite !in_app.
      repeat destruct H2; auto.
      exploit set_footprint_map_incl; eauto. intros [A|B]; auto.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto.
      simpl. intros. intro. destruct H4. subst.
      eapply H2. rewrite !in_app.
      exploit get_loc_footprint_map_in_range; eauto. intros IN.
      apply in_app in IN as [A|B]; auto. }
    destruct RACC as (Hm1 & RACC).
    econstructor; eauto. econstructor. 
    (* sound_cont *)
    eapply sound_cont_unchanged; eauto.
    eapply Mem.unchanged_on_implies. eapply assign_loc_unchanged_on; eauto.
    simpl. intros. intro. destruct H4. subst.
    eapply DIS1. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_in_range; eauto. eauto. reflexivity.
    (* norepet *)
    simpl. rewrite app_assoc. eapply list_norepet_app.
    repeat apply conj; eauto.
    eapply list_norepet_append_right; eauto.
    red. intros. intro. subst. rewrite in_app in H2.
    destruct H2. eapply DIS1; eauto. apply in_app; auto.
    destruct (path_of_place p) eqn: POP.
    exploit set_footprint_map_incl; eauto. intros [A|B].
    eapply DIS1; eauto. apply in_app; auto.
    eapply N3'; eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
    (* wf_own_env *)
    eapply wf_own_env_init_place; eauto.

  (* step_seq *)
  - inv SOUND. inv STMT.
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_seq *)
  - inv SOUND. inv STMT. inv CONT.
    econstructor; eauto.
  (* step_continue_seq *)
  - inv SOUND. inv STMT. inv CONT.
    econstructor; eauto.
    econstructor.
  (* step_break_seq *)
  - inv SOUND. inv STMT. inv CONT.
    econstructor; eauto.
    econstructor.
  (* step_ifthenelse *)
  - inv SOUND. inv STMT.
    simpl_getIM IM.        
    destruct b.
    + exploit analyze_succ; eauto.
      rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
      simpl. left. eauto.      
      unfold transfer. rewrite <- GETINIT. rewrite MCOND. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite MCOND. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
    + exploit analyze_succ; eauto.
      rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
      simpl. right. eauto.      
      unfold transfer. rewrite <- GETINIT. rewrite MCOND. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite MCOND. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
  (* step_loop *)
  - inv SOUND. inv STMT.
    simpl_getIM IM.
    exploit analyze_succ; eauto.
    rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
    simpl. eauto.
    unfold transfer. rewrite <- GETINIT. rewrite START. auto.
    unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
    intros (mayinit3 & mayuninit3 & GIM & SO).
    econstructor; eauto.
    econstructor; eauto.
  (* step_skip_or_continue_loop *)
  - inv SOUND. inv CONT.    
    simpl_getIM IM.
    destruct H; subst; inv STMT.
    + exploit analyze_succ; eauto.
      rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
      simpl. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite START. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
      econstructor; eauto.
    + exploit analyze_succ; eauto.
      rewrite <- GETINIT. rewrite <- GETUNINIT. eauto.
      simpl. eauto.
      unfold transfer. rewrite <- GETINIT. rewrite START. auto.
      unfold transfer. rewrite <- GETUNINIT. rewrite START. auto.
      intros (mayinit3 & mayuninit3 & GIM & SO).
      econstructor; eauto.
      econstructor; eauto.
  (* step_break_loop *)
  - inv SOUND. inv STMT. inv CONT.
    econstructor; eauto.
    econstructor; eauto.
Qed.


Lemma initial_state_sound: forall q s,
    query_inv rs_own (se, w) q ->
    initial_state ge q s ->
    sound_state s /\ wt_state s.
Proof.
  intros q s QINV INIT.
  split.
  2: { eapply wt_initial_state; eauto.
       unfold mod_sg.
       inv QINV. inv INIT. simpl. eauto. }
  inv INIT. inv QINV. simpl in *.
  set (sg1 := {|
         rs_sig_generic_origins := orgs;
         rs_sig_origins_relation := org_rels;
         rs_sig_args := type_list_of_typelist targs;
         rs_sig_res := tres;
         rs_sig_cc := tcc;
               rs_sig_comp_env := prog_comp_env prog |}) in *.
  assert (RACC: exists Hm1, rsw_acc w (rsw sg1 (flat_map footprint_flat fpl) m Hm1)).
  { rewrite <- H3. eapply rsw_acc_shrink.
    red. intros. eapply EQ; eauto.
    eapply Mem.unchanged_on_refl. }
  destruct RACC as (Hm1 & RACC).
  eapply sound_callstate with (sg := sg1); eauto.
  econstructor. simpl. eauto.
  simpl. eauto.
Qed.

Lemma external_sound: forall s q,
    sound_state s ->
    wt_state s ->
    at_external ge s q ->
    exists wA, symtbl_inv rs_own wA se /\ query_inv rs_own wA q /\
            forall r, reply_inv rs_own wA r ->
                 (exists s', after_external s r s' (* do we really need
                 this exists s'? It is repeated in partial safe *)
                        /\ forall s', after_external s r s' -> sound_state s' /\ wt_state s').
Proof.
  intros s q SOUND WTST ATEXT.
  inv ATEXT. inv SOUND.
  generalize WTST as WTST1. intros. inv WTST.
  assert (Hm1: Mem.sup_include (flat_map footprint_flat fpl) (Mem.support m)).
  { eapply Mem.sup_include_trans.
    2: eapply Hm.
    red. intros. eapply in_app; auto. }
  set (sg1:= {|
                rs_sig_generic_origins := orgs;
                rs_sig_origins_relation := org_rels;
                rs_sig_args := type_list_of_typelist targs;
                rs_sig_res := tres;
                rs_sig_cc := cconv;
                rs_sig_comp_env := ge |}) in *.
  exists (se, (rsw sg1 (flat_map footprint_flat fpl) m Hm1)). simpl.
  (* find_funct rewriting *)
  rewrite H in FUNC. inv FUNC. simpl in *. inv FUNTY.
  rewrite H in FIND. inv FIND. simpl in *. inv FTY.
  repeat apply conj; auto.
  - eapply rs_own_query_intro with (fpl := fpl).
    eapply list_norepet_append_right; eauto.
    eauto.
    (* wt_footprint_list *)
    eauto.
    red. intros; auto. reflexivity.
  - intros r (w1 & ACC1 & WTR). inv ACC1.
    inv WTR.
    (* 1. state existence *)
    exists (Returnstate rv k m'). split.
    econstructor.
    (* 2. invariant preservation *)
    intros s' AFEXT.
    split.
    2: { eapply wt_state_external_preservation; eauto.
         econstructor; eauto. }
    inv AFEXT.
    unfold sg1 in *. simpl in *.
    assert (TYCC: typeof_cont_call (rs_sig_res sg) k = rty).
    { replace sg with mod_sg.
      eapply wt_call_cont_type_eq; eauto.
      eapply rsw_acc_sg_eq; eauto. }
    eapply list_norepet_app in NOREP as (N1 & N2 & N3).
    assert (SUP: Mem.sup_include (footprint_flat rfp ++ flat_fp_frame fpf) (Mem.support m')).
    { red. unfold sup_In. intros.
      apply in_app in H0. destruct H0.
      eapply Hm'. eapply INCL. eauto.
      eapply Mem.unchanged_on_support. eauto. eapply Hm.
      eapply in_app. eauto. }
    assert (RACC: rsw_acc (rsw sg (flat_fp_frame fpf ++ flat_map footprint_flat fpl) m Hm)
                    (rsw sg (footprint_flat rfp ++ flat_fp_frame fpf) m' SUP)).
    { econstructor.
      eapply Mem.unchanged_on_implies; eauto.
      intros. intro. eapply H0. eapply in_app; eauto.
      red. intros.
      rewrite !in_app in H1. destruct H1.
      (* b in rfp *)
      intro. eapply SEP. intro. eapply H0. eapply in_app; eauto.
      eapply INCL. eauto. auto.
      (* b in fpf : contradition *)
      intro. eapply H0. eapply in_app; auto. }
    eapply sound_returnstate with (sg := sg) (fpf:= fpf); eauto.
    (* norepet *)
    eapply list_norepet_app. repeat apply conj; auto.
    (* disjointness between rfp and fpf *)
    red. intros. intro. subst.
    (* two cases: block y is in (fpl) or not *)
    red in SEP. destruct (in_dec eq_block y (flat_map footprint_flat fpl)).
    eapply N3; eauto.
    exploit SEP; eauto. eapply Hm. eapply in_app; eauto.
    (* sound_stacks *)
    eapply sound_stacks_unchanged_on; eauto.
    eapply Mem.unchanged_on_implies; eauto.
    simpl. intros. intro. eapply N3; eauto.
    (* rsw_acc *)
    eapply rsw_acc_trans; eauto.
Qed.    
    
Lemma final_sound: forall s r,
    sound_state s ->
    wt_state s ->
    final_state s r ->
    reply_inv rs_own (se, w) r.
Proof.
  intros s r SOUND WTST FINAL.
  inv FINAL. inv SOUND. inv WTST.  
  simpl.
  assert (SUP: Mem.sup_include (footprint_flat rfp) (Mem.support m)).
  { eapply Mem.sup_include_trans. 2: eauto.
    red. intros. eapply in_app; eauto. }    
  exists (rsw sg (footprint_flat rfp) m SUP).
  split.
  (* rsw_acc *)
  eapply rsw_acc_trans. eauto.
  econstructor. eapply Mem.unchanged_on_refl.
  eapply flat_footprint_separated_shrink.
  eapply incl_appl. apply incl_refl.  
  (* wt_query *)
  assert (SGEQ: mod_sg = sg).
  { unfold mod_sg. inv ACC; eauto. }
  subst. simpl in *.
  eapply rs_own_reply_intro with (rfp:= rfp); eauto.
  all: try rewrite SG_COMP_ENV; auto.
  eapply incl_refl.
  eapply list_norepet_append_left; eauto.
Qed.

(** Sound state must not be memory error state *)

(* Defererence of a location has no memory error *)
Lemma deref_loc_no_mem_error: forall fp b ofs ty m
        (WTFP: wt_footprint ce ty fp)
        (BM: bmatch ce m b (Ptrofs.unsigned ofs) fp)
        (ERR: deref_loc_mem_error ty m b ofs),
        False.
Proof.
  intros. inv ERR.
  destruct ty; intros; try (simpl in *; congruence).
  - inv H. inv WTFP; inv BM. inv MODE.
    eauto with mem.
  - inv WTFP; inv BM.
    rewrite H in MODE. inv MODE. eauto with mem.
  - inv WTFP; inv BM.
    rewrite H in MODE. inv MODE. eauto with mem.
  - inv WTFP; inv BM.
    rewrite H in MODE. inv MODE. eauto with mem.
  - inv WTFP; inv BM; simpl in *; try congruence.
    inv H. eauto with mem.
  - inv WTFP; inv BM. simpl in *.
    inv WT.
Qed.


(** The evaluation of place has no memory error  *)

(* This lemma requires eval_place_sound *)
Lemma eval_place_no_mem_error: forall p m le own fpm
    (MM: mmatch fpm ce m le own)
    (ERR: eval_place_mem_error ce le m p)
    (WFOWN: wf_env fpm ce m le)
    (WT: wt_place (env_to_tenv le) ce p)
    (POWN: dominators_is_init own p = true),
    False.
Proof.
  induction p; intros; inv ERR; inv WT.
  - eapply IHp; eauto.
  - eapply IHp. 1-5: eauto. 
    eapply dominators_is_init_deref1. eauto.
  - exploit dominators_is_init_deref1; eauto. intros DOM.
    exploit eval_place_sound; eauto.
    intros (fp & A1 & A2 & A3).
    (* show that the location (l, ofs) is bmatch so
    deref_loc_mem_error is impossible *)
    exploit MM. eauto.
    eapply dominators_is_init_deref2; eauto.
    intros (BM & FULL).
    eapply deref_loc_no_mem_error; eauto.
  - exploit dominators_is_init_downcast; eauto.
  - exploit dominators_is_init_downcast; eauto. intros DOM.
    exploit eval_place_sound; eauto.
    intros (fp & A1 & A2 & A3).
    exploit valid_owner_place_footprint; eauto.
    intros (fp' & ofs' & fofs & GFP & VOWN & EQ).
    exploit MM. eapply GFP.
    unfold dominators_is_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN. auto.
    intros (BM & FULL).
    exploit valid_owner_bmatch; eauto.
    intros BM1.
    rewrite WT2 in *. inv A2. inv BM1.
    simpl in *; try congruence. inv BM1.
    eapply H3. rewrite EQ.
    eapply Mem.load_valid_access; eauto.
Qed.

Lemma eval_pexpr_no_mem_error: forall pe m le own init uninit universe fpm
    (MM: mmatch fpm ce m le own)
    (ERR: eval_pexpr_mem_error ce le m pe)
    (WFOWN: wf_env fpm ce m le)
    (WT: wt_pexpr (env_to_tenv le) ce pe)
    (SOWN: sound_own own init uninit universe)
    (POWN: move_check_pexpr init uninit universe pe = true),
    False.
Proof.
  induction pe; intros; try (inv ERR; inv WT); simpl in POWN; try congruence.
  - destruct (scalar_type (typeof_place p)) eqn: TYP; try congruence.
    eapply andb_true_iff in POWN as (A1 & A2).
    assert (INIT: dominators_is_init own p = true).
    { eapply dominators_must_init_sound; eauto. }
    eapply eval_place_no_mem_error; eauto.
  - destruct (scalar_type (typeof_place p)) eqn: TYP; try congruence.
    eapply andb_true_iff in POWN as (B1 & B2).
    assert (INIT: dominators_is_init own p = true).
    { eapply dominators_must_init_sound; eauto. }
    exploit eval_place_sound; eauto.
    intros (fp & A1 & A2 & A3).
    exploit valid_owner_place_footprint; eauto.
    intros (fp1 & ofs1 & fofs1 & G1 & G2 & G3).
    exploit MM. eauto.
    eapply must_init_sound. eauto. eauto.
    intros (BM & FULL).
    exploit valid_owner_bmatch; eauto. intros BM1.
    rewrite <- G3 in BM1.
    eapply deref_loc_no_mem_error; eauto.
  - destruct (typeof_place p) eqn: PTY; try congruence.
    eapply andb_true_iff in POWN as (B1 & B2).
    assert (INIT: dominators_is_init own p = true).
    { eapply dominators_must_init_sound; eauto. }
    eapply eval_place_no_mem_error; eauto.
  - destruct (typeof_place p) eqn: PTY; try congruence.
    eapply andb_true_iff in POWN as (B1 & B2).
    assert (INIT: dominators_is_init own p = true).
    { eapply dominators_must_init_sound; eauto. }
    exploit eval_place_sound; eauto.
    intros (fp & A1 & A2 & A3).
    exploit MM. eauto.
    eapply must_init_sound. eauto. eauto.
    intros (BM & FULL).
    rewrite PTY in *. inv WTP1.
    inv A2; inv BM. simpl in MODE. try congruence.
    eapply H2.
    eapply Mem.load_valid_access. eauto.
  - eapply IHpe; eauto.
  - eapply andb_true_iff in POWN as (A1 & A2).
    destruct H0.
    eapply IHpe1; eauto.
    eapply IHpe2; eauto.
Qed.

Lemma eval_expr_no_mem_error: forall e m le own init uninit universe fpm
    (MM: mmatch fpm ce m le own)
    (ERR: eval_expr_mem_error ce le m e)
    (WFOWN: wf_env fpm ce m le)
    (WT: wt_expr (env_to_tenv le) ce e)
    (SOWN: sound_own own init uninit universe)
    (POWN: move_check_expr' ce init uninit universe e = true),
    False.
Proof.
  intros. destruct e; inv ERR; inv WT.
  - simpl in POWN.
    destruct place_eq in POWN.
    + eapply andb_true_iff in POWN as (A1 & A2).
      assert (INIT: dominators_is_init own p = true).
      { eapply dominators_must_init_sound; eauto. }      
      inv H0.
      * eapply eval_place_no_mem_error; eauto.
      * exploit eval_place_sound; eauto.
        intros (fp & B1 & B2 & B3).
        (* show that (b, ofs) is sem_wt_loc *)
        exploit movable_place_sem_wt; eauto.
        red. auto. intros WTLOC.
        eapply deref_loc_no_mem_error; eauto.
        eapply sem_wt_loc_implies_bmatch. eauto.
    + rewrite !andb_true_iff in POWN.
      destruct POWN as ((A1 & A2) & A3).
      assert (INIT: dominators_is_init own p = true).
      { eapply dominators_must_init_sound; eauto. }
      inv H0.      
      * eapply eval_place_no_mem_error; eauto.
      * exploit eval_place_sound. 1-5: eauto. 
        intros (fp & B1 & B2 & B3).
        exploit valid_owner_place_footprint. eauto. eapply WT1.
        intros (fp1 & ofs1 & fofs & C1 & C2 & C3).
        (* show that (b, ofs) is sem_wt_loc using mmatch and is_full *)
        exploit MM. eauto.
        eapply must_init_sound. eauto. eauto.
        intros (BM & FULL).
        exploit FULL.
        erewrite <- is_full_same. eauto.
        eapply sound_own_universe. eauto.
        intros WTLOC.
        eapply deref_loc_no_mem_error; eauto.
        eapply sem_wt_loc_implies_bmatch. rewrite C3.
        eapply valid_owner_sem_wt_loc; eauto.
  - inv POWN.
    eapply eval_pexpr_no_mem_error; eauto.
Qed.

(* It requires lots of invariant because we need to use eval_expr_sem_wt *)
Lemma eval_exprlist_no_mem_error: forall al tyl fpm1 m le own1 init uninit init1 uninit1 universe
    (MM: mmatch fpm1 ce m le own1)
    (WF: list_norepet (flat_fp_map fpm1))
    (DIS: list_disjoint (footprint_of_env le) (flat_fp_map fpm1))
    (ERR: eval_exprlist_mem_error ce le m ge al tyl)
    (SOUND: sound_own own1 init uninit universe)
    (CHECK: move_check_exprlist ce init uninit universe al = Some (init1, uninit1))
    (WFENV: wf_env fpm1 ce m le)
    (WT: wt_exprlist le ce al)
    (WFOWN: wf_own_env le ce own1),
    False.
Proof.
  induction al; intros; inv ERR.
  - inv WT. simpl in CHECK.
    destruct (move_check_expr ce init uninit universe a) eqn: CK1; try congruence.
    destruct p.
    unfold move_check_expr in CK1.
    destruct (move_check_expr' ce init uninit universe a) eqn: CK2; try congruence.    
    eapply eval_expr_no_mem_error; eauto.
  - inv WT. simpl in CHECK.
    destruct (move_check_expr ce init uninit universe a) eqn: CK1; try congruence.
    destruct p as (init2 & uninit2).
    unfold move_check_expr in CK1.
    destruct (move_check_expr' ce init uninit universe a) eqn: CK2; try congruence.
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own1 (moved_place a)) init2 uninit2 universe).
    { destruct (moved_place a) eqn: MP; simpl; inv CK1; auto.
      eapply move_place_sound. auto. }
    exploit eval_expr_sem_wt; eauto.
    intros (fp2 & fpm2 & WTVAL1 & WTFP1 & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (* show fpm2 is norepet *)
    generalize NOREP1 as NOREP2. intros.
    eapply list_norepet_app in NOREP2 as (N1 & N2 & N3).
    assert (DIS1: list_disjoint (footprint_of_env le) (flat_fp_map fpm2)).
    { red. intros.
      eapply DIS. eauto.
      eapply EQUIV1. eapply in_app; auto. }
    eapply IHal; eauto.
Qed.    
    
Lemma access_mode_by_copy: forall ty,
    access_mode ty = Ctypes.By_copy ->
    (exists orgs id, ty = Tstruct orgs id) \/ (exists orgs id, ty = Tvariant orgs id).
Proof.
  destruct ty; intros A; simpl in *; try (inv A; congruence); eauto.
  destruct i; destruct s; try congruence.
  destruct f; try congruence.
Qed.

Lemma assign_loc_no_mem_error: forall ty m b ofs v fp
    (ERR: assign_loc_mem_error ce ty m b ofs v)
    (AL: (alignof ce ty | Ptrofs.unsigned ofs))
    (* note that the value may be an address of enum/struct *)
    (WTVAL: sem_wt_val ce m fp v)
    (WTFP: wt_footprint ce ty fp)
    (* guaranteed by eval_place_sound *)
    (PERM: Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof ce ty) Cur Writable),
    False.
Proof.
  intros; inv ERR.
  - eapply H0. red.
    erewrite sizeof_by_value; eauto.
    split; eauto.
    erewrite alignof_by_value; eauto.
  - eapply H0.
    exploit access_mode_by_copy; eauto.
    intros [(orgs & id & TY) | (orgs & id & TY)]; subst.
    + inv WTFP. congruence.
      simpl in WF. congruence.
      inv WTVAL. simpl. eauto.
    + inv WTFP. inv WTVAL.
      simpl in WF. congruence.
      inv WTVAL. simpl. eauto.
  - eapply H0. eauto.
Qed.

Lemma deref_loc_rec_footprint_no_mem_error: forall tys m b ofs ty fp b1 ofs1 ty1 fp1
    (WTFP: wt_footprint ge ty1 fp1)
    (DEF: deref_loc_rec_footprint m b (Ptrofs.unsigned ofs) ty fp tys b1 ofs1 ty1 fp1)
    (ERR: deref_loc_rec_mem_error m b ofs tys),
    False.
Proof.
  induction tys; intros; simpl in *.
  - inv ERR.
  - inv DEF. inv ERR.
    + eapply IHtys. 2-3 : eauto.
      econstructor; eauto.
    + exploit deref_loc_rec_footprint_eq; eauto. intros (A1 & A2). subst.
      eapply deref_loc_no_mem_error with (fp:= (fp_box b1 (sizeof ce ty1) fp1)) (b:= b2) (ofs:= ofs1). 
      econstructor; eauto.
      econstructor; eauto. auto.
Qed.


(* It is not easy to directly prove that step_drop is total safe
because there are some dynamic type checking in the semantics. For now
we just pove that step-drop has no memory error *)
Lemma step_dropstate_no_mem_error: forall s,
    sound_state s ->
    wt_state s ->
    step_drop_mem_error ge s ->
    False.
Proof.
  intros s SOUND WTST ERR; try (inv ERR; inv SOUND).
  - inv DROPMEMB.
    (* repeated code in the following 4 cases. TODO: make it a
    lemma *)
    unfold ce in *. rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.    
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty <= co_sizeof co).
    { destruct (co_sv co) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit variant_field_offset_in_range_complete; eauto. lia. }
    exploit field_offset_in_range_add; eauto.
    intros OFSEQ.
    (* end of repeated code *)
    eapply deref_loc_rec_footprint_no_mem_error. eapply WTFP. rewrite OFSEQ. eauto.
    auto.
  - inv DROPMEMB.
    unfold ce in *. rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.    
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty1 <= co_sizeof co).
    { destruct (co_sv co) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit variant_field_offset_in_range_complete; eauto. lia. }
    exploit field_offset_in_range_add; eauto.
    intros OFSEQ.
    eapply deref_loc_rec_footprint_no_mem_error. eapply WTFP. rewrite OFSEQ. eauto.
    auto.
  - inv DROPMEMB.
    unfold ce in *. rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.    
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty1 <= co_sizeof co).
    { destruct (co_sv co) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit variant_field_offset_in_range_complete. 3: eauto. all: eauto.
      lia. }
    exploit field_offset_in_range_add. 2: eauto. eauto. eauto.
    intros OFSEQ.
    exploit deref_loc_rec_footprint_eq.
    rewrite OFSEQ. eauto. all: eauto.
    intros (A1 & A2). subst.
    inv WTFP; inv WTLOC. simpl in *. congruence.
    eapply TAG. eapply Mem.load_valid_access. eauto.
  - inv DROPMEMB.
    unfold ce in *. rewrite CO1 in CO. inv CO.
    rewrite FOFS in FOFS0. inv FOFS0.    
    assert (R: 0 <= fofs0 /\ fofs0 + sizeof ge fty <= co_sizeof co0).
    { destruct (co_sv co0) eqn: COSV.
      eapply field_offset_in_range_complete; eauto.
      exploit variant_field_offset_in_range_complete; eauto. lia. }
    exploit field_offset_in_range_add; eauto.
    intros OFSEQ.
    simpl in NOREP.
    eapply list_norepet_app in NOREP as (N1 & N2 & N3).    
    exploit drop_box_rec_progress_and_unchanged. eauto.
    intro. eapply DIS. apply in_app; eauto.
    rewrite OFSEQ. eauto.
    intros (m2 & DROP & UNC).
    eapply drop_box_rec_progress_no_mem_error; eauto.
Qed.

(* If the evaluation of p2 is memory error, and SPLIT holds, then the
evaluation of p1 must be memory errro *)
Lemma sound_split_fully_own_place_no_mem_error: forall l p1 p2 m b ofs fp b1 ofs1 ty1 fp1 le own fpm fp2
  (SPLIT: sound_split_fully_own_place m p1 b ofs fp l p2 b1 ofs1 ty1 fp1)
  (ERR: eval_place_mem_error ge le m p2)
  (* The following premises are used to prove that (b, ofs) is equal
  to the result of eval_place p1. And then prove (b1, ofs1) is equal
  to the evaluation of p2 *)
  (MM: mmatch fpm ge m le own)
  (DOM: dominators_is_init own p1 = true)
  (GFP: get_loc_footprint_map le (path_of_place p1) fpm = Some (b, ofs, fp2))
  (WFENV: wf_env fpm ge m le)
  (WTP: wt_place le ge p1),
    eval_place_mem_error ge le m p1.
Proof.
  induction l; intros; inv SPLIT; auto.
  inv ERR.
  + eauto.
  + exploit sound_split_fully_own_place_type_inv; eauto.
    intros TYA. rewrite TYA in *.
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A2. eauto. intros B5. inv B5.
    inv H2. simpl in *. inv H. exfalso.
    eapply H0. eapply Mem.load_valid_access; eauto.
Qed.

(* It is not easy to directly prove that step_drop is total safe
because there are some dynamic type checking in the semantics. For now
we just pove that step-drop has no memory error *)
Lemma step_dropplace_no_mem_error: forall s,
    sound_state s ->
    wt_state s ->
    step_dropplace_mem_error ge s ->
    False.
Proof.
  intros s SOUND WTST ERR; try (inv ERR; inv SOUND).
  - inv SDP. inv SPLIT.
    assert (NERR: ~ eval_place_mem_error ge le m r).
    { intro. eapply eval_place_no_mem_error; eauto. }
    eapply NERR. eapply sound_split_fully_own_place_no_mem_error; eauto.
  - inv SDP. inv SPLIT.
    (* the same as the proof of sound_split_fully_own_place_no_mem_error *)
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A2. eauto. intros B5. inv B5.
    inv PVAL. simpl in *. inv H.
    eapply H0. eapply Mem.load_valid_access; eauto.
  - inv SDP. inv SPLIT.
    (* same as the last case *)
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A2. eauto. intros B5. inv B5.
    inv PVAL; simpl in *; try congruence. inv H. rewrite LOAD in H0.
    inv H0. inv FREE.
    + eapply H2. eapply Mem.load_valid_access; eauto.
    + eapply H4.
      rewrite Z.sub_0_l in *.
      rewrite SIZE in H1. 
      destruct (Val.eq (Vptrofs (Ptrofs.repr (sizeof ce ty1))) (Vptrofs sz)); try congruence.
      eapply Vptrofs_det in e. subst.
      rewrite Z.add_0_l. rewrite Ptrofs.unsigned_repr. eauto.
      lia.
  - inv SDP. 
    assert (NERR: ~ eval_place_mem_error ge le m r).
    { intro. eapply eval_place_no_mem_error; eauto. }
    eapply NERR. eapply sound_split_fully_own_place_no_mem_error; eauto.
  - inv SDP. 
    assert (NERR: ~ eval_place_mem_error ge le m r).
    { intro. eapply eval_place_no_mem_error; eauto. }
    eapply NERR. eapply sound_split_fully_own_place_no_mem_error; eauto.
  - inv SDP.
    exploit sound_split_fully_own_place_eval_place; eauto.
    intros (b3 & ofs3 & A1 & A2).
    exploit eval_place_get_loc_footprint_map_equal; eauto.
    intros (B1 & B2 & B3 & B4). subst.
    exploit A2. eauto. intros B5. inv B5.
    rewrite PTY in *. inv WTFP; simpl in *; try congruence; inv WTLOC.
    eapply ERR0.
    eapply Mem.load_valid_access; eauto.
Qed.

(* It requires lots of invariant because it would use assign_loc_sound
to prove wf_env after assigning a parameter. *)
Lemma bind_parameters_no_mem_error: forall pl vl fpl fpm1 m1 own1 le
   (MM: mmatch fpm1 ce m1 le own1)
   (ERR: bind_parameters_mem_error ce le m1 pl vl)
   (CAST: val_casted_list vl (type_of_params pl))
   (NOREP1: list_norepet (flat_map footprint_flat fpl))
   (WTVAL: sem_wt_val_list ce m1 fpl vl)
   (WTFPL: wt_footprint_list ge (type_list_of_typelist (type_of_params pl)) fpl)
   (NOREP2: list_norepet (footprint_of_env le ++ flat_fp_map fpm1))
   (EMPFP: forall id ty, In (id, ty) pl -> exists fp, fpm1 ! id = Some fp)
   (VALIDTYS: forall id ty, In (id, ty) pl -> valid_type ty = true)
   (DIS1: list_disjoint (flat_map footprint_flat fpl) (footprint_of_env le ++ flat_fp_map fpm1))
   (* we need to consider the footprints in vl are disjoint with the allocated blocks *)
   (DIS2: list_disjoint (footprint_of_env le) (flat_map footprint_of_val vl))
   (WFOWN: wf_own_env le ce own1)
   (WFENV: wf_env fpm1 ce m1 le),
    False.
Proof.
  induction pl; intros; inv ERR.
  - inv WTVAL. inv WTFPL.
    exploit wf_env_freeable; eauto. intros (PERM & VALID).
    eapply assign_loc_no_mem_error; eauto.
    eapply Z.divide_0_r.
    eapply Mem.range_perm_implies; eauto. constructor.
  - inv WTVAL. inv WTFPL. inv CAST.
    (* copy from bind_parameters_sound *)
    exploit EMPFP. simpl. left. eauto. intros (fp & A1).
    exploit assign_loc_sound. eauto. instantiate (1 := Plocal id ty). eauto.
    eauto. eapply Z.divide_0_r. auto.
    instantiate (1 := a1). simpl in NOREP1. eapply list_norepet_append_left; eauto.
    auto. auto. auto.
    simpl. rewrite H1. rewrite A1. eauto.
    eauto. econstructor. unfold env_to_tenv. erewrite PTree.gmap1. rewrite H1. auto.
    eapply VALIDTYS; eauto. simpl. eauto.
    auto. simpl in DIS1. eapply list_disjoint_app_l in DIS1.
    destruct DIS1. auto.
    auto.
    intros (fpm2 & SFP & MM2 & NOREP3 & WFENV2).   
    simpl in NOREP1.
    intros. simpl in SFP. rewrite A1 in SFP. inv SFP.
    exploit IHpl. eapply MM2. eauto. auto. eapply list_norepet_append_right; eauto.
    (* sem_wt_val_list in m0 *)
    eapply sem_wt_val_list_unchanged_blocks. eauto.
    eapply Mem.unchanged_on_implies.
    eapply assign_loc_unchanged_on. eauto.
    simpl. intros. intro. destruct H2. subst.
    destruct H.
    eapply DIS1. simpl. eapply in_app; eauto.
    eapply in_app. left. eapply in_footprint_of_env; eauto. reflexivity.
    eapply DIS2. eapply in_footprint_of_env; eauto. simpl.
    eapply in_app; eauto. reflexivity.
    (* wt_footprint_list *)
    auto. eauto. auto.
    (* EMPFP *)    
    intros. rewrite PTree.gsspec.
    destruct peq; subst. eauto. eapply EMPFP. simpl. eauto.
    (* valid_type *)
    intros. eapply VALIDTYS. eapply in_cons. eauto.
    (* DIS1 *)
    simpl in DIS1. red. intros.
    intro. subst. rewrite in_app in H0.
    destruct H0. eapply DIS1. eapply in_app; eauto.
    eapply in_app; eauto. reflexivity.
    eapply in_flat_map in H0.
    destruct H0 as ((id1 & fp1) & IN1 & IN2).
    eapply PTree.elements_complete in IN1. rewrite PTree.gsspec in IN1.
    destruct peq in IN1; subst. inv IN1. simpl in IN2.
    eapply list_norepet_app in NOREP1 as (N1 & N2 & N3).
    eapply N3; eauto.
    eapply DIS1. eapply in_app; eauto. eapply in_app. right.
    eapply in_flat_map. exists (id1, fp1). split; eauto.
    eapply PTree.elements_correct; eauto. reflexivity.
    (* DIS2 *)
    simpl in DIS2. eapply list_disjoint_app_r. eauto.
    (* wf_own_env *)
    assert (WTP: wt_place le ce (Plocal id ty)).
    { econstructor. unfold env_to_tenv. rewrite PTree.gmap1.
      rewrite H1. eauto. eapply VALIDTYS. simpl. eauto. }
    eapply wf_own_env_init_place. auto. auto. auto.
    (* wf_env *)
    auto. contradiction.
Qed.

Lemma footprint_norepet_implies_freelist_no_overlap: forall l,
    list_norepet (map (fun elt : positive * (block * type) => fst (snd elt)) l) ->
    SimplLocalsproof.freelist_no_overlap (map (block_of_binding ge) l).
Proof.
  induction l; intros; simpl in *; auto.
  destruct a as (id & (b & ty)). simpl in *. split.
  inv H. eauto.
  intros. inv H. left.
  eapply in_map_iff in H0.
  destruct H0 as ((id1 & (b1 & ty1)) & IN1 & IN2). simpl in IN1. inv IN1.
  intro. subst. 
  eapply H3. eapply in_map_iff. exists (id1, (b, ty1)).  eauto.
Qed.
  
Lemma step_no_mem_error: forall s,
    sound_state s ->
    wt_state s ->
    step_mem_error ge s ->
    False.
Proof.
  intros s SOUND WTST ERR; inv ERR.
  (* 1-3: step_assign *)
  1-3: inv SOUND; inv WTST; inv STMT; inv WT1; simpl in TR; simpl_getIM IM;
  destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence;
  unfold move_check_expr in MOVE1;  
  destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence;
  destruct p0 as (mayinit' & mayuninit');
  destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence;
  simpl in NOREP;
  generalize NOREP as NOREP'; intros;
  eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
  { eapply eval_expr_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    eapply eval_place_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM & VALID).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.    
    eapply assign_loc_no_mem_error; eauto.
    eapply Mem.range_perm_implies; eauto.
    constructor. }

  (* 1-5: step_assign_variant *)
  1-5: inv SOUND; inv WTST; inv STMT; simpl in TR; simpl_getIM IM;
  destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence;
  unfold move_check_expr in MOVE1;
  destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence;
  destruct p0 as (mayinit' & mayuninit');
  destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence;
  inv WT1;
  simpl in NOREP;
  generalize NOREP as NOREP'; intros;
  eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
  {  eapply eval_expr_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    eapply eval_place_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM & VALID).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    replace (genv_cenv (globalenv se prog)) with (genv_cenv ge) in * by auto.
    rewrite CO in WT4. inv WT4.
    exploit variant_field_offset_in_range_eq; eauto.
    rewrite <- TYP. eauto.
    intros (OFSEQ & R1 & R2 & R3).
    eapply assign_loc_no_mem_error; eauto.
    rewrite OFSEQ. eapply variant_field_offset_aligned_add; eauto.
    rewrite <- TYP. auto.
    (* permission *)
    rewrite OFSEQ.
    red. intros. eapply Mem.perm_implies. eapply PERM. rewrite TYP. lia.
    constructor. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM & VALID).
    exploit (@list_equiv_norepet1 block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    replace (genv_cenv (globalenv se prog)) with (genv_cenv ge) in * by auto.
    rewrite CO in WT4. inv WT4.
    exploit variant_field_offset_in_range_eq; eauto.
    rewrite <- TYP. eauto.
    intros (OFSEQ & R1 & R2 & R3).
    assert (PADDREQ: eval_place (globalenv se prog) le m2 p b ofs).
    { exploit eval_place_footprint_unchanged.
      2: eapply PADDR1. eauto. eauto. auto.
      all: eauto.
      intros (bs & UNC & NBS & INCL & DIS).
      eapply UNC; eauto.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on. eauto.
      simpl. intros.
      destruct H.
      intro. destruct H1. subst. eapply DIS; eauto.
      simpl. auto.
      destruct H; subst. intro. destruct H. eapply H1.
      rewrite OFSEQ in *. rewrite TYP.
      replace (prog_comp_env prog) with ce in H2 by auto.
      lia. }
    eapply eval_place_progress_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt; eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM1 & WFENV1 & NOREP1 & EQUIV1 & WFOWN1).
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }    
    exploit dominators_must_init_sound; eauto. intros DOM.
    exploit eval_place_sound. eapply PADDR1. all: eauto.
    intros (pfp & GFP & WTFP3 & PRAN & PERM & VALID).
    exploit (@list_equiv_norepet1 block). eapply NOREP1. eauto. eauto.
    intros (N6 & N7 & N8).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    replace (genv_cenv (globalenv se prog)) with (genv_cenv ge) in * by auto.
    rewrite CO in WT4. inv WT4.
    exploit variant_field_offset_in_range_eq; eauto.
    rewrite <- TYP. eauto.
    intros (OFSEQ & R1 & R2 & R3).
    assert (PADDREQ: eval_place (globalenv se prog) le m2 p b ofs).
    { exploit eval_place_footprint_unchanged.
      2: eapply PADDR1. eauto. eauto. auto.
      all: eauto.
      intros (bs & UNC & NBS & INCL & DIS).
      eapply UNC; eauto.
      eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on. eauto.
      simpl. intros.
      destruct H.
      intro. destruct H1. subst. eapply DIS; eauto.
      simpl. auto.
      destruct H; subst. intro. destruct H. eapply H1.
      rewrite OFSEQ in *. rewrite TYP.
      replace (prog_comp_env prog) with ce in H2 by auto.
      lia. }
    exploit eval_place_det. eapply PADDR. eauto. intros (E1 & E2). subst.
    eapply ERR0.
    red. split.
    (* permission *)
    exploit CONSISTENT. eauto. intros CON.
    generalize (sizeof_variant_ge4_complete ge co0 CON WT5). intros GE4.
    assert (SZEQ: sizeof ce (typeof_place p) = co_sizeof co0).
    { rewrite TYP. simpl. unfold ce. rewrite CO. auto. }    
    red. intros. simpl in H. erewrite <- Mem.unchanged_on_perm.
    eapply Mem.perm_implies. eapply PERM; eauto.
    rewrite SZEQ. lia. constructor.
    eapply assign_loc_unchanged_on; eauto. simpl.
    intro. destruct H0. rewrite OFSEQ in *. lia. auto.    
    (* alignment *)
    eapply Z.divide_trans; eauto. rewrite TYP.
    simpl. unfold ce. rewrite CO. 
    erewrite co_consistent_alignof; eauto. rewrite WT5.
    eapply tag_align_divide_composite. }

  (* 1-5: step_box_error *)
  1-5: inv SOUND; inv WTST; inv STMT; simpl in TR; simpl_getIM IM;
  destruct (move_check_expr ce mayinit mayuninit universe e) eqn: MOVE1; try congruence;
  unfold move_check_expr in MOVE1;
  destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVECKE; try congruence;
  destruct p0 as (mayinit' & mayuninit');
  destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence;
  inv TR; inv WT1;
  (* destruct list_norepet *)
  simpl in NOREP;
  generalize NOREP as NOREP'; intros;
  eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
  { eapply H1.
    eapply Mem.valid_access_implies.
    eapply Mem.valid_access_alloc_same; eauto.
    lia. generalize (sizeof_pos ge (typeof e)). lia.
    rewrite size_chunk_Mptr. rewrite align_chunk_Mptr.
    eapply Z.divide_opp_r. eapply Z.divide_refl.
    constructor. }
  (* 1-4: prove mmatch in m3 (using lots of automatic tactic to reduce
  the size of code *)
  1-4 :
    assert (BNIN: ~ In b (flat_fp_frame (fpf_func le fpm fpf))) by
    (intro; eapply Mem.fresh_block_alloc; eauto; eapply Hm; auto);
    (* show that m1 -> m3 unchanges the blocks in le and fpm *)
    assert (UNC1: Mem.unchanged_on (fun b' _ => In b' (flat_fp_frame (fpf_func le fpm fpf))) m1 m3) by
     (simpl; eapply Mem.unchanged_on_trans;
      [eapply Mem.alloc_unchanged_on; eauto |
        eapply Mem.store_unchanged_on; eauto]);
    assert (MM1: mmatch fpm ce m3 le own) by
    (eapply mmatch_unchanged; try eapply MM; 
          eapply Mem.unchanged_on_implies; try eapply UNC1; simpl; intros;

      rewrite app_assoc; eapply in_app; auto);
    assert (WFENV1: wf_env fpm ce m3 le) by
     (eapply wf_env_unchanged; eauto;
      eapply Mem.unchanged_on_implies; eauto;
      simpl; intros; eapply in_app; auto).
  { eapply eval_expr_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt. eapply MM1. all: eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM2 & WFENV2 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    eapply assign_loc_no_mem_error; eauto.
    eapply Z.divide_0_r.
    rewrite Z.add_0_l. red. intros.
    eapply Mem.perm_implies. eapply Mem.perm_store_1. eauto.
    eapply Mem.perm_alloc_2; eauto.
    generalize (size_chunk_pos Mptr). intros POS. unfold ce in H5.
    rewrite H in WT4. inv WT4.
    unfold ge in *. rewrite <- SZEQ. rewrite Ptrofs.unsigned_zero in H5. lia.
    constructor. }
  { exploit eval_expr_sem_wt. eapply MM1. all: eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM2 & WFENV2 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    exploit cast_val_is_casted; eauto. intros CASTED.                
    exploit assign_loc_sem_wt. eapply H4. eapply Z.divide_0_r.
    all: eauto. intro.
    eapply BNIN. simpl. rewrite !in_app.
    right. left. eapply EQUIV1. eapply in_app; auto.
    intros WTLOC1.
    assert (UNC2: Mem.unchanged_on (fun b' _ => In b' (flat_fp_frame (fpf_func le fpm fpf))) m3 m4).
    { eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto. simpl. intros. intro.
      destruct H8. subst. eapply BNIN. eauto. }
    (* show m4 is sound in the new own_env *)
    assert (MM3: mmatch fpm2 ce m4 le (move_place_option own (moved_place e))).
    { eapply mmatch_unchanged. eapply MM2.
      eapply Mem.unchanged_on_implies. eapply UNC2. simpl. intros.
      rewrite !in_app in H6. rewrite !in_app.
      destruct H6; auto. right. left. eapply EQUIV1. eapply in_app; auto. }
    assert (WFENV3: wf_env fpm2 ce m4 le).
    { eapply wf_env_unchanged. eapply WFENV2.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. eapply in_app; auto. }
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    (* eval_place_sound *)
    eapply dominators_must_init_sound in MOVE2; eauto.
    eapply eval_place_no_mem_error; eauto. }
  { exploit eval_expr_sem_wt. eapply MM1. all: eauto.
    intros (vfp & fpm2 & WTVAL & WTFP & MM2 & WFENV2 & NOREP1 & EQUIV1 & WFOWN1).
    exploit sem_cast_sem_wt; eauto.
    intros (fp' & WTVAL2 & WTFP2 & FPEQ). rewrite FPEQ in *.
    exploit cast_val_is_casted; eauto. intros CASTED.                
    exploit assign_loc_sem_wt. eapply H4. eapply Z.divide_0_r.
    all: eauto. intro.
    eapply BNIN. simpl. rewrite !in_app.
    right. left. eapply EQUIV1. eapply in_app; auto.
    intros WTLOC1.
    assert (UNC2: Mem.unchanged_on (fun b' _ => In b' (flat_fp_frame (fpf_func le fpm fpf))) m3 m4).
    { eapply Mem.unchanged_on_implies.
      eapply assign_loc_unchanged_on; eauto. simpl. intros. intro.
      destruct H9. subst. eapply BNIN. eauto. }
    (* show m4 is sound in the new own_env *)
    assert (MM3: mmatch fpm2 ce m4 le (move_place_option own (moved_place e))).
    { eapply mmatch_unchanged. eapply MM2.
      eapply Mem.unchanged_on_implies. eapply UNC2. simpl. intros.
      rewrite !in_app in H7. rewrite !in_app.
      destruct H7; auto. right. left. eapply EQUIV1. eapply in_app; auto. }
    assert (WFENV3: wf_env fpm2 ce m4 le).
    { eapply wf_env_unchanged. eapply WFENV2.
      eapply Mem.unchanged_on_implies; eauto.
      simpl. intros. eapply in_app; auto. }
    (** sound_own after moving the place in the expression *)
    assert (SOWN1: sound_own (move_place_option own (moved_place e)) mayinit' mayuninit' universe).
    { destruct (moved_place e) eqn: MP; simpl; inv MOVE1; auto.
      eapply move_place_sound. auto. }
    (* eval_place_sound *)
    eapply dominators_must_init_sound in MOVE2; eauto.
    exploit eval_place_sound; eauto. 
    intros (pfp & GFP & WTFP3 & PRAN & PERM & VALID).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.
    (* prove assign_loc of the pointer does not cause memory error *)
    rewrite H in *.
    inv H6; simpl in *; try congruence.
    inv H7. eapply H8. red.
    split; auto.
    eapply Mem.range_perm_implies; eauto. constructor. }
  
  (* step_dropplace_mem_error *)
  { eapply step_dropplace_no_mem_error; eauto. }

  (* step_drop_mem_error *)
  { eapply step_dropstate_no_mem_error; eauto. }

  (* step_call_mem_error1 *)
  { inv WTST; inv SOUND. inv STMT. inv WT1.
    inv H. inv H1. }
  (* step_call_mem_error2 *)
  { inv SOUND; inv WTST. inv WT1. inv STMT. inv TR.
    simpl_getIM IM. 
    destruct (move_check_exprlist ce mayinit mayuninit universe al) eqn: MOVE1; try congruence.
    destruct p0 as (mayinit' & mayuninit').
    destruct (move_check_assign mayinit' mayuninit' universe p) eqn: MOVE2; try congruence.
    (* destruct list_norepet *)
    simpl in NOREP.
    generalize NOREP as NOREP'. intros.
    eapply list_norepet3_fpm_changed in NOREP as (N1 & N2 & N3 & N4 & N5 & DIS1).
    eapply eval_exprlist_no_mem_error; eauto. }

  (* step_internal_function_error *)
  { inv H. inv SOUND. inv WTST. 
    (* lots of code copied from function_entry_sound *)
    exploit find_funct_move_check. eapply FIND. intros SPEC. 
    inv SPEC. simpl in FUNC.
    simpl in FIND. rewrite FIND in FUNC. inv FUNC.
    simpl in FUNTY. unfold type_of_function in FUNTY. inv FUNTY.
    unfold move_check_function in CKFUN.
    monadInv CKFUN.
    destruct x1 as ((initMap & uninitMap) & universe). monadInv EQ2.
    (* try to destruct init_own_env *)
    unfold init_own_env in OWN1.
    destruct (collect_func ge f) eqn: COL; simpl in OWN1; try congruence.
    set (empty:= (PTree.map
                    (fun (_ : positive) (_ : LPaths.t) => Paths.empty)
                    t)) in *.
    set (uninit := (add_place_list t
                      (places_of_locals (fn_params f ++ fn_vars f)) empty)) in *.
    generalize OWN1. clear OWN1.
    set (flag := check_own_env_consistency empty empty uninit t).
    generalize (eq_refl flag).
    generalize flag at 1 3.
    intros flag0 E. destruct flag0; try congruence.
    intros. 
    exploit analyze_collect_func_inv; eauto. intros COL1.
    rewrite COL in COL1. inv COL1.
    assert (WFOWN1: wf_own_env e ge own1).
    { inv OWN1. eapply check_universe_wf_own_env.
      destruct x1.
      rewrite bind_vars_app in EQ0.
      replace (PTree.empty type) with (env_to_tenv (PTree.empty (block * type))) in EQ0 by auto.
      erewrite alloc_variables_bind_vars_eq in EQ0.
      2: eauto. eapply EQ0.
      intros id paths EMP. unfold empty in EMP. erewrite PTree.gmap in EMP.
      destruct (universe ! id) eqn: G; simpl in EMP; try congruence.
      inv EMP. eapply Paths.empty_1. }
    assert (MM1: mmatch (init_footprint_map ce (fn_params f ++ fn_vars f) (PTree.empty footprint)) ce m1 e own1).
    { eapply mmatch_no_init_place.
      intros. inv OWN1.
      unfold is_init. simpl.
      unfold empty. unfold PathsMap.get.
      rewrite PTree.gmap. destruct (universe ! (local_of_place p)); simpl.
      auto. auto. }
    set (fpm1 := (init_footprint_map ce (fn_params f ++ fn_vars f) (PTree.empty footprint))) in *.    
    assert (WFENV1: wf_env fpm1 ce m1 e).
    { eapply alloc_variables_wf_env. 
      eapply wf_env_empty. eauto. unfold var_names. rewrite map_app.
      eauto.
      (* intros. eapply PTree.gempty.     *)
      unfold check_cyclic_struct_res in EQ2. destruct forallb eqn: CYC in EQ2; try congruence.
      intros. erewrite forallb_forall in CYC. eapply CYC. eapply in_map_iff.
      exists (id, ty). eauto.
      unfold check_valid_types in EQ3. destruct forallb eqn: VAL in EQ3; try congruence.
      intros. erewrite forallb_forall in VAL. eapply VAL. eapply in_map_iff.
      exists (id, ty). eauto.  }
    assert (WTVAL1: sem_wt_val_list ge m1 fpl vargs).
    { eapply sem_wt_val_list_unchanged_blocks. eauto.
      eapply alloc_variables_unchanged_on; eauto. }
    exploit alloc_variables_norepet; eauto.
    intros. rewrite PTree.gempty in H. inv H.
    econstructor.
    intros (NOREPLE & NVALID).
    assert (NVALID1: forall id b ty, e!id = Some (b, ty) -> ~ Mem.valid_block m b).
    { intros. exploit NVALID; eauto.
      intros [A1|A2]. auto. rewrite PTree.gempty in A2. inv A2. }    
    (* show that fpm1 is empty *)
    generalize (init_footprint_map_flat (fn_params f ++ fn_vars f) (PTree.empty footprint)).
    intros EQUIV.
    replace (flat_fp_map (PTree.empty footprint)) with (@nil block) in EQUIV by auto.
    exploit @list_equiv_nil_r; eauto. intros NIL. fold fpm1 in NIL.    
    eapply bind_parameters_no_mem_error. eapply MM1. eauto. eauto.
    eapply list_norepet_append_right; eauto. eauto. eauto.
    (* norepet *)
    unfold fpm1.
    erewrite NIL. rewrite app_nil_r. auto.
    intros.  
    exploit (init_footprint_map_flat_element (fn_params f ++ fn_vars f)).
    eapply in_app; eauto.
    intros (fp & A1 & A2). exists fp. eauto.
    (* valid_type *)
    unfold check_valid_types in EQ3. destruct forallb eqn: VAL in EQ3; try congruence.
    intros. erewrite forallb_forall in VAL. eapply VAL. eapply in_map_iff.
    exists (id, ty). split; auto. eapply in_app; auto.  
    (* disjoint *)
    unfold fpm1.
    rewrite NIL. rewrite app_nil_r.
    red. intros. intro. subst.
    exploit in_footprint_of_env_inv; eauto. intros (id1 & ty1 & LE).
    eapply NVALID1; eauto. eapply Hm; eauto.
    eapply in_app; eauto.
    (* disjointness between le and vl *)
    red. intros. intro. subst.
    exploit in_footprint_of_env_inv. eauto. intros (id & ty & IN1).
    eapply NVALID1; eauto.
    eapply sem_wt_val_list_valid_blocks; eauto.
    auto. auto. }

  (* step_return_1_error1 *)
  { inv SOUND. inv WTST. inv WT1. inv STMT.
    inv TR. simpl_getIM IM.
    set (e:= (if scalar_type (typeof_place p)
            then Epure (Eplace p (typeof_place p))
            else Emoveplace p (typeof_place p))) in *.
    destruct (move_check_expr' ce mayinit mayuninit universe e) eqn: MOVE1; try congruence.
    assert (WTE: wt_expr le ce e).
    { unfold e. destruct (scalar_type (typeof_place p)) eqn: PTY; econstructor; auto.
      econstructor. auto. }
    assert (TYEQ: typeof e = typeof_place p).
    { unfold e. destruct (scalar_type (typeof_place p)) eqn: PTY; auto. }
    assert (NOERR: ~ eval_expr_mem_error ge le m e).
    { intro.
      eapply eval_expr_no_mem_error; eauto. }
    apply NOERR. unfold e.
    destruct (scalar_type); auto.
    econstructor. auto. inv H. auto. }
  (* step_return_1_error2 *)
  { inv SOUND.
    assert (X: exists m', Mem.free_list m (blocks_of_env ge le) = Some m').
    { apply SimplLocalsproof.can_free_list.
      - (* permissions *)
        intros. unfold blocks_of_env in H0.          
        exploit list_in_map_inv; eauto. intros [[id [b' ty]] [EQ IN]].
        unfold block_of_binding in EQ; inv EQ.
        eapply wf_env_freeable; eauto.
        eapply PTree.elements_complete; eauto.
      - (* no overlap *)
        unfold blocks_of_env.
        simpl in NOREP. eapply list_norepet_app in NOREP as (N1 & N2 & N3).
        unfold footprint_of_env in N1.
        eapply footprint_norepet_implies_freelist_no_overlap; eauto. }
    destruct X. congruence. }

  (* step_returnstate_error1 *)
  { inv SOUND. inv WTST. inv STK. inv WT1.
    eapply eval_place_no_mem_error; eauto. }
  (* step_returnstate_error2 *)
  { inv SOUND. inv WTST. inv STK. inv WT1.
    (* evaluate the place *)
    exploit eval_place_sound; eauto.
    intros (pfp & GFP & WTFP1 & PRAN & PERM & VALIDB).
    exploit get_loc_footprint_map_align; eauto. intros ALIGN.        
    (* assign no error *)
    eapply assign_loc_no_mem_error; eauto.
    eapply Mem.range_perm_implies; eauto. constructor. }

  (* step_ifthenelse_error *)
  { inv SOUND. inv WTST. inv STMT. inv WT1. simpl in CHECK.
    simpl_getIM IM. destruct a; try congruence.
    inv H.
    destruct (move_check_pexpr mayinit mayuninit universe p) eqn: CK; try congruence.
    inv WT0.
    eapply eval_pexpr_no_mem_error; eauto. }
Qed.

End MOVE_CHECK.

(** Specific definition of partial safe *)
(* Definition partial_safe ge (L: lts li_rs li_rs state) (s: state) : Prop := *)
(*   not_stuck L s \/ step_mem_error ge s. *)

Definition mem_error prog se (s: state) : Prop :=
  step_mem_error (globalenv se prog) s.

(* I is the generic partial safe invariant *)
Lemma move_check_module_safe (I: invariant li_rs) p p1:
  module_type_safe I I (semantics p) (mem_error p) ->  
  (* Genv.valid_for (erase_program (program_of_program p)) se ->  *)
  move_check_program p = OK p1 ->
  module_type_safe (inv_compose I rs_own) (inv_compose I rs_own) (semantics p) SIF.
  (* module_safe_se (semantics p) (inv_compose I rs_own) (inv_compose I rs_own) not_stuck se. *)
Proof.
  intros [SAFE] MVCHK. destruct SAFE as (SINV & PRE).
  (* w1 is the world in partial safe *)
  set (IS := fun se1 '(w1, (se2, w2)) s =>
               SINV se1 w1 s
               /\ sound_state p w2 se2 s
               /\ wt_state p se2 (mod_sg w2) s
               (** adhoc: for now we add this invariant here to deal
               with typing information passed between modules. This
               invariant is hard-code in the initial state *)
               /\ rs_sig_comp_env (mod_sg w2) = p.(prog_comp_env)).
  red. constructor.
  eapply (Module_type_safe_components li_rs li_rs (semantics p) (inv_compose I rs_own) (inv_compose I rs_own) SIF IS).
  intros se (w1 & (se' & w2)) (SYMINV1 & SYMINV2) VSE. simpl in SYMINV2. subst.
  simpl in VSE.
  generalize (PRE se w1 SYMINV1 VSE). intros PRE1.
  (* specification of move checking *)
  exploit move_check_program_meet_spec; eauto.
  intros SPEC. inv SPEC.
  econstructor.
  (* internal_step_preserves *)
  - intros s t s' (SINV1 & SOUND & WTST & CE) STEP.
    simpl. repeat apply conj; auto.
    + eapply internal_step_preserves; eauto.
    + eapply step_sound; eauto.
    + eapply step_sound; eauto.
  (* internal_state_progress *)
  - intros s (SINV1 & SOUND & WTST & CE).
    exploit @internal_state_progress; eauto. intros [A|B].
    auto.
    (* memory error is impossible in sound_state *)
    right. red. eapply step_no_mem_error; simpl; eauto.
  (* initial_preserves_progress *)
  - intros q VQ (QINV1 & QINV2).
    (** partial safe also allow initial_state???? *)
    exploit @initial_preserves_progress; eauto.
    intros (s & INIT & SINV1).
    exists s. split; auto.
    intros s' INIT'.
    (* establish rs_sig_comp_env (mod_sg w2) = globalenv se p in the
    initial state *)
    assert (CE: rs_sig_comp_env (mod_sg w2) = globalenv se p).
    { inv QINV2. inv INIT'. simpl. auto. }
    red. exploit initial_state_sound; eauto.
    intros (SOUND & WT).
    repeat apply conj; auto.
  (* external_preserves_progress *)
  - intros s q (SINV1 & SOUND & WTST & SE) ATEXT.
    exploit @external_preserves_progress; eauto.
    intros (wI & SYM1 & QINV1 & AFEXT1).    
    exploit external_sound; eauto. 
    intros ((wrs & se') & SYM2 & QINV2 & AFEXT2).
    exists (wI, (wrs, se')). repeat apply conj; auto.
    (* after external *)
    intros r (RINV1 & RINV2).
    exploit AFEXT1; eauto.
    intros (s' & AFST & AF).
    exists s'. split; auto.
    intros s'' AFST'.
    exploit AFEXT2; eauto. intros (s''' & AFST'' & AF').
    red.  simpl in AF'. repeat apply conj; auto.
    eapply AF'. eauto. eapply AF'. eauto.
  (* final_state_preserves *)
  - intros s r (SINV1 & SOUND & WTST & CE) FINAL.
    exploit @final_state_preserves; eauto.
    intros RINV1.
    exploit @final_sound; simpl; eauto. 
Qed.

(* Definition rs_own_inv p '(se, w) := sound_state p (se, w) se. *)

(* Lemma sound_rustir_preserves p: *)
(*   move_check_program p = OK p -> *)
(*   preserves (semantics p) rs_own rs_own (rs_own_inv p). *)
(* Proof. *)
(*   intros. *)
(*   assert (CE: forall se, composite_env_consistent (globalenv se p)). *)
(*   { intros. eapply build_composite_env_consistent. *)
(*     instantiate (1 := (prog_types p)). destruct p; simpl; eauto. } *)
(*   constructor; intros; destruct w; simpl in *; subst. *)
(*   - eapply step_sound; eauto. *)
(*     constructor. *)
(*   - eapply initial_state_sound; eauto. *)
(*     constructor. *)
(*     auto. *)
(*   - exploit external_sound_progress; eauto. *)
(*     constructor. *)
(*     intros (wA & SINV & QINV & RINV). *)
(*     exists wA. repeat apply conj; auto. *)
(*     intros. eapply external_sound_preserve; eauto. *)
(*     constructor. *)
(*   - exploit final_sound_progress; eauto. *)
(*     constructor. *)
(* Qed. *)

(* Lemma sound_rustir_self_sim p: *)
(*   move_check_program p = OK p -> *)
(*   forward_simulation rs_own rs_own (semantics p) (semantics p). *)
(* Proof. *)
(*   intros. *)
(*   eapply preserves_fsim with (IS := rs_own_inv p). *)
(*   eapply sound_rustir_preserves. *)
(*   auto. *)
(* Qed. *)
 

