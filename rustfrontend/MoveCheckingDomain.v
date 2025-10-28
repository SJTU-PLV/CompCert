Require Import Coqlib .
Require Import Errors Maps.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep SmallstepLinking SmallstepLinkingSafe.
Require Import LanguageInterface CKLR Invariant.
Require Import Rusttypes Rustlight Rustlightown.
Require Import RustOp RustIR RustIRcfg Rusttyping.
Require Import Errors.
Require Import InitDomain InitAnalysis.
Require Import RustIRown MoveChecking.
Require Import MoveCheckingFootprint.
Require Import Wfsimpl.

Import ListNotations.


Section COMP_ENV.

Variable ce: composite_env.

(** * Definitions of semantics typedness (TODO: support user-defined semantics types) *)

Definition alignof_comp (id: ident) :=
  match ce ! id with
  | Some co => co_alignof co
  | None => 1
  end.

Definition sizeof_comp (id: ident) :=
  match ce ! id with
  | Some co => co_sizeof co
  | None => 0
  end.



(* Semantics well typed location is mutually defined with semantics
well typed value *)
Inductive sem_wt_loc (m: mem) : footprint -> block -> Z -> Prop :=
| sem_wt_base: forall ty b ofs chunk v
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (* (NOTBOX: forall ty', ty <> Tbox ty') *)
    (WT: sem_wt_val m (fp_scalar ty) v),
    sem_wt_loc m (fp_scalar ty) b ofs
| sem_wt_box: forall b ofs fp b1 sz1 v
    (LOAD: Mem.load Mptr m b ofs = Some v)
    (WT: sem_wt_val m (fp_box b1 sz1 fp) v),
    sem_wt_loc m (fp_box b1 sz1 fp) b ofs
| sem_wt_struct: forall b ofs fpl id
    (* all fields are semantically well typed *)
    (FWT: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        sem_wt_loc m ffp b (ofs + fofs)),
    sem_wt_loc m (fp_struct id fpl) b ofs
| sem_wt_enum: forall fp b ofs tagz fid fofs id orgs
    (* Interpret the field by the tag and prove that it is well-typed *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz)))
    (FWT: sem_wt_loc m fp b (ofs + fofs)),
    sem_wt_loc m (fp_enum id orgs tagz fid fofs fp) b ofs

with sem_wt_val (m: mem) : footprint -> val -> Prop :=
| wt_val_unit:
  sem_wt_val m (fp_scalar Tunit) (Vint Int.zero)
| wt_val_int: forall sz si n,
    (* Cop.cast_int_int sz si n = n -> *)
    sem_wt_val m (fp_scalar (Tint sz si)) (Vint n)
| wt_val_single: forall n,
    sem_wt_val m (fp_scalar (Tfloat Ctypes.F32)) (Vsingle n)
| wt_val_float: forall n,
    sem_wt_val m (fp_scalar (Tfloat Ctypes.F64)) (Vfloat n)
| wt_val_long: forall si n,
    sem_wt_val m (fp_scalar (Tlong si)) (Vlong n)
| wt_val_box: forall b fp sz
    (** Box pointer must be in the starting point of a block *)
    (* The value stored in (b,0) has type ty and occupies footprint fp *)
    (WTLOC: sem_wt_loc m fp b 0)
    (VALID: Mem.range_perm m b (- size_chunk Mptr) sz Cur Freeable)
    (SIZE: Mem.load Mptr m b (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (* sz >0 is used to make sure extcall_ext_free succeeds and sz <=
    max_unsigned is used to provent overflow when traversing some
    field offsets *)
    (RANGE: 0 < sz <= Ptrofs.max_unsigned),
    sem_wt_val m (fp_box b sz fp) (Vptr b Ptrofs.zero)
(* TODO *)
(* | wt_val_ref: forall b ofs ty org mut, *)
(*     sem_vt_val (Vptr b ofs) (Treference org mut ty) *)
| wt_val_struct: forall b ofs id fpl
    (WTLOC: sem_wt_loc m (fp_struct id fpl) b (Ptrofs.unsigned ofs))
    (AL: (alignof_comp id | Ptrofs.unsigned ofs))
    (* The permission of the location is readable to make sure
    assign_loc has no memory error *)
    (PERM: Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id) Cur Readable)
    (* range_perm cannot ensure that b is valid *)
    (VALID: Mem.valid_block m b),
    sem_wt_val m (fp_struct id fpl) (Vptr b ofs)
| wt_val_enum: forall b ofs fp tagz fid fofs id orgs
    (WTLOC: sem_wt_loc m (fp_enum id orgs tagz fid fofs fp) b (Ptrofs.unsigned ofs))
    (AL: (alignof_comp id | Ptrofs.unsigned ofs))
    (PERM: Mem.range_perm m b (Ptrofs.unsigned ofs) (Ptrofs.unsigned ofs + sizeof_comp id) Cur Readable)
    (VALID: Mem.valid_block m b),
    sem_wt_val m (fp_enum id orgs tagz fid fofs fp) (Vptr b ofs)
.


Definition sem_wt_val_list (m: mem) fpl vl : Prop :=
  list_forall2 (sem_wt_val m) fpl vl.

Inductive bmatch (m: mem) (b: block) (ofs: Z) : footprint -> Prop :=
| bm_box: forall b1 fp sz
    (LOAD: Mem.load Mptr m b ofs = Some (Vptr b1 Ptrofs.zero))
    (SIZE: Mem.load Mptr m b1 (- size_chunk Mptr) = Some (Vptrofs (Ptrofs.repr sz)))
    (VRES: Mem.range_perm m b1 (- size_chunk Mptr) sz Cur Freeable)
    (RANGE: 0 < sz <= Ptrofs.max_unsigned),
    bmatch m b ofs (fp_box b1 sz fp)
| bm_struct: forall fpl id
    (* all fields are semantically well typed *)
    (FMATCH: forall fid fofs ffp,
        find_fields fid fpl = Some (fid, fofs, ffp) ->
        bmatch m b (ofs + fofs) ffp),
    bmatch m b ofs (fp_struct id fpl)
| bm_enum: forall fp id tagz fid fofs orgs 
    (* Interpret the field by the tag and prove that it is well-typed *)
    (* [p] whose value has footprint (fp_enum tagz fp) is actually has
    tag tagz *)
    (TAG: Mem.load Mint32 m b ofs = Some (Vint (Int.repr tagz))) 
    (BM: bmatch m b (ofs + fofs) fp),
    bmatch m b ofs (fp_enum id orgs tagz fid fofs fp)
| bm_scalar: forall ty chunk v
    (* (TY: scalar_type ty = true) *)
    (MODE: Rusttypes.access_mode ty = Ctypes.By_value chunk)
    (LOAD: Mem.load chunk m b ofs = Some v)
    (WT: sem_wt_val m (fp_scalar ty) v),
    bmatch m b ofs (fp_scalar ty)
(** TODO: bm_reference  *)
.

End COMP_ENV.

Global Hint Constructors sem_wt_val sem_wt_loc: sem_ty.

Lemma in_norepet_footprint_list_unique: forall fpl id fofs1 fofs2 ffp1 ffp2,
    list_norepet (name_footprints fpl) ->
    In (id, fofs1, ffp1) fpl ->
    In (id, fofs2, ffp2) fpl ->
    fofs1 = fofs2 /\ ffp1 = ffp2.
Proof.
  induction fpl; intros.
  - inv H0.
  - inv H0. inv H1.
    + inv H0. eauto.
    + inv H. exfalso.
      eapply H3. eapply in_map_iff.
      exists (id, fofs2, ffp2). eauto.
    + inv H1.
      * inv H. exfalso.
      eapply H3. eapply in_map_iff.
      exists (id, fofs1, ffp1). eauto.
      * inv H. eauto.
Qed.

Lemma sem_wt_loc_footprint_valid_block: forall fp m b0 b ofs ty ce
    (COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co))),
    sem_wt_loc ce m fp b0 ofs ->
    wt_footprint ce ty fp ->
    In b (footprint_flat fp) ->
    Mem.valid_block m b.
Proof.
  induction fp using strong_footprint_ind; intros until ce; intros ? WTLOC WTFP IN.
  - inv IN.
  - inv IN.
  - simpl in IN. destruct IN.
    + subst. inv WTLOC. inv WT.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies.
      eapply Mem.load_valid_access. eauto. constructor.
    + inv WTLOC. inv WT. inv WTFP.
      eauto.
  - inv WTLOC. simpl in IN.
    inv WTFP.
    eapply in_flat_map in IN as (((fid & fofs) & ffp) & A1 & A2).
    destruct (find_fields fid fpl) eqn: FIND.
    2: { exploit find_none. eapply FIND. eapply A1. simpl.
         rewrite dec_eq_true. congruence. }
    repeat destruct p.
    exploit find_fields_some; eauto. intros (B1 & B2). subst.
    exploit in_norepet_footprint_list_unique. rewrite FLAT.
    eapply COMP_NOREP. eauto. eapply A1. eapply B2. intros (C1 & C2). subst.
    exploit WT2. eauto. intros (fty & F1 & F2 & F3).
    eapply H. eauto. eauto.
    eapply FWT. eauto. eapply F3. auto.
  - inv WTLOC. inv WTFP. 
    simpl in IN. eauto.
Qed.

Lemma sem_wt_val_footprint_valid_block: forall fp m b v ty ce
     (* used to guarantee that all the footprints in struct are not redundant *)
    (COMP_NOREP: forall id co, ce ! id = Some co -> list_norepet (name_members (co_members co))),
    sem_wt_val ce m fp v ->
    wt_footprint ce ty fp ->
    In b (footprint_flat fp) ->
    Mem.valid_block m b.
Proof.
  induction fp using strong_footprint_ind; intros until ce; intros ? WTVAL WTFP IN.
  - inv IN.
  - inv IN.
  - simpl in IN. destruct IN.
    + subst. inv WTVAL.
      eapply Mem.valid_access_valid_block.
      eapply Mem.valid_access_implies.
      eapply Mem.load_valid_access. eauto. constructor.
    + inv WTVAL. inv WTFP.
      eapply sem_wt_loc_footprint_valid_block. eauto.
      eapply WTLOC. eauto. auto.      
  - inv WTVAL. simpl in IN.
    inv WTLOC. inv WTFP.
    eapply in_flat_map in IN as (((fid & fofs) & ffp) & A1 & A2).
    destruct (find_fields fid fpl) eqn: FIND.
    2: { exploit find_none. eapply FIND. eapply A1. simpl.
         rewrite dec_eq_true. congruence. }
    repeat destruct p.
    exploit find_fields_some; eauto. intros (B1 & B2). subst.
    exploit in_norepet_footprint_list_unique. rewrite FLAT.
    eapply COMP_NOREP. eauto. eapply A1. eapply B2. intros (C1 & C2). subst.
    exploit WT2. eauto. intros (fty & F1 & F2 & F3).
    eapply sem_wt_loc_footprint_valid_block. eauto.
    eapply FWT. eauto. eapply F3. auto.
  - inv WTVAL. inv WTFP. inv WTLOC.
    simpl in IN. eapply sem_wt_loc_footprint_valid_block; eauto.
Qed.

(** * Semantics Interface *)

(* Similar to inject_separated: m contains footprint fp1 and fp2 is
the extended footprint which is not in m *)
Definition flat_footprint_separated (fp1 fp2: flat_footprint) (m : mem) : Prop :=
  forall b, ~ In b fp1 ->
       In b fp2 ->
       ~ Mem.valid_block m b.

(** Unused because it is equivalent to
flat_footprint_separated. footprint which not in fp1 and valid in m is
not in fp2 *)
Definition flat_footprint_incr (fp1 fp2: flat_footprint) (m: mem) : Prop :=
  forall b, ~ In b fp1 ->
       Mem.valid_block m b ->
       ~ In b fp2.
  
Lemma flat_footprint_separated_refl: forall fp m,
    flat_footprint_separated fp fp m.
Proof.
  intros. red. intros. congruence.
Qed.

(* If the footprint shrinks, the flat_footprint_separated is
    satisfied trivially *)
Lemma flat_footprint_separated_shrink: forall l1 l2 m,
    incl l2 l1 ->
    flat_footprint_separated l1 l2 m. 
Proof.
  intros. red. intros. intro. eapply H0. auto.
Qed.

Inductive rs_own_world :=
  rsw (sg: rust_signature)
    (fp: flat_footprint)
    (m: mem)
    (* used to prove Sbox *)
    (Hm: Mem.sup_include fp (Mem.support m)).

(** FIXME: we may require that fp is norepet *)
Inductive rs_own_query : rs_own_world -> rust_query -> Prop :=
| rs_own_query_intro: forall sg m vf args fpl fp Hm,
    let ce := rs_sig_comp_env sg in
    forall (NOREP: list_norepet (flat_map footprint_flat fpl))
    (SEMWT: sem_wt_val_list ce m fpl args)
    (* footprints are well-typed *)
    (WTFP: wt_footprint_list ce (rs_sig_args sg) fpl)
    (* structured footprint is equivalent with the flat footprint in the interface *)
    (EQ: list_equiv fp (flat_map footprint_flat fpl)),
    rs_own_query (rsw sg fp m Hm) (rsq vf sg args m)
.

(* Only consider ownership transfer for now. The footprints of generic
origins are more complicated *)
Inductive rsw_acc : rs_own_world -> rs_own_world -> Prop :=
| rsw_acc_intro: forall sg fp fp' m m' Hm Hm'
    (UNC: Mem.unchanged_on (fun b ofs => ~ In b fp) m m')
    (* new footprint is separated *)
    (SEP: flat_footprint_separated fp fp' m),
    (* block not in fp must be not in fp' otherwise it is not a frame rule *)
    (* (INCR: flat_footprint_incr fp fp' m), *)
    rsw_acc (rsw sg fp m Hm) (rsw sg fp' m' Hm').

Inductive rs_own_reply : rs_own_world -> rust_reply -> Prop :=
| rs_own_reply_intro: forall rfp m rv sg fp Hm,
    let ce := rs_sig_comp_env sg in
    forall (SEMWT: sem_wt_val ce m rfp rv)
    (WTFP: wt_footprint ce (rs_sig_res sg) rfp)
    (CAST: val_casted rv (rs_sig_res sg))
    (* rfp is extracted from fpl *)
    (INCL: incl (footprint_flat rfp) fp)
    (NOREP: list_norepet (footprint_flat rfp)),
    rs_own_reply (rsw sg fp m Hm) (rsr rv m)
.

Definition rs_own : invariant li_rs :=
  {|
    inv_world := Genv.symtbl * rs_own_world;
    symtbl_inv := fun '(se, _) => eq se;
    query_inv := fun '(_, w) q => rs_own_query w q;
    reply_inv := fun '(_, w) r => exists w', rsw_acc w w' /\ rs_own_reply w' r |}.


(* Unused: Rust type used in interface *)
Inductive rtype : Type :=
(* primitive types excluding struct and enum *)
| rt_int (sz: Ctypes.intsize) (sg: Ctypes.signedness)
| rt_box (ty: rtype)
| rt_comp
    (id: ident)
    (sv: struct_or_variant)
    (fields: list (ident * rtype))
    (attr: Ctypes.attr)
    (orgs: list origin)
    (rels: list origin_rel)
(* used in recursive type  *)
| rt_comp_rec (id: ident)
.

(* Property of rsw_acc *)

Lemma rsw_acc_refl: forall w,
    rsw_acc w w.
Proof.
  intros. destruct w.
  econstructor.
  eapply Mem.unchanged_on_refl.
  red. intros. congruence.
Qed.
  
Lemma rsw_acc_trans: forall w1 w2 w3,
    rsw_acc w1 w2 ->
    rsw_acc w2 w3 ->
    rsw_acc w1 w3.
Proof.
  intros. inv H. inv H0.
  econstructor.
  - (* cannot use unchanged_on_trans because fp is not useful in m' *)
    inv UNC. inv UNC0.
    econstructor.
    + eauto with mem.
    (* perm *)
    + intros.
      assert (A: ~ In b fp').
      { intro. eapply SEP; eauto. }
      split; intros.
      * eapply unchanged_on_perm0; eauto.
        eapply unchanged_on_support; auto.
        eapply unchanged_on_perm; eauto.
      * eapply unchanged_on_perm; eauto.
        eapply unchanged_on_perm0; eauto.
        eapply Mem.perm_valid_block.
        eapply unchanged_on_perm0 in H1; eauto.
        eapply unchanged_on_support. eauto.
    (* contents *)
    + intros.
      assert (A: Mem.valid_block m b).
      eapply Mem.perm_valid_block. eauto.
      assert (B: ~ In b fp').
      { intro. eapply SEP; eauto. }
      erewrite unchanged_on_contents0; eauto.
      eapply unchanged_on_perm; eauto.
  (* flat_footprint_separated *)
  - red. intros.
    destruct (Mem.sup_dec b (Mem.support m)); auto.
    (* impossible *)
    (* 1. b is in not fp' (by SEP) ; 2. b is in fp'0; 3. so b is not
    in m' support (by SEP0) *)
    assert (A: ~ In b fp').
    { intro. eapply SEP; eauto. }
    intro. eapply Mem.unchanged_on_support in H1; eauto.
    eapply SEP0; eauto.
Qed.    


(** * Semantics invariant *)

Section FPM.

Variable fpm : fp_map.
  
Definition mmatch ce (m: mem) (e: env) (own: own_env): Prop :=
  forall p b ofs fp,
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) ->
    is_init own p = true ->
    bmatch ce m b ofs fp
    /\ (is_full own.(own_universe) p = true ->
       sem_wt_loc ce m fp b ofs).


Record wf_env (ce: composite_env) (m: mem) (e: env): Prop := {
    wf_env_footprint: forall id b ty,
      e!id = Some (b, ty) ->
      (* Do we need to ensure the location is sem_wt? *)
      exists fp, fpm!id = Some fp
            /\ wt_footprint ce ty fp;
    
    (* stack blocks and the blocks in footprint map are disjoint. This
    property can be expressed in sound_state *)
    (* wf_env_disjoint: *)
    (* list_disjoint (footprint_of_env e) (flat_fp_map fpm) *)

    (* The permission of stack blocks is freeable *)
    wf_env_freeable: forall id b ty,
      e!id = Some (b, ty) ->
      Mem.range_perm m b 0 (sizeof ce ty) Cur Freeable /\
        Mem.valid_block m b ;
  }.

End FPM.


(* Some useful invariant of the own_env in the move checking, such as
if a place p is init, then all its dominators is init. Those
properties are only guaranteed by the move checking, so we cannot
prove it in the semantics. One problem is how to establish and
preserve this invariant in the function entry and every step. May be
we should do some checking for each function *)

Record wf_own_env le ce (own: own_env) : Prop := {
    wf_own_dominators: forall p,
      is_init own p = true ->
      dominators_is_init own p = true;

    (* if a place is in the universe, all its dominators are in
    universe. It is used to prove wf_own_dominators when doing
    init_place. *)
    wf_own_dominators_complete: forall p p1,
      in_universe own p = true ->
      In p1 (place_dominators p) ->
      in_universe own p1 = true;
    
    (* validation property *)
    wf_own_universe_shallow: forall p1 p2,
      in_universe own p1 = true ->      
      in_universe own p2 = true ->
      is_prefix_strict p1 p2 = true ->
      is_shallow_prefix p1 p2 = false;

    (* all place in the universe has no downcast *)
    wf_own_no_downcast: forall p fid ty,
      in_universe own p = true ->
      ~ In (ph_downcast ty fid) (snd (path_of_place p));

    (* if a place is not full, it must be box type. Remember that if a
    struct/or some other scalar place is in the universe, it must be
    full. *)
    wf_own_type: forall p,
      in_universe own p = true ->
      is_full (own_universe own) p = false ->
      exists ty, typeof_place p = Tbox ty;

    (* all the places in the universe is wt_place *)
    wf_own_wt_place: forall p,
      in_universe own p = true ->
      wt_place le ce p;
  }.

(* easy because none of the property in wf_own_env rely on some place
in init set *)
Lemma wf_own_env_move_place: forall own p le ce,
    wf_own_env le ce own ->
    wf_own_env le ce (move_place own p).
Proof.
  intros own p le ce WFOWN.
  econstructor.
  - intros.
    eapply move_place_init_is_init in H as A1.
    eapply wf_own_dominators in A1 as A2. 2: eauto.
    eapply move_irr_place_dominator_still_init; eauto.
  - intros. unfold move_place, remove_place, in_universe in *. simpl in *.
    eapply wf_own_dominators_complete; eauto.
  - intros.
    eapply wf_own_universe_shallow; eauto.
  - intros.
    eapply wf_own_no_downcast; eauto.
  - intros.
    eapply wf_own_type; eauto.
  - intros.
    eapply wf_own_wt_place; eauto.
Qed.

 
Lemma wf_own_env_init_place: forall own p le ce,
    wt_place le ce p ->
    dominators_is_init own p = true ->
    wf_own_env le ce own ->
    wf_own_env le ce (init_place own p).
Proof.
  intros own p le ce WTP DOM WFOWN.
  econstructor.
  - intros.    
    exploit init_irrelavent_place_still_not_owned_inv. eauto.
    intros [A|B].
    + eapply wf_own_dominators in A as A1. 2: eauto. 
      eapply init_place_dominators_still_init; eauto.      
    + assert (INU: in_universe own p0 = true).
      { erewrite in_universe_eq.
        eapply is_init_in_universe. eapply H.
        unfold init_place. simpl. eapply PathsMap.eq_refl. }      
      eapply init_dominator_init_prefix.
      intros. eapply wf_own_dominators_complete; eauto. 
      eapply is_prefix_wt; eauto.
      eapply wf_own_wt_place; eauto. auto.
  - intros. unfold init_place, add_place, in_universe in *. simpl in *.
    eapply wf_own_dominators_complete; eauto.
  - intros.
    eapply wf_own_universe_shallow; eauto.
  - intros.
    eapply wf_own_no_downcast; eauto.
  - intros.
    eapply wf_own_type; eauto.
  - intros.
    eapply wf_own_wt_place; eauto.
Qed.
    

Section COMP_ENV.

Variable ce: composite_env.

(* Lemma downcaset_dominators_eq: forall p fid fty, *)
(*     place_dominators p = place_dominators (Pdowncast p fid fty). *)
(* Proof. *)
(*   induction p; intros; simpl; auto. *)

Inductive valid_owner_offset_footprint : place -> Z -> footprint -> footprint -> Prop :=
| valid_owner_local: forall id ty fp,
    valid_owner_offset_footprint (Plocal id ty) 0 fp fp
| valid_owner_deref: forall p ty fp,
    valid_owner_offset_footprint (Pderef p ty) 0 fp fp
| valid_owner_field: forall p fty fid fp,
    valid_owner_offset_footprint (Pfield p fid fty) 0 fp fp
| valid_owner_downcast: forall p fid fty fp fp1 tagz fofs ofs id orgs
    (PTY: typeof_place p = Tvariant orgs id)
    (* (CO: ce ! id = Some co) *)
    (* (FOFS: variant_field_offset ce fid co.(co_members) = OK fofs) *)
    (* (TAG: field_tag fid co.(co_members) = Some tagz) *)
    (VOWN: valid_owner_offset_footprint p ofs (fp_enum id orgs tagz fid fofs fp) fp1),
    valid_owner_offset_footprint (Pdowncast p fid fty) (ofs + fofs) fp fp1.

Lemma valid_owner_footprint_flat_eq: forall fp1 fp2 p ofs,
    valid_owner_offset_footprint p ofs fp1 fp2 ->
    footprint_flat fp1 = footprint_flat fp2.
Proof.
  induction 1; auto.
Qed.


(** So adhoc soluation: define a non-sense valid_owner_offset_footprint to prove the following two lemmas *)
Lemma valid_owner_place_footprint: forall p fpm e b ofs fp
    (PFP: get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp))
    (WT: wt_place e ce p),
  exists fp' ofs' fofs,
    get_loc_footprint_map e (path_of_place (valid_owner p)) fpm = Some (b, ofs', fp')
    /\ valid_owner_offset_footprint p fofs fp fp'
    /\ ofs = ofs' + fofs.
(* relationship between fp and fp'? *)
                          (* get_footprint *)
Proof.
  induction p; intros; simpl in *.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - exists fp, ofs, 0. repeat apply conj; auto.
    econstructor. lia.
  - destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app_inv in PFP.
    destruct PFP as (b1 & ofs1 & fp1 & GET1 & GET2).
    inv WT.
    exploit IHp; eauto.
    intros (fp2 & ofs2 & fofs2 & PFP1 & VOFS1 & OFSEQ).
    simpl in GET2. destruct fp1; try congruence.
    rewrite WT2 in GET2.
    destruct ident_eq in GET2; simpl in GET2; try congruence. subst.
    destruct list_eq_dec in GET2; simpl in GET2; try congruence. subst.
    destruct ident_eq in GET2; simpl in GET2; try congruence. subst.
    (* destruct type_eq in GET2; simpl in GET2; try congruence. *)
    inv GET2.
    do 3 eexists. repeat apply conj.
    eauto. econstructor; eauto.    lia.
    (* ??? use the fact that variant_field_offset is constant to prove *)
Qed.

Lemma valid_owner_bmatch: forall p m b ofs1 fofs1 fp1 fp,
    bmatch ce m b ofs1 fp1 ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    bmatch ce m b (ofs1 + fofs1) fp.
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  (* rewrite PTY in H0. inv H0. *)
  inv H0.
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.

Lemma valid_owner_sem_wt_loc: forall p m b ofs1 fofs1 fp1 fp,
    sem_wt_loc ce m fp1 b ofs1 ->
    valid_owner_offset_footprint p fofs1 fp fp1 ->
    sem_wt_loc ce m fp b (ofs1 + fofs1).
Proof.
  induction p; intros; simpl in *; inv H0; try rewrite Z.add_0_r; auto.
  exploit IHp; eauto. intros.
  inv H0. simpl in *. try congruence. 
  replace ((ofs1 + (ofs + fofs))) with (ofs1 + ofs + fofs) by lia.
  auto.
Qed.
      
(* get_loc_footprint_map can succeed if the place is well-typed, the
footprint is well-typed and the footprint is well shaped by
mmatch. This lemma is used in dropplace state soundness. Because there
is no static analysis result in dropplace, we need to use own_env to
show p's dominators are init *)
Lemma get_loc_footprint_map_progress: forall e m p own fpm
    (MM: mmatch fpm ce m e own)
    (WFOWN: wf_env fpm ce m e)
    (WT: wt_place (env_to_tenv e) ce p)
    (POWN: dominators_is_init own p = true)
    (** No downcast in the places *)
    (WF: forall fid ty, ~ In (ph_downcast ty fid) (snd (path_of_place p))),
  exists b ofs fp,
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp)
    /\ wt_footprint ce (typeof_place p) fp.
Proof.
  induction p; intros.
  (* Plocal *)
  - inv WT. exploit get_tenv_some; eauto. intros (b0 & A).    
    exploit wf_env_footprint; eauto. intros (fp & FP & WTFP).
    exists b0, 0, fp. repeat apply conj. simpl. rewrite A. rewrite FP. auto.
    simpl. auto.
  (* Pfield *)
  - inv WT.
    (** TODO: make it a lemma: prove p's dominators are init *)
    assert (PDOM: dominators_is_init own p = true).
    { eapply dominators_is_init_field. eauto. }             
    assert (IHWF: forall (fid : ident) (ty : type),
               ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. intro. eapply WF. simpl. destruct (path_of_place p) eqn: POP. simpl in *.
      eapply in_app. eauto. }
    exploit IHp; eauto.        
    intros (b & ofs & fp & PFP & WTFP).
    (* exploit field_type_implies_field_tag; eauto. intros (tag & FTAG & TAGN). *)
    (** Inversion of WTFP *)
    rewrite WT2 in WTFP. inv WTFP; simpl in *; try congruence.
    rewrite WT3 in CO. inv CO.
    exploit WT0; eauto. intros (ffp & fofs & INFPL & FOFS& WTFP1).
    exists b, (ofs+fofs), ffp. repeat apply conj; auto.
    (* get_loc_footprint_map *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl.  rewrite INFPL. auto.        
  (* Pderef *)
  - inv WT.
    unfold dominators_is_init in POWN. simpl in POWN.
    eapply andb_true_iff in POWN. destruct POWN as (PINIT & POWN).
    assert (IHWF: forall (fid : ident) (ty : type),
               ~ In (ph_downcast ty fid) (snd (path_of_place p))).
    { intros. intro. eapply WF. simpl. destruct (path_of_place p) eqn: POP. simpl in *.
      eapply in_app. eauto. }
    exploit IHp; eauto.
    intros (b & ofs & fp & PFP & WTFP).
    exploit MM; eauto. 
    intros (BM & FULL).
    destruct (typeof_place p) eqn: PTY; simpl in WT2; try congruence.
    inv WT2.
    (* fp must not be fp_emp that is why we need mmatch *)
    inv WTFP; inv BM; simpl in *; try congruence.
    exists b0, 0, fp0. repeat apply conj.    
    (* get_loc_footprint_map *)
    destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app. eauto.
    simpl. auto.
    (* wt_footprint *)
    simpl. auto.
  (* Pdowncast: impossible *)
  - exfalso. eapply WF.
    simpl. destruct (path_of_place p) eqn: POP. simpl. eapply in_app.
    right. econstructor. eauto.
Qed.

(** IMPRTANT TODO: use this lemma to prove eval_place_sound. Think
about the field type in wt_footprint is correct or not? *)
Lemma get_wt_place_footprint_wt: forall p fpm e b ofs m fp,
    wf_env fpm ce m e ->
    wt_place e ce p ->
    get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp) ->
    wt_footprint ce (typeof_place p) fp.
Proof.
  intros until fp. intros WFENV WTP GFP.
  destruct (path_of_place p) eqn: POP.
  simpl in *.
  destruct (e!i) eqn: A; try congruence.
  destruct p0.
  destruct (fpm ! i) eqn: B; try congruence.
  exploit wf_env_footprint; eauto. intros (fp1 & C1 & C2).
  rewrite B in C1. inv C1.
  eapply get_loc_footprint_eq in GFP.
  eapply get_wt_footprint_wt; eauto.
  eapply wt_place_wt_path; eauto.
Qed.

End COMP_ENV.

(** wf_env is preserved if we do not change the stacks of the memory *)
Lemma wf_env_unchanged: forall e ce m1 m2 fpm,
    wf_env fpm ce m1 e ->
    Mem.unchanged_on (fun b _ => In b (footprint_of_env e)) m1 m2 ->
    wf_env fpm ce m2 e.
Proof.
  intros until fpm. intros WFENV UNC.
  econstructor.
  - intros. eapply wf_env_footprint; eauto.
  - intros.
    generalize (wf_env_freeable _ _ _ _ WFENV id b ty H); eauto.
    intros (PERM & VAL).
    split; auto.
    red. intros. erewrite <- Mem.unchanged_on_perm; eauto.
    simpl. eapply in_footprint_of_env; eauto.
    eapply Mem.unchanged_on_support; eauto.    
Qed.

(* Sometimes we change the contents in the stacks but the permission
is unchanged (most of the time) *)
Lemma wf_env_perm_unchanged: forall e ce m1 m2 fpm,
    (forall b1 ofs1 k p, Mem.perm m1 b1 ofs1 k p <-> Mem.perm m2 b1 ofs1 k p) ->
    Mem.sup_include (Mem.support m1) (Mem.support m2) ->
    wf_env fpm ce m1 e ->
    wf_env fpm ce m2 e.
Proof.
  intros until fpm. intros UNC SUP WFENV.
  econstructor.
  - intros. eapply wf_env_footprint; eauto.
  - intros.
    split.
    red. intros. eapply UNC; eauto.
    eapply wf_env_freeable; eauto.
    eapply SUP.
    eapply wf_env_freeable; eauto.
Qed.


(* used to prove the premise of [mmatch_move_place_sound] *)
Lemma must_movable_exists_shallow_prefix: forall ce init uninit universe p
    (MOVE: must_movable ce init uninit universe p = true),
    Paths.Exists (fun p1 : Paths.elt => is_shallow_prefix (valid_owner p) p1 = true) (PathsMap.get (local_of_place p) universe).
Proof.
  intros ce. pattern ce. apply well_founded_ind with (R:= removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold must_movable, must_movable_fix in *.
  erewrite unroll_Fix in *.
  destruct (typeof_place p) eqn: PTY; simpl in *; try congruence.
  Ltac solve_exists p:= exists p; split; [eapply must_init_in_universe; eauto| eapply valid_owner_is_shallow_prefix].
  1-4 : solve_exists p.    
  - destruct must_init eqn: INIT; try congruence.
    destruct is_full eqn: FULL in MOVE; try congruence; solve_exists p.
  - destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
    destruct (must_init init uninit universe p) eqn: INIT.
    + destruct is_full eqn: FULL; try congruence.
      solve_exists p.
    + destruct (co_members co) eqn: MEMBS; try congruence.
      simpl in MOVE. destruct m.
      eapply andb_true_iff in MOVE as (M1 & M2).
      replace t with (typeof_place (Pfield p id t)) in M1 by auto.
      exploit IH; eauto.
      eapply PTree_removeR; eauto.
      intros (p2 & IN & SHA).
      exists p2. simpl in *. split; auto.
      eapply is_shallow_prefix_trans. 2: eauto. 
      eapply is_shallow_prefix_trans. eapply valid_owner_is_shallow_prefix.
      eapply is_shallow_prefix_field.
  - destruct (ce1 ! i) eqn: CO; try congruence.
    eapply andb_true_iff in MOVE as (M1 & M2).
    solve_exists p.
Qed.
      
Lemma maxv:
  Ptrofs.max_unsigned = 18446744073709551615.
Proof.
  unfold Ptrofs.max_unsigned. unfold Ptrofs.modulus. unfold Ptrofs.wordsize.
  unfold two_power_nat. unfold Wordsize_Ptrofs.wordsize.
  replace Archi.ptr64 with true by reflexivity. reflexivity.
Qed.

(* if a place passes must_movable checking, then the location of this
place is sem_wt_loc. wt_footprint here is used to make sure that the
footprint of this place (obtained by get_loc_footprint_map) has the
same structure as its type, which is used to prevent dynamic footprint
splitting! *)

Lemma movable_place_sem_wt: forall ce ce1 fp fpm m e own p b ofs init uninit universe
    (MM: mmatch fpm ce m e own)
    (POWN: must_movable ce1 init uninit universe p = true)
    (SOUND: sound_own own init uninit universe)
    (PFP: get_loc_footprint_map e (path_of_place p) fpm = Some (b, ofs, fp))
    (WTFP: wt_footprint ce (typeof_place p) fp)
    (EXTEND: ce_extends ce1 ce),
    sem_wt_loc ce m fp b ofs.
Proof.
  intros ce. intros c. pattern c. apply well_founded_ind with (R := removeR).
  eapply well_founded_removeR.
  intros ce1 IH. intros. unfold must_movable, must_movable_fix in *.
  erewrite unroll_Fix in *.
  destruct (typeof_place p) eqn: PTY; simpl in POWN; try congruence.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  - exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & FULL). inv WTFP; inv BM.
    econstructor; eauto.
  (* Tbox *)
  - destruct (must_init init uninit universe p) eqn: INIT; try congruence.
    destruct (is_full universe p) eqn: PFULL.
    (* p is full: it must be sem_wt *)
    eapply MM. eauto. eapply must_init_sound; eauto.
    erewrite <- is_full_same; eauto. eapply sound_own_universe. eauto.    
    (* adhoc generalization *)
    clear PFULL.
    generalize dependent p. generalize dependent b.
    generalize dependent fp. generalize dependent ofs.
    induction t; intros; simpl in *; try congruence.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p Tunit)) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). inv WT; inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    (* The same as Tunit case (just copying) *)
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tint i s))) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). inv WT; inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tlong s))) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). inv WT; inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    + exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. eauto.
      econstructor; eauto.
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tfloat f))) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). inv WT; inv BM1; simpl in *; try congruence.
      econstructor; simpl; eauto.
    (* Induction case *)
    + destruct (must_init init uninit universe (Pderef p (Tbox t))) eqn: INIT2; try congruence.
      destruct (is_full universe (Pderef p (Tbox t))) eqn: PFULL1.
      (* case1: deref p is full: it must be sem_wt *)
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor; eauto. econstructor; eauto.
      destruct (path_of_place p) eqn: POP.
      eapply MM. instantiate (1 := Pderef p (Tbox t)).
      simpl. rewrite POP. erewrite get_loc_footprint_map_app. eauto.
      eauto. simpl. auto.
      eapply must_init_sound; eauto.
      erewrite <- is_full_same; eauto. eapply sound_own_universe. eauto.
      (* case2: deref p is not full *)      
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & FULL). inv WTFP; inv BM; simpl in *; try congruence.
      econstructor. simpl. eauto. eauto.
      econstructor; eauto.
      eapply IHt; eauto. simpl. auto.
      (* get_loc_footprint_map *)
      simpl. destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_app; eauto.
    (* Tstruct *)
    + destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
      (* fp is not empty *)
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). inv WTFP; inv BM; simpl in *; try congruence.
      clear GCO. generalize P as P1. intros P1. eapply EXTEND in P. rewrite P in *.
      econstructor. simpl. eauto. eauto. econstructor; eauto.
      (* two cases *)
      destruct (must_init init uninit universe (Pderef p (Tstruct l id1))) eqn: INIT1; try congruence.
      (** Case1 check that p is full so we can derive sem_wt_loc by mmatch *)
      destruct (is_full universe (Pderef p (Tstruct l id1))) eqn: FULL; try congruence.
      (* construct footprint of Pderef p to use mmatch *)
      assert (PFP1: get_loc_footprint_map e (path_of_place (Pderef p (Tstruct l id1))) fpm = Some (b0, 0, fp0)).
      { simpl. destruct (path_of_place p) eqn: POP.
        eapply get_loc_footprint_map_app; eauto. }
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM1 & WTLOC1). simpl in *.
      (* prove sem_wt_loc: first eliminate Tbox *)
      eapply WTLOC1.
      erewrite <- is_full_same. eauto. eapply sound_own_universe; eauto.
      (** Case2: p is not in the universe *)
      destruct (co_members co) eqn: COMEMBS; try congruence.
      rewrite <- COMEMBS in *. clear COMEMBS.
      erewrite forallb_forall in POWN.
      (** Get the structure of fp by wt_footprint *)
      inv WT; simpl in *; try congruence. 
      eapply sem_wt_struct. intros.
      (* replace fty with (typeof_place (Pfield (Pderef p (Tstruct l id1)) fid fty)) by auto. *)
      (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
      exploit WT2; eauto. intros (fty & A & B & C).
      eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
      eapply PTree_removeR. eauto. eauto.
      assert (INMEM: In (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield (Pderef p (Tstruct l id1)) fid fty, fty)) (co_members co))).
      { exploit field_type_implies_field_tag. eapply A.
        intros (tag & FTAG & NTH). eapply list_nth_z_in in NTH.
        eapply in_map_iff. exists (Member_plain fid fty).
        rewrite  P in CO. inv CO.
        split; eauto. }
      generalize (POWN (Pfield (Pderef p (Tstruct l id1)) fid fty, fty) INMEM).
      instantiate (1 := Pfield (Pderef p (Tstruct l id1)) fid fty).
      eauto.
      auto.
      (* get_loc_footprint_map *)
      simpl. destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_app; eauto.
      eapply get_loc_footprint_map_app; eauto.
      simpl. eauto. simpl. rewrite H. auto.
      (* wt_footprint *)
      simpl. auto.
      (* ce_extend *)
      eapply ce_extends_remove. auto.
    (* Tvariant *)
    + destruct (ce1 ! i) eqn: CO; try congruence.      
      eapply andb_true_iff in POWN. destruct POWN as (INIT1 & FULL).
      exploit MM. eauto. eapply must_init_sound; eauto.
      intros (BM & WTLOC). (* rewrite PTY in *. *)
      inv WTFP; inv BM; simpl in *; try congruence.
      eapply EXTEND in CO. rewrite CO in *.      
      econstructor; eauto. 
      econstructor; eauto.
      cut (is_full own.(own_universe) (Pderef p (Tvariant l i)) = true).
      eapply MM.
      simpl. destruct (path_of_place p) eqn: POP.
      eapply get_loc_footprint_map_app; eauto.      
      eapply must_init_sound; eauto.
      erewrite <- is_full_same; eauto.
      eapply sound_own_universe; eauto.      
  (* Tstruct *)
  - destruct (get_composite ce1 i) eqn: GCO; try congruence. subst.
    destruct (must_init init uninit universe p) eqn: INIT; try congruence.
    (** Case1 check that p is full so we can derive sem_wt_loc by mmatch *)
    destruct (is_full universe p) eqn: FULL; try congruence.
    exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & WTLOC).  eapply WTLOC.
    erewrite <- is_full_same. eauto. eapply sound_own_universe; eauto.    
    (** Case2: p is not in the universe *)
    destruct (co_members co) eqn: COMEMBS; try congruence.
    rewrite <- COMEMBS in *. clear COMEMBS.
    erewrite forallb_forall in POWN.
    (** Get the structure of fp by wt_footprint *)
    inv WTFP; simpl in *; try congruence.
    eapply sem_wt_struct. intros.
    (* strengthen the wt_footprint of struct to require that all
    element in fpl is in the composite members *)
    exploit WT2; eauto. intros (fty & A & B & C).
    eapply IH. instantiate (1 := (PTree.remove id1 ce1)).
    eapply PTree_removeR. eauto. eauto.
    assert (INMEM: In (Pfield p fid fty, fty) (map (fun '(Member_plain fid fty) => (Pfield p fid fty, fty)) (co_members co))).
    { exploit field_type_implies_field_tag. eapply A.
      intros (tag & FTAG & NTH). eapply list_nth_z_in in NTH.
      eapply in_map_iff. exists (Member_plain fid fty).
      generalize P as P1. intros. eapply EXTEND in P1.
      rewrite P1 in CO. inv CO.
      split; eauto. }    
    generalize (POWN (Pfield p fid fty, fty) INMEM).
    instantiate (1 := (Pfield p fid fty)). eauto.    
    auto.
    (* place_footprint *)
    simpl. destruct (path_of_place p) eqn: POP.
    eapply get_loc_footprint_map_app; eauto.
    simpl. rewrite H. auto.
    (* wt_footprint *)
    simpl. auto.
    (* ce_extend *)
    eapply ce_extends_remove; eauto.
  (* Tvariant *)
  - destruct (ce1 ! i) eqn: CO; try congruence.
    eapply andb_true_iff in POWN. destruct POWN as (INIT & FULL).
    exploit MM. eauto. eapply must_init_sound; eauto.
    intros (BM & WTLOC). 
    inv WTFP; inv BM; simpl in *; try congruence. 
    eapply WTLOC.
    erewrite <- is_full_same; eauto.
    eapply sound_own_universe; eauto.
Qed.

(* properties of place_dominator *)

Lemma place_dominator_local: forall p p',
    place_dominator p = Some p' ->
    local_of_place p = local_of_place p'.
Proof.
  induction p; simpl; auto.
  congruence.
  intros. inv H. auto.
  intros. inv H. auto.
Qed.

Lemma place_dominator_strict_prefix: forall p p',
    place_dominator p = Some p' ->
    is_prefix_strict p' p = true.
Proof.
  induction p; simpl; auto; try congruence; intros.
  - exploit IHp. eauto. intros A. eapply is_prefix_strict_trans. eauto.
    eapply is_prefix_strict_field.
  - inv H. eapply is_prefix_strict_deref.
  - inv H. eapply is_prefix_strict_downcast.
Qed.


(** Definition of shallow prefix path *)


(* Inductive not_shallow_prefix_paths: list path -> Prop := *)
(* | not_shallow_prefix_paths1: forall phs, *)
(*     not_shallow_prefix_paths (ph_deref :: phs) *)
(* | not_shallow_prefix_paths2: forall phs ph, *)
(*     not_shallow_prefix_paths phs -> *)
(*     not_shallow_prefix_paths (ph :: phs). *)

Definition not_shallow_prefix_paths (phl: list path) : Prop :=
  In ph_deref phl.

(* Set [vfp] to the path [phl] of [fp1], if [phl] is not shallow paths
which means that if contains dereference, then [fp2] is still
bmatch *)
Lemma bmatch_set_not_shallow_paths: forall phl m b ofs fp1 fp2 vfp ce,
    bmatch ce m b ofs fp1 ->
    set_footprint phl vfp fp1 = Some fp2 ->
    not_shallow_prefix_paths phl ->
    bmatch ce m b ofs fp2.
Proof.
  induction phl; intros; simpl in *; try congruence.
  red in H1. inv H1.
  red in H1. inv H1.
  - destruct fp1; try congruence.
    destruct (set_footprint phl vfp fp1); try congruence. inv H0.
    inv H. econstructor; eauto.
  - destruct a; try congruence.
    + destruct fp1; try congruence.
      destruct (set_footprint phl vfp fp1) eqn: A; try congruence.      
      inv H0. inv H. econstructor; eauto.
    + destruct fp1; try congruence.
      destruct (find_fields fid fpl) eqn: A; try congruence.
      repeat destruct p.
      exploit find_fields_some. eapply A.
      intros (B1 & B2). subst.
      destruct (set_footprint phl vfp f) eqn: B; try congruence.
      inv H0. inv H. econstructor.
      intros.            
      exploit find_fields_some. eauto. intros (C1 & C2).
      destruct (ident_eq fid i).
      * subst. erewrite find_fields_set_spec in H; eauto.
        inv H. destruct peq; try congruence.
        eapply IHphl; eauto.
      * eapply FMATCH.
        eapply find_fields_different_field with (fid:=fid) (id:= i); eauto. 
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct (ident_eq i id) in H0; try congruence; subst.
      destruct (list_eq_dec ident_eq l orgs) in H0; try congruence; subst.
      destruct (ident_eq fid fid0) in H0; try congruence; subst.
      destruct (set_footprint phl vfp fp1) eqn: S in H0; try congruence.
      inv H0. inv H.
      econstructor; eauto.
Qed.
      
Lemma not_nil_app_end {A: Type} : forall (l: list A),
    l <> nil ->
    exists a l', l = l' ++ [a].
Proof.
  induction l. congruence.
  intros. destruct l.
  exists a, nil. eauto.
  exploit IHl; eauto. congruence.
  intros (a1 & l' & A1). exists a1, (a::l'). rewrite A1. auto.
Qed.


Lemma paths_contain_is_shallow: forall l1 l2,
    paths_contain l1 (l1 ++ l2) = true ->
    is_shallow_prefix_paths l2 = true ->
    paths_shallow_contain l1 (l1 ++ l2) = true.
Proof.
  induction l1; intros; simpl in *. auto.
  destruct path_eq; try congruence. eauto.
Qed.
  
Lemma path_of_not_shallow_prefix: forall p1 p2 l1 l2 id
    (NSHA: is_shallow_prefix p1 p2 = false)
    (* is_prefix here is used to avoid syntatic well-typedness *)
    (PRE: is_prefix p1 p2 = true)
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2)),
    not_shallow_prefix_paths l2.
Proof.
  intros.
  unfold is_shallow_prefix in NSHA. 
  unfold is_prefix in PRE.
  rewrite POP1 in *. rewrite POP2 in *.
  destruct ident_eq in *; try congruence; simpl in *.
  destruct (is_shallow_prefix_paths l2) eqn: A.
  exploit paths_contain_is_shallow; eauto. congruence.
  eapply negb_false_iff in A.
  destruct in_dec in A; simpl in *; try congruence. auto.
Qed.

Lemma paths_shallow_contain_true_implies: forall l1 l2,
    paths_shallow_contain l1 (l1 ++ l2) = true ->
    is_shallow_prefix_paths l2 = true.
Proof.
  induction l1; intros; simpl in *. auto.
  destruct path_eq; try congruence; auto.
Qed.

Lemma is_shallow_prefix_paths_true: forall l,
    is_shallow_prefix_paths l = true ->
    ~ not_shallow_prefix_paths l.
Proof.
  intros. unfold is_shallow_prefix_paths in H.
  eapply negb_true_iff in H. destruct in_dec in H; simpl in *; auto.
  congruence.
Qed.

(* If the path contains no deref, then p1 must be shallow prefix of
p2. This lemma is unused *)
Lemma path_of_not_shallow_prefix_reverse: forall p1 p2 l1 l2 id
    (NSHA: not_shallow_prefix_paths l2)
    (POP1: path_of_place p1 = (id, l1))
    (POP2: path_of_place p2 = (id, l1 ++ l2)),
    is_shallow_prefix p1 p2 = false.
Proof.
  intros.
  unfold is_shallow_prefix.
  rewrite POP1. rewrite POP2.
  eapply andb_false_iff. right.
  destruct (paths_shallow_contain l1 (l1 ++ l2)) eqn: A; auto.
  exploit paths_shallow_contain_true_implies. eauto. intros.
  exploit is_shallow_prefix_paths_true.  eauto. auto. contradiction.
Qed.  

(** Setting wt_footprint to footprint map  *)

Lemma name_footprints_set_field_same: forall fpl fid fp,
    name_footprints (set_field fid fp fpl) = name_footprints fpl.
Proof.
  induction fpl; simpl; eauto; intros.
  destruct a. destruct p. destruct ident_eq; subst.
  simpl. f_equal. simpl. f_equal. eauto.
Qed.

Lemma name_footprints_update_same: forall fpl,
    name_footprints (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl) = name_footprints fpl.
Proof.
  induction fpl; simpl; eauto; intros.
  destruct a. destruct p. 
  f_equal. eauto. 
Qed.


Lemma set_wt_footprint: forall phl ty1 vty ce (WTPH: wt_path ce ty1 phl vty) fp1 vfp fp2,
    set_footprint phl vfp fp1 = Some fp2 ->
    wt_footprint ce ty1 fp1 ->
    (* we should not say that vfp is well typed in ce! *)
    wt_footprint ce vty vfp ->
    wt_footprint ce ty1 fp2.
Proof.
  induction 1; intros until fp2; intros SET WTFP1 WTFP2.
  - simpl in *. inv SET. auto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1.
    inv B1.
    eapply IHWTPH. eauto. eauto.
    econstructor. simpl in WP2. inv WP2. auto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    destruct (find_fields fid fpl) eqn: FIND; try congruence.
    repeat destruct p. inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1.
    inv B1.
    eapply IHWTPH. eauto. eauto.
    (* prove wt_footprint of the struct footprint *)
    econstructor; eauto.
    + intros. rewrite WP2 in CO. inv CO.
      exploit WT1. eauto.
      intros (ffp & fofs & C1 & C2 & C3).
      erewrite find_fields_set_spec with (fofs:= fofs) (ffp:= ffp); eauto.
      destruct peq.
      * subst. exists vfp, fofs.
        repeat apply conj; auto.
        rewrite WP3 in H. inv H. auto.
      * eauto. 
    + intros. rewrite WP2 in CO. inv CO.
      exploit find_fields_some. eapply FIND. intros (C1 & C2). subst.
      destruct (peq i fid0).
      * subst.
        exploit WT2.  eauto. intros (fty & F1 & F2 & F3).
        erewrite find_fields_set_spec with (fofs:= z) (ffp:= f) in H; eauto.
        inv H. destruct peq; try congruence. eauto.
      * exploit find_fields_different_field. eauto. eauto.
        intros FIND1.
        exploit WT2.  eauto. intros (fty & F1 & F2 & F3).
        eauto.
    + erewrite name_footprints_set_field_same; eauto.
  - exploit set_footprint_app_inv; eauto.
    intros (fp3 & vfp1 & A1 & A2 & A3).
    simpl in A2. destruct fp3; try congruence.
    destruct ident_eq in A2; try congruence.
    destruct list_eq_dec in A2; try congruence.
    destruct ident_eq in A2; try congruence.
    inv A2.
    exploit get_wt_footprint_wt; eauto. intros B1. 
    inv B1. eapply IHWTPH. eauto. auto.
    econstructor; eauto.
    rewrite WP2 in CO. inv CO. rewrite WP3 in FTY. inv FTY.
    auto.
Qed.

(** IMPORTANT TODO: wf_env remain valid if we set a wt_footprint *)
Lemma wf_env_set_wt_footprint: forall p fpm1 fpm2 ce e m fp
    (WFENV: wf_env fpm1 ce m e)
    (* how to know the type match the type located in the path of the
    footprint map? *)
    (WTFP: wt_footprint ce (typeof_place p) fp)
    (WTP: wt_place e ce p)
    (SET: set_footprint_map (path_of_place p) fp fpm1 = Some fpm2),
    wf_env fpm2 ce m e.
Proof.
  intros.
  destruct (path_of_place p) eqn: POP.
  unfold set_footprint_map in SET.
  destruct (fpm1 ! i) eqn: A1; try congruence.
  destruct (set_footprint l fp f) eqn: A2; try congruence.
  inv SET.
  constructor. intros. exploit wf_env_footprint; eauto.
  intros (fp1 & B1 & B2).
  rewrite PTree.gsspec.
  destruct peq; subst.
  - exists f0.
    rewrite A1 in B1. inv B1.
    split; auto.
    (* prove wt_footprint after setting *)
    eapply set_wt_footprint.
    eapply wt_place_wt_path; eauto.
    eauto. auto. auto.
  - eauto.
  - intros. eapply wf_env_freeable; eauto.
Qed.


Lemma find_fields_clear_footprint1: forall fpl fid fofs ffp,
    find_fields fid fpl = Some (fid, fofs, ffp) ->
    find_fields fid
      (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl) =
      Some (fid, fofs, (clear_footprint_rec ffp)).
Proof.
  induction fpl; simpl; intros; try congruence.
  destruct a. destruct p.
  destruct ident_eq.
  - subst. inv H. auto.
  - eauto.
Qed.

Lemma find_fields_clear_footprint2: forall fpl fid fofs ffp,
    find_fields fid
      (map (fun '(fid, fofs, ffp) => (fid, fofs, clear_footprint_rec ffp)) fpl) =
      Some (fid, fofs, ffp) ->
    exists ffp', find_fields fid fpl = Some (fid, fofs, ffp')
            /\ ffp = clear_footprint_rec ffp'.
Proof.
  induction fpl; simpl; intros; try congruence.
  destruct a. destruct p.
  destruct ident_eq.
  - subst. inv H. eauto.
  - eauto.
Qed.

Lemma wt_footprint_clear: forall fp ce ty,
    wt_footprint ce ty fp ->
    wt_footprint ce ty (clear_footprint_rec fp).
Proof.
  induction fp using strong_footprint_ind; intros; simpl; auto.
  - inv H. econstructor. destruct ty; simpl in *; try congruence.
  - inv H. econstructor. congruence.
  - inv H0. econstructor; eauto.
    + intros. exploit WT1; eauto.
      intros (ffp & fofs & A1 & A2 & A3).
      exists (clear_footprint_rec ffp), fofs. repeat apply conj; auto.
      * eapply find_fields_clear_footprint1. eauto.
      * exploit find_fields_some; eauto.
        intros (B1 & B2).
        eapply H; eauto.
    + intros.
      exploit find_fields_clear_footprint2; eauto.
      intros (ffp' & A1 & A2). subst.
      exploit WT2; eauto.
      intros (fty & B1 & B2 & B3).
      exists fty. repeat apply conj; auto.
      exploit find_fields_some; eauto.
      intros (C1 & C2).
      eapply H; eauto.
    + intros. 
      erewrite name_footprints_update_same; eauto.
  - inv H. econstructor. congruence.
Qed.    
      
(* clear some footprint does not affect wf_env *)
Lemma wf_env_clear_footprint: forall fpm1 fpm2 ce e id m phl,
    wf_env fpm1 ce m e ->
    clear_footprint_map e (id, phl) fpm1 = Some fpm2 ->
    wf_env fpm2 ce m e.
Proof.
  intros until phl. intros WF CLR.
  unfold clear_footprint_map in CLR.
  destruct (get_loc_footprint_map e (id, phl) fpm1) eqn: A; try congruence.
  repeat destruct p.
  unfold set_footprint_map in CLR.
  destruct (fpm1 ! id) eqn: A1; try congruence.
  destruct (set_footprint phl (clear_footprint_rec f) f0) eqn: A2; try congruence.
  inv CLR.
  constructor. intros. exploit wf_env_footprint; eauto.
  intros (fp1 & B1 & B2).
  rewrite PTree.gsspec.
  destruct peq; subst.
  - exists f1.
    rewrite A1 in B1. inv B1.
    split; auto. 
    (* prove wt_footprint after setting *)
    unfold get_loc_footprint_map in A. rewrite H in A. rewrite A1 in A.
    exploit get_wt_footprint_exists_wt; eauto.
    eapply get_loc_footprint_eq; eauto.
    intros (ty1 & T1 & T2).  
    eapply set_wt_footprint; eauto.
    (* wt_footprint remain if clear the footprint *)
    eapply wt_footprint_clear. auto.
  - eauto.
  - intros. eapply wf_env_freeable; eauto.
Qed.

(* Properties of sem_wt_loc *)

Lemma sem_wt_subpath: forall phl fp1 b1 ofs1 b2 ofs2 fp2 ce m,
    sem_wt_loc ce m fp1 b1 ofs1 ->
    get_loc_footprint phl fp1 b1 ofs1 = Some (b2, ofs2, fp2) ->
    sem_wt_loc ce m fp2 b2 ofs2.
Proof.
  induction phl; intros.
  - simpl in H0. inv H0. auto.
  - simpl in H0. destruct a.
    + destruct fp1; try congruence.
      inv H. inv WT. eapply IHphl; eauto.
    + destruct fp1; try congruence.
      inv H.
      destruct (find_fields fid fpl) eqn: FIND; try congruence.
      repeat destruct p.
      exploit find_fields_some; eauto. intros (A & B). subst.      
      exploit FWT; eauto. 
    + destruct fp1; try congruence.
      destruct ty; try congruence.
      destruct ident_eq in H0; subst; try congruence.
      destruct list_eq_dec in H0; subst; try congruence.
      destruct ident_eq in H0; subst; try congruence.
      inv H. eauto.
Qed.

Lemma sem_wt_loc_implies_bmatch: forall fp m b ofs ce,
    sem_wt_loc ce m fp b ofs ->
    bmatch ce m b ofs fp.
Proof.
  induction fp using strong_footprint_ind; intros.
  - inv H.
  - inv H. econstructor; eauto.
  - inv H. inv WT.
    econstructor; eauto.
  - inv H0. econstructor.
    intros.
    exploit find_fields_some; eauto. intros (A & B).
    exploit FWT; eauto.
  - inv H. econstructor; eauto.
Qed.

Lemma move_check_exprlist_result: forall al init uninit universe ce init1 uninit1,
    move_check_exprlist ce init uninit universe al = Some (init1, uninit1) ->
    init1 = remove_place_list (moved_place_list al) init /\
      uninit1 = add_place_list universe (moved_place_list al) uninit.
Proof.
  induction al; intros until uninit1; intros A; simpl in *; try (inv A; eauto).
  unfold move_check_expr in H0.
  destruct (move_check_expr' ce init uninit universe a); try congruence.
  destruct (moved_place a) eqn: MP; simpl; eauto.
Qed.  


(** Translation validation of wf_own_env in function entry *)

Ltac simpl_paths_mem :=
  let IN := fresh "IN" in
  match goal with
  | [H: Paths.mem ?p (PathsMap.get ?id ?s) = true |- _ ] =>
      eapply Paths.mem_2 in H; unfold PathsMap.get in H;
      destruct (s!id) eqn: IN;
      [|unfold LPaths.bot in H; exfalso; eapply Paths.empty_1; eauto]
  end.

Lemma check_universe_wf_own_env: forall le ce universe init uninit P1 P2
    (CHECK: check_universe_wf le ce universe = OK tt)
    (EMPTY: forall id paths, init ! id = Some paths ->
                        Paths.Empty paths),
    wf_own_env le ce (mkown init uninit universe P1 P2).
Proof.
  intros.
  unfold check_universe_wf in CHECK.
  destruct (check_universe_wf' ce le universe) eqn: CK; try congruence.
  unfold check_universe_wf' in CK. erewrite PTree_Properties.for_all_correct in CK.
  econstructor; simpl; intros; try (unfold in_universe in *; simpl in *).
  - unfold is_init in H.
    eapply Paths.mem_2 in H. unfold PathsMap.get in H. simpl in H.
    destruct (@PTree.get LPaths.t (local_of_place p) init) eqn: A.
    exploit EMPTY; eauto. unfold LPaths.bot in H.
    generalize (Paths.empty_1 H). contradiction.
  - repeat simpl_paths_mem.
    exploit CK. eauto.
    intros CK1. rewrite !andb_true_iff in CK1.
    destruct CK1 as ((((C0 & C1) & C2) & C3) & C4).
    unfold check_universe_dominator_complete in C0.
    eapply Paths.for_all_2 in C0.    
    unfold PathsMap.get. erewrite is_prefix_same_local.
    2: eapply place_dominators_are_prefixes; eauto.
    rewrite IN.
    eapply C0 in H.
    erewrite forallb_forall in H.
    eapply H in H0. auto.
    red. solve_proper.    
  - repeat simpl_paths_mem.
    destruct (path_of_place p1) eqn: POP1.
    destruct (path_of_place p2) eqn: POP2.
    rewrite local_of_paths_of_place in *.
    rewrite POP1 in *. rewrite POP2 in *. simpl in *.
    destruct (ident_eq i i0).
    + subst. exploit CK. eauto.
      intros CK1. rewrite !andb_true_iff in CK1.
      destruct CK1 as ((((C0 & C1) & C2) & C3) & C4).
      rewrite IN0 in IN. inv IN.
      unfold check_universe_shallow in C1. 
      eapply Paths.for_all_2 in C1.
      eapply negb_true_iff.
      eapply C1 in H. eapply Paths.for_all_2 in H.
      assert (IN3: Paths.In p2 (Paths.filter (fun p2 : Paths.elt => is_prefix_strict p1 p2) t)).
      { eapply Paths.filter_3. red. solve_proper. auto. auto. }
      eapply H in IN3. auto.
      red. solve_proper. red.
      unfold Proper. reflexivity.
    + unfold is_shallow_prefix.
      rewrite POP1. rewrite POP2. destruct ident_eq; try congruence.
      simpl. auto.
  - simpl_paths_mem.
    destruct (path_of_place p) eqn: POP. simpl in *.
    exploit CK. eauto.
    intros CK1. rewrite !andb_true_iff in CK1.
    destruct CK1 as ((((C0 & C1) & C2) & C3) & C4).
    unfold check_universe_no_downcast in C2.
    eapply Paths.for_all_2 in C2.
    eapply C2 in H.
    erewrite forallb_forall in H. rewrite POP in *.
    simpl in H. intro.
    eapply H in H0. congruence.
    red. unfold Proper. reflexivity.
  - simpl_paths_mem.
    destruct (path_of_place p) eqn: POP. simpl in *.
    exploit CK. eauto.
    intros CK1. rewrite !andb_true_iff in CK1.
    destruct CK1 as ((((C0 & C1) & C2) & C3) & C4).
    unfold check_universe_own_type in C3.
    eapply Paths.for_all_2 in C3.
    assert (IN1: Paths.In p (Paths.filter (fun p : Paths.elt => negb (is_full_internal t p)) t)).
    { eapply Paths.filter_3. red. solve_proper.
      auto. unfold is_full in H0.
      unfold PathsMap.get in H0.
      rewrite IN in H0.  eapply negb_true_iff; eauto. }
    eapply C3 in IN1. destruct (typeof_place p); try congruence. eauto.
    red. unfold Proper. reflexivity.
  - simpl_paths_mem.
    destruct (path_of_place p) eqn: POP.
    exploit CK. eauto.
    intros CK1. rewrite !andb_true_iff in CK1.
    destruct CK1 as ((((C0 & C1) & C2) & C3) & C4).
    unfold check_universe_wt_place in C4.
    eapply Paths.for_all_2 in C4.
    eapply C4 in H.    
    destruct (type_check_place ce le p) eqn: TCK; try congruence.
    destruct u.
    eapply type_check_place_sound; eauto.
    red. unfold Proper. reflexivity.
Qed.

Require Import Permutation.                                    

Section SEQ.

Variable sem_data: mem -> footprint -> block -> Z -> Prop.

Section LINKOFS.
  
Variable link_ofs: Z.

(* The footprint structure is specific to the data type *)
Inductive sem_Seq (m: mem) : flat_footprint -> list footprint -> block -> Z -> block -> Z -> Prop :=
| sem_Seq_nil: forall b1 ofs1 b2 ofs2
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b2 (Ptrofs.repr ofs2))),
    sem_Seq m nil nil b1 ofs1 b2 ofs2
| sem_Seq_cons: forall b1 ofs1 b2 ofs2 b l fp fpl
    (LOAD: Mem.load Mptr m b1 ofs1 = Some (Vptr b (Ptrofs.repr link_ofs)))
    (DATA: sem_data m fp b 0)
    (NEXT: sem_Seq m l fpl b link_ofs b2 ofs2),
    (** TODO: add permission properties *)    
    sem_Seq m (b :: l) (fp :: fpl) b1 ofs1 b2 ofs2.

Definition Seq (m: mem) (l: flat_footprint) (fpl: list footprint) (b1: block) (ofs1: Z) (b2: block) (ofs2: Z) : Prop :=
  sem_Seq m l fpl b1 ofs1 b2 ofs2.

Definition Cycle (m: mem) (l: flat_footprint) (fpl: list footprint) (b: block) (ofs: Z) : Prop :=
  Seq m l fpl b ofs b ofs.

End LINKOFS.

Section DLINKOFS.

Variable link_ofs: Z.

(* semantics type of doubly-linked list exposed to other module *)
Definition DCycle (m: mem) (bs: flat_footprint) (b: block) (ofs: Z) : Prop :=
  exists l fpl, Permutation bs (l ++ flat_map footprint_flat fpl)
           /\ Cycle link_ofs m l fpl b ofs
           /\ Cycle (link_ofs + size_chunk Mptr) m (rev l) (rev fpl) b (ofs + size_chunk Mptr).

End DLINKOFS.
               
End SEQ.
                                    
