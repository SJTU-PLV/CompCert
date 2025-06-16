Require Import Coqlib Maps Errors Integers Floats.
Require Import AST Linking Memory.
Require Import Ctypes Cop Csyntax Clight.
Require Import Rusttypes Rustlight RustIR.
Require Import Clightgen.

Import ListNotations.

(* monadInv for bind_res and bind and bind_res *)

(** ** Properties of the monad *)

Remark bind_inversion_sym:
  forall (A B: Type) (f: mon A) (g: A -> mon B) (y: B) (z1 z3: generator),
  bind f g z1 = Res y z3 ->
  exists x, exists z2, 
  f z1 = Res x z2 /\ g x z2 = Res y z3.
Proof.
  intros until z3. unfold bind. destruct (f z1).
  congruence.
  caseEq (g a g'); intros; inv H0.
  econstructor; econstructor; eauto.
Qed.

Remark bind2_inversion_sym:
  forall (A B C: Type) (f: mon (A*B)) (g: A -> B -> mon C) (y: C
    ) (z1 z3: generator),
  bind2 f g z1 = Res y z3 ->
  exists x1, exists x2, exists z2,
  f z1 = Res (x1,x2) z2 /\ g x1 x2 z2 = Res y z3.
Proof.
  unfold bind2. intros.
  exploit bind_inversion_sym; eauto.
  intros [[x1 x2] [z2]]. 
  exists x1; exists x2; exists z2; auto.
Qed.

Ltac monadInv_sym1 H :=
  match type of H with
  | (Res _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _) =>
      inversion H
  | (bind ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let z := fresh "z" in (                           
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion_sym _ _ F G X Z Z' H) as [x [z [EQ1 EQ2]]];
      clear H;
      try (monadInv_sym1 EQ2)))))
   | (bind2 ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion_sym _ _ _ F G X Z Z' H) as [x [y [z [EQ1 EQ2]]]];
      clear H;
      try (monadInv_sym1 EQ2))))))
  | (match ?X with left _ => _ | right _ => error _ end = OK _) =>
      destruct X; [try (monadInv_sym1 H) | discriminate]
  end.

Ltac monadInv_sym H :=
  match type of H with
  | (@ret _ _ _ = Res _ _) => monadInv_sym1 H
  | (@error _ _ _ = Res _ _) => monadInv_sym1 H
  | (bind ?F ?G ?Z = Res ?X ?Z') => monadInv_sym1 H
  | (bind2 ?F ?G ?Z = Res ?X ?Z') => monadInv_sym1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  | (?F _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_sym1 H
  end.


Remark bind_inversion_comb:
  forall (A B: Type) (f: Errors.res A) (g: A -> mon B) (y: B) (z1 z3: generator),
  bind_res f g z1 = Res y z3 ->
  exists x, 
  f = OK x /\ g x z1 = Res y z3.
Proof.
  intros until z3. unfold bind_res. destruct f.
  caseEq (g a z1); intros; inv H0.
  econstructor; econstructor; eauto.
  congruence.
Qed.

Remark bind2_inversion_comb:
  forall (A B C: Type) (f: Errors.res (A*B)) (g: A -> B -> mon C) (y: C
    ) (z1 z3: generator),
  bind_res2 f g z1 = Res y z3 ->
  exists x1, exists x2,
  f = OK (x1,x2) /\ g x1 x2 z1 = Res y z3.
Proof.
  unfold bind_res2. intros.
  exploit bind_inversion_comb; eauto.
  intros [[x1 x2]]. 
  exists x1; exists x2;  auto.
Qed.

Ltac monadInv_comb1 H :=
  match type of H with
  | (Res _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@ret _ _ _ = Res _ _) =>
      inversion H; clear H; try subst
  | (@error _ _ _ = Res _ _) =>
      inversion H
  | (bind_res ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let z := fresh "z" in (                           
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion_comb _ _ F G X Z Z' H) as [x [EQ1 EQ2]];
      clear H;
      try (monadInv_comb1 EQ2)))))
  | (bind_res2 ?F ?G ?Z = Res ?X ?Z') =>
      let x := fresh "x" in (
      let y := fresh "y" in (
      let z := fresh "z" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion_comb _ _ _ F G X Z Z' H) as [x [y [EQ1 EQ2]]];
      clear H;
      try (monadInv_comb1 EQ2))))))
  | (match ?X with left _ => _ | right _ => error _ end = OK _) =>
      destruct X; [try (monadInv_comb1 H) | discriminate]
  end.

Ltac monadInv_comb H :=
  match type of H with
  | (@ret _ _ _ = Res _ _) => monadInv_comb1 H
  | (@error _ _ _ = Res _ _) => monadInv_comb1 H
  | (bind_res ?F ?G ?Z = Res ?X ?Z') => monadInv_comb1 H
  | (bind_res2 ?F ?G ?Z = Res ?X ?Z') => monadInv_comb1 H
  | (?F _ _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  | (?F _ = Res _ _) =>
      ((progress simpl in H) || unfold F in H); monadInv_comb1 H
  end.


Record tr_composite_env (ce: composite_env) (tce: Ctypes.composite_env) : Prop :=
  { tr_composite_some:
    forall id co,
    ce!id = Some co ->        
         match co.(co_sv) with
         | Struct =>
             exists tco, tce!id = Some tco /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             map transl_composite_member co.(co_members) = tco.(Ctypes.co_members) /\
             (* co.(co_attr) = tco.(Ctypes.co_attr) /\ *)
             co.(co_sizeof) = tco.(Ctypes.co_sizeof) /\
             co.(co_alignof) = tco.(Ctypes.co_alignof)
             (* co.(co_rank) = tco.(Ctypes.co_rank) *)
         | TaggedUnion =>
             exists tco union_id tag_fid union_fid union,
             let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
             let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in
             let m := (map transl_composite_member co.(co_members)) in
             tce!id = Some tco /\ tce!union_id = Some union /\
             tco.(Ctypes.co_su) = Ctypes.Struct /\
             tco.(Ctypes.co_members) = [tag_member; union_member] /\
             tag_fid <> union_fid /\
             tco.(Ctypes.co_sizeof) = co.(co_sizeof) /\
             tco.(Ctypes.co_alignof) = co.(co_alignof) /\
             (* tco.(Ctypes.co_rank) = co.(co_rank) /\ *)
             union.(Ctypes.co_su) = Union /\
             union.(Ctypes.co_members) = m /\
             (* To specify *)
             union.(Ctypes.co_sizeof) = align (Ctypes.sizeof_composite tce Union m) (Ctypes.alignof_composite tce m) /\
             union.(Ctypes.co_alignof) = (Ctypes.alignof_composite tce m)
             (* union.(Ctypes.co_rank) = Ctypes.rank_members tce m *)
         end;

    tr_composite_consistent: composite_env_consistent ce }    
.

Lemma alignof_match: forall ce tce ty,
    tr_composite_env ce tce ->
    complete_type ce ty = true ->
    Ctypes.alignof tce (to_ctype ty) = alignof ce ty.
Proof.
  induction ty; simpl; auto; intros TR COM; unfold align_attr;simpl;
    destruct (ce!i) eqn: CO; try congruence.
  apply TR in CO.
  destruct (co_sv c).
  destruct CO as (tco & A & B & C & D & E). rewrite A. auto.
  destruct CO as (? & ? & ? & ? & ? & A & B & C & D & E & F & G & H & I).
  rewrite A. auto.
  apply TR in CO.
  destruct (co_sv c).
  destruct CO as (tco & A & B & C & D & E). rewrite A. auto.
  destruct CO as (? & ? & ? & ? & ? & A & B & C & D & E & F & G & H & I).
  rewrite A. auto.
Qed.

  
Lemma sizeof_match: forall ce tce ty,
    tr_composite_env ce tce ->
    complete_type ce ty = true ->
    Ctypes.sizeof tce (to_ctype ty) = sizeof ce ty.
Proof.
  (* induction ty; simpl; auto; intros TR COM; unfold align_attr;simpl;
    try destruct (ce!i) eqn: CO; try congruence.
  rewrite IHty; auto. *)
  Admitted.
  (* apply TR in COM.
  destruct (co_sv c).
  destruct CO as (tco & A & B & C & D & E). rewrite A. auto.
  destruct CO as (? & ? & ? & ? & ? & A & B & C & D & E & F & G & H & I).
  rewrite A. auto.
  apply TR in CO.
  destruct (co_sv c).
  destruct CO as (tco & A & B & C & D & E). rewrite A. auto.
  destruct CO as (? & ? & ? & ? & ? & A & B & C & D & E & F & G & H & I).
  rewrite A. auto.
Qed. *)


Lemma field_offset_rec_match: forall ce tce membs fid ofs start,
    tr_composite_env ce tce ->    
    complete_members ce membs = true ->
    field_offset_rec ce fid membs start = OK ofs ->
    Ctypes.field_offset_rec tce fid (map transl_composite_member membs) start = OK (ofs, Full).
Proof.
  (* induction membs; simpl; intros fid ofs start TR FOFS.
  congruence.
  inv FOFS.
  destruct a. simpl in *.
  eapply andb_true_iff in H0. destruct H0.
  destruct (ident_eq fid id). subst.
  unfold Ctypes.bitalignof, bitalignof in *. 
  erewrite alignof_match; eauto. intros. inv H1. auto.
  intros FOFS.
  eapply IHmembs; eauto. 
  unfold Ctypes.bitalignof, Ctypes.bitsizeof.
  erewrite alignof_match; eauto. erewrite sizeof_match; eauto.
Qed. *)
Admitted.

Lemma field_offset_match: forall ce tce membs fid ofs,
    tr_composite_env ce tce ->
    complete_members ce membs = true ->
    field_offset ce fid membs = OK ofs ->
    Ctypes.field_offset tce fid (map transl_composite_member membs) = OK (ofs, Full).
Proof.
  unfold Ctypes.field_offset, field_offset.
  intros.
  eapply field_offset_rec_match with (start := 0); eauto.
Qed.

Lemma struct_field_offset_match: forall ce tce id fid co ofs,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    co.(co_sv) = Struct ->
    field_offset ce fid co.(co_members) = OK ofs ->
    exists tco, tce ! id = Some tco /\
           Ctypes.field_offset tce fid tco.(Ctypes.co_members) = OK (ofs, Full).
Proof.
  intros until ofs.
  intros TR CO STRUCT FOFS.
  generalize (tr_composite_some _ _ TR id co CO).
  rewrite STRUCT. intros (tco & A & B & C & D).
  exists tco. split; auto.
  rewrite <- C.
  eapply field_offset_match; eauto.
  (* prove complete members *)
  eapply tr_composite_consistent; eauto.
Qed.

Lemma alignof_composite_match: forall ce tce ms,
    tr_composite_env ce tce ->
    complete_members ce ms = true ->
    Ctypes.alignof_composite tce (map transl_composite_member ms) = alignof_composite' ce ms.
Proof.
  induction ms; intros; simpl; auto.
  rewrite IHms. destruct a. simpl.
  erewrite alignof_match. eauto.
  auto.
  simpl in H0. eapply andb_true_iff in H0. destruct H0. auto.
  auto.
  simpl in H0. eapply andb_true_iff in H0. destruct H0. auto.
Qed.

Lemma union_field_offset_eq: forall ms tce fid,
    existsb (fun m : member => ident_eq fid (name_member m)) ms = true ->
    union_field_offset tce fid (map transl_composite_member ms) = OK (0, Full).
Proof.
  induction ms; simpl. congruence.
  intros tce fid. destruct a. simpl.
  destruct (ident_eq fid id); simpl.
  intros. rewrite align_same. f_equal.
  unfold Ctypes.bitalignof.
  generalize  (Ctypes.alignof_pos tce (to_ctype t)). lia.
  eapply Z.divide_0_r.
  eauto.
Qed.

Lemma variant_field_offset_match: forall ce tce co id,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    co.(co_sv) = TaggedUnion ->
    exists tco union_id tag_fid union_fid union,
      let tag_member := Ctypes.Member_plain tag_fid Ctypes.type_int32s in
      let union_member := Ctypes.Member_plain union_fid (Tunion union_id noattr) in
      tce!id = Some tco /\ tce!union_id = Some union /\
        tco.(Ctypes.co_members) = [tag_member; union_member] /\
        tag_fid <> union_fid /\
        (forall fid ofs, variant_field_offset ce fid co.(co_members) = OK ofs ->
                    exists ofs1 ofs2,
                      Ctypes.field_offset tce union_fid tco.(Ctypes.co_members) = OK (ofs1, Full)
                      /\ union_field_offset tce fid union.(Ctypes.co_members) = OK (ofs2, Full)
                      /\ ofs = ofs1 + ofs2)
.
Proof.
  intros until id. intros TR CO ENUM.
  generalize (tr_composite_some _ _ TR id co CO). rewrite ENUM.
  intros (tco & union_id & tag_fid & union_fid & union & A & B & C & D & E & F & G & H & I & J & K).
  exists tco, union_id, tag_fid, union_fid, union. simpl.
  repeat split;auto.
  unfold variant_field_offset.
  intros fid ofs.
  destruct (existsb (fun m : member => ident_eq fid (name_member m)) (co_members co)) eqn: EB; try congruence.
  intros. inv H0.
  exists (align 32 (alignof_composite' ce (co_members co) * 8) / 8), 0.
  split; try split.
  - rewrite D. unfold Ctypes.field_offset.
    simpl.
    destruct (ident_eq union_fid tag_fid). subst. contradiction.
    destruct (ident_eq union_fid union_fid); try contradiction.
    unfold Ctypes.bitalignof. simpl.
    rewrite B. unfold Ctypes.align_attr. simpl.
    rewrite K. 
    erewrite alignof_composite_match. unfold Ctypes.bitsizeof.
    simpl. eauto.
    auto.
    eapply tr_composite_consistent; eauto.
  - rewrite I. eapply union_field_offset_eq. auto.
  - lia.
Qed.    

Lemma sizeof_struct_match_aux: forall ce tce ms m n,
    tr_composite_env ce tce ->
    complete_type ce (type_member m) = true ->
    complete_members ce ms = true ->
    bitsizeof_struct ce (next_field ce n m) ms =
  Ctypes.bitsizeof_struct tce (Ctypes.next_field tce n (transl_composite_member m))
    (map transl_composite_member ms).
Proof.
Admitted.
  (* unfold next_field, Ctypes.next_field.
  induction ms; destruct m; simpl; auto.
  intros TR COM COMS.
  unfold bitalignof, Ctypes.bitalignof.
  erewrite alignof_match.
  unfold bitsizeof, Ctypes.bitsizeof.
  erewrite sizeof_match. eauto.
  1-4 : auto.
  intros n TR COM COMS.
  exploit (IHms a (align n (bitalignof ce t) + bitsizeof ce t)).
  auto.
  eapply andb_true_iff. erewrite andb_comm. eauto.
  eapply andb_true_iff.  eauto.
  destruct a. simpl.
  intros. rewrite H.
  eapply andb_true_iff in COMS. destruct COMS.
  unfold bitalignof, Ctypes.bitalignof.
  repeat erewrite alignof_match.
  unfold bitsizeof, Ctypes.bitsizeof.
  repeat erewrite sizeof_match. eauto.
  simpl in *.
  1-8 : eauto.
Qed. *)

Lemma sizeof_struct_match: forall ce tce ms,
    tr_composite_env ce tce ->
    complete_members ce ms = true ->
    sizeof_struct ce ms = Ctypes.sizeof_struct tce (map transl_composite_member ms).
Proof.
  destruct ms; simpl; auto.
  intros TR COM.
  unfold sizeof_struct, Ctypes.sizeof_struct in *.
  f_equal. simpl.
  eapply sizeof_struct_match_aux; auto.
  eapply andb_true_iff. erewrite andb_comm. eauto.
  eapply andb_true_iff.  eauto.
Qed.  
  
    
Lemma sizeof_variant_match: forall ce tce ms,
    tr_composite_env ce tce ->
    complete_members ce ms = true ->
    sizeof_variant' ce ms = Ctypes.sizeof_union tce (map transl_composite_member ms).
Proof.
Admitted.
  (* destruct ms; simpl; auto.
  intros TR COM.
  f_equal.
  destruct m; simpl.
  symmetry. eapply sizeof_match. auto.
  eapply andb_true_iff. erewrite andb_comm. eauto.
  eapply andb_true_iff in COM. destruct COM.
  induction ms.
  simpl. auto.
  simpl. f_equal.
  destruct a; simpl.
  symmetry. eapply sizeof_match. auto.
  simpl in * .
  eapply andb_true_iff. erewrite andb_comm. eauto.
  eapply IHms.
  eapply andb_true_iff.  eauto.
Qed. *)

  
Lemma complete_type_match: forall ce tce m,
      tr_composite_env ce tce ->
      complete_type ce (type_member m) = true ->
      Ctypes.complete_type tce (Ctypes.type_member (transl_composite_member m)) = true.
Proof.
  destruct m; simpl;intros TR TCOMP.
  induction t;simpl in *; auto; try destruct (ce ! i) eqn: CO; try congruence.
  eapply TR in CO. destruct (co_sv c).
  destruct CO. intuition. rewrite H0. auto.
  destruct CO as (a & b & d & e & f & g & h). rewrite g. auto.
  eapply TR in CO. destruct (co_sv c).
  destruct CO. intuition. rewrite H0. auto.
  destruct CO as (a & b & d & e & f & g & h). rewrite g. auto.
Qed.

Lemma complete_members_match: forall ce tce ms,
    tr_composite_env ce tce ->
    complete_members ce ms = true ->
    Ctypes.complete_members tce (map transl_composite_member ms) = true.
Proof.
  induction ms; simpl; auto.
  intros A B.
  destruct (complete_type ce (type_member a)) eqn: COMP.
  exploit IHms; eauto. intros C.
  rewrite C. erewrite complete_type_match; eauto.
  rewrite andb_false_l in B.
  congruence.
Qed.
  
  
(* prove a general one *)
Lemma transl_composites_meet_spec_aux: forall co_defs tco_defs ce0 ce1 tce0 tce1,
    (* (CON: composite_env_consistent ce0) *)
    (* (TCON: Ctypes.composite_env_consistent tce0), *)
    transl_composites co_defs = Some tco_defs ->
    add_composite_definitions ce0 co_defs = OK ce1 ->
    Ctypes.add_composite_definitions tce0 tco_defs = OK tce1 ->
    tr_composite_env ce0 tce0 ->
    tr_composite_env ce1 tce1.
Proof.
  induction co_defs as [|d1 defs]; simpl;
    intros tco_defs ce0 ce1 tce0 tce1 TRANSL CE1 TCE1 MENV.
  unfold transl_composites in *. simpl in *.
  unfold Ctypes.link_composite_defs in *. simpl in *. inv TRANSL.
  simpl in *. inv CE1. inv TCE1. auto.

  generalize MENV. intros (MENVCE0 & CON).
  unfold transl_composites in *. simpl in *.


  set (f := (fun elt : option (Ctypes.composite_definition * option Ctypes.composite_definition)
             => match elt with
               | Some _ => true
               | None => false
               end)) in *.
  
  
  destruct (transl_composite_def d1) eqn: TD1.
  2: { rewrite andb_false_l in TRANSL. congruence. }
  rewrite andb_true_l in TRANSL.
  destruct (forallb f (map transl_composite_def defs)) eqn: TDS; try congruence.
  destruct p as (tco, opt_utco).
  inv TRANSL.

  destruct d1 as (id1, sv1, ms1, orgs1, rels1).
  monadInv CE1.
  simpl in TD1.
  destruct( create_union_idents id1) as ((uid, tfid), ufid).

  (* case: sv1 = Struct *)
  destruct sv1.
  - inv TD1. simpl in *.
    monadInv TCE1.
    
    unfold composite_of_def in EQ.
    destruct (ce0 ! id1) eqn: VALID1; try congruence.
    destruct (complete_members ce0 ms1) eqn: COMPLETE1; try congruence.
    unfold Ctypes.composite_of_def in EQ1.        
    destruct (tce0 ! id1) eqn: TVALID1; try congruence.
    destruct (Ctypes.complete_members tce0 (map transl_composite_member ms1)) eqn: TCOMPLETE1; try congruence.
    assert (EXTEND: forall (id : positive) (co : composite), ce0 ! id = Some co -> (PTree.set id1 x ce0) ! id = Some co).
    { intros. destruct (ident_eq id1 id).
      subst. rewrite VALID1 in H. congruence.
      rewrite PTree.gso; auto. }    
    assert (TEXTEND: forall (id : positive) (co : Ctypes.composite), tce0 ! id = Some co -> (PTree.set id1 x0 tce0) ! id = Some co).
    { intros. destruct (ident_eq id1 id).
      subst. rewrite TVALID1 in H. congruence.
      rewrite PTree.gso; auto. }

    assert (MENV1: tr_composite_env (PTree.set id1 x ce0) (PTree.set id1 x0 tce0)).
    { constructor.
      intros id co GET.
      inv EQ. simpl in *.
      destruct (peq id id1). 
      + rewrite PTree.gsspec in GET.
        subst.
 rewrite peq_true in GET. inv GET.
        exists x0. split. apply PTree.gss.
        inv EQ1. simpl. repeat split; auto.
        (* sizeof *)
        f_equal. eapply sizeof_struct_match;auto.
        f_equal. symmetry. eapply alignof_composite_match; auto.
        f_equal. symmetry. eapply alignof_composite_match; auto.

      + rewrite PTree.gso in *; auto.
        eapply MENV in GET as GET1.
        destruct (co_sv co); auto.
        destruct GET1 as (tco & union_id & tag_fid & union_fid & uco & GETTCO & GETUCO & A).
        exists tco, union_id, tag_fid, union_fid, uco. simpl.
        destruct (ident_eq id1 union_id); subst.
        rewrite TVALID1 in GETUCO. congruence.
        rewrite PTree.gso; auto.
        
        erewrite sizeof_union_stable.
        erewrite Ctypes.alignof_composite_stable.
        eauto. eauto. 
        eapply complete_members_match. eauto.
        eapply co_consistent_complete; eauto.
        eauto.
        eapply complete_members_match. eauto.
        eapply co_consistent_complete; eauto.

      + red. intros id co CO.
      eapply composite_consistent_stable. eapply EXTEND.
      rewrite PTree.gsspec in *.
      destruct (peq id id1). inv CO.
      inv EQ. econstructor; simpl; auto.            
      eapply CON; eauto. 
    }

    (* use I.H. *)
    eapply IHdefs. 4: eapply MENV1.
    (* composite_env_consistent (PTree.set id1 x ce0) *)
    (* Ctypes.composite_env_consistent (PTree.set id1 x0 tce0) *)
    (* { red. intros id tco TCO. *)
    (*   eapply Ctypes.composite_consistent_stable. eapply TEXTEND. *)
    (*   rewrite PTree.gsspec in *. *)
    (*   destruct (peq id id1). inv TCO. *)
    (*   inv EQ1. econstructor; simpl; auto.             *)
    (*   eapply TCON; eauto. } *)
    eauto. auto. auto.

  (* sv = Taggedunion *)
  - destruct (ident_eq tfid ufid) as [|TFIDNEQ]; try congruence.
    subst.
    inv TD1. simpl in TCE1.
    monadInv TCE1.

    unfold composite_of_def in EQ.
    destruct (ce0 ! id1) eqn: VALID1; try congruence.
    destruct (complete_members ce0 ms1) eqn: COMPLETE1; try congruence.
    unfold Ctypes.composite_of_def in EQ1.        
    destruct (tce0 ! uid) eqn: TVALID1; try congruence.
    destruct (Ctypes.complete_members tce0 (map transl_composite_member ms1)) eqn: TCOMPLETE1; try congruence.
    unfold Ctypes.composite_of_def in EQ3.
    rewrite PTree.gsspec in EQ3.
    destruct (peq id1 uid) as [|ID1UIDNEQ]; try congruence.    
    destruct (tce0 ! id1) eqn: TVALID2; try congruence.
    destruct (Ctypes.complete_members (PTree.set uid x0 tce0)
            [Ctypes.Member_plain tfid Ctypes.type_int32s;
            Ctypes.Member_plain ufid (Tunion uid noattr)]) eqn: TCOMPLETE2; try congruence.
    assert (EXTEND: forall (id : positive) (co : composite), ce0 ! id = Some co -> (PTree.set id1 x ce0) ! id = Some co).
    { intros. destruct (ident_eq id1 id).
      subst. rewrite VALID1 in H. congruence.
      rewrite PTree.gso; auto. }
    assert (TEXTEND: forall (id : positive) (co : Ctypes.composite), tce0 ! id = Some co -> (PTree.set uid x0 tce0) ! id = Some co).
    { intros.
      (*  destruct (ident_eq id1 id). *)
      (* subst.  rewrite TVALID2 in H. congruence. *)
      (* rewrite PTree.gso; auto. *)
      destruct (ident_eq uid id); try congruence.
      rewrite PTree.gso; auto. }
    assert (TEXTEND1: forall (id : positive) (co : Ctypes.composite), (PTree.set uid x0 tce0) ! id = Some co -> (PTree.set id1 x1 (PTree.set uid x0 tce0)) ! id = Some co).
    { intros. destruct (ident_eq id1 id).
      subst. destruct (ident_eq uid id); try congruence.
      rewrite PTree.gso in H. 
      rewrite TVALID2 in H. congruence.
      auto. rewrite PTree.gso; auto. }
    
    assert (MENV1: tr_composite_env (PTree.set id1 x ce0) (PTree.set id1 x1 (PTree.set uid x0 tce0))).
    { constructor.
      intros id co GET.
      destruct (peq id id1). 
      + rewrite PTree.gsspec in GET.
        subst.
        rewrite peq_true in GET. inv GET.
        inv EQ. simpl.
        exists x1, uid, tfid, ufid, x0.
        split. apply PTree.gss.
        split. rewrite PTree.gso;auto. apply PTree.gss.
        split. inv EQ3. auto.
        split. inv EQ3. simpl. auto.
        split. auto.
        split. inv EQ3. simpl. clear EQ4 EQ0.
        (* FIXME: lots of unstructed code *)
        { f_equal. unfold Ctypes.sizeof_struct, Ctypes.bitsizeof_struct.
          simpl. unfold sizeof_variant.
          replace ((Ctypes.bitsizeof (PTree.set uid x0 tce0) Ctypes.type_int32s)) with 32.
          f_equal.
          unfold Ctypes.bitalignof, Ctypes.bitsizeof.
          simpl. rewrite PTree.gss.
          unfold align_attr. simpl.          
          replace (Ctypes.co_alignof x0) with (alignof_composite' ce0 ms1).
          replace (Ctypes.co_sizeof x0) with (align (sizeof_variant' ce0 ms1) (alignof_composite' ce0 ms1)).
          auto.
          inv EQ1. simpl. unfold align_attr. simpl.
          erewrite sizeof_variant_match.
          erewrite alignof_composite_match; eauto.
          auto. auto.
          inv EQ1. simpl. unfold align_attr. simpl.
          erewrite alignof_composite_match; eauto.
          unfold Ctypes.bitsizeof. simpl. auto.
          unfold align_attr. simpl. rewrite PTree.gss.
          inv EQ1. simpl. unfold align_attr. simpl.
          erewrite alignof_composite_match; eauto.          
          assert (Z.max 4 (Z.max (alignof_composite' ce0 ms1) 1) = Z.max 4 (alignof_composite' ce0 ms1)).
          rewrite Z.max_assoc. rewrite Z.max_l. auto.
          erewrite  Z.max_le_iff. left. lia.
          rewrite H. auto. }

        split. inv EQ3. simpl. clear EQ4 EQ0.
        rewrite PTree.gss.
        inv EQ1. simpl. unfold align_attr. simpl.
        erewrite alignof_composite_match; eauto.
        assert (Z.max 4 (Z.max (alignof_composite' ce0 ms1) 1) = Z.max 4 (alignof_composite' ce0 ms1)).
        rewrite Z.max_assoc. rewrite Z.max_l. auto.
        erewrite  Z.max_le_iff. left. lia.
        rewrite H. auto.

        split. inv EQ1. auto.
        split. inv EQ1. auto.
        split.
        rewrite sizeof_union_stable with (env:= tce0); auto.
        rewrite Ctypes.alignof_composite_stable with (env:= tce0); auto.
        inv EQ1. auto.
        rewrite Ctypes.alignof_composite_stable with (env:= tce0); auto.
        inv EQ1. auto.

      + rewrite PTree.gso in *; auto.
        destruct (ident_eq uid id). subst.
        (* id <> uid *)
        { eapply MENV in GET as GET1.
          rewrite TVALID1 in GET1. destruct co_sv.
          destruct GET1 as (tco & A & B). congruence.
          destruct GET1 as (tco & union_id & tag_fid & union_fid & uco & GETTCO & GETUCO & A).
          congruence. }
        rewrite PTree.gso in *; auto.
          
        eapply MENV in GET as GET1.
        destruct (co_sv co); auto.
        destruct GET1 as (tco & union_id & tag_fid & union_fid & uco & GETTCO & GETUCO & A & B & C & D & E & F & G & H & I).
        exists tco, union_id, tag_fid, union_fid, uco. simpl.
        destruct (ident_eq id1 union_id); subst.
        rewrite TVALID2 in GETUCO. congruence.
        rewrite PTree.gso; auto.
        destruct (ident_eq uid union_id); subst.
        rewrite TVALID1 in GETUCO. congruence.
        rewrite PTree.gso; auto.
        
        repeat split; auto.
        erewrite sizeof_union_stable.
        erewrite Ctypes.alignof_composite_stable.
        eauto. eauto. 
        eapply complete_members_match. eauto.
        eapply co_consistent_complete; eauto.
        eauto.
        eapply complete_members_match. eauto.
        eapply co_consistent_complete; eauto.
        erewrite Ctypes.alignof_composite_stable.
        eauto. eauto. 
        eapply complete_members_match. eauto.
        eapply co_consistent_complete; eauto.

      (* composite_env_consistent (PTree.set id1 x ce0) *)
      + red. intros id co CO.
      eapply composite_consistent_stable. eapply EXTEND.
      rewrite PTree.gsspec in *.
      destruct (peq id id1). inv CO.
      inv EQ. econstructor; simpl; auto.            
      eapply CON; eauto.
    }

    (* use I.H. *)
    eapply IHdefs. 4: eapply MENV1.
    (* composite_env_consistent (PTree.set id1 x ce0) *)
    (* Ctypes.composite_env_consistent (PTree.set id1 x1 (PTree.set uid x0 tce0)) *)
    (* { red. intros id tco TCO. *)
    (*   do 2 rewrite PTree.gsspec in *. *)
    (*   assert (TCON1: Ctypes.composite_consistent (PTree.set uid x0 tce0) x1). *)
    (*   { inv EQ3. econstructor; simpl; auto. } *)
    (*   eapply Ctypes.composite_consistent_stable. eapply TEXTEND1. *)
    (*   destruct (peq id id1). inv TCO. auto. *)
    (*   assert (TCON2: Ctypes.composite_consistent tce0 x0). *)
    (*   { inv EQ1. econstructor; simpl; auto. } *)
    (*   eapply Ctypes.composite_consistent_stable. eapply TEXTEND. *)
    (*   destruct (peq id uid). inv TCO. auto. *)
      
    (*   eapply TCON; eauto. } *)
    eauto. auto. auto.
Qed.
    
Lemma transl_composites_meet_spec: forall co_defs tco_defs ce tce,
    transl_composites co_defs = Some tco_defs ->
    build_composite_env co_defs = OK ce ->
    Ctypes.build_composite_env tco_defs = OK tce ->
    tr_composite_env ce tce.
Proof.
  unfold build_composite_env, Ctypes.build_composite_env.
  intros. eapply transl_composites_meet_spec_aux; eauto.
  constructor.
  intros.
  rewrite PTree.gempty in *. congruence.
  red. intros.
  rewrite PTree.gempty in *. congruence.
Qed.
  
  
Section SPEC.

Variable ce: composite_env.
Variable tce: Ctypes.composite_env.
Variable dropm: PTree.t ident.
Variable glues: PTree.t Clight.function.

Definition tr_trivial_meet_spec (s : statement) : Prop :=
    match s with 
    | Sbox _ _ 
    | Scall _ _ _
    | Sdrop _ 
    | Ssequence _ _
    | Sifthenelse _ _ _
    | Sloop _ => False
    | _ => True
    end.
    
Inductive tr_stmt (locals: list ident) : statement -> Clight.statement -> Prop :=
(* We only require there **exists** a [tce] which satisfies the
tr_composite relation *)
| tr_trivial: forall s ts g,
    tr_trivial_meet_spec s ->
    transl_stmt ce tce dropm locals s g = Res ts g ->
    tr_stmt locals s ts
| tr_box: forall p e stmt lhs e' temp temp_ty deref_ty,
    temp_ty = to_ctype (typeof_place p) ->
    deref_ty = to_ctype (deref_type (typeof_place p)) ->
    transl_Sbox ce tce locals temp temp_ty deref_ty e = OK (stmt, e') ->
    place_to_cexpr ce tce p = OK lhs ->
    tr_stmt locals (Sbox p e) (Clight.Ssequence stmt (Clight.Sassign lhs e'))
| tr_call: forall p e l temp e' l' assign pe,
    expr_to_cexpr_list ce tce locals l = OK l' ->
    expr_to_cexpr ce tce locals e = OK e' ->
    place_to_cexpr ce tce p = OK pe ->
    assign = Clight.Sassign pe (Etempvar temp (to_ctype (typeof_place p))) ->
    tr_stmt locals (Scall p e l) (Clight.Ssequence (Clight.Scall (Some temp) e' l') assign)
| tr_drop: forall p set_stmt drop_stmt temp pe,
    set_stmt = Clight.Sset temp (Eaddrof pe (Tpointer (to_ctype (typeof_place p)) noattr)) ->
    place_to_cexpr ce tce p = OK pe ->
    expand_drop dropm temp (typeof_place p) = Some drop_stmt ->
    tr_stmt locals (Sdrop p) (Clight.Ssequence set_stmt drop_stmt)
| tr_seq: forall s1 s2 s1' s2',
    tr_stmt locals s1 s1' ->
    tr_stmt locals s2 s2' ->
    tr_stmt locals (Ssequence s1 s2) (Clight.Ssequence s1' s2')
| tr_ifthenelse: forall e e' s1 s2 s1' s2',
    expr_to_cexpr ce tce locals e = OK e' ->
    tr_stmt locals s1 s1' ->
    tr_stmt locals s2 s2' ->
    tr_stmt locals (Sifthenelse e s1 s2) (Clight.Sifthenelse e' s1' s2')
| tr_loop: forall s s',
      tr_stmt locals s s' ->
      tr_stmt locals (Sloop s) (Clight.Sloop s' Clight.Sskip)
.

Inductive tr_function: function -> Clight.function -> Prop :=
| tr_function_normal: forall f tf
    (* It is necessary to prove te!drop_id = None in eval_Evar_global *)
    (WFNAMES: list_disjoint (var_names (f.(fn_params) ++ f.(fn_vars))) (malloc_id :: free_id :: (map snd (PTree.elements dropm))))
    (COMPLETE: forall id ty, In (id, ty) (f.(fn_params) ++ f.(fn_vars)) -> complete_type ce ty = true),
    f.(fn_drop_glue) = None ->
    tr_stmt (var_names (f.(fn_params) ++ f.(fn_vars))) f.(fn_body) tf.(Clight.fn_body) ->
    Clight.fn_return tf = to_ctype (fn_return f) ->
    Clight.fn_callconv tf = fn_callconv f ->
    Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) ->
    Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) ->
    tr_function f tf
(* | tr_function_drop_glue1: forall f tf comp_id, *)
(*     f.(fn_drop_glue) = Some comp_id -> *)
(*     glues!comp_id = None -> *)
(*     tr_stmt f.(fn_body) tf.(Clight.fn_body) -> *)
(*     Clight.fn_return tf = to_ctype (fn_return f) -> *)
(*     Clight.fn_callconv tf = fn_callconv f -> *)
(*     Clight.fn_params tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_params) -> *)
(*     Clight.fn_vars tf = map (fun elt => (fst elt, to_ctype (snd elt))) f.(fn_vars) -> *)
(*     tr_function f tf *)
| tr_function_drop_glue: forall f comp_id glue,
    (* (WFNAMES: list_disjoint (Clight.var_names (glue.(Clight.fn_params) ++ glue.(Clight.fn_vars))) (malloc_id :: free_id :: (map snd (PTree.elements dropm)))), *)
    f.(fn_drop_glue) = Some comp_id ->
    (* We can ensure that every composite has a drop glue in Clightgen
    because if ce!id = Some co and tr_composite ce tce then
    drop_glue_for_composite does not return None *)
    glues!comp_id = Some glue ->
    tr_function f glue
.


Lemma transl_stmt_meet_spec: forall s ts locals g g',
    transl_stmt ce tce dropm locals s g = Res ts g' ->
    tr_stmt locals s ts.
Proof.
  induction s; simpl; intros until g'; intros TRANSL;
    try (monadInv_sym TRANSL); simpl; try (try (eapply tr_trivial); try(instantiate (1 := g')); simpl; auto; fail).
  - econstructor. simpl. eauto. instantiate (1:= g'). monadInv_comb TRANSL. simpl.
    rewrite EQ. rewrite EQ1. eauto.  
  - monadInv_comb TRANSL. econstructor. simpl. eauto. instantiate (1:= g'). simpl.
    rewrite EQ. rewrite EQ1. simpl. rewrite EQ0. eauto. 
  - monadInv_comb EQ0. eapply tr_box; eauto.
  - monadInv_comb EQ0. destruct expand_drop eqn: EXP in EQ2.
    monadInv_sym EQ2. eapply tr_drop; eauto. monadInv_sym EQ2.
  - monadInv_comb TRANSL. monadInv_sym EQ3.
    eapply tr_call; eauto. 
  - eapply tr_seq; eauto. 
  - monadInv_comb TRANSL. monadInv_sym EQ0.
    eapply tr_ifthenelse; eauto. 
  - eapply tr_loop. eauto. 
  - monadInv_comb TRANSL. econstructor. simpl. auto. instantiate (1:= g'). simpl.
    rewrite EQ. auto.  
    (* monadInv_sym TRANSL. econstructor. simpl. auto. instantiate (1:= g'). simpl. auto.  *)
Qed.

Lemma transl_function_meet_spec: forall f tf,
    transl_function ce tce dropm glues f = OK tf ->
    tr_function f tf.
Proof.
  unfold transl_function. intros f tf TR.
  destruct (fn_drop_glue f) eqn: DROP.
  destruct (glues ! i) eqn: GLUE.
  inv TR. eapply tr_function_drop_glue; eauto.
  congruence.
  unfold transl_function_normal in TR.
  destruct (transl_stmt) eqn: TRSTMT in TR.
  congruence.
  destruct (list_norepet_dec ident_eq (Clight.var_names (gen_trail g'))) eqn: A in TR; try congruence.
  destruct (list_disjoint_dec ident_eq (var_names (fn_params f ++ fn_vars f))
              (malloc_id :: free_id :: map snd (PTree.elements dropm))) in TR; try congruence.
  destruct (forallb (fun ty : type => complete_type ce ty) (map snd (fn_params f ++ fn_vars f))) eqn: COMPLETE; try congruence.
  inv TR.
  eapply tr_function_normal; eauto.
  (* complete type *)
  intros. eapply forallb_forall in COMPLETE; eauto. eapply in_map_iff.
  exists (id,ty). auto.  
  simpl. eapply transl_stmt_meet_spec. eauto.
Qed.

End SPEC.

Record clgen_env : Type :=
  { clgen_src_cenv: Rusttypes.composite_env;
    clgen_tgt_cenv: Ctypes.composite_env;
    clgen_dropm: PTree.t ident;
    clgen_glues: PTree.t Clight.function }.
                         
Definition build_clgen_env (p: RustIR.program) (tp: Clight.program) : clgen_env :=
  let dropm := generate_dropm p in
  let glues := generate_drops p.(prog_comp_env) tp.(Ctypes.prog_comp_env) dropm in
  Build_clgen_env p.(prog_comp_env) tp.(Ctypes.prog_comp_env) dropm glues.

Inductive tr_fundef (ctx: clgen_env): fundef -> Clight.fundef -> Prop :=
| tr_internal: forall f tf,
    tr_function ctx.(clgen_src_cenv) ctx.(clgen_tgt_cenv) ctx.(clgen_dropm) ctx.(clgen_glues) f tf ->
    tr_fundef ctx (Internal f) (Ctypes.Internal tf)
| tr_external_malloc: forall targs tres cconv orgs rels,
    tr_fundef ctx (External orgs rels EF_malloc targs tres cconv) malloc_decl
| tr_external_free: forall targs tres cconv orgs rels,
    tr_fundef ctx (External orgs rels EF_free targs tres cconv) free_decl
| tr_external: forall ef targs tres cconv orgs rels,
    ef <> EF_malloc /\ ef <> EF_free ->
    tr_fundef ctx (External orgs rels ef targs tres cconv) (Ctypes.External ef (to_ctypelist targs) (to_ctype tres) cconv).

Lemma transl_fundef_meet_spec: forall f tf ctx id,
    transl_fundef ctx.(clgen_src_cenv) ctx.(clgen_tgt_cenv) ctx.(clgen_dropm) ctx.(clgen_glues) id f = OK tf ->
    tr_fundef ctx f tf.
Proof.
  destruct f;simpl; intros.
  monadInv H. econstructor. eapply transl_function_meet_spec. auto.
  destruct e; inv H; try econstructor; auto; try (split; congruence).
Qed.

Lemma generate_dropm_inv_list_helper: forall (p:program) id gid,
  list_norepet (prog_defs_names p)->
  (generate_dropm p) ! id = Some gid 
  -> exists f, In (gid , (Gfun (Internal f))) (prog_defs p) /\ f.(fn_drop_glue)= Some id. 
Proof.
    intros.
    apply PTree_Properties.in_of_list in H0. 
    induction (prog_defs p). inv H0.
    destruct a. simpl in H0. destruct g eqn: G. destruct f eqn: F.
    destruct (fn_drop_glue f0) eqn: DROP. 
    simpl in *. rewrite DROP in H0. inv H0. inv H1. 
    exists f0. split; auto. 
    apply IHl in H1. destruct H1 as [f1 [A B]]. exists f1; auto. 
    apply IHl in H0. destruct H0 as [f1 [A B]]. exists f1. split; auto. simpl. tauto. 
    apply IHl in H0. destruct H0 as [f1 [A B]]. exists f1. split; auto. simpl. tauto.
    apply IHl in H0. destruct H0 as [f1 [A B]]. exists f1. split; auto. simpl. tauto.
  Qed. 

Lemma generate_dropm_inv: forall p id gid,
    (generate_dropm p) ! id = Some gid ->
    list_norepet (prog_defs_names p) ->
    exists f, (prog_defmap p) ! gid = Some (Gfun (Internal f)) /\ f.(fn_drop_glue) = Some id.
Proof. 
  intros. 
  exploit generate_dropm_inv_list_helper; eauto. intros (f & A & B). 
  exists f. split; auto. apply PTree_Properties.of_list_norepet; auto. 
Qed. 

(* Is it enough? *)
Lemma generate_drops_inv: forall ce tce dropm id co f,
    tr_composite_env ce tce ->
    ce ! id = Some co ->
    (generate_drops ce tce dropm) ! id = Some f ->
    let co_ty := Ctypes.Tstruct id noattr in
    let param_ty := Tpointer co_ty noattr in
    let deref_param := Clight.Ederef (Evar param_id param_ty) co_ty in
    (* list_disjoint [param_id] (malloc_id :: free_id :: (map snd (PTree.elements dropm))) /\ *)
    match co.(co_sv) with
    | Struct =>
        let stmt_list := drop_glue_for_members ce dropm deref_param co.(co_members) in
        f = {| Clight.fn_return := Ctypes.Tvoid;
              Clight.fn_callconv := cc_default;
              Clight.fn_params := [(param_id, param_ty)];
              Clight.fn_vars := [];
              fn_temps := [];
              Clight.fn_body := Clight.Ssequence Clight.Sskip stmt_list |}
    | TaggedUnion =>
        exists union_id tag_fid union_fid tco uco,
        let get_tag := Efield deref_param tag_fid Ctypes.type_int32s in
        let get_union := Efield deref_param union_fid (Tunion union_id noattr) in
        let drop_switch_branches :=
          (make_labelled_drop_stmts ce dropm get_union 0 co.(co_members)) in
        let stmt := Sswitch get_tag drop_switch_branches in
        f = {| Clight.fn_return := Ctypes.Tvoid;
              Clight.fn_callconv := cc_default;
              Clight.fn_params := [(param_id, param_ty)];
              Clight.fn_vars := [];
              fn_temps := [];
              Clight.fn_body := stmt |}
        (* compute the field offset *)
        /\ tce ! id = Some tco
        /\ tce ! union_id = Some uco
        (* tag field offset is 0 *)
        /\ Ctypes.field_offset tce tag_fid tco.(Ctypes.co_members) = OK (0, Full)        
        /\ (forall fid ofs,
              variant_field_offset ce fid co.(co_members) = OK ofs ->
              exists ofs1 ofs2,
                Ctypes.field_offset tce union_fid tco.(Ctypes.co_members) = OK (ofs1, Full)
                /\ Ctypes.union_field_offset tce fid uco.(Ctypes.co_members) = OK (ofs2, Full)
                /\ ofs = ofs1 + ofs2)
    end.
Proof.
  intros until f.
  intros TR CO.
  unfold generate_drops.
  rewrite PTree.gmap. rewrite CO.
  simpl.
  intros DROP. inv DROP.
  unfold generate_drops_acc, drop_glue_for_composite.
  generalize (tr_composite_some _ _ TR _ _ CO).
  destruct (co_sv co) eqn: SV.
  - intros (tco & A & B & C & D & E).
    eauto.
  - intros (tco & uid & tfid & ufid & uco & A & B & C & D & E & F & G & H & I & J & K).
    exists uid, tfid, ufid, tco, uco. simpl.
    rewrite A. rewrite C. rewrite D.
    repeat split; auto.
    unfold Ctypes.field_offset. simpl.
    destruct (ident_eq tfid tfid); try congruence.
    rewrite align_same. f_equal. unfold Ctypes.bitalignof. simpl. lia.
    apply Z.divide_0_r.
    (* prove variant_field_offset_match twice here!!! *)
    unfold variant_field_offset.
    intros fid ofs.
    destruct (existsb (fun m : member => ident_eq fid (name_member m)) (co_members co)) eqn: EB; try congruence.
    intros. inv H0.
    exists (align 32 (alignof_composite' ce (co_members co) * 8) / 8), 0.
    split; try split.
  + unfold Ctypes.field_offset.
    simpl.
    destruct (ident_eq ufid tfid). subst. contradiction.
    destruct (ident_eq ufid ufid); try contradiction.
    unfold Ctypes.bitalignof. simpl.
    rewrite B. unfold Ctypes.align_attr. simpl.
    rewrite K. 
    erewrite alignof_composite_match. unfold Ctypes.bitsizeof.
    simpl. eauto.
    auto.
    eapply tr_composite_consistent; eauto.
  + rewrite I. eapply union_field_offset_eq. auto.
  + lia.
Qed.


Lemma select_switch_sem_match_aux: forall ce dropm param membs tag memb idx,
    list_nth_z membs (tag - idx) = Some memb ->
    exists s, seq_of_labeled_statement (select_switch tag (make_labelled_drop_stmts ce dropm param idx membs)) = (Clight.Ssequence (Clight.Ssequence (drop_glue_for_member ce dropm param memb) Clight.Sbreak) s).
Proof.
  induction membs.
  simpl. congruence.
  simpl. intros. destruct zeq in H.
  assert (tag = idx) by lia. inv H.
  unfold select_switch. simpl. rewrite zeq_true.
  simpl. eauto.
  unfold select_switch. simpl.
  rewrite zeq_false; try lia.
  assert (Z.pred (tag - idx) = tag - (idx + 1)) by lia. rewrite H0 in *.
  exploit IHmembs.
  eauto. 
  intros (s & A).
  unfold select_switch in A.
  destruct (select_switch_case tag (make_labelled_drop_stmts ce dropm param (idx + 1) membs)) eqn: SEL.
  eauto. eauto.
Qed.
 
Lemma select_switch_sem_match: forall ce dropm param membs tag memb,
    list_nth_z membs tag = Some memb ->
    exists s, seq_of_labeled_statement (select_switch tag (make_labelled_drop_stmts ce dropm param 0 membs)) = (Clight.Ssequence (Clight.Ssequence (drop_glue_for_member ce dropm param memb) Clight.Sbreak) s).
Proof.
  intros. 
  eapply select_switch_sem_match_aux. rewrite Z.sub_0_r.
  auto.
Qed.
