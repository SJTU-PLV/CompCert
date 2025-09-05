Require Import Zwf.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.
Require Import Events.
Require Import Inject InjectFootprint Memory.
Require Import Globalenvs.

Import ListNotations.

Local Notation "a # b" := (NMap.get _ b a) (at level 1).
Local Notation "a ## b" := (ZMap.get b a) (at level 1).

(** Memory footprint defined as a function from memory locations to
bool *)

(* For now, as we want to reuse some definitions from Injectfootprint
(e.g., loc_in_reach_find) to construct memfp, we define memfp as a
pure function from block * Z to bool *)
Definition memfp : Type := block -> Z -> bool.

(* Inverse injection, which is used to construct memfp *)
Definition meminj_inv : Type := block -> Z -> option (block * Z).

Inductive valid_val (m: mem) (mfp: memfp): val -> Prop :=
| valid_val_int:
  forall i, valid_val m mfp (Vint i)
| valid_val_long:
  forall i, valid_val m mfp (Vlong i)
| valid_val_float:
  forall f, valid_val m mfp (Vfloat f)
| valid_val_single:
  forall f, valid_val m mfp (Vsingle f)
| valid_val_ptr: forall b ofs
  (VMV: Mem.perm m b (Ptrofs.unsigned ofs) Cur Readable ->
        mfp b (Ptrofs.unsigned ofs) = true),
  valid_val m mfp (Vptr b ofs)
| val_valid_val_undef:
    valid_val m mfp Vundef.

Inductive valid_val_list m (mfp: memfp): list val -> Prop:=
  | valid_val_list_nil :
      valid_val_list m mfp nil
  | valid_val_list_cons : forall v vl ,
      valid_val m mfp v -> valid_val_list m mfp vl->
      valid_val_list m mfp (v :: vl).

(* increments of memory footprint *)

Definition memfp_incr (mfp1 mfp2: memfp) : Prop :=
  forall b ofs, mfp1 b ofs = true -> mfp2 b ofs = true.

Definition memfp_separated (mfp1 mfp2: memfp) (m: mem) : Prop := 
  forall b ofs, 
    mfp1 b ofs = false ->
    mfp2 b ofs = true ->
    ~ Mem.valid_block m b.

Inductive valid_memval (m: mem) (mfp: memfp): memval -> Prop :=
  | valid_memval_byte:
      forall n, valid_memval m mfp (Byte n)
  | valid_memval_frag:
      forall v q n,
      valid_val m mfp v ->
      valid_memval m mfp (Fragment v q n)
  | valid_memval_undef:
      valid_memval m mfp Undef.

(* Unary Memory Injection --- Validity of Memory *)

Record mem_valid (mfp: memfp) (m: mem) : Prop :=
  mk_mem_valid {
      (* The footprint must have permission? As we construct the
      footprint for those have permission, this predicate is correct *)
      mv_perm: forall b ofs,
        mfp b ofs = true ->
        Mem.perm m b ofs Max Nonempty;
      (* It is not required, because mi_align is used to derive
      valid_access for the target from the source valid_access. But in
      safety proofs, it should not guaranteed by the unary injp *)
      (* mv_align: *)
      (* forall b ofs delta p chunk, *)
      (*   mfp b delta = true -> *)
      (*   Mem.range_perm m b (delta + ofs) (delta + ofs + size_chunk chunk) Max p -> *)
      (*   (align_chunk chunk | delta); *)
      (* No need to restrict the value properties! *)
      (* mv_memval: *)
      (* forall b delta, *)
      (*   mfp b delta = true -> *)
      (*   Mem.perm m b delta Cur Readable -> *)
      (*   valid_memval m mfp (ZMap.get delta (NMap.get _ b m.(Mem.mem_contents))) *)
    }.

Record memory_valid' (mfp: memfp) (m: mem) : Prop :=
  mk_memory_valid {
    mv_inj:
      mem_valid mfp m;
    mv_dom:
      forall b delta, mfp b delta = true -> Mem.valid_block m b;
      (* It cannot be proved as if source memory has unbound size (for
      example, if we have Mem.perm m b o where o is greater than
      max_unsigned), than mi_representable may also be satisfied
      (there is (Ptrofs.unsigned o) in mi_representable). Intuitively,
      mi_representable only inject in-bound permission *)
    (* mv_representable: *)
    (*   forall b ofs, *)
    (*   mfp b ofs = true -> *)
    (*   Mem.perm m b ofs Max Nonempty \/ Mem.perm m b (ofs - 1) Max Nonempty -> *)
    (*   0 <= ofs <= Ptrofs.max_unsigned; *)
  }.

Definition memory_valid := memory_valid'.

Definition fp_dom_in (mfp: memfp) s := 
  forall b o, mfp b o = true -> Mem.sup_In b s.

(** Kripke relation with memory protection for some regions of memory *)

Inductive mem_valid_world :=
  mvw (mfp: memfp) (m: mem) (HMV: memory_valid mfp m).

Inductive mvw_acc : mem_valid_world -> mem_valid_world -> Prop :=
| rsw_acc_intro: forall mfp mfp' m m' Hm Hm'
    (RO: Mem.ro_unchanged m m')
    (MAXPERM: injp_max_perm_decrease m m')
    (UNC: Mem.unchanged_on (fun b ofs => mfp b ofs = false) m m')
    (INCR: memfp_incr mfp mfp')
    (SEP: memfp_separated mfp mfp' m),
    mvw_acc (mvw mfp m Hm) (mvw mfp' m' Hm').

(** Invariant for symbol table *)

Record valid_stbl (mfp: memfp) (ge: Genv.symtbl) := {
  vge_dom:
    forall b, sup_In b (Genv.genv_sup ge) ->
         mfp b 0 = true;
}.

Inductive mem_valid_stbl : mem_valid_world -> Genv.symtbl -> Prop :=
  mem_valid_stbl_intro : forall (mfp : memfp) (m : Mem.mem)
                           (Hm : memory_valid mfp m) (se : Genv.symtbl),
      valid_stbl mfp se ->
      Mem.sup_include (Genv.genv_sup se) (Mem.support m) ->
      mem_valid_stbl (mvw mfp m Hm) se.

(** Cnstruction of inverse function *) 

(* Similar to loc_in_reach_find in Memory.v but we require that the locations with Undef/Vundef can not be in the imagre of this inverse injection *)

Definition check_memval m mv : bool :=
  match mv with
  | Undef => false
  | Byte _ => true
  | Fragment v _ _ =>
      match v with 
      | Vundef => false
      | Vptr b o =>
          (* The pointer must point to nonempty location *)
          Mem.perm_dec m b (Ptrofs.unsigned o) Max Nonempty
      | _ => true
      end
  end.

Definition check_memval_perm m1 (b1: block) (o1: Z) : bool :=
  if Mem.perm_dec m1 b1 o1 Cur Readable then
    check_memval m1 ((Mem.mem_contents m1) # b1 ## o1)
  (* Is it correct? *)
  else true.

Definition loc_out_of_reach_undef (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
    f b0 = Some(b, delta) -> 
    ~ Mem.perm m b0 (ofs - delta) Max Nonempty
    \/ check_memval_perm m b0 (ofs - delta) = false.

(* 
Section REVERSE.
  
  Variable m1 m2 : mem.
  Variable j12 : meminj.
  
  (* Variable b2: block. *)
  (* Variable o2: Z. *)
  
  Definition check_position b1 o1 (pos1: Z * Mem.memperm) : bool :=
    if (zeq o1 (fst pos1)) then 
      check_memval_perm m1 b1 o1
    else false.

  (* find (b_1,o_1) in block b_1 *)
  Definition block_find b1 b2 o2 : option (block * Z) :=
    match j12 b1 with
    |Some (b2',delta) =>
       if eq_block b2 b2' then
         let pmap1 := (Mem.mem_access m1 b1) in
         let elements := Mem.perm_elements_any (ZMap.elements pmap1) in
         match find (check_position b1 (o2 - delta)) elements with
         |Some (o1,_) => Some (b1,o2 - delta)
         |None => None
         end
       else None
    |_ => None
    end.

  (* find (b_1,o_1) in all blocks in s *)
  Fixpoint loc_in_reach_find' (b2: block) (o2: Z) (bl : list block ): option (block * Z) :=
    match bl with
    | nil => None
    | hd :: tl =>
        match block_find hd b2 o2 with
        | Some a => Some a
        | None => loc_in_reach_find' b2 o2 tl
        end
    end.

  (*specific find function, find (b_1,o_1) in sup(m_1)*)
  Definition loc_in_reach_find (b2: block) (o2: Z) :=
    loc_in_reach_find' b2 o2 (Mem.sup_list (Mem.support m1)).

  
  Lemma block_find_valid: forall b b2 o2 b1 o1,
      block_find b b2 o2 = Some (b1, o1) ->
      j12 b1 = Some (b2, o2 - o1) 
      /\ Mem.perm m1 b1 o1 Max Nonempty 
      /\ check_memval_perm m1 b1 o1 = true.
  Proof.
    intros. unfold block_find in H.
    destruct (j12 b) as [[b2' d]|] eqn:Hj; try congruence.
    destruct eq_block; try congruence.
    destruct find eqn:FIND; try congruence.
    destruct p. inv H.
    apply find_some in FIND. unfold check_position in FIND.
    destruct FIND.
    destruct zeq; try congruence. inv e. simpl in H1. inv H1.
    split. replace (o2 - (o2 - d)) with d by lia. eauto.
    split.
    unfold Mem.perm. unfold Mem.perm_order'.
    apply Mem.in_perm_any_1 in H.
    destruct H as [PERM IN].
    apply ZMap.elements_complete in IN.
    unfold NMap.get.
    rewrite IN. destruct (m Max); eauto.
    constructor.
    auto.
  Qed.
  
  Lemma loc_in_reach_find'_rec: forall s b2 o2 b1 o1,
      loc_in_reach_find' b2 o2 s = Some (b1, o1) ->
      j12 b1 = Some (b2, o2 - o1) /\ Mem.perm m1 b1 o1 Max Nonempty
      /\ check_memval_perm m1 b1 o1 = true.
  Proof.
    induction s; intros; subst; simpl; eauto.
    - inv H.
    - simpl in H. destruct block_find eqn:BLOCK. destruct p.
      inv H. eapply block_find_valid; eauto.
      eauto.
  Qed.

  Lemma loc_in_reach_find_valid: forall b2 o2 b1 o1,
      loc_in_reach_find b2 o2 = Some (b1,o1) ->
      j12 b1 = Some (b2,o2 - o1)
      /\ Mem.perm m1 b1 o1 Max Nonempty
      /\ check_memval_perm m1 b1 o1 = true.
  Proof.
    intros. unfold loc_in_reach_find in H.
    eapply loc_in_reach_find'_rec; eauto.
  Qed.

  Lemma block_find_none : forall b b2 o2 d,
      block_find b b2 o2 = None ->
      j12 b = Some (b2,d) -> 
      ~ Mem.perm m1 b (o2 - d) Max Nonempty 
      \/ check_memval_perm m1 b (o2 -d) = false.
  Proof.
    intros. unfold block_find in H.
    destruct (j12 b) as [[b2' d']|] eqn:Hj; try congruence. inv H0.
    rewrite pred_dec_true in H; eauto.
    destruct find eqn:FIND; try congruence.
    destruct p. inv H.

    assert (forall z, In z (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m1 b)))
                 -> check_position b (o2 - d) z = false).
    apply find_none. eauto.
    destruct (Mem.perm_dec m1 b (o2 - d) Max Nonempty); auto.
    unfold Mem.perm, Mem.perm_order' in p.
    destruct (((Mem.mem_access m1) # b) ## (o2 - d) Max) eqn:PERM; try contradiction.
    exploit H0. eapply Mem.in_perm_any; eauto.
    eapply ZMap.elements_correct. eauto.
    setoid_rewrite Mem.access_default. 
    intro. rewrite H1 in PERM. congruence.
    unfold check_position. simpl.
    rewrite pred_dec_true; eauto. 
  Qed.
  
  Lemma loc_in_reach_find'_none_rec : forall s b2 o2,
      loc_in_reach_find' b2 o2 s = None ->
      forall b1 d1, 
        j12 b1 = Some (b2,d1) -> 
        In b1 s -> 
        ~ Mem.perm m1 b1 (o2 - d1) Max Nonempty
        \/ check_memval_perm m1 b1 (o2 -d1) = false. 
  Proof.
    induction s; intros.
    - inv H1.
    - simpl in *. destruct block_find eqn:FIND. congruence.
      destruct H1. subst.
      eapply block_find_none; eauto. eauto.
Qed.
      

  Lemma loc_in_reach_find_none:
    forall b o, loc_in_reach_find b o = None -> 
           Mem.inject j12 m1 m2 ->
           loc_out_of_reach_undef j12 m1 b o.
  Proof.
    intros. unfold loc_in_reach_find in H.
    red. intros. eapply loc_in_reach_find'_none_rec; eauto.
    generalize H0 as INJ. intros.
    inv H0. destruct (Mem.sup_dec b0 (Mem.support m1)). apply Mem.sup_list_in. auto.
    exploit Mem.mi_freeblocks; eauto.
    intro. congruence.
  Qed.

  (* closure of loc_in_reach_find *)

  Lemma loc_in_reach_find_closure: forall b2 o2 b1 o1 b2' o2' q n,
      loc_in_reach_find b2 o2 = Some (b1, o1) ->
      Mem.perm m2 b2 o2 Cur Readable ->
      Mem.inject j12 m1 m2 ->
      (Mem.mem_contents m2) # b2 ## o2 = Fragment (Vptr b2' (Ptrofs.repr o2')) q n ->
      exists b1' o1', loc_in_reach_find b2' o2' = Some (b1', o1').
  Proof.
    intros until n. intros FIND PERMC INJ CONT.
    exploit loc_in_reach_find'_rec; eauto. intros (A1 & A2 & A3).
    (* show that the values in (b1,o1) and (b2, o2) are injected *)
    exploit Mem.mi_perm_inv; eauto. instantiate (3 := o1). 
    replace (o1 + (o2- o1)) with o2 by lia. eauto.
    intros [P|P]; try congruence.
    exploit Mem.mi_memval; eauto. eapply INJ. intros VINJ.
    replace (o1 + (o2- o1)) with o2 in * by lia. 
    rewrite CONT in VINJ. inv VINJ.
    2: { unfold check_memval_perm in A3. rewrite <- H0 in A3.
         destruct (Mem.perm_dec m1 b1 o1 Cur Readable); try congruence.
         inv A3. }
    unfold check_memval_perm in A3. rewrite <- H in A3.
    destruct (Mem.perm_dec m1 b1 o1 Cur Readable); try congruence.
    inv H1; inv A3.    
    destruct (loc_in_reach_find b2' o2') as [(b1' & o1')|] eqn: FIND'; eauto.
    exploit loc_in_reach_find_none; eauto. 

    (* exists b0, (Ptrofs.unsigned ofs1). *)
    (* Mem.mi_no_overlap *)
    (* Mem.loc_in_reach_find *)
Admitted.

End REVERSE.
*)

(* Construct the inverse function of the memory injection from the
injection *)
Definition inv_inj (j: meminj) (m: mem) : meminj_inv :=
  Mem.loc_in_reach_find m j.

Definition injected (invj: meminj_inv) b ofs : bool :=
  if invj b ofs then true else false.

Definition meminj_inv_memfp (invj: meminj_inv) : memfp :=
  fun b ofs => injected invj b ofs.


(** properties of inv_inj and meminj_inv_memfp *)

(* Lemma check_memval_perm_readable: forall m b o, *)
(*     Mem.perm m b o Cur Readable -> *)
(*     check_memval_perm m b o = true -> *)
(*     check_memval m (((Mem.mem_contents m) # b) ## o) = true. *)
(* Admitted. *)

(* Lemma check_memval_perm_false: forall m b o, *)
(*     check_memval_perm m b o = false -> *)
(*     ~ Mem.perm m b o Cur Readable \/ check_memval m ((Mem.mem_contents m) # b) ## o = false. *)
(* Admitted. *)

(* Lemma memval_inject_implies_valid: forall j m tm sb tb o2 o1, *)
(*     Mem.inject j m tm -> *)
(*     loc_in_reach_find m j tb o2 = Some (sb, o1) -> *)
(*     Mem.perm m sb o1 Cur Readable -> *)
(*     memval_inject j ((Mem.mem_contents m) # sb ## o1) ((Mem.mem_contents tm) # tb ## o2) -> *)
(*     valid_memval tm (fun b ofs => if loc_in_reach_find m j b ofs then true else false) ((Mem.mem_contents tm) # tb ## o2). *)
(* Proof. *)
(*   intros until o1. intros INJ FIND PERM VINJ. *)
(*   exploit loc_in_reach_find_valid; eauto. intros (A1 & A2 & A3). *)
(*   exploit check_memval_perm_readable; eauto. intros CHECK. *)
(*   destruct (((Mem.mem_contents m) # sb) ## o1) eqn: MV1; simpl in CHECK; try congruence; *)
(*     inv VINJ; try econstructor. *)
(*   destruct v; try congruence; inv H0; try econstructor. *)
(*   eapply proj_sumbool_true in CHECK as CHCEK1. *)
(*   intros PERM2.  *)
(*   assert (ADDEQ: (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta))) = Ptrofs.unsigned i + delta). *)
(*   { exploit Mem.mi_representable; eauto. intros (R1 & R2). *)
(*     generalize (Ptrofs.unsigned_range i). intros R3. *)
(*     unfold Ptrofs.add. rewrite !Ptrofs.unsigned_repr. reflexivity. *)
(*     lia. rewrite !Ptrofs.unsigned_repr. auto. lia. } *)
(*   rewrite ADDEQ in *. *)
(*   destruct (loc_in_reach_find m j b2 (Ptrofs.unsigned i + delta)) as [(b1 & o1')|] eqn: FIND1; auto. *)
(*   exploit loc_in_reach_find_none; eauto. *)
(*   intros [A|A]. *)
(*   - exfalso. eapply A. *)
(*     replace (Ptrofs.unsigned i + delta - delta) with (Ptrofs.unsigned i) by lia. *)
(*     auto. *)
(*   - replace (Ptrofs.unsigned i + delta - delta) with (Ptrofs.unsigned i) in * by lia. *)
(*     (* use A3 to show that the pointer (b,i) point to  *) *)

(*     (* show that (b, i) is Readable *) *)
(*     exploit Mem.mi_perm_inv; eauto. intros [B | B]; try congruence. *)
(*     exploit check_memval_perm_false; eauto. intros [C | C]; try congruence. *)

    
  
(*   (* destruct tv; intros; try constructor. *) *)
(*   (* inv H0. *) *)
(*   (* - admit. *) *)
(*   (* - *) *)
(* Admitted. *)

Lemma inject_implies_valid_memory: forall m tm j,
    Mem.inject j m tm ->
    memory_valid (meminj_inv_memfp (inv_inj j m)) tm.
Proof.
  intros m tm j INJ. generalize INJ as INJ1. inv INJ.
  unfold meminj_inv_memfp, inv_inj, injected. constructor.
  - constructor.
    + intros. simpl in H.
      destruct (Mem.loc_in_reach_find m j b ofs) as [(tb & to)|] eqn: FIND; try congruence.
      exploit Mem.loc_in_reach_find_valid; eauto. intros (A & B).
      replace ofs with (to + (ofs - to)) by lia.
      eapply Mem.mi_perm; eauto. 
  (* + intros. *)
  (*   destruct (loc_in_reach_find m j b delta) as [(sb & to)|] eqn: FIND; try congruence. *)
  (*   exploit loc_in_reach_find_valid. eauto. intros (A & B & C). *)
  (*   exploit Mem.mi_perm_inv; eauto. *)
  (*   instantiate (3 := to). *)
  (*   replace (to + (delta - to)) with delta by lia. eauto. *)
  (*   intros [A1|A2]; try congruence. *)
  (*   exploit Mem.mi_memval; eauto.  *)
  (*   replace (to + (delta - to)) with delta by lia. eauto. *)
  (*   intros VINJ. *)
  (*   (* exploit  *) *)
  (* inv VINJ. constructor. *)
  (* admit.  *)
  (* - intros. *)
  (*   destruct (Mem.loc_in_reach_find m j b ofs) as [(sb & o1)|] eqn: FIND; auto. *)
  (*   exploit Mem.loc_in_reach_find_valid; eauto. intros (A1 & A2). *)
  (*   exfalso. eapply H. eapply mi_mappedblocks; eauto. *)
  - intros. 
    destruct (Mem.loc_in_reach_find m j b delta) as [(sb & o1)|] eqn: FIND; try congruence.
    eapply mi_mappedblocks. eapply Mem.loc_in_reach_find_valid; eauto.
  (* - intros. *)
  (*   destruct (Mem.loc_in_reach_find m j b ofs) as [(sb & o1)|] eqn: FIND; try congruence. *)
  (*   exploit Mem.loc_in_reach_find_valid; eauto. intros (A1 & A2). *)
  (*   exploit mi_representable; eauto. left. *)
  (*   instantiate (1 := Ptrofs.repr o1). Ptrofs.unsigned_repr *)
Qed.

(* Move to Memory.v *)
Lemma in_perm_nonempty: forall b o m,
    Mem.perm m b o Max Nonempty ->
    In o (map fst (Mem.perm_elements_any ((ZMap.elements (Mem.mem_access m) # b)))).
Proof.
  intros.
  red in H. red in H. 
  destruct (((Mem.mem_access m) # b) ## o Max) eqn: PERM; try contradiction.  
  eapply in_map_iff. exists (o, (((Mem.mem_access m) # b) ## o)). 
  split; auto.
  eapply Mem.in_perm_any; eauto.
  eapply ZMap.elements_correct; eauto.
  rewrite Mem.access_default.
  intro.
  rewrite H0 in PERM. congruence.
Qed.

(** Construction of inverse injection and source memory (m1') in the
return *)

Definition meminj_inv_add (invj: meminj_inv) (mfp': memfp) (tb: block) (sb: block) : meminj_inv :=
  fun b ofs => 
    if eq_block b tb then
      if mfp' tb ofs then 
        Some (sb, ofs)
      else 
        None
    else invj b ofs.

(* Given the updated footprint mfp', construct corresponded blocks for
target blocks s2 in source memory with support s1 *)
Fixpoint update_meminj_fp' (mfp': memfp) (s2: list block) (j: meminj) (invj: meminj_inv) (s1: sup) (added: list block) : meminj * meminj_inv * sup :=
  match s2 with
  | nil => (j, invj, s1)
  | tb :: tl =>
      (* check that is tb already been added to the injection *)
      if in_dec eq_block tb added then
        update_meminj_fp' mfp' tl j invj s1 added
      else
        let sb := Mem.fresh_block s1 in
        update_meminj_fp' mfp' tl (meminj_add j sb (tb, 0)) (meminj_inv_add invj mfp' tb sb) (sup_incr s1) (tb :: added)
  end.

(* update the injection with the old injection and the new footprint,
and also returns the updated support for m1 (i.e., the source
memory) *)
Definition update_meminj_fp (j: meminj) (invj: meminj_inv) (m1 m2 m2': mem) (mfp': memfp) : meminj * meminj_inv * sup :=
  let s2 := Mem.sup_list (Mem.support m2) in
  let s2' := Mem.sup_list (Mem.support m2') in
  let new_s2' := filter (fun b => negb (in_dec eq_block b s2)) s2' in
  update_meminj_fp' mfp' new_s2' j invj (Mem.support m1) nil.

(* update memory value *)

Definition memval_map_inv (f: meminj_inv) (mv:memval) : memval :=
  match mv with
  |Fragment (Vptr b ofs) q n =>
       match f b (Ptrofs.unsigned ofs) with
       |Some (b', delta) =>
          let v' := Vptr b' (Ptrofs.repr delta) in
          Fragment v' q n
       |None => Undef
       end
  |_ => mv
  end.


(** step2: assign memory values to the new blocks in source memory,
using the updated inverse injection to inject the values from target
to source. step3: update the memory values in the old blocks of source
memory with the updated inverse injection *)
Section STEP23.
  
Variable m1 m2 m2' : mem.
Variable s1' : sup.
Variable j12 j12' : meminj.
Variable j21' : meminj_inv.

(* Hypothesis DOMIN1: inject_dom_in j12 (Mem.support m1). *)
(* Hypothesis INCR1 : inject_incr j12 j12'. *)


(* Hypothesis SUPINCR1 : Mem.sup_include (Mem.support m1) s1'. *)

(* update the source memory locations that are injected back by j21' *)

Fixpoint content_perm_from_m2'_rec (elements: list (Z * Mem.memperm)) (tb: block) : (list (Z * memval)) * (list (Z * Mem.memperm)) :=
  match elements with
  | nil => (nil, nil)
  | (o2, p) :: tl =>  
      (* For now, we can assume that all locations in tb corresponded
      to locations in a single source block sb, thanks to the
      construction of j21' *)
      match j21' tb o2 with
      | Some (_, _) =>
          let (vl, pl) := content_perm_from_m2'_rec tl tb in
          (* The construction of j21' also ensures that o1 = o2. To
          simplify the proofs of norepetion of offset, we use o2 *)
          ((o2, memval_map_inv j21' ((Mem.mem_contents m2') # tb ## o2)) :: vl,
            (o2, p) :: pl)
      | None =>
          content_perm_from_m2'_rec tl tb
      end
  end.

                                      
(* ensure that sb is a new block in m1'. For simplicity, we can assume
that tb is the holistic injection of sb *)
Definition content_perm_from_m2' (sb : block) : (list (Z * memval)) * (list (Z * Mem.memperm)) :=
  match j12' sb with
  | Some (tb, o2) => 
      let elements_m2' := Mem.perm_elements_any (ZMap.elements ((Mem.mem_access m2') # tb)) in
      content_perm_from_m2'_rec elements_m2' tb
  | None =>
      (nil, nil)
  end.


Definition copy_content_perm_new_block (sb: block) (vmap: ZMap.t memval) (perm_map: ZMap.t Mem.memperm) : ZMap.t memval * ZMap.t Mem.memperm :=
  let (vl, pl) := content_perm_from_m2' sb in
  (Mem.setN' vl vmap, Mem.setN' pl perm_map).
    
    
Lemma content_perm_from_m2'_rec_none1: forall l vl pl tb o1,
    ~ In o1 (map fst l)->
    content_perm_from_m2'_rec l tb = (vl, pl) ->
    ~ In o1 (map fst vl) /\ ~ In o1 (map fst pl).
Proof.
  induction l; intros. simpl in H0. inv H0. auto.
  simpl in H. eapply Decidable.not_or in H.
  destruct a as (o1' & p). simpl in H.
  destruct H as (A & B).
  simpl in H0.
  destruct (j21' tb o1') as [(sb & o2)|].
  - destruct (content_perm_from_m2'_rec l tb) as (vl1 & pl1) eqn: F.
    inv H0.
    split.
    + simpl. red. eapply Decidable.not_or_iff. split; auto. 
      eapply IHl; eauto.
    + simpl. red. eapply Decidable.not_or_iff. split; auto. 
      eapply IHl; eauto.
  - eapply IHl; eauto.
Qed.

Lemma content_perm_from_m2'_rec_norepet: forall l tb vl pl,
    list_norepet (map fst l) ->
    content_perm_from_m2'_rec l tb = (vl, pl) ->
    list_norepet (map fst pl) /\ list_norepet (map fst vl).
Proof.
  induction l; intros. inv H. inv H0.
  simpl. split; econstructor.
  inv H. simpl in H0. destruct a as (o2 & p).
  destruct (j21' tb o2) as [(sb & o1)|] eqn: INJ.
  - destruct (content_perm_from_m2'_rec l tb) eqn: A.
    inv H0. simpl.
    exploit IHl; eauto. intros (A1 & A2).
    split; simpl in *; econstructor; eauto.
    eapply content_perm_from_m2'_rec_none1; eauto.
    eapply content_perm_from_m2'_rec_none1; eauto.
  - simpl in *. eauto.
Qed.

Lemma content_perm_from_m2'_rec_none2: forall l vl pl tb o1,
    In o1 (map fst l) ->
    j21' tb o1 = None ->
    content_perm_from_m2'_rec l tb = (vl, pl) ->
    ~ In o1 (map fst vl) /\ ~ In o1 (map fst pl).
Proof.
  induction l; intros. simpl in H0. inv H0. auto.
  destruct a as (o1' & p). 
  destruct (in_dec zeq o1 (map fst l)).
  - destruct (zeq o1 o1').
    + subst. simpl in H1.
      rewrite H0 in H1. eapply IHl; eauto.
    + simpl in H1.
      destruct (j21' tb o1') as [(tb' & o1'')|] eqn: INJ.
      * destruct (content_perm_from_m2'_rec l tb) as (vl1 & pl1) eqn: A.
        inv H1. simpl.
        exploit IHl; eauto. intros (B1 & B2). 
        split.
        -- intro. destruct H1; try congruence.
        -- intro. destruct H1; try congruence.
      * eapply IHl; eauto.
  - simpl in H. destruct H; auto.
    subst. simpl in H1. rewrite H0 in H1.
    eapply content_perm_from_m2'_rec_none1; eauto.
Qed.


Lemma content_perm_from_m2'_rec_some_aux: forall l vl pl tb o1 sb o1' p,
    In (o1, p) l ->
    j21' tb o1 = Some (sb, o1') ->
    content_perm_from_m2'_rec l tb = (vl, pl) ->
    In (o1, memval_map_inv j21' ((Mem.mem_contents m2') # tb) ## o1) vl
    /\  In (o1, p) pl.
Proof.
  induction l; intros. inv H.
  inv H.
  - simpl in H1. rewrite H0 in H1.
    destruct (content_perm_from_m2'_rec l tb) as (vl1 & pl1) eqn: A.
    inv H1.
    split; econstructor; eauto.
  - simpl in H1. 
    destruct a as (o2' & p1).
    destruct (j21' tb o2') as [(sb' & o1'')|] eqn: INJ.
    + destruct (content_perm_from_m2'_rec l tb) as (vl1 & pl1) eqn: A.
      inv H1. simpl. split.
      * right. eapply IHl; eauto.
      * right. eapply IHl; eauto.
    + eapply IHl; eauto.
Qed.

Lemma content_perm_from_m2'_rec_some: forall vl pl tb o1 sb o1',
    Mem.perm m2' tb o1 Max Nonempty ->
    j21' tb o1 = Some (sb, o1') ->
    content_perm_from_m2'_rec (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m2') # tb)) tb = (vl, pl) ->
    In (o1, memval_map_inv j21' ((Mem.mem_contents m2') # tb) ## o1) vl
    /\ In (o1, (Mem.mem_access m2') # tb ## o1) pl.
Proof.
  intros.
  exploit content_perm_from_m2'_rec_some_aux; eauto. 
  do 2 red in H. 
  destruct (((Mem.mem_access m2') # tb) ## o1 Max) eqn: PERM; try contradiction.
  eapply Mem.in_perm_any. eapply ZMap.elements_correct. reflexivity.
  erewrite Mem.access_default. intro.
  rewrite H2 in PERM. congruence.
  eauto.
Qed.

Lemma copy_content_perm_new_block_result: forall sb vmap perm_map vmap' perm_map' o1,
    copy_content_perm_new_block sb vmap perm_map = (vmap', perm_map') ->
    vmap' ## o1 =
      match j12' sb with
      | Some (tb, _) =>
          if Mem.perm_dec m2' tb o1 Max Nonempty then
            (* Note that j12' sb must be Some (tb, 0) so o1 = o2 *)
            match j21' tb o1 with
            | Some (_, _) =>
                memval_map_inv j21' (((Mem.mem_contents m2') # tb) ## o1)
            | None =>
                vmap ## o1
            end
          else vmap ## o1
      | None =>
          vmap ## o1
      end
    /\ perm_map' ## o1 = 
        match j12' sb with
        | Some (tb, _) =>
            if Mem.perm_dec m2' tb o1 Max Nonempty then
              match j21' tb o1 with
              | Some (_, _) =>
                  ((Mem.mem_access m2') # tb) ## o1
              | None =>
                  perm_map ## o1
              end
            else perm_map ## o1
        | None => perm_map ## o1
        end.
              
Proof.
  intros until o1. intros COPY.
  unfold copy_content_perm_new_block, content_perm_from_m2' in COPY.
  destruct (j12' sb) as [(tb & o2) |] eqn: INJ1.
  2: { inv COPY. split; auto. }
  destruct (Mem.perm_dec m2' tb o1 Max Nonempty).
  - destruct (content_perm_from_m2'_rec (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m2') # tb)) tb) as (vl & pl) eqn: COPY1. inv COPY.
    exploit content_perm_from_m2'_rec_norepet; eauto. 
    eapply Mem.fst_perm_any_norepet. eapply ZMap.elements_keys_norepet.
    intros (N1 & N2).
    destruct (j21' tb o1) as [(sb' & o1') |] eqn: INJ.
    + exploit content_perm_from_m2'_rec_some; eauto. intros (IN1 & IN2).
      erewrite Mem.setN'_inside.
      split. reflexivity.
      erewrite Mem.setN'_inside. reflexivity.
      all: auto.
    + exploit content_perm_from_m2'_rec_none2; eauto.
      eapply in_perm_nonempty. auto.
      intros (NIN1 & NIN2).
      erewrite !Mem.setN'_outside; eauto.
  - destruct (content_perm_from_m2'_rec (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m2') # tb)) tb) as (vl & pl) eqn: COPY1. inv COPY.
    exploit content_perm_from_m2'_rec_none1; eauto.
    instantiate (1 := o1).
    intro. eapply n. 
    eapply in_map_iff in H as ((o1' & p) & A1 & A2). inv A1.
    eapply Mem.in_perm_any_1 in A2 as (B1 & B2).
    red. red. 
    erewrite ZMap.elements_complete with (v:=p). 
    destruct (p Max); try congruence. econstructor. auto.
    intros (NIN1 & NIN2).
    erewrite !Mem.setN'_outside; eauto.
Qed.


Program Definition inject_new_block (m: mem) (sb: block) := 
  if Mem.sup_dec sb (Mem.support m1) then m
  else 
    let vm_pm := copy_content_perm_new_block sb ((Mem.mem_contents m) # sb) ((Mem.mem_access m) # sb) in
  {| Mem.mem_contents := NMap.set _ sb (fst vm_pm) (Mem.mem_contents m);
    Mem.mem_access := NMap.set _ sb (snd vm_pm) (Mem.mem_access m);
    Mem.support := Mem.support m |}.
Next Obligation. 
  erewrite NMap.gsspec.
  destruct NMap.elt_eq; subst.
  - destruct ((copy_content_perm_new_block sb (Mem.mem_contents m) # sb (Mem.mem_access m) # sb)) as (vm & pm) eqn: COPY.
    exploit copy_content_perm_new_block_result. eauto.
    instantiate (1 := ofs). intros (A & B). simpl.
    rewrite B.
    destruct (j12' sb) as [(tb & o2)|].
    + destruct Mem.perm_dec.
       * destruct (j21' tb ofs) as [(sb' & o1')|]; eapply Mem.access_max; eauto.
       * eapply Mem.access_max; eauto.
    + eapply Mem.access_max; eauto.
  - eapply Mem.access_max; eauto.
Defined.
Next Obligation. 
  erewrite NMap.gsspec.
  destruct NMap.elt_eq; subst.
  - destruct ((copy_content_perm_new_block sb (Mem.mem_contents m) # sb (Mem.mem_access m) # sb)) as (vm & pm) eqn: COPY.
    exploit copy_content_perm_new_block_result. eauto.
    instantiate (1 := ofs). intros (A & B). simpl.
    rewrite B.
    destruct (j12' sb) as [(tb & o2)|] eqn: INJ1.
    + destruct Mem.perm_dec.
       * destruct (j21' tb ofs) as [(sb' & o1')|] eqn: INJ2. 
         -- eapply Mem.nextblock_noaccess. eauto.
            
  (*      * eapply Mem.nextblock_noaccess; eauto. *)
  (*   + eapply Mem.nextblock_noaccess; eauto. *)
  (* - eapply Mem.access_max; eauto. *)
            (* not so easy *)
Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Fixpoint copy_new_sup (bl: list block) m : mem :=
  match bl with
  | nil => m
  | hd :: tl => inject_new_block (copy_new_sup tl m) hd
   end.

 Lemma copy_new_sup_support : forall s m,
 Mem.support (copy_new_sup s m) = Mem.support m.
 Proof.
   induction s; intros; simpl; auto.
   unfold inject_new_block. destruct Mem.sup_dec; simpl; auto.
 Qed.      

Definition step2_new_blocks : mem :=
  copy_new_sup (Mem.sup_list s1') (Mem.supext s1' m1).

(* step3: copy the contents of old blocks of m1 into m1' *)

(* perms: the source permission. j12 sb = Some (tb, o2) *)
Fixpoint content_perm_filter' (perms : list (Z * Mem.memperm)) (sb tb: block) (o2: Z) : (list (Z * memval)) * (list (Z * Mem.memperm)) :=
  match perms with
  | nil => (nil, nil)
  | (o1, _) :: tl =>      
      let new_perm := (Mem.mem_access m2') # tb ## (o1 + o2)%Z in
      let (vl, pl) := content_perm_filter' tl sb tb o2 in
      let pl' := (o1, new_perm) :: pl in
      let m2v := (Mem.mem_contents m2') # tb ## (o1 + o2)%Z in
      (* if the permission of this location in the target is
          Readable (as we just copy the target permission to the
          source, using the target permission is correct) *)
      if Mem.perm_dec m2' tb (o1 + o2) Cur Readable then
        if Mem.perm_dec m1 sb o1 Max Writable then 
          ((o1, memval_map_inv j21' m2v) :: vl,
            pl')
        else (vl, pl')
      else (vl, pl')
  end.

Definition content_perm_filter (sb : block) :=
  (* We use perm_elements_any because we do not want to make the
  locations that have no permissions to be mapped locations *)
  let elements := Mem.perm_elements_any (ZMap.elements ((Mem.mem_access m1) # sb)) in
  match j12 sb with
  | Some (tb, o2) => 
      content_perm_filter' elements sb tb o2
  | None =>
      (nil, nil)
  end.

(* update contents and permission of all positions in vmap and
perm_map which are from the updating memory m in inject_old_block *)
Definition copy_content_perm_old_block (sb: block) (vmap: ZMap.t memval) (perm_map: ZMap.t Mem.memperm) : ZMap.t memval * ZMap.t Mem.memperm :=
  let (vl, pl) := content_perm_filter sb in
  (Mem.setN' vl vmap, Mem.setN' pl perm_map).


Lemma content_perm_filter_none_aux1: forall l vl pl sb tb o1 o2,
    ~ In o1 (map fst l) ->
    content_perm_filter' l sb tb o2 = (vl, pl) ->
    ~ In o1 (map fst vl) /\ ~ In o1 (map fst pl).
Proof.
  induction l; intros. simpl in H0. inv H0. auto.
  simpl in H. eapply Decidable.not_or in H.
  destruct a as (o1' & p). simpl in H.
  destruct H as (A & B).
  simpl in H0.
  destruct content_perm_filter' as (vl1 & pl1) eqn: F in H0.
  destruct (Mem.perm_dec m2' tb (o1' + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1' Max Writable); inv H0; simpl.
      * exploit IHl; eauto. intros (N1 & N2).
        split.
        -- intro. destruct H. eauto.
           eapply N1. auto.
        -- intro. destruct H. eauto.
           eapply N2. auto.
      * split. eapply IHl; eauto.
        intro. destruct H; try congruence.
        eapply IHl; eauto.
    + inv H0. simpl. 
      split. eapply IHl; eauto.
      intro. destruct H; try congruence.
      eapply IHl; eauto.
Qed.


Lemma content_perm_filter_norepet: forall l sb tb o vl pl,
    list_norepet (map fst l) ->
    content_perm_filter' l sb tb o = (vl, pl) ->
    list_norepet (map fst pl) /\ list_norepet (map fst vl).
Proof.
  induction l; intros. inv H. inv H0.
  simpl. split; econstructor.
  inv H. simpl in H0. destruct a as (o2 & p).
  destruct content_perm_filter' as (vl1 & pl1) eqn: A in H0.
  destruct (Mem.perm_dec m2' tb (o2 + o) Cur Readable).
  + destruct (Mem.perm_dec m1 sb o2 Max Writable).
    * inv H0. simpl.
      exploit IHl; eauto. intros (N1 & N2).
      split; simpl in *; econstructor; eauto.
      eapply content_perm_filter_none_aux1; eauto.
      eapply content_perm_filter_none_aux1; eauto.
    * inv H0. simpl.
      split.
      -- econstructor. eapply content_perm_filter_none_aux1; eauto.
         eapply IHl; eauto.
      -- eapply IHl; eauto.
  + inv H0. simpl.
    split.
    -- econstructor. eapply content_perm_filter_none_aux1; eauto.
       eapply IHl; eauto.
    -- eapply IHl; eauto.
Qed.


Lemma content_perm_filter_none_aux2: forall l vl pl sb tb o1 o2 (NOREP: list_norepet (map fst l)),
    In o1 (map fst l) ->
    content_perm_filter' l sb tb o2 = (vl, pl) ->
    (~ Mem.perm m2' tb (o1 + o2) Cur Readable \/
       ~ Mem.perm m1 sb o1 Max Writable) ->
    ~ In o1 (map fst vl).
Proof.
  induction l; intros. inv H.
  inv H.
  - simpl in H0. destruct a as (o1 & p).
    inv NOREP.
    destruct content_perm_filter' as (vl1 & pl1) eqn: F in H0.
    simpl in H1. destruct H1.
    + destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable); try congruence.
      inv H0. simpl. eapply content_perm_filter_none_aux1; eauto.
    + destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
      * destruct (Mem.perm_dec m1 sb o1 Max Writable); try congruence.
        inv H0. simpl. eapply content_perm_filter_none_aux1; eauto.
      * inv H0. simpl. eapply content_perm_filter_none_aux1; eauto.
  - inv NOREP. simpl in H0.
    destruct a as (o1' & p).
    destruct content_perm_filter' as (vl1 & pl1) eqn: F in H0.
    destruct (Mem.perm_dec m2' tb (o1' + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1' Max Writable); inv H0.
      * simpl. intro. destruct H.
        -- subst. simpl in H4. congruence.
        -- eapply IHl; eauto.
      * eapply IHl; eauto.
    + inv H0. eapply IHl; eauto.
Qed.

Lemma content_perm_filter_none: forall vl pl sb tb o1 o2,
    content_perm_filter' (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m1) # sb)) sb tb o2 = (vl, pl) ->
    Mem.perm m1 sb o1 Max Nonempty ->
    (~ Mem.perm m2' tb (o1 + o2) Cur Readable \/
       ~ Mem.perm m1 sb o1 Max Writable) ->
    ~ In o1 (map fst vl).
Proof.
  intros. eapply content_perm_filter_none_aux2; eauto.
  eapply Mem.fst_perm_any_norepet. eapply ZMap.elements_keys_norepet.
  eapply in_perm_nonempty. auto.
Qed.

Lemma content_perm_filter_some_aux: forall l vl pl sb tb o1 o2,
    In o1 (map fst l) ->
    content_perm_filter' l sb tb o2 = (vl, pl) ->
    In (o1, ((Mem.mem_access m2') # tb) ## (o1 + o2)) pl
    /\ (Mem.perm m2' tb (o1 + o2) Cur Readable ->            
       Mem.perm m1 sb o1 Max Writable ->
       In (o1, memval_map_inv j21' ((Mem.mem_contents m2') # tb) ## (o1 + o2)) vl).
Proof.
  induction l; intros. inv H.
  inv H. 
  - simpl in H0. destruct a as (o1 & p).
    destruct content_perm_filter' as (vl1 & pl1) in H0.
    destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1 Max Writable).
      * inv H0. simpl. split; auto.
      * inv H0. simpl. split; auto.
        intros. contradiction.
    + inv H0. simpl. split; auto.
      intros. contradiction.
  - simpl in H0.
    destruct a as (o1' & p).
    destruct content_perm_filter' as (vl1 & pl1) eqn: F in H0.
    destruct (Mem.perm_dec m2' tb (o1' + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1' Max Writable).
      * inv H0. simpl. split; auto.
        right.
        eapply IHl; eauto.
        intros. right.
        eapply IHl; eauto.
      * inv H0. simpl. split; auto.
        right.
        eapply IHl; eauto.
        intros. eapply IHl; eauto.
    + inv H0. simpl. split; auto.
      right.
      eapply IHl; eauto.
      intros. eapply IHl; eauto.
Qed.

Lemma content_perm_filter_some: forall vl pl sb tb o1 o2,
    content_perm_filter' (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m1) # sb)) sb tb o2 = (vl, pl) ->
    Mem.perm m1 sb o1 Max Nonempty ->
    In (o1, ((Mem.mem_access m2') # tb) ## (o1 + o2)) pl
    /\ (Mem.perm m2' tb (o1 + o2) Cur Readable ->            
       Mem.perm m1 sb o1 Max Writable ->
       In (o1, memval_map_inv j21' ((Mem.mem_contents m2') # tb) ## (o1 + o2)) vl).
Proof.
  intros. 
  eapply content_perm_filter_some_aux; eauto.
  eapply in_perm_nonempty. auto.
Qed.

Lemma in_perm_any_2: forall m b o,
    In o (map fst (Mem.perm_elements_any (ZMap.elements (Mem.mem_access m) # b))) ->
    Mem.perm m b o Max Nonempty.
Proof.
  intros. unfold Mem.perm, Mem.perm_order'.
  eapply in_map_iff in H as ((o1 & p) & A1 & A2).
  inv A1. eapply Mem.in_perm_any_1 in A2 as (B1 & B2).
  simpl. erewrite ZMap.elements_complete; eauto.
  destruct (p Max); try congruence.
  econstructor.
Qed.

Lemma copy_content_perm_old_block_result: forall sb vmap perm_map vmap' perm_map' o1,
    copy_content_perm_old_block sb vmap perm_map = (vmap', perm_map') ->
    (* Mem.perm m1 sb o1 Max Nonempty -> *)
    vmap' ## o1 = match j12 sb with
                   | Some (tb, o2) => 
                       let new_perm := (Mem.mem_access m2') # tb ## (o1 + o2)%Z in
                       let m2v := ((Mem.mem_contents m2')#tb)## (o1 + o2)%Z in
                       if Mem.perm_dec m2' tb (o1 + o2) Cur Readable then
                         if Mem.perm_dec m1 sb o1 Max Writable then              
                           memval_map_inv j21' m2v 
                         else vmap ## o1 else vmap ## o1
                  | None => vmap## o1
                  end
    /\ perm_map' ## o1 = match j12 sb with
                        | Some (tb, o2) => 
                            if Mem.perm_dec m1 sb o1 Max Nonempty then
                              (Mem.mem_access m2') # tb ## (o1 + o2)
                            else
                              perm_map ## o1
                        | None => 
                            perm_map ## o1
                        end.
Proof.
  intros until o1. intros COPY.
  unfold copy_content_perm_old_block, content_perm_filter in COPY.
  destruct (j12 sb) as [ [tb o2]|] eqn: INJSB.
  - simpl. 
    destruct content_perm_filter' as (vl & pl) eqn: F. inv COPY.
    exploit content_perm_filter_norepet; eauto.
    eapply Mem.fst_perm_any_norepet.
    eapply ZMap.elements_keys_norepet. intros (N1 & N2).
    destruct (Mem.perm_dec m1 sb o1 Max Nonempty).
    + exploit content_perm_filter_some; eauto.
      intros (A1 & A2).
      destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
      * destruct (Mem.perm_dec m1 sb o1 Max Writable).
        -- erewrite !Mem.setN'_inside; eauto. 
        -- erewrite Mem.setN'_outside. 
           erewrite !Mem.setN'_inside; eauto.
           eapply content_perm_filter_none; eauto.
      * erewrite Mem.setN'_outside. 
        erewrite !Mem.setN'_inside; eauto.
        eapply content_perm_filter_none; eauto.
    + exploit content_perm_filter_none_aux1; eauto.
      intro. eapply n. eapply in_perm_any_2; eauto.
      intros (A1 & A2).
      destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
      * destruct (Mem.perm_dec m1 sb o1 Max Writable).
        -- exfalso. eapply n. eapply Mem.perm_implies; eauto. constructor.
        -- erewrite !Mem.setN'_outside; eauto.
      * erewrite !Mem.setN'_outside; eauto.      
  - simpl in COPY. inv COPY. split; reflexivity.
Qed.

Program Definition inject_old_block (m: mem) (sb: block) := 
  (* if j12' sb then *)
  if Mem.sup_dec sb (Mem.support m) then
    let (vm, pm) := copy_content_perm_old_block sb ((Mem.mem_contents m) # sb) ((Mem.mem_access m) # sb) in
  {| Mem.mem_contents := NMap.set _ sb vm (Mem.mem_contents m);
    Mem.mem_access := NMap.set _ sb pm (Mem.mem_access m);
    Mem.support := Mem.support m |}
  else m.
  (* else m. *)
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
      
Fixpoint copy_old_sup' (bl:list block) m : mem :=
   match bl with
   | nil => m
   | hd :: tl => inject_old_block (copy_old_sup' tl m) hd
   end.

 Lemma copy_old_sup'_support : forall s m,
 Mem.support (copy_old_sup' s m) = Mem.support m.
 Proof.
   induction s; intros; simpl; auto.
   unfold inject_old_block. destruct Mem.sup_dec; simpl; auto.
   destruct copy_content_perm_old_block.
   simpl. auto.
 Qed.

(* Copy the contents and permissions in (support m1) into m1' *)
Definition step3_old_blocks (s: sup) m : mem := copy_old_sup' (Mem.sup_list s) m.

End STEP23.

Definition inverse_inj_valid1 (j21: meminj_inv) (j12: meminj) : Prop := 
  forall b1 b2 o1 o2, 
    j21 b2 o2 = Some (b1,o1) ->
    j12 b1 = Some (b2,o2 - o1).

Definition inverse_inj_valid2 (s1: Mem.sup) (j21: meminj_inv) (j12: meminj) : Prop := 
  forall b1 b2 b1' o1 o1' o2, 
    ~ Mem.sup_In b1 s1 ->
    j12 b1 = Some (b2, o2 - o1) ->
    (* Note that j21 b2 o2 may map to None *)
    j21 b2 o2 = Some (b1', o1') ->
    b1 = b1' /\ o1 = o1'.


(** The construction proof of source memory m1' *)

Section CONSTR_PROOF.
  Variable m1 m2 m2': mem.
  Variable j12 j12': meminj.
  Variable j21': meminj_inv.
  Variable s1': sup.
  
  Hypothesis ROUNC2: Mem.ro_unchanged m2 m2'.
  Hypothesis DOMIN1: inject_dom_in j12 (Mem.support m1).
  (* Hypothesis DOMIN1': inject_dom_in j12' (Mem.support m1'). *)
  (* Hypothesis UNCHANGE1: Mem.unchanged_on (loc_unmapped j12) m1 m1'. *)
  Hypothesis UNCHANGE2: Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2'.
  Hypothesis INJ12 : Mem.inject j12 m1 m2.
  Hypothesis SUPINCR1 : Mem.sup_include (Mem.support m1) s1'.
  Hypothesis INCR1 : inject_incr j12 j12'.
  Hypothesis INCRDISJ1 : inject_incr_disjoint j12 j12' (Mem.support m1) (Mem.support m2).
  Hypothesis INCRNOLAP'1:inject_incr_no_overlap' j12 j12'.
  Hypothesis MAXPERM2 : injp_max_perm_decrease m2 m2'.
  Hypothesis IMGIN1': inject_image_in j12' (Mem.support m2').
  (* Hypothesis DOMIN2': inject_dom_in j2' s2'. *)
  Hypothesis DOMIN1': inject_dom_in j12' s1'.
  Hypothesis INCRNEW1: inject_incr_newblock1 j12 j12' (Mem.support m2).
  Hypothesis ADDZERO: update_add_zero j12 j12'.
  (* Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2'). *)
  (* Hypothesis ADDSAME : update_add_same j2 j2' j1'. *)
  (* Hypothesis ADDBLOCK: update_add_block (Mem.support m2) s2' j1' j2'. *)

  Hypothesis INVINJ1: inverse_inj_valid1 j21' j12'.
  Hypothesis INVINJ2: inverse_inj_valid2 (Mem.support m1) j21' j12'.
  (* We may also need to prove inverse_inj_valid m1' j21' j12' *)

  Definition m1'1 := step2_new_blocks m1 m2 m2' s1' j12 j12' j21'.
  Definition m1' := step3_old_blocks m1 m2 m2' s1' j12 j12' j21' (Mem.support m1) m1'1.
  
  Lemma m1'1_support : Mem.support m1'1 = s1'.
  Proof. unfold m1'1. Admitted.
  Lemma m1'_support : Mem.support m1' = s1'.
  Proof. Admitted.

  Lemma memval_INJ12': forall mv,
      memval_inject j12' (memval_map_inv j21' mv) mv.
  Proof.
    destruct mv; simpl; try econstructor.
    destruct v; try econstructor; try econstructor.
    destruct (j21' b (Ptrofs.unsigned i)) as [(sb & delta) |] eqn: J; try econstructor.
    eapply INVINJ1 in J as A1.
    econstructor; eauto.
    rewrite <- Valuesrel.add_repr.
    replace (delta + (Ptrofs.unsigned i - delta)) with (Ptrofs.unsigned i) by lia.
    rewrite Ptrofs.repr_unsigned. reflexivity.
Qed.        

  Lemma step3_old_blocks_sup_perm_content1: forall m b1 o1 b2 o2,
      j12 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Max Nonempty ->
      Mem.support m = s1' ->
      (forall k p, Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b1) b1 o1 k p <-> Mem.perm m2' b2 o2 k p)
      /\ (Mem.perm m2' b2 o2 Cur Readable ->            
         Mem.perm m1 b1 o1 Max Writable ->         
          memval_inject j12' (mem_memval (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b1) b1 o1) (mem_memval m2' b2 o2)).
  Proof.
    intros. unfold inject_old_block.
    exploit DOMIN1. eauto. intros SUP1. 
    assert (SUP1' : sup_In b1 (Mem.support m)).
    { eapply SUPINCR1 in SUP1. rewrite H1. auto. }
    destruct Mem.sup_dec; try congruence.
    unfold copy_content_perm_old_block. 
    destruct (content_perm_filter m1 m2' j12 j21' b1) as (vl & pl) eqn: F.
    unfold Mem.perm at 1, mem_memval. simpl. 
    setoid_rewrite NMap.gss.
    exploit (copy_content_perm_old_block_result m1 m2' j12 j21' b1 ((Mem.mem_contents m) # b1) ((Mem.mem_access m) # b1)).
    unfold copy_content_perm_old_block. rewrite F. reflexivity.
    instantiate (1 := o1). auto. rewrite H. simpl.
    intros (A & B).
    rewrite B. replace (o1 + (o2 - o1)) with o2 in * by lia. split. 
    - destruct (Mem.perm_dec m1 b1 o1 Max Nonempty); try congruence.
      reflexivity.
    - intros. 
      destruct Mem.perm_dec in A; try congruence.
      destruct Mem.perm_dec in A; try congruence.
      rewrite A.
      eapply memval_INJ12'.
  Qed.
  
  Lemma step3_old_blocks_sup_perm_content2: forall m b b1 o1,
      b <> b1 ->
      (forall k p, Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b1 o1 k p <-> Mem.perm m b1 o1 k p)
      /\ (mem_memval (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b1 o1) = (mem_memval m b1 o1).
  Proof.
    intros. unfold inject_old_block.
    destruct Mem.sup_dec.
    - destruct copy_content_perm_old_block.
      unfold Mem.perm, mem_memval. simpl.
      setoid_rewrite NMap.gso; try congruence.
      split; reflexivity.
    - split; reflexivity.
  Qed.      
    
  Lemma step3_old_blocks_sup_perm_content3: forall m b o1,
      loc_unmapped j12 b o1 ->
      (forall k p, Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b o1 k p <-> Mem.perm m b o1 k p)
      /\ mem_memval (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b o1 = (mem_memval m b o1).
  Proof.
    intros. unfold inject_old_block.
    destruct Mem.sup_dec.
    - destruct copy_content_perm_old_block eqn: A.
      unfold Mem.perm, mem_memval. simpl.
      setoid_rewrite NMap.gss. 
      exploit copy_content_perm_old_block_result; eauto.
      intros (B1 & B2).
      red in H. rewrite H in *. rewrite B1, B2.
      split; reflexivity.
    - split; reflexivity.
  Qed.      

  Lemma step3_old_blocks_sup_perm_content4: forall m b o1,
      ~ Mem.perm m1 b o1 Max Nonempty ->
      (forall k p, Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b o1 k p <-> Mem.perm m b o1 k p)
      /\ mem_memval (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b o1 = (mem_memval m b o1).
  Proof.
    intros. unfold inject_old_block.
    destruct Mem.sup_dec.
    - destruct copy_content_perm_old_block eqn: A.
      unfold Mem.perm, mem_memval. simpl.
      setoid_rewrite NMap.gss. 
      exploit copy_content_perm_old_block_result; eauto.
      instantiate (1 := o1).
      intros (B1 & B2).
      destruct (j12 b) as [(tb & o2) |] eqn: INJ.
      + destruct (Mem.perm_dec m1 b o1 Max Nonempty); try congruence.
        destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
        * destruct (Mem.perm_dec m1 b o1 Max Writable).
          -- exfalso. eapply n. eapply Mem.perm_implies; eauto. constructor.
          -- rewrite B1, B2. simpl. split; reflexivity.
        * rewrite B1, B2. simpl. split; reflexivity.
      + rewrite B1, B2. simpl. split; reflexivity.
    - split; reflexivity.
  Qed.      
  
  Lemma step3_old_blocks_sup_perm_content5: forall m b o1,
      ~ Mem.perm m1 b o1 Max Writable ->
      mem_memval (inject_old_block m1 m2 m2' s1' j12 j12' j21' m b) b o1 = (mem_memval m b o1).
  Proof.
    intros. unfold inject_old_block.
    destruct Mem.sup_dec.
    - destruct copy_content_perm_old_block eqn: A.
      unfold Mem.perm, mem_memval. simpl.
      setoid_rewrite NMap.gss.
      exploit copy_content_perm_old_block_result; eauto.
      instantiate (1 := o1).
      intros (B1 & B2).
      destruct (j12 b) as [(tb & o2) |] eqn: INJ.
      + destruct (Mem.perm_dec m1 b o1 Max Nonempty); try congruence.
        * destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
          -- destruct (Mem.perm_dec m1 b o1 Max Writable).
             ++ congruence.
             ++ rewrite B1. simpl. auto.
          -- rewrite B1. simpl. auto.
      * destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
        -- destruct (Mem.perm_dec m1 b o1 Max Writable).
             ++ congruence.
             ++ rewrite B1. simpl. auto.
        -- rewrite B1. simpl. auto.
      + auto.
    - split; reflexivity.
  Qed.



  Lemma step3_old_blocks_sup_perm_content: forall bl m b1 o1 b2 o2,
        j12 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        In b1 bl ->
        Mem.support m = s1' ->
        (forall k p, Mem.perm (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1 k p <-> Mem.perm m2' b2 o2 k p) 
        /\ (Mem.perm m2' b2 o2 Cur Readable ->
           Mem.perm m1 b1 o1 Max Writable ->
           memval_inject j12' (mem_memval (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1) (mem_memval m2' b2 o2)).
  Proof.
    induction bl; intros.
    - inv H1.
    - simpl. destruct (eq_block b1 a).
      + subst a. 
        eapply step3_old_blocks_sup_perm_content1; eauto.
        rewrite <- H2. eapply copy_old_sup'_support.
      + destruct H1. congruence.        
        exploit step3_old_blocks_sup_perm_content2.
        intro. eapply n. symmetry. eapply H3.
        intros (A & B).
        split. 
        * etransitivity. eapply A. eapply IHbl; eauto.
        * intros. rewrite B.
          eapply IHbl; eauto.
  Qed.

  Lemma step3_old_blocks_sup_perm_content_unchanged: forall bl m b1 o1,
        ~ In b1 bl ->
        Mem.support m = s1' ->
        (forall k p, Mem.perm (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1 k p <-> Mem.perm m b1 o1 k p) 
        /\  mem_memval (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1 = (mem_memval m b1 o1).
  Proof.
    induction bl; intros.
    - simpl. split; intros; try reflexivity.
    - simpl. simpl in H.
      eapply Decidable.not_or in H. destruct H.
      exploit step3_old_blocks_sup_perm_content2. eapply H.
      intros (A & B).
      split. 
      + etransitivity. eapply A. eapply IHbl; eauto.
      + intros. rewrite B.
        eapply IHbl; eauto.
  Qed.


  Lemma step3_old_blocks_sup_content_not_writable: forall bl m b1 o1 b2 o2,
        j12 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        In b1 bl ->
        Mem.support m = s1' ->
        Mem.perm m2' b2 o2 Cur Readable ->
        ~ Mem.perm m1 b1 o1 Max Writable ->
        (mem_memval (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1) = (mem_memval m b1 o1).
  Proof.
    induction bl; intros.
    - inv H1.
    - simpl. destruct (eq_block b1 a).
      + subst a.
        etransitivity.
        eapply step3_old_blocks_sup_perm_content5. auto.
        destruct (in_dec eq_block b1 bl).
        * eapply IHbl; eauto.
        * eapply  step3_old_blocks_sup_perm_content_unchanged; auto.
      + etransitivity.
        eapply step3_old_blocks_sup_perm_content2. auto.
        destruct H1; try congruence.
        eapply IHbl; eauto.
  Qed.
  

  Lemma old_injected_block_perm: forall b1 o1 b2 o2 k p,
          j12 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          Mem.perm m1' b1 o1 k p <->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. unfold m1'.
    eapply step3_old_blocks_sup_perm_content; eauto.
    eapply DOMIN1. eauto.
    eapply m1'1_support.
  Qed.

  Lemma old_injected_block_perm1: forall b1 o1 b2 o2 k p,
          j12 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          Mem.perm m1' b1 o1 k p ->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. eapply old_injected_block_perm; eauto.
  Qed.


  Lemma old_injected_block_perm2: forall b1 o1 b2 o2 k p,
          j12 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          Mem.perm m2' b2 o2 k p ->
          Mem.perm m1' b1 o1 k p.
  Proof.
    intros. eapply old_injected_block_perm; eauto.
  Qed.

  Lemma old_injected_block_content_inject: forall b1 o1 b2 o2,
      j12 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      memval_inject j12' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. eapply step3_old_blocks_sup_perm_content; eauto.
    eapply Mem.perm_implies. eauto. econstructor.
    eapply DOMIN1; eauto.
    eapply m1'1_support.
    eapply old_injected_block_perm1; eauto.
    eapply Mem.perm_implies. eauto. econstructor.
  Qed.    



  Lemma step3_old_blocks_sup_perm_content_unchanged1: forall bl m b1 o1,
      In b1 bl ->
      ~ Mem.perm m1 b1 o1 Max Nonempty ->
      Mem.support m = s1' ->
      (forall k p, Mem.perm (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' bl m) b1 o1 k p <-> Mem.perm m b1 o1 k p) 
      /\  mem_memval (copy_old_sup' m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 = (mem_memval m b1 o1).
  Proof.
    induction bl; intros.
    - inv H. 
    - simpl. destruct (eq_block b1 a).
      + subst a.
        exploit step3_old_blocks_sup_perm_content4. eauto.
        instantiate (1 := (copy_old_sup' m1 m2 m2' s1' j12 j12' j21'  bl m)).
        intros (A & B).
        split.
        * intros. etransitivity. eapply A. 
          destruct (in_dec eq_block b1 bl).
          -- eapply IHbl; eauto.
          -- eapply step3_old_blocks_sup_perm_content_unchanged; eauto.
        * rewrite B. 
          destruct (in_dec eq_block b1 bl).
          -- eapply IHbl; eauto.
          -- eapply step3_old_blocks_sup_perm_content_unchanged; eauto.
      + split.
        * intros. etransitivity.
          eapply step3_old_blocks_sup_perm_content2; eauto.
          eapply IHbl; eauto. destruct H; try congruence.
        * intros. etransitivity.
          eapply step3_old_blocks_sup_perm_content2; eauto.
          eapply IHbl; eauto. destruct H; try congruence.
  Qed.


  Lemma step2_inject_new_blocks_sup_perm_content2: forall m b b1 o1,
      b <> b1 ->
      (forall k p, Mem.perm (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b) b1 o1 k p <-> Mem.perm m b1 o1 k p)
      /\ (mem_memval (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b) b1 o1) = (mem_memval m b1 o1).
  Proof.
    intros. unfold inject_new_block.
    destruct Mem.sup_dec.
    - split; reflexivity.
    - unfold Mem.perm, mem_memval. simpl.
      destruct copy_content_perm_new_block.
      setoid_rewrite NMap.gso; try congruence.
      split; reflexivity.
  Qed.      
  
  Lemma step2_new_blocks_sup_perm_content_unchanged: forall bl m b1 o1,
        ~ In b1 bl ->
        Mem.support m = s1' ->
        (forall k p, Mem.perm (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 k p <-> Mem.perm m b1 o1 k p) 
        /\  mem_memval (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 = (mem_memval m b1 o1).
  Proof.
    induction bl; intros.
    - simpl. split; intros; try reflexivity.
    - simpl. simpl in H.
      eapply Decidable.not_or in H. destruct H.
      exploit step2_inject_new_blocks_sup_perm_content2. eapply H.
      intros (A & B).
      split. 
      + etransitivity. eapply A. eapply IHbl; eauto.
      + intros. rewrite B.
        eapply IHbl; eauto.
  Qed.

  Lemma step2_new_blocks_sup_perm_content_unchanged1: forall bl m b1 o1,
      Mem.sup_In b1 (Mem.support m1) ->
        Mem.support m = s1' ->
      (forall k p, Mem.perm (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 k p <-> Mem.perm m b1 o1 k p) 
      /\  mem_memval (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 = (mem_memval m b1 o1).
  Proof.
    induction bl; intros.
    - simpl. split; intros; try reflexivity.
    - simpl. destruct (eq_block a b1).
      + subst.
        unfold inject_new_block.
        destruct Mem.sup_dec; try congruence. eapply IHbl; eauto.
      + exploit step2_inject_new_blocks_sup_perm_content2. eapply n.
        intros (A & B).
        split.
        * etransitivity. eapply A. eapply IHbl; eauto.
        * intros. rewrite B.
          eapply IHbl; eauto.
  Qed.


  (* used in step2_new_blocks_nonempty_in_reach *)
  Lemma step2_inject_new_blocks_nonempty_in_reach: forall m b1 o1 b2 o2,
      j12' b1 = Some (b2, o2 - o1) ->
      ~ Mem.sup_In b1 (Mem.support m1) ->
      Mem.support m = s1' ->
      ~ Mem.perm m b1 o1 Max Nonempty ->
      Mem.perm (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b1) b1 o1 Max Nonempty ->
      j21' b2 o2 = Some (b1, o1) /\ Mem.perm m2' b2 o2 Max Nonempty.
  Proof.
    intros until o2. intros A B C E D.
    unfold inject_new_block in D. 
    destruct Mem.sup_dec; try congruence.
    unfold Mem.perm in D. simpl in D.
    destruct (copy_content_perm_new_block m2' j12' j21' b1 (Mem.mem_contents m) # b1
                (Mem.mem_access m) # b1) as (vm, pm)  eqn: COPY.
    setoid_rewrite NMap.gss in D.
    destruct (pm ## o1 Max) eqn: PERM. 
    2: { simpl in D. rewrite PERM in D. inv D. }
    exploit (copy_content_perm_new_block_result m2' j12' j21' b1 ((Mem.mem_contents m) # b1) ((Mem.mem_access m) # b1)). eapply COPY.
    instantiate (1:= o1).
    rewrite A. intros (A1 & A2).
    destruct (Mem.perm_dec m2' b2 o1 Max Nonempty) eqn: PERM2.
    - destruct (j21' b2 o1) as [(b1' & o1') |] eqn: INJ.
      + exploit ADDZERO; eauto.
        destruct (j12 b1) as [(?b & ?o) |] eqn: J.
        eapply DOMIN1 in J; congruence. auto.
        intros OEQ.
        assert (o1 = o2) by lia. subst o1.
        exploit INVINJ2. eauto. eapply A. eauto.
        intros (C1 & C2). subst. split. eauto. auto.
      + rewrite A2 in PERM.
        unfold Mem.perm in E.
        rewrite PERM in E. exfalso.
        eapply E. econstructor.


(* exploit INVINJ2; eauto. intros INJ.  *)
(*         exploit ADDZERO. 2: eapply A. eapply inject_dom_in_inv; eauto. *)
(*         intros. *)
(*         assert (o2 = o1) by lia. subst. *)
(*         rewrite INJ in *. auto. *)
(*       rewrit *)
(* destruct (j21' b2 o1) as [(b1' & o1') |] eqn: INJ. *)
(*       + exploit  *)
        
(*         (* Lemma inverse_inj_valid2: forall b1 b2 o1 o2, *) *)
(*         (*     j12' b1 = Some (b2, o2 - o1) -> *) *)
            

(* exploit ADDZERO; eauto. *)
(*         destruct (j12 b1) as [(?b & ?o) |] eqn: J. *)
(*         eapply DOMIN1 in J; congruence. auto. *)
(*         intros OEQ. *)
(*         assert (o1 = o2) by lia. subst o1. split; auto. *)
(*         exploit INVINJ1. eauto. intros INJ1. *)
(*         exploit inject_dom_in_inv. eapply DOMIN1. eauto. intros INJ2. *)
(*         exploit INCRDISJ1; eauto. intros (N1 & N2). *)
(*         assert (INJ4: j12 b1' = None).  *)
(*         {  *)
(*         exploit ADDZERO. 2: eapply INJ1. eauto. intros.  *)
(*         assert (o2 = o1') by lia. subst. *)
(*         destruct (eq_block b1 b1'); subst; auto. *)
(*         exploit INCRNOLAP'1; eauto. intros. contradiction. *)
      (* + rewrite A2 in PERM. *)
      (*   unfold Mem.perm in E. *)
      (*   rewrite PERM in E. exfalso. *)
      (*   eapply E. econstructor. *)
    - rewrite A2 in PERM.
      unfold Mem.perm in E.
      rewrite PERM in E. exfalso.
      eapply E. econstructor.
  Qed.
  
  Lemma supext_support: forall s m,
      Mem.sup_include (Mem.support m) s ->
      Mem.support (Mem.supext s m) = s.
  Proof.
    intros.
    unfold Mem.supext.
    destruct Mem.sup_include_dec. auto.
    congruence.
  Qed.

  Lemma old_injected_block_content_not_writable: forall b1 o1 b2 o2,
      j12 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1 b1 o1 Cur Readable ->
      Mem.perm m1' b1 o1 Cur Readable ->
      ~ Mem.perm m1 b1 o1 Max Writable ->
      (mem_memval m1' b1 o1) = (mem_memval m1 b1 o1).
  Proof.
    intros. 
    unfold m1'. etransitivity.    
    eapply step3_old_blocks_sup_content_not_writable; eauto.
    eapply Mem.perm_cur_max.
    eapply Mem.perm_implies; eauto. constructor.
    eapply DOMIN1; eauto.
    eapply m1'1_support.
    eapply old_injected_block_perm1; eauto.
    eapply Mem.perm_cur_max.    
    eapply Mem.perm_implies; eauto. constructor.    
    etransitivity.
    eapply step2_new_blocks_sup_perm_content_unchanged1; eauto.
    eapply supext_support. auto.
    eapply supext_unchanged_on. reflexivity. instantiate (1 := fun _ _ => True).
    simpl. auto. auto.
Qed.

  Lemma step_copy_new_sup_nonempty_in_reach: forall l m b1 b2 o1 o2,
      j12' b1 = Some (b2, o2 - o1) ->
      ~ Mem.sup_In b1 (Mem.support m1) ->
      In b1 l ->
      ~ Mem.perm m b1 o1 Max Nonempty ->
      Mem.support m = s1' ->
      Mem.perm (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  l m) b1 o1 Max Nonempty ->
      j21' b2 o2 = Some (b1, o1) /\ Mem.perm m2' b2 o2 Max Nonempty.
  Proof.
    induction l. intros. inv H1.
    intros until o2. intros INJ NIN IN NPERM SUP PERM.
    destruct (eq_block b1 a). 
    - subst a. simpl in PERM.
      destruct (in_dec eq_block b1 l).
      + destruct (Mem.perm_dec (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  l m)  b1 o1 Max Nonempty). 
        * eapply IHl; eauto.
        * eapply step2_inject_new_blocks_nonempty_in_reach. eauto. eauto.
          2: eapply n.
          rewrite <- SUP.
          eapply copy_new_sup_support. auto.
      + eapply step2_inject_new_blocks_nonempty_in_reach. eauto. eauto.
        instantiate (1 := (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  l m)).
        rewrite <- SUP.
        eapply copy_new_sup_support .
        intro. eapply NPERM. eapply step2_new_blocks_sup_perm_content_unchanged; eauto.
        auto.
    - simpl in PERM.
      eapply IHl. eauto. auto. destruct IN. congruence. auto.
      eauto. auto.      
      eapply step2_inject_new_blocks_sup_perm_content2. eauto. auto.
  Qed.
      
  (* The locations in m1' that have permission must be injected from m2' *)
  Lemma step2_new_blocks_nonempty_in_reach: forall b1 b2 o1 o2,
      j12' b1 = Some (b2, o2 - o1) ->
      ~ Mem.sup_In b1 (Mem.support m1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      j21' b2 o2 = Some (b1, o1) /\ Mem.perm m2' b2 o2 Max Nonempty.
  Proof.
    intros until o2. intros A B C.
    unfold m1' in C.
    exploit step3_old_blocks_sup_perm_content_unchanged; eauto.
    eapply m1'1_support. instantiate (1 := o1).
    intros (A1 & A2). 
    eapply A1 in C. clear A1 A2.
    unfold m1'1 in C. 
    unfold step2_new_blocks in C.
    eapply step_copy_new_sup_nonempty_in_reach; eauto.
    eapply DOMIN1'; eauto.
    unfold Mem.supext. destruct Mem.sup_include_dec; try congruence.
    unfold Mem.perm. simpl.
    unfold Mem.perm_order'.
    erewrite Mem.nextblock_noaccess. congruence. auto.
    unfold Mem.supext. destruct Mem.sup_include_dec; try congruence.
    simpl. auto.
  Qed.
  
  Lemma step2_new_blocks_sup_perm_content1: forall m b1 o1 b2 o2,
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      ~ Mem.sup_In b1 (Mem.support m1) ->
      Mem.support m = s1' ->
      (forall k p, Mem.perm (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b1) b1 o1 k p <-> Mem.perm m2' b2 o2 k p)
      /\ (memval_inject j12' (mem_memval (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b1) b1 o1) (mem_memval m2' b2 o2)).
  Proof.
    intros. unfold inject_new_block. 
    destruct Mem.sup_dec; try congruence.
    unfold Mem.perm, mem_memval. simpl.
    destruct (copy_content_perm_new_block m2' j12' j21' b1 (Mem.mem_contents m) # b1
                (Mem.mem_access m) # b1) as (vm, pm)  eqn: COPY.    
    setoid_rewrite NMap.gss.
    exploit (copy_content_perm_new_block_result m2' j12' j21' b1 ((Mem.mem_contents m) # b1) ((Mem.mem_access m) # b1)). eapply COPY.
    instantiate (1 := o1). rewrite H.
    (* show that m2' has permission in this location *)
    exploit step2_new_blocks_nonempty_in_reach; eauto.
    intros (A1 & A2). 
    (* show that o1 = o2 *)
    exploit ADDZERO; eauto. 
    destruct (j12 b1) as [(?b & ?o) |] eqn: J.
    eapply DOMIN1 in J; congruence. auto.
    intros OEQ.
    assert (o1 = o2) by lia. subst.
    destruct (Mem.perm_dec m2' b2 o2 Max Nonempty).
    2: congruence.
    rewrite A1.
    intros (A & B). simpl.
    rewrite A. rewrite B.
    split.
    - reflexivity.
    - eapply memval_INJ12'.
  Qed.
  
  Lemma step2_new_blocks_sup_perm_content: forall bl m b1 o1 b2 o2,
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      ~ Mem.sup_In b1 (Mem.support m1) ->
      In b1 bl ->
      Mem.support m = s1' ->
      (forall k p, Mem.perm (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1 k p <-> Mem.perm m2' b2 o2 k p) 
        /\ (memval_inject j12' (mem_memval (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m) b1 o1) (mem_memval m2' b2 o2)).
  Proof.
    induction bl; intros.
    - inv H2.
    - simpl. destruct (eq_block b1 a).
      + subst a. 
        eapply step2_new_blocks_sup_perm_content1; eauto.
        rewrite <- H3. eapply copy_new_sup_support.
      + destruct H2. congruence.        
        exploit step2_inject_new_blocks_sup_perm_content2.
        intro. eapply n. symmetry. eapply H4.
        intros (A & B).
        split. 
        * etransitivity. eapply A. eapply IHbl; eauto.
        * intros. rewrite B.
          eapply IHbl; eauto.
  Qed.

  
  Lemma new_injected_block_perm: forall b1 o1 b2 o2 k p,
      j12 b1 = None ->      
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (Mem.perm m1' b1 o1 k p <->
         Mem.perm m2' b2 o2 k p).
  Proof.
    intros. unfold m1'.
    exploit INCRDISJ1; eauto.
    intros (S1 & S2).
    etransitivity. eapply step3_old_blocks_sup_perm_content_unchanged; eauto.
    eapply m1'1_support.
    unfold m1'1.
    eapply step2_new_blocks_sup_perm_content; eauto.
    erewrite <- Mem.sup_list_in. eapply DOMIN1'; eauto.
    eapply supext_support. auto.
  Qed.
  
  Lemma new_injected_block_perm1: forall b1 o1 b2 o2 k p,
      j12 b1 = None ->      
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 k p ->
      Mem.perm m2' b2 o2 k p.
  Proof.
    intros. eapply new_injected_block_perm; eauto.
    eauto with mem.
  Qed.

  Lemma new_injected_block_perm2: forall b1 o1 b2 o2 k p,
      j12 b1 = None ->      
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->      
      Mem.perm m2' b2 o2 k p ->
      Mem.perm m1' b1 o1 k p.
  Proof.
    intros.
    eapply new_injected_block_perm; eauto.
  Qed.


  (* similar to step2_content_inject *)
  Lemma new_injected_block_content_inject : forall b1 o1 b2 o2,
      j12 b1 = None ->
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->     
      memval_inject j12' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
    intros. unfold m1'.
    exploit INCRDISJ1; eauto.
    intros (S1 & S2).
    exploit step3_old_blocks_sup_perm_content_unchanged. eapply S1.
    eapply m1'1_support.
    unfold m1'1.
    intros (A & B). unfold step3_old_blocks.    
    erewrite B.
    eapply step2_new_blocks_sup_perm_content; eauto.
    eapply Mem.perm_implies. 
    eapply Mem.perm_max.
    eauto. constructor.
    eapply DOMIN1'; eauto.
    eapply supext_support. auto.
  Qed.    
        

  Lemma unchanged_inject_new_block: forall m b,
      Mem.unchanged_on (fun b _ => Mem.valid_block m1 b) m (inject_new_block m1 m2 m2' s1' j12 j12' j21'  m b).
  Proof.
    intros. unfold inject_new_block.
    destruct Mem.sup_dec.
    eapply Mem.unchanged_on_refl. 
    econstructor; simpl.
    - simpl. eapply Mem.sup_include_refl.
    - intros. unfold Mem.perm. simpl.
      setoid_rewrite NMap.gso. reflexivity.
      intro. eapply n. subst. eauto.
    - intros. simpl.
      setoid_rewrite NMap.gso. reflexivity.
      intro. eapply n. subst. eauto.
  Qed.
  
  Lemma unchanged_copy_new_sup: forall bl m,
      Mem.unchanged_on (fun b _ => Mem.valid_block m1 b) m (copy_new_sup m1 m2 m2' s1' j12 j12' j21'  bl m).
  Proof.
    induction bl; intros.
    - simpl. eapply Mem.unchanged_on_refl.
    - simpl. eapply Mem.unchanged_on_trans.
      2: eapply unchanged_inject_new_block.
      eauto.
  Qed.


  Lemma unchanged_valid_blocks_step2: Mem.unchanged_on (fun b _ => Mem.valid_block m1 b) m1 m1'1.
  Proof.
    eapply Mem.unchanged_on_trans. eapply supext_unchanged_on.
    instantiate (1:= Mem.supext s1' m1). reflexivity.
    eapply unchanged_copy_new_sup.
  Qed.

  Lemma unchanged_step2: Mem.unchanged_on (loc_unmapped j12) m1 m1'1.
  Proof.
    unfold m1'1, step2_new_blocks.
    eapply Mem.unchanged_on_implies with (P := fun b _ => Mem.valid_block m1 b).
    eapply unchanged_valid_blocks_step2.
    intros. auto.
  Qed.    

      
  Lemma unchanged_inject_old_block: forall b m,
      Mem.unchanged_on (loc_unmapped j12) m (inject_old_block m1 m2 m2' s1' j12 j12' j21'  m b).
  Proof.
    intros. constructor.
    - unfold inject_old_block. destruct Mem.sup_dec; simpl.
      destruct copy_content_perm_old_block. eapply Mem.sup_include_refl.
      eapply Mem.sup_include_refl.
    - intros. destruct (eq_block b b0).
      + subst. symmetry. eapply step3_old_blocks_sup_perm_content3; auto.
      + symmetry. eapply step3_old_blocks_sup_perm_content2; auto.
    - intros.
      intros. destruct (eq_block b b0).
      + subst. eapply step3_old_blocks_sup_perm_content3; auto.
      + eapply step3_old_blocks_sup_perm_content2; auto.
  Qed.
  
  Lemma unchanged_step3_copy_old_sup: forall bl m,
      Mem.unchanged_on (loc_unmapped j12) m
        (copy_old_sup' m1 m2 m2' s1' j12 j12' j21'  bl m).
  Proof.
    induction bl; intros.
    - simpl. eapply Mem.unchanged_on_refl.
    - simpl.
      eapply Mem.unchanged_on_trans. eapply IHbl; eauto.
      eapply unchanged_inject_old_block.
  Qed.
  
  Lemma unchanged_step3: Mem.unchanged_on (loc_unmapped j12) m1'1 m1'.
  Proof.
    unfold m1', step3_old_blocks.
    eapply unchanged_step3_copy_old_sup.
  Qed.

  Lemma UNC1: Mem.unchanged_on (loc_unmapped j12) m1 m1'.
  Proof.
    unfold m1'.
    eapply Mem.unchanged_on_trans.
    eapply unchanged_step2.
    eapply unchanged_step3.
  Qed.

  Lemma MAXPERM1: injp_max_perm_decrease m1 m1'.
  Proof.
    red. intros b ofs p A B.
    unfold m1' in B. 
    destruct (j12 b) as [(tb & o)|] eqn: INJ.
    - destruct (Mem.perm_dec m1 b ofs Max Nonempty).
      + replace o with ((ofs + o) - ofs) in INJ by lia. 
        exploit step3_old_blocks_sup_perm_content; eauto.
        eapply m1'1_support. intros (B1 & B2).
        eapply B1 in B.
        eapply MAXPERM2 in B. eapply Mem.perm_inject_inv in B; eauto.
        destruct B. eauto. congruence.
        replace (ofs + o - ofs) with o in INJ by lia. auto.
        eapply Mem.mi_mappedblocks; eauto.
      + exploit step3_old_blocks_sup_perm_content_unchanged1. 
        eapply A. eauto. eapply m1'1_support. intros (C1 & C2).
        eapply C1 in B. 
        exfalso. eapply n.
        eapply Mem.unchanged_on_perm. eapply unchanged_valid_blocks_step2.
        simpl. auto. auto. 
        eapply Mem.perm_implies; eauto. constructor.
    - eapply Mem.unchanged_on_perm.
      eapply UNC1. red. auto. auto. auto.
  Qed.

                             
  Lemma ROUNC1: Mem.ro_unchanged m1 m1'.
  Proof.
    apply Mem.ro_unchanged_memval_bytes.
    red. intros b o1 VALID PERM1' NOPERM1.
    exploit MAXPERM1. eauto. eapply Mem.perm_cur_max; eauto.
    intros PERM1. 
    destruct (j12 b) as [(tb & o)|] eqn: INJ.
    - replace o with ((o1 + o) - o1) in INJ by lia. 
      exploit old_injected_block_perm1; eauto. 
      eapply Mem.perm_implies; eauto. constructor.
      intros PERM2'.
      assert (forall k p, Mem.perm m2 tb (o1 + o) k p -> Mem.perm m1 b o1 k p).
      { intros. 
        exploit Mem.mi_perm_inv; eauto. instantiate (3 := o1).
        replace (o1 + (o1 + o - o1)) with (o1 + o) by lia. eauto.
        intros [A|B]. 
        2: { exfalso. eapply B. eapply Mem.perm_implies; eauto. constructor. }
        auto. }
      (* use ro_unchanged of m2 *)
      apply Mem.ro_unchanged_memval_bytes in ROUNC2 as ROUNC2'. 
      exploit ROUNC2'. instantiate (1 := tb).
      eapply Mem.mi_mappedblocks; eauto. eauto. 
      intro. eapply NOPERM1. auto.
      intros (A1 & A2).
      split; auto.
      symmetry. eapply old_injected_block_content_not_writable; eauto.
    - split.
      + eapply Mem.unchanged_on_perm. eapply UNC1. 1-3: auto. 
      + symmetry. eapply Mem.unchanged_on_contents.
        eapply UNC1. auto.
        eapply Mem.unchanged_on_perm. eapply UNC1. 1-3: auto. 
  Qed.
    
    
  Lemma INJ12': Mem.inject j12' m1' m2'.
  Proof.
    constructor.
    - constructor.
      (* permission *)
      + intros.
        destruct (subinj_dec j12 j12' b1 b2 delta INCR1 H).
        (* old injected block *)
        * eapply old_injected_block_perm with (o2 := ofs + delta) (o1 := ofs) (b1 := b1).
          replace (ofs + delta - ofs) with delta by lia. auto.
          (* injected block has nonempty permission in m1, ensured by
          MAXPERM1 *)
          eapply MAXPERM1. eapply DOMIN1. eauto. 
          eauto with mem. auto.
        (* new injected block *)
        * eapply new_injected_block_perm1 with (o1 := ofs); eauto.
          replace (ofs + delta - ofs) with delta by lia. auto.
      (* alignment *)
      + intros.
        destruct (subinj_dec j12 j12' b1 b2 delta INCR1 H).
        * eapply Mem.mi_align. eapply INJ12. eauto.
          red. intros. eapply MAXPERM1. eapply DOMIN1. eauto.
          eapply H0. eauto.
        * exploit ADDZERO; eauto. intros. subst.
          eapply Z.divide_0_r.
      (* contents *)
      + intros.
        destruct (subinj_dec j12 j12' b1 b2 delta INCR1 H).
        * destruct (Mem.perm_dec m1 b1 ofs Max Writable).
          -- eapply old_injected_block_content_inject; eauto.
             replace (ofs + delta - ofs) with delta by lia. eauto. 
          (* The location is not Writable in m1 *)
          -- generalize ROUNC1. intros ROUNC1.
             apply Mem.ro_unchanged_memval_bytes in ROUNC2 as ROUNC2'.
             apply Mem.ro_unchanged_memval_bytes in ROUNC1 as ROUNC1'.
             exploit ROUNC1'; eauto. 
             eapply Mem.valid_block_inject_1; eauto.
             intros [PERM1 MVAL1]. rewrite <- MVAL1.
             assert (NOTWRITE: ~ Mem.perm m2 b2 (ofs + delta) Max Writable).
             { intro. exploit Mem.mi_perm_inv; eauto. intros [A|B].
               - congruence.
               - eapply B. eauto with mem. }             
             exploit ROUNC2'; eauto.
             eapply Mem.valid_block_inject_2. apply e. eauto.
             eapply old_injected_block_perm; eauto.
             replace (ofs + delta - ofs) with delta by lia. auto.
             eauto with mem.
             intros [PERM2 MVAL2]. rewrite <- MVAL2.
             inversion INJ12. inversion mi_inj.
             eapply memval_inject_incr; eauto.
        (* new injected block *)
        * eapply new_injected_block_content_inject; eauto.
          replace (ofs + delta - ofs) with delta by lia. auto.
    (* mi_freeblocks *)
    - intros.
      destruct (j12' b) as [[b2 d]|] eqn:?; auto.
      eapply DOMIN1' in Heqo. rewrite <- m1'_support in Heqo.
      exfalso. eapply H. eauto.
    (* mi_mappedblocks *)
    - intros. red. eapply IMGIN1'. eauto.
    - eapply update_meminj_no_overlap1. eapply MAXPERM1.
      all: eauto. 
    (* mi_representable *)
    - intros. destruct (j12 b) as [[b2' d']|] eqn: Hj1b.
      + apply INCR1 in Hj1b as H'. rewrite H in H'. inv H'.
        inversion INJ12.
        eapply mi_representable; eauto.
        destruct H0.
        left. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
        right. eapply MAXPERM1; eauto. unfold Mem.valid_block. eauto.
      + exploit ADDZERO; eauto. intro. subst. split. lia.
        generalize (Ptrofs.unsigned_range_2 ofs). lia.
    (* mi_perm_inv *)
    - intros. 
      destruct (subinj_dec j12 j12' b1 b2 delta INCR1 H).
      + destruct (Mem.perm_dec m1' b1 ofs Max Nonempty); eauto.
        left.
        eapply old_injected_block_perm2; eauto.
        replace (ofs + delta - ofs) with delta by lia. auto.
        eapply MAXPERM1; eauto.
        eapply DOMIN1. eauto.
      + destruct (Mem.perm_dec m1' b1 ofs Max Nonempty); eauto.
        left.
        eapply new_injected_block_perm2; eauto.
        replace (ofs + delta - ofs) with delta by lia. auto.
Qed.


End CONSTR_PROOF.

Lemma UNC2: forall m1 m2 m2' j,     
    Mem.inject j m1 m2 ->
    Mem.unchanged_on (fun (b : block) (ofs : Z) => meminj_inv_memfp (inv_inj j m1) b ofs = false) m2 m2' ->
    Mem.unchanged_on (loc_out_of_reach j m1) m2 m2'.
Proof.
  intros. eapply Mem.unchanged_on_implies; eauto.
  intros. simpl.
  unfold meminj_inv_memfp, injected, inv_inj.
  destruct (Mem.loc_in_reach_find m1 j b ofs) as [(tb & o)|] eqn: FIND; auto.
  exploit Mem.loc_in_reach_find_valid; eauto. intros (A & B).
  exfalso. eapply H1; eauto. replace (ofs - (ofs - o)) with o by lia.
  auto.
Qed.

(** Properties of inverse injection  *)

Lemma inv_inj_valid1: forall j m,
    inverse_inj_valid1 (inv_inj j m) j.
Proof.
  intros. red. intros. 
  exploit Mem.loc_in_reach_find_valid; eauto. intros (A1 & A2).
  auto.
Qed.

    
Lemma meminj_add_dom_in: forall j b o s,
    inject_dom_in j s ->
    inject_dom_in (meminj_add j (Mem.fresh_block s) (b, o)) (Mem.sup_incr s).
Proof.
  intros. red. unfold meminj_add. intros.
  destruct eq_block.
  - inv H0. eapply Mem.sup_incr_in1.
  - red in H. eapply Mem.sup_incr_in. right. eauto.
Qed.

Lemma inverse_inj_valid1_add: forall invj mfp tb sb j
    (DIS: forall b1 b2 o1 o2, invj b2 o2 = Some (b1, o1) -> b1 <> sb),
    inverse_inj_valid1 invj j ->
    inverse_inj_valid1 (meminj_inv_add invj mfp tb sb) (meminj_add j sb (tb,0)).
Proof.
  intros. red in H. red.
  intros. unfold meminj_inv_add, meminj_add in *.
  destruct eq_block; eauto.
  - subst.
    destruct (mfp tb o2) eqn: A; try congruence.
    inv H0. rewrite pred_dec_true; auto. f_equal. f_equal. lia.
  - eapply DIS in H0 as A. rewrite pred_dec_false. eauto. auto.
Qed.

Lemma inverse_inj_valid2_add: forall s0 s b j mfp invj
    (DIS: forall sb o, ~ j sb = Some (b, o)),
    (* Mem.sup_include s0 s -> *)
    inverse_inj_valid2 s0 invj j ->
    inverse_inj_valid2 s0 (meminj_inv_add invj mfp b (fresh_block s))
      (meminj_add j (fresh_block s) (b, 0)).
Proof.
  intros until invj. intros DIS INV. red in INV. red.   
  intros. unfold meminj_inv_add, meminj_add in *. 
  destruct (eq_block b1 (fresh_block s)).
  - subst. inv H0. rewrite pred_dec_true in H1; auto.
    destruct (mfp b2 o2); try congruence. 
    inv H1. split. auto. lia.
  - destruct eq_block in H1; subst.
    + destruct (mfp b o2) eqn: FP; try congruence.
      inv H1. exfalso. eapply DIS; eauto.
    + eauto.
Qed.

  (* rewrite pred_dec_false in H1.  *)
  (* 2: { intro. eapply H0. subst. eapply Mem.sup_incr_in1. } *)
  (* destruct eq_block in H2. *)
  (* - subst. *)
  (* exploit H; eauto. intro. eapply H0. eapply Mem.sup_incr_in2. auto. *)

  (* destruct eq_block. *)
  (* - subst. destruct (mfp b o2) eqn: FP in H2. *)
  (*   + inv H2.  *)
  (* intros A. rewrite pred_dec_false. auto. *)
  (* intro. subst. erewrite DIS in A. congruence. *)


Lemma update_meminj_fp_prop_rec: forall s s1 s2 s1' s2' j invj mfp' j' invj' added s0
    (INCL: forall b, In b s -> Mem.sup_In b s2' /\ ~ Mem.sup_In b s2),
    Mem.sup_include s2 s2' ->
    fp_dom_in mfp' s2' ->
    inject_dom_in j s1  ->
    inject_image_in j s2' ->
    inverse_inj_valid1 invj j ->    
    inverse_inj_valid2 s0 invj j -> 
    Mem.sup_include s0 s1 ->
    update_meminj_fp' mfp' s j invj s1 added = (j', invj', s1') ->
    (* properties of added blocks *)
    (forall b, In b added -> ~ Mem.sup_In b s2) ->
    (forall b, In b s -> ~ In b added -> forall sb o, ~ j sb = Some (b, o)) ->
    inverse_inj_valid1 invj' j'
    /\ inverse_inj_valid2 s0 invj' j' 
    /\ Mem.sup_include s1 s1'
    /\ inject_image_in j' s2'
    /\ inject_dom_in j' s1'
    /\ inject_incr_newblock1 j j' s2
    /\ update_add_zero j j'
    /\ inject_incr j j'
    /\ inject_incr_disjoint j j' s1 s2
    /\ inject_incr_no_overlap' j j'
    (* properties for no_overlap which extends the incr_disjoint to
    consider the extension of s2*)
    /\ (forall b b' o, j b = None -> j' b = Some (b', o) -> In b' s /\ ~ In b' added).
Proof.
  induction s; intros until s0; intros ? SUPINCL FPDOM DOMIN1 IMGIN1 INVINJ1 INVINJ2 SUPINCL0 UPD ADD1 ADD2.
  - simpl in UPD. inv UPD.
    repeat apply conj; try congruence; eauto.
  - simpl in UPD. 
    destruct (in_dec eq_block a added).
    + exploit (IHs s1 s2 s1' s2' j invj mfp' j' invj' added s0); auto.
      * intros. eapply INCL. eapply in_cons. eauto.
      * intros. eapply ADD2. eapply in_cons; auto. auto.
      * intros (A & B & C & D & E & F & G & H & I & J & K).
        repeat apply conj; auto.
        intros. exploit K; eauto. intros (A1 & A2). split; auto.
        eapply in_cons; auto.
    + exploit (INCL a). econstructor. auto. intros (IN1 & IN2).
      exploit (IHs (sup_incr s1) s2 s1' s2' (meminj_add j (fresh_block s1) (a, 0)) (meminj_inv_add invj mfp' a (fresh_block s1)) mfp' j' invj' (a::added) s0); auto.
      * intros. eapply INCL. eapply in_cons. eauto.
      * eapply meminj_add_dom_in; auto.
      * red. unfold meminj_add. intros.
        destruct eq_block in H. inv H. auto. eauto.
      * eapply inverse_inj_valid1_add; auto.
        intros. exploit INVINJ1. eauto. intros.
        exploit DOMIN1. eauto. intros.
        intro. subst. eapply Mem.freshness. eauto.
      * eapply inverse_inj_valid2_add; eauto.
        eapply ADD2. econstructor. auto. auto.
      * eapply Mem.sup_include_trans; eauto.
      * intros. destruct H. subst. eauto. eauto.
      * intros. unfold meminj_add.
        destruct eq_block. subst. intro.
        eapply H0. inv H1. econstructor; auto.
        eapply ADD2. eapply in_cons. auto. intro. eapply H0.
        eapply in_cons. auto.
      * intros (A & B & C & D & E & F & G & H & I & J & K).
        assert (INCRNEW1: inject_incr_newblock1 j j' s2).
        { red. intros.
          destruct (eq_block b1 (fresh_block s1)); subst.
          ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
             intros A1. rewrite H1 in A1. inv A1. auto.
          ++ eapply F. unfold meminj_add. rewrite pred_dec_false; eauto. eauto. }        
        repeat apply conj; auto.
        -- eapply Mem.sup_include_trans; eauto.
        -- red. intros.
           destruct (eq_block b1 (fresh_block s1)); subst.
           ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
              intros A1. rewrite H1 in A1. inv A1. auto.
           ++ eapply G. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
        -- red. intros.
           destruct (eq_block b (fresh_block s1)); subst.
           ++ exploit inject_dom_in_inv. eapply DOMIN1. eapply Mem.freshness. intros. 
              congruence.
           ++ eapply H. unfold meminj_add. rewrite pred_dec_false; eauto. 
        -- red. intros.
           destruct (eq_block b (fresh_block s1)); subst.
           ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
              intros A1. rewrite H1 in A1. inv A1. split; auto.
              eapply Mem.freshness.
           ++ exploit I. unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
              intros (I1 & I2). split; auto.
              intro. eapply I1. eapply Mem.sup_incr_in2. auto.
        -- red. intros.
           destruct (eq_block b1 (fresh_block s1)); 
             destruct (eq_block b2 (fresh_block s1)); subst; try congruence.
           ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
              intros A1. rewrite H3 in A1. inv A1. 
              exploit K. instantiate (1 := b2).
              unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
              intros (A1& A2). intro. eapply A2. subst. econstructor; auto.
           ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
              intros A1. rewrite H4 in A1. inv A1. 
              exploit K. instantiate (1 := b1).
              unfold meminj_add. rewrite pred_dec_false; eauto. eauto.
              intros (A1& A2). intro. eapply A2. subst. econstructor; auto.
           ++ eapply J. eapply H0.
              unfold meminj_add. rewrite pred_dec_false; eauto. 
              unfold meminj_add. rewrite pred_dec_false; eauto. all: eauto.
        -- intros. 
           destruct (eq_block b (fresh_block s1)); subst.
           ++ exploit H. unfold meminj_add. rewrite pred_dec_true; eauto.
              intros A1. rewrite H1 in A1. inv A1. split; auto. econstructor; auto.
           ++ exploit K; eauto.
              unfold meminj_add. rewrite pred_dec_false; eauto. 
              intros (A1 & A2). split; auto. eapply in_cons; auto. 
              eapply not_in_cons; eauto.
Qed.
              

Lemma update_meminj_fp_prop: forall j invj m1 m2 m2' mfp' j' invj' s1',
    Mem.sup_include (Mem.support m2) (Mem.support m2') ->
    fp_dom_in mfp' (Mem.support m2') ->
    inject_dom_in j (Mem.support m1)  ->
    inject_image_in j (Mem.support m2) ->
    inverse_inj_valid1 invj j ->
    inverse_inj_valid2 (Mem.support m1) invj j ->
    update_meminj_fp j invj m1 m2 m2' mfp' = (j', invj', s1') ->
    inverse_inj_valid1 invj' j' 
    /\ inverse_inj_valid2 (Mem.support m1) invj' j' 
    /\ Mem.sup_include (Mem.support m1) s1'
    /\ inject_image_in j' (Mem.support m2')
    /\ inject_dom_in j' s1'
    /\ inject_incr_newblock1 j j' (Mem.support m2)
    /\ update_add_zero j j'
    /\ inject_incr j j'
    /\ inject_incr_disjoint j j' (Mem.support m1) (Mem.support m2)
    /\ inject_incr_no_overlap' j j'.
Proof.
  intros until s1'. intros SUPINCL FPDOM DOMIN1 IMGIN1 INVINJ1 INVINJ2 UPD.
  unfold update_meminj_fp in UPD.
  exploit update_meminj_fp_prop_rec. 3-9: eauto.
  instantiate (1 := (Mem.support m2)).
  all: eauto.
  - intros. eapply filter_In in H. destruct H.
    split. eapply Mem.sup_list_in. eauto.
    eapply negb_true_iff in H0. 
    destruct in_dec in H0; simpl in *; try congruence.
    intro. eapply n. eapply Mem.sup_list_in; eauto.
  - red. intros. eapply Mem.sup_include_trans. eapply SUPINCL.
    eauto. eauto.
  - intros. intro. eapply IMGIN1 in H1.
    eapply filter_In in H. destruct H.
    eapply negb_true_iff in H2. 
    destruct in_dec in H2; simpl in *; try congruence.
    eapply n. eapply Mem.sup_list_in; eauto.
  - intros (A & B & C & D & E & F & G & H & I & J & K).
    repeat apply conj; auto.
Qed.


(* Incoming related memorys m1 and m2 that are related by injp, and
module accessibility is an unary relation (the mvw_acc), to construct
the outgoing source memory m1' and the injp_acc relation *)
Lemma mem_protect_injp: forall m1 m2 j (INJ: Mem.inject j m1 m2),
    exists (Hm: memory_valid (meminj_inv_memfp (inv_inj j m1)) m2),
      let mfp := meminj_inv_memfp (inv_inj j m1) in
      (forall mfp' m2' Hm',
          mvw_acc (mvw mfp m2 Hm) (mvw mfp' m2' Hm') ->
          exists (invj': meminj_inv) j' m1' INJ',
            (** TODO: relation between invj', j' and mfp', which is used
          to establish value injection in the new j' *)
            injp_acc (injpw j m1 m2 INJ) (injpw j' m1' m2' INJ')).
Proof.
  intros.
  exists (inject_implies_valid_memory m1 m2 j INJ).
  simpl. 
  intros mfp' m2' Hm' MACC.
  set (invj := inv_inj j m1) in *.
  (* construction of injection, inverse injection and the fresh support for m1 *)
  destruct (update_meminj_fp j invj m1 m2 m2' mfp') as ((j' & invj') & s1') eqn: UPT.
  inv MACC.
  generalize (inject_implies_image_in _ _ _ INJ).
  intros IMGIN2.
  generalize (inject_implies_dom_in _ _ _ INJ).
  intros DOMIN1.
  exploit (update_meminj_fp_prop j invj m1 m2 m2' mfp' j' invj' s1'); eauto.
  eapply Mem.unchanged_on_support. eauto.
  red. intros. eapply mv_dom; eauto.
  eapply inv_inj_valid1.
  (* use the fact the there is no block outside m1 but injected by j  *)
  { red. intros. eapply Mem.mi_freeblocks in H; eauto. congruence. }
  intros (INVINJ1 & INVINJ2 & SUPINCL1 & IMGIN1' & DOMIN1' & INCRNEW1 & ADDZERO & INJINCR & INJDIS & INJNOLAP).
    (* generalize (inject_incr_inv _ _ _ _ _ _ _ DOMIN12 IMGIN12 DOMIN23 DOMIN13' SUPINCL1 INCR13 DISJ13). *)
    (* intros (j12' & j23' & m2'_sup & INCRn1 & INCRn2 & JEQ & INCR12 & INCR23 & SUPINCL2 & DOMIN12' & IMGIN12' & DOMIN23' & INCRDISJ12 & INCRDISJ23 & INCRNOLAP & ADDZERO & ADDEXISTS & ADDSAME & ADDNB). *)
  set (m1' := m1' m1 m2 m2' j j' invj' s1').  
  eapply UNC2 in UNC.
  set (INJ12' := INJ12' m1 m2 m2' j j' invj' s1' RO DOMIN1 UNC INJ SUPINCL1 INJINCR INJDIS INJNOLAP MAXPERM IMGIN1' DOMIN1' INCRNEW1 ADDZERO INVINJ1 INVINJ2).
  exists invj', j', m1', INJ12'. 
  (* injp_acc *)
  econstructor; eauto.
  eapply ROUNC1. all: eauto. 
  eapply MAXPERM1; eauto.
  eapply UNC1. 
Qed.

