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

(* Construct the inverse function of the memory injection from the
injection *)
Definition inv_inj (j: meminj) (m: mem) : meminj_inv :=
  Mem.loc_in_reach_find m j.

Definition injected (invj: meminj_inv) b ofs : bool :=
  if invj b ofs then true else false.

Definition meminj_inv_memfp (invj: meminj_inv) : memfp :=
  fun b ofs => injected invj b ofs.

Inductive valid_val (mfp: memfp): val -> Prop :=
| valid_val_int:
  forall i, valid_val mfp (Vint i)
| valid_val_long:
  forall i, valid_val mfp (Vlong i)
| valid_val_float:
  forall f, valid_val mfp (Vfloat f)
| valid_val_single:
  forall f, valid_val mfp (Vsingle f)
| valid_val_ptr: forall b ofs
  (VMV: mfp b (Ptrofs.unsigned ofs) = true),
  valid_val mfp (Vptr b ofs)
| val_valid_val_undef:
    valid_val mfp Vundef.

Inductive valid_val_list (mfp: memfp): list val -> Prop:=
  | valid_val_list_nil :
      valid_val_list mfp nil
  | valid_val_list_cons : forall v vl ,
      valid_val mfp v -> valid_val_list mfp vl->
      valid_val_list mfp (v :: vl).

(* increments of memory footprint *)

Definition memfp_incr (mfp1 mfp2: memfp) : Prop :=
  forall b ofs, mfp1 b ofs = true -> mfp2 b ofs = true.

Definition memfp_separated (mfp1 mfp2: memfp) (m: mem) : Prop := 
  forall b ofs, 
    mfp1 b ofs = false ->
    mfp2 b ofs = true ->
    ~ Mem.valid_block m b.

Inductive valid_memval (mfp: memfp): memval -> Prop :=
  | valid_memval_byte:
      forall n, valid_memval mfp (Byte n)
  | valid_memval_frag:
      forall v q n,
      valid_val mfp v ->
      valid_memval mfp (Fragment v q n)
  | valid_memval_undef:
      valid_memval mfp Undef.

(* Unary Memory Injection --- Validity of Memory *)

Record mem_valid (mfp: memfp) (m: mem) : Prop :=
  mk_mem_valid {
      (* not sure: the footprint must have permission? *)
      mv_perm: forall b ofs k,
        mfp b ofs = true ->
        Mem.perm m b ofs k Nonempty;
      mv_align:
      forall b ofs delta p chunk,
        mfp b delta = true ->
        Mem.range_perm m b (delta + ofs) (delta + ofs + size_chunk chunk) Max p ->
        (align_chunk chunk | delta);
      mv_memval:
      forall b ofs delta,
        mfp b delta = true ->
        Mem.perm m b (delta + ofs) Cur Readable ->
        valid_memval mfp (ZMap.get (delta + ofs) (NMap.get _ b m.(Mem.mem_contents)))
    }.

Record memory_valid' (mfp: memfp) (m: mem) : Prop :=
  mk_memory_valid {
    mv_inj:
      mem_valid mfp m;
    mv_freeblocks:
      forall b ofs, ~(Mem.valid_block m b) -> mfp b ofs = false;
    mv_mappedblocks:
      forall b delta, mfp b delta = true -> Mem.valid_block m b;
    mv_representable:
      forall b ofs,
      mfp b ofs = true ->
      Mem.perm m b ofs Max Nonempty \/ Mem.perm m b (ofs - 1) Max Nonempty ->
      0 <= ofs <= Ptrofs.max_unsigned;
  }.

Definition memory_valid := memory_valid'.

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

(** Properties of inv_inj and meminj_inv_memfp *)

Lemma inject_implies_valid_memory: forall m tm j,
    Mem.inject j m tm ->
    memory_valid (meminj_inv_memfp (inv_inj j m)) tm.
Admitted.

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
Fixpoint update_meminj_fp' (mfp': memfp) (s2: list block) (j: meminj) (invj: meminj_inv) (s1: sup) : meminj * meminj_inv * sup :=
  match s2 with
  | nil => (j, invj, s1)
  | tb :: tl =>
      let sb := Mem.fresh_block s1 in
      update_meminj_fp' mfp' tl (meminj_add j sb (tb, 0)) (meminj_inv_add invj mfp' tb sb) (sup_incr s1)
  end.

(* update the injection with the old injection and the new footprint,
and also returns the updated support for m1 (i.e., the source
memory) *)
Definition update_meminj_fp (j: meminj) (invj: meminj_inv) (m1 m2 m2': mem) (mfp': memfp) : meminj * meminj_inv * sup :=
  let s2 := Mem.sup_list (Mem.support m2) in
  let s2' := Mem.sup_list (Mem.support m2') in
  let new_s2' := filter (fun b => negb (in_dec eq_block b s2)) s2' in
  update_meminj_fp' mfp' new_s2' j invj (Mem.support m1).

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


Fixpoint block_ofs_val_elements (elements : list Z) (tb: block) (vmap2 : ZMap.t memval) (f: meminj_inv) : list (block * Z * memval) :=
  match elements with
    | nil => nil
    | z :: elements' =>
        match f tb z with
        | Some (sb, ofs) =>            
            let mapvalue := memval_map_inv f (vmap2 ## z) in
            (sb, ofs, mapvalue) :: block_ofs_val_elements elements' tb vmap2 f
        | None =>
            block_ofs_val_elements elements' tb vmap2 f
        end
  end.

(* This function iterate the memory contents [vmap2] of block [tb] in
the target memory, inject the value (using f) of the locations that
have Readable permission to the source memory m1 *)
Definition update_src_mem_content (pmap2 : Mem.perm_map) (f:meminj_inv) (tb: block) (m1: NMap.t (ZMap.t memval)) (vmap2: ZMap.t memval) : NMap.t (ZMap.t memval) :=
  let elements := ZMap.elements pmap2 in
  let ofs_elements := Mem.perm_elements_readable elements in
  let val_elements := block_ofs_val_elements ofs_elements tb vmap2 f in
  fold_left (fun acc '(b, ofs, v) => NMap.set _ b (ZMap.set ofs v (acc#b)) acc) val_elements m1.


Fixpoint block_ofs_perm_elements (elements : list (Z * (perm_kind -> option permission))) (tb: block) (f: meminj_inv) : list (block * Z * (perm_kind -> option permission)) :=
  match elements with
    | nil => nil
    | (z, p) :: elements' =>
        match f tb z with
        | Some (sb, ofs) =>            
            (sb, ofs, p) :: block_ofs_perm_elements elements' tb f
        | None =>
            block_ofs_perm_elements elements' tb f
        end
  end.

(* The version of updating permission of update_src_mem_content *)
Definition update_src_mem_access (pmap2 : Mem.perm_map) (f:meminj_inv) (tb: block) (m1: NMap.t Mem.perm_map) (vmap2: Mem.perm_map) : NMap.t Mem.perm_map :=
  let elements := Mem.perm_elements_any (ZMap.elements vmap2) in
  let perm_elements := block_ofs_perm_elements elements tb f in
  fold_left (fun acc '(b, ofs, v) => NMap.set _ b (ZMap.set ofs v (acc#b)) acc) perm_elements m1.


(** step2: assign memory values to the new blocks in source memory,
using the updated inverse injection to inject the values from target
to source. step3: update the memory values in the old blocks of source
memory with the updated inverse injection *)
Section STEP23.
  
Variable m1 m2 m2' : mem.
Variable s1' : sup.
Variable j12 j12' : meminj.
Variable j21' : meminj_inv.

Hypothesis SUPINCR1 : Mem.sup_include (Mem.support m1) s1'.

(* update the source memory locations that are injected back by j21' *)

Program Definition inject_new_block (m: mem) (tb: block) := 
  if Mem.sup_dec tb (Mem.support m2) then m
  else 
    {| Mem.mem_contents := 
        update_src_mem_content ((Mem.mem_access m2') # tb) j21' tb (Mem.mem_contents m) ((Mem.mem_contents m2') # tb);
      Mem.mem_access := 
        update_src_mem_access ((Mem.mem_access m2') # tb) j21' tb (Mem.mem_access m) ((Mem.mem_access m2') # tb);
      Mem.support := Mem.support m |}.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition step2_new_blocks : mem :=
  fold_left inject_new_block (Mem.support m2') (Mem.supext s1' m1).

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


Lemma content_perm_filter_norepet: forall l sb tb o vl pl,
    list_norepet (map fst l) ->
    content_perm_filter' l sb tb o = (vl, pl) ->
    list_norepet (map fst pl) /\ list_norepet (map fst vl).
Admitted.

Lemma content_perm_filter_none_aux1: forall l vl pl sb tb o1 o2,
    ~ In o1 (map fst l) ->
    content_perm_filter' l sb tb o2 = (vl, pl) ->
    ~ In o1 (map fst vl).
Proof.
  induction l; intros. simpl in H0. inv H0. auto.
  simpl in H. eapply Decidable.not_or in H.
  destruct a as (o1' & p). simpl in H.
  destruct H as (A & B).
  simpl in H0.
  destruct content_perm_filter' as (vl1 & pl1) eqn: F in H0.
  destruct (Mem.perm_dec m2' tb (o1' + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1' Max Writable); inv H0; simpl.
      * intro. destruct H; eauto.
        eapply IHl; eauto.
      * eauto.
    + inv H0. eauto.
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

Lemma copy_content_perm_old_block_result: forall sb vmap perm_map vmap' perm_map' o1,
    copy_content_perm_old_block sb vmap perm_map = (vmap', perm_map') ->
    Mem.perm m1 sb o1 Max Nonempty ->
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
                            (Mem.mem_access m2') # tb ## (o1 + o2)
                        | None => 
                            perm_map ## o1
                        end.
Proof.
  intros until o1. intros COPY PERM.
  unfold copy_content_perm_old_block, content_perm_filter in COPY.
  destruct (j12 sb) as [ [tb o2]|] eqn: INJSB.
  - simpl. 
    destruct content_perm_filter' as (vl & pl) eqn: F. inv COPY.
    exploit content_perm_filter_norepet; eauto.
    eapply Mem.fst_perm_any_norepet.
    eapply ZMap.elements_keys_norepet. intros (N1 & N2).
    exploit content_perm_filter_some; eauto.
    intros (A1 & A2).
    destruct (Mem.perm_dec m2' tb (o1 + o2) Cur Readable).
    + destruct (Mem.perm_dec m1 sb o1 Max Writable).
      * erewrite !Mem.setN'_inside; eauto. 
      * erewrite Mem.setN'_outside. 
        erewrite !Mem.setN'_inside; eauto.
        eapply content_perm_filter_none; eauto.
    + erewrite Mem.setN'_outside. 
      erewrite !Mem.setN'_inside; eauto.
      eapply content_perm_filter_none; eauto.
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
  (* Hypothesis MAXPERM1 : injp_max_perm_decrease m1 m1'. *)
  Hypothesis IMGIN1': inject_image_in j12' (Mem.support m2').
  (* Hypothesis DOMIN2': inject_dom_in j2' s2'. *)
  Hypothesis DOMIN1': inject_dom_in j12' s1'.
  Hypothesis INCRNEW1: inject_incr_newblock1 j12 j12' (Mem.support m2).
  Hypothesis ADDZERO: update_add_zero j12 j12'.
  (* Hypothesis ADDEXISTS: update_add_exists j1 j1' (compose_meminj j1' j2'). *)
  (* Hypothesis ADDSAME : update_add_same j2 j2' j1'. *)
  (* Hypothesis ADDBLOCK: update_add_block (Mem.support m2) s2' j1' j2'. *)

  Definition m1'1 := step2_new_blocks m1 m2 m2' s1' j12 j12' j21' SUPINCR1.
  Definition m1' := step3_old_blocks m1 m2 m2' s1' j12 j12' j21' SUPINCR1 (Mem.support m1) m1'1.
  
  Lemma m1'1_support : Mem.support m1'1 = s1'.
  Proof. unfold m1'1. Admitted.
  Lemma m1'_support : Mem.support m1' = s1'.
  Proof. Admitted.

  Lemma step3_old_blocks_sup_perm1: forall m b1 o1 b2 o2 k p,
        j12 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        Mem.support m = s1' ->
        Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' SUPINCR1 m b1) b1 o1 k p <-> Mem.perm m2' b2 o2 k p.
  Proof.
    intros. unfold inject_old_block.
    exploit DOMIN1. eauto. intros SUP1. 
    assert (SUP1' : sup_In b1 (Mem.support m)).
    { eapply SUPINCR1 in SUP1. rewrite H1. auto. }
    destruct Mem.sup_dec; try congruence.
    unfold copy_content_perm_old_block. 
    destruct (content_perm_filter m1 m2' j12 j21' b1) as (vl & pl) eqn: F.
    unfold Mem.perm. simpl. 
    setoid_rewrite NMap.gss.
    exploit (copy_content_perm_old_block_result m1 m2 m2' s1' j12 j12' j21' SUPINCR1 b1 ((Mem.mem_contents m) # b1) ((Mem.mem_access m) # b1)).
    unfold copy_content_perm_old_block. rewrite F. reflexivity.
    instantiate (1 := o1). auto. rewrite H. simpl.
    intros (A & B).
    rewrite B. replace (o1 + (o2 - o1)) with o2 by lia. reflexivity.
  Qed.
  
  Lemma step3_old_blocks_sup_perm2: forall m b b1 o1 k p,
      b <> b1 ->
      Mem.perm (inject_old_block m1 m2 m2' s1' j12 j12' j21' SUPINCR1 m b) b1 o1 k p <-> Mem.perm m b1 o1 k p.
  Proof.
    intros. unfold inject_old_block.
    destruct Mem.sup_dec.
    - destruct copy_content_perm_old_block.
      unfold Mem.perm. simpl.
      setoid_rewrite NMap.gso; try congruence.
      reflexivity.
    - reflexivity.
  Qed.      
    
  Lemma step3_old_blocks_sup_perm: forall bl m b1 o1 b2 o2 k p,
        j12 b1 = Some (b2, o2 - o1) ->
        Mem.perm m1 b1 o1 Max Nonempty ->
        In b1 bl ->
        Mem.support m = s1' ->
        Mem.perm (copy_old_sup' m1 m2 m2' s1' j12 j12' j21' SUPINCR1 bl m) b1 o1 k p <-> Mem.perm m2' b2 o2 k p.
  Proof.
    induction bl; intros.
    - inv H1.
    - simpl. destruct (eq_block b1 a).
      + subst a. 
        eapply step3_old_blocks_sup_perm1; eauto.
        rewrite <- H2. eapply copy_old_sup'_support.
      + destruct H1. congruence.
        etransitivity.
        eapply step3_old_blocks_sup_perm2; eauto.
        eauto.
  Qed.

  Lemma old_injected_block_perm: forall b1 o1 b2 o2 k p,
          j12 b1 = Some (b2, o2 - o1) ->
          Mem.perm m1 b1 o1 Max Nonempty ->
          Mem.perm m1' b1 o1 k p <->
          Mem.perm m2' b2 o2 k p.
  Proof.
    intros. unfold m1'.
    eapply step3_old_blocks_sup_perm; eauto.
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


  Lemma new_injected_block_perm: forall b1 o1 b2 o2 k p,
      j12 b1 = None ->      
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Max Nonempty ->
      (Mem.perm m1' b1 o1 k p <->
         Mem.perm m2' b2 o2 k p).
  Proof.
  Admitted.

  
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


  (* similar to copy_content_inject *)
  Lemma old_injected_block_content_inject : forall b1 o1 b2 o2,
      j12 b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->
      Mem.perm m1 b1 o1 Max Writable ->
      memval_inject j12' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
  Admitted.

  (* similar to step2_content_inject *)
  Lemma new_injected_block_content_inject : forall b1 o1 b2 o2,
      j12 b1 = None ->
      j12' b1 = Some (b2, o2 - o1) ->
      Mem.perm m1' b1 o1 Cur Readable ->     
      memval_inject j12' (mem_memval m1' b1 o1) (mem_memval m2' b2 o2).
  Proof.
  Admitted.


  Lemma MAXPERM1: injp_max_perm_decrease m1 m1'.
  Admitted.


  Lemma UNC1: Mem.unchanged_on (loc_unmapped j12) m1 m1'.
  Admitted.

  Lemma UNC2: Mem.unchanged_on (loc_out_of_reach j12 m1) m2 m2'.
  Admitted.

  Lemma ROUNC1: Mem.ro_unchanged m1 m1'.
  Admitted.

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


(* Incoming related memorys m1 and m2 that are related by injp, and
module accessibility is an unary relation (the mvw_acc), to construct
the outgoing source memory m1' and the injp_acc relation *)
Lemma mem_protect_injp: forall m1 m2 j (INJ: Mem.inject j m1 m2),
  exists invj (Hm: memory_valid (meminj_inv_memfp invj) m2),   
    let mfp := meminj_inv_memfp invj in
    (forall mfp' m2' Hm',
        mvw_acc (mvw mfp m2 Hm) (mvw mfp' m2' Hm') ->
        exists (invj': meminj_inv) j' m1' INJ',
          (** TODO: relation between invj', j' and mfp', which is used
          to establish value injection in the new j' *)
          injp_acc (injpw j m1 m2 INJ) (injpw j' m1' m2' INJ')).
Proof.
  intros.
  exists (inv_inj j m1), (inject_implies_valid_memory m1 m2 j INJ).
  simpl. 
  intros mfp' m2' Hm' MACC.
  set (invj := inv_inj j m1) in *.
  (* construction of injection, inverse injection and the fresh support for m1 *)
  destruct (update_meminj_fp j invj m1 m2 m2' mfp') as ((j' & invj') & s1').
  assert (SUPINCL1: Mem.sup_include (Mem.support m1) s1'). admit.
  set (m1' := m1' m1 m2 m2' j j' invj' s1' SUPINCL1).
  set (INJ12' := INJ12' m1 m2 m2' j j' invj' s1' SUPINCL1).
  exists invj', j', m1', INJ12'. inv MACC.
  (* injp_acc *)
  econstructor; eauto.
  eapply ROUNC1.
  eapply MAXPERM1.
  eapply UNC1. eapply UNC2.
