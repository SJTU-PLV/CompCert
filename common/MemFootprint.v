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
Require Import InjectFootprint Memory.
Require Import Globalenvs.

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

(** Construction of inverse injection and source memory (the same
steps as m2'1 and m2' in Injectfootprint) *)

Definition meminj_inv_add (invj: meminj_inv) (tb: block) (lo hi: Z) (sb: block) (slo: Z) : meminj_inv :=
  fun b ofs => 
    if eq_block b tb && zle lo ofs && zlt ofs hi then
      Some (sb, slo + hi - lo)
    else
      invj b ofs.

(* update the injection with the old injection and the new footprint,
and also returns the updated support *)
Fixpoint update_meminj_fp (intvs: list (block * Z * Z)) (j: meminj) (invj: meminj_inv) (s: sup) : meminj * meminj_inv * sup :=
  match intvs with
  | nil => (j, invj, s)
  | (tb, lo, hi) :: tl =>
      let sb := Mem.fresh_block s in
      update_meminj_fp tl (meminj_add j sb (tb, lo)) (meminj_inv_add invj tb lo hi sb 0) (sup_incr s)
  end.

Require Import Mergesort.

Module ZOrder.
  Definition t := Z.
  Definition leb := Z.leb.
  Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
  Proof.
    intros x y; case (Zle_bool_total x y); auto.
  Qed.

End ZOrder.

Module ZSort := Mergesort.Sort(ZOrder).

Require Import ZArith List.
Import ListNotations.

(* We’ll need a function to extend the current interval if the next
element is consecutive, or start a new interval otherwise. *)
Fixpoint intervals_aux (cur : option (Z * Z)) (l : list Z) : list (Z * Z) :=
  match l, cur with
  | [], None => []
  | [], Some (a,b) => [(a,b)]
  | x :: xs, None => intervals_aux (Some (x, Z.succ x)) xs
  | x :: xs, Some (a,b) =>
      if Z.eqb x b then
        (* extend the current interval *)
        intervals_aux (Some (a, Z.succ x)) xs
      else
        (* close the current interval and start a new one *)
        (a,b) :: intervals_aux (Some (x, Z.succ x)) xs
  end.

Definition intervals (l : list Z) : list (Z*Z) :=
  intervals_aux None l.


Definition loc_in_reach_intervals_block (b: block) (mfp: Z -> bool) (locs: list Z) : list (block * Z * Z) :=
  let in_reach_locs := filter mfp locs in
  let sorted_locs := ZSort.sort in_reach_locs in
  map (fun '(lo, hi) => (b, lo, hi)) (intervals sorted_locs).

Definition loc_in_reach_intervals (s: list block) (mfp: memfp) (m: mem) : list (block * Z * Z) :=
  concat (map (fun b => loc_in_reach_intervals_block b (mfp b)
                       (* filter the locations that at least have Nonempty permission *)
                       (map fst (Mem.perm_elements_any (ZMap.elements (NMap.get _ b m.(Mem.mem_access))))))
                       s).

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

(* merge two permission (choose the smaller one) *)

Definition join_perm (p1 p2: permission) : permission :=
  match p1, p2 with
  | Nonempty, _
  | _, Nonempty => Nonempty
  | Readable, _
  | _, Readable => Readable
  | Writable, _
  | _, Writable => Writable
  | _, _ => Freeable
  end.

Definition join_option_perm (op1 op2: option permission) : option permission :=
  match op1, op2 with
  | None, _
  | _, None => None
  | Some p1, Some p2 => Some (join_perm p1 p2)
  end.

(* We cannot directly use the permission in the target memory as that
in the source, because it may deviate from the permission in the old
source memory. And also we cannot use the original permission in the
old source memory in the new memory, as it may break the injection
(imagine that the orignal permission is Writable, but the new target
memory has Readable as the new permission). Therefore, we use this
join operation to choose a righ permission. *)
Definition join_memperm (perm1 perm2: Mem.memperm) : Mem.memperm :=
  fun k => join_option_perm (perm1 k) (perm2 k).

(* perms: the source permission *)
Fixpoint content_filter' (perms : list (Z * Mem.memperm)) (sb: block): list (Z * memval) :=
  match perms with
  | nil => nil
  | (o1, p) :: tl =>
      (* only care old injection? *)
      match j12 sb with
      | Some (tb, o2) =>
          let joined_perm := join_memperm p ((Mem.mem_access m2') # tb ## (o1 + o2)%Z) in
          (* if the original permission of this location is Readable *)
          if Mem.perm_order'_dec (joined_perm Cur) Readable then
            if Mem.perm_dec m1 sb o1 Max Writable then
              (o1, memval_map_inv j21' ((Mem.mem_contents m2') # tb ## (o1 + o2)%Z))
                :: content_filter' tl sb 
            else content_filter' tl sb 
          else content_filter' tl sb 
      | None => content_filter' tl sb 
      end
  end.

Definition content_filter (sb : block) :=
  let elements := ZMap.elements ((Mem.mem_access m1) # sb) in
  content_filter' elements sb.

(* update contents of all positions with nonempty permission in block b_2 *)
Definition copy_content_old_block (sb: block) (vmap: ZMap.t memval) :=
  let elements := content_filter sb in
  Mem.setN' elements vmap.

Program Definition inject_old_block (m: mem) (sb: block) := 
  if j12' sb then
    if Mem.sup_dec sb (Mem.support m) then
      {| Mem.mem_contents := Mem.pmap_update sb 
                               (copy_content_old_block sb)
                               (Mem.mem_contents m);
        Mem.mem_access := Mem.pmap_update sb 
                               (copy_perm_old_block sb)
                               (Mem.mem_perm m);
        Mem.support := Mem.support m |}
