(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

Require Import Recdef.
Require Import Zwf.
Require Import Axioms Coqlib Errors Maps AST Linking.
Require Import Integers Floats Values Memory.

Declare Scope pair_scope.
Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

(** Auxiliary function for initialization of global variables. *)

Function store_zeros (m: mem) (b: block) (p: Z) (n: Z) {wf (Zwf 0) n}: option mem :=
  if zle n 0 then Some m else
    match Mem.store Mint8unsigned m b p Vzero with
    | Some m' => store_zeros m' b (p + 1) (n - 1)
    | None => None
    end.
Proof.
  intros. red. lia.
  apply Zwf_well_founded.

Qed.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable V: Type.  (**r The type of information attached to variables *)

(** The type of symbol tables. *)

Record symtbl: Type := mkstbl {
  genv_public: list ident;              (**r which symbol names are public *)
  genv_symb: PTree.t block;             (**r mapping symbol -> block *)
  genv_info: NMap.t (option (globdef unit unit));
  genv_sup: sup;                     (**r next symbol pointer *)
  genv_symb_range: forall id b, PTree.get id genv_symb = Some b -> sup_In b genv_sup;
  genv_info_range: forall b g, NMap.get _ b genv_info = Some g -> sup_In b genv_sup;
  genv_vars_inj: forall id1 id2 b,
    PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2
}.

(** The type of global environments. *)

Record t: Type := mkgenv {
  to_senv :> symtbl;
  genv_defs: NMap.t (option (globdef F V));  (**r mapping block -> definition *)
  genv_defs_range: forall b g, NMap.get _ b genv_defs = Some g -> sup_In b (genv_sup to_senv);
}.

(** ** Lookup functions *)

(** [find_symbol ge id] returns the block associated with the given name, if any *)

Definition find_symbol (ge: symtbl) (id: ident) : option block :=
  PTree.get id ge.(genv_symb).

Definition has_symbol (ge: symtbl) (id: ident) : Prop :=
  exists b, find_symbol ge id = Some b.

(** [symbol_address ge id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
  to [id]. *)

Definition symbol_address (ge: symtbl) (id: ident) (ofs: ptrofs) : val :=
  match find_symbol ge id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

(** [public_symbol ge id] says whether the name [id] is public and defined. *)

Definition public_symbol (ge: symtbl) (id: ident) : bool :=
  match find_symbol ge id with
  | None => false
  | Some _ => In_dec ident_eq id ge.(genv_public)
  end.

(** [find_info ge b] returns the symbol information associated with the given address. *)

Definition find_info (ge: symtbl) (b: block) : option (globdef unit unit) :=
  NMap.get _ b ge.(genv_info).

(** [find_def ge b] returns the global definition associated with the given address. *)

Definition find_def (ge: t) (b: block) : option (globdef F V) :=
  NMap.get _ b ge.(genv_defs).

(** [find_funct_ptr ge b] returns the function description associated with
    the given address. *)

Definition find_funct_ptr (ge: t) (b: block) : option F :=
  match find_def ge b with Some (Gfun f) => Some f | _ => None end.

(** [find_funct] is similar to [find_funct_ptr], but the function address
    is given as a value, which must be a pointer with offset 0. *)

Definition find_funct (ge: t) (v: val) : option F :=
  match v with
  | Vptr b ofs => if Ptrofs.eq_dec ofs Ptrofs.zero then find_funct_ptr ge b else None
  | _ => None
  end.

(** [invert_symbol ge b] returns the name associated with the given block, if any *)

Definition invert_symbol (ge: symtbl) (b: block) : option ident :=
  PTree.fold
    (fun res id b' => if eq_block b b' then Some id else res)
    ge.(genv_symb) None.

(** [find_var_info ge b] returns the information attached to the variable
   at address [b]. *)

Definition find_var_info (ge: symtbl) (b: block) : option (globvar unit) :=
  match find_info ge b with Some (Gvar v) => Some v | _ => None end.

(** [block_is_volatile ge b] returns [true] if [b] points to a global variable
  of volatile type, [false] otherwise. *)

Definition block_is_volatile (ge: symtbl) (b: block) : bool :=
  match NMap.get _ b ge.(genv_info) with
  | Some (Gvar gv) => gv.(gvar_volatile)
  | _ => false
  end.

(** [is_internal] identifies pointers to internal functions *)

Definition is_internal `{Fii: FundefIsInternal F} (ge: t) (v: val) :=
  match find_funct ge v with
    | Some fd => fundef_is_internal fd
    | None => false
  end.

(** ** Constructing symbol tables *)

Program Definition add_global (ge: symtbl) (idg: ident * globdef unit unit) : symtbl :=
  @mkstbl
    ge.(genv_public)
    (PTree.set idg#1 (fresh_block ge.(genv_sup)) ge.(genv_symb))
    (NMap.set _ (fresh_block ge.(genv_sup)) (Some (idg#2)) ge.(genv_info))
    (sup_incr (ge.(genv_sup)))
    _ _ _.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. destruct (peq id i). inv H. apply Mem.sup_incr_in1.
  apply Mem.sup_incr_in2. eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite NMap.gsspec in H. destruct (NMap.elt_eq b (fresh_block genv_sup0)).
  inv H. apply Mem.sup_incr_in1. apply Mem.sup_incr_in2. eauto.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H. rewrite PTree.gsspec in H0.
  destruct (peq id1 i); destruct (peq id2 i).
  congruence.
  inv H. apply genv_symb_range0 in H0. apply freshness in H0. destruct H0.
  inv H. inv H0. apply genv_symb_range0 in H2. apply freshness in H2. destruct H2.
  eauto.
Qed.

Definition add_globals (ge: symtbl) (gl: list (ident * globdef unit unit)) : symtbl :=
  List.fold_left add_global gl ge.

Lemma add_globals_app:
  forall gl2 gl1 ge,
  add_globals ge (gl1 ++ gl2) = add_globals (add_globals ge gl1) gl2.
Proof.
  intros. apply fold_left_app.
Qed.

Program Definition empty_stbl (pub: list ident): symtbl :=
  @mkstbl pub (PTree.empty _) (NMap.init _ None) sup_empty _ _ _.

Definition symboltbl (p: program unit unit) :=
  add_globals (empty_stbl p.(prog_public)) p.(prog_defs).

(** Proof principles *)

Section GLOBALENV_PRINCIPLES.

Variable P: symtbl -> Prop.

Lemma add_globals_preserves:
  forall gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> P (add_global ge (id, g))) ->
  P ge -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  auto.
  destruct a. apply IHgl; auto.
Qed.

Lemma add_globals_ensures:
  forall id g gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> P (add_global ge (id, g))) ->
  (forall ge, P (add_global ge (id, g))) ->
  In (id, g) gl -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  contradiction.
  destruct H1. subst a. apply add_globals_preserves; auto.
  apply IHgl; auto.
Qed.

Lemma add_globals_unique_preserves:
  forall id gl ge,
  (forall ge id1 g, P ge -> In (id1, g) gl -> id1 <> id -> P (add_global ge (id1, g))) ->
  ~In id (map fst gl) -> P ge -> P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  auto.
  destruct a. apply IHgl; auto.
Qed.

Lemma add_globals_unique_ensures:
  forall gl1 id g gl2 ge,
  (forall ge id1 g1, P ge -> In (id1, g1) gl2 -> id1 <> id -> P (add_global ge (id1, g1))) ->
  (forall ge, P (add_global ge (id, g))) ->
  ~In id (map fst gl2) -> P (add_globals ge (gl1 ++ (id, g) :: gl2)).
Proof.
  intros. rewrite add_globals_app. simpl. apply add_globals_unique_preserves with id; auto.
Qed.

Remark in_norepet_unique:
  forall id g (gl: list (ident * globdef unit unit)),
  In (id, g) gl -> list_norepet (map fst gl) ->
  exists gl1 gl2, gl = gl1 ++ (id, g) :: gl2 /\ ~In id (map fst gl2).
Proof.
  induction gl as [|[id1 g1] gl]; simpl; intros.
  contradiction.
  inv H0. destruct H.
  inv H. exists nil, gl. auto.
  exploit IHgl; eauto. intros (gl1 & gl2 & X & Y).
  exists ((id1, g1) :: gl1), gl2; split; auto. rewrite X; auto.
Qed.

Lemma add_globals_norepet_ensures:
  forall id g gl ge,
  (forall ge id1 g1, P ge -> In (id1, g1) gl -> id1 <> id -> P (add_global ge (id1, g1))) ->
  (forall ge, P (add_global ge (id, g))) ->
  In (id, g) gl -> list_norepet (map fst gl) -> P (add_globals ge gl).
Proof.
  intros. exploit in_norepet_unique; eauto. intros (gl1 & gl2 & X & Y).
  subst gl. apply add_globals_unique_ensures; auto. intros. eapply H; eauto.
  apply in_or_app; simpl; auto.
Qed.

End GLOBALENV_PRINCIPLES.

(** ** Constructing global environments *)

Variable se: symtbl.

Definition add_globdef
  (defs: NMap.t (option (globdef F V))) (id: ident) (g: globdef F V) :=
  match (genv_symb se) ! id with
    | Some b => NMap.set _ b (Some g) defs
    | None => defs
  end.

Program Definition globalenv (p: program F V): t :=
  mkgenv se (PTree.fold add_globdef (prog_defmap p) (NMap.init _ None)) _.
Next Obligation.
  revert H. rewrite PTree.fold_spec.
  pattern (PTree.elements (prog_defmap p)). apply rev_ind.
  - simpl. unfold NMap.get. rewrite NMap.gi.  discriminate.
  - intros idg defs IH. rewrite fold_left_app. simpl. unfold add_globdef at 1.
    destruct ((genv_symb se) ! (idg#1)) eqn:H; auto.
    apply genv_symb_range in H.
    rewrite NMap.gsspec. destruct eq_block; subst; eauto.
Qed.

(** ** Compatibility between symbol tables and skeletons *)

Definition valid_for (p: program unit unit) se :=
  forall id g, (prog_defmap p) ! id = Some g ->
  exists b g',
    find_symbol se id = Some b /\
    find_info se b = Some g' /\
    linkorder g g'.

Lemma valid_for_linkorder (p1 p2: program unit unit):
  linkorder p1 p2 ->
  valid_for p2 se ->
  valid_for p1 se.
Proof.
  intros (_ & _ & Hp) Hp2.
  intros id g Hg.
  edestruct Hp as (g' & Hg' & Hgg' & _); eauto.
  edestruct Hp2 as (b & g'' & Hb & Hbg' & ?); eauto.
  exists b, g''. intuition auto.
  eapply linkorder_trans; eauto.
Qed.

(** ** Properties of the operations over global environments *)

Theorem public_symbol_exists:
  forall ge id, public_symbol ge id = true -> exists b, find_symbol ge id = Some b.
Proof.
  unfold public_symbol; intros. destruct (find_symbol ge id) as [b|].
  exists b; auto.
  discriminate.
Qed.

Theorem shift_symbol_address:
  forall ge id ofs delta,
  symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta.
Proof.
  intros. unfold symbol_address, Val.offset_ptr. destruct (find_symbol ge id); auto.
Qed.

Theorem shift_symbol_address_32:
  forall ge id ofs n,
  Archi.ptr64 = false ->
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (symbol_address ge id ofs) (Vint n).
Proof.
  intros. unfold symbol_address. destruct (find_symbol ge id).
- unfold Val.add. rewrite H. auto.
- auto.
Qed.

Theorem shift_symbol_address_64:
  forall ge id ofs n,
  Archi.ptr64 = true ->
  symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (symbol_address ge id ofs) (Vlong n).
Proof.
  intros. unfold symbol_address. destruct (find_symbol ge id).
- unfold Val.addl. rewrite H. auto.
- auto.
Qed.

Theorem find_funct_inv:
  forall ge v f,
  find_funct ge v = Some f -> exists b, v = Vptr b Ptrofs.zero.
Proof.
  intros until f; unfold find_funct.
  destruct v; try congruence.
  destruct (Ptrofs.eq_dec i Ptrofs.zero); try congruence.
  intros. exists b; congruence.
Qed.

Theorem find_funct_find_funct_ptr:
  forall ge b,
  find_funct ge (Vptr b Ptrofs.zero) = find_funct_ptr ge b.
Proof.
  intros; simpl. apply dec_eq_true.
Qed.

Theorem find_funct_ptr_iff:
  forall ge b f, find_funct_ptr ge b = Some f <-> find_def ge b = Some (Gfun f).
Proof.
  intros. unfold find_funct_ptr. destruct (find_def ge b) as [[f1|v1]|]; intuition congruence.
Qed.

Theorem find_var_info_iff:
  forall ge b v, find_var_info ge b = Some v <-> find_info ge b = Some (Gvar v).
Proof.
  intros. unfold find_var_info. destruct (find_info ge b) as [[f1|v1]|]; intuition congruence.
Qed.

Theorem find_symbol_injective:
  forall ge id1 id2 b,
  find_symbol ge id1 = Some b ->
  find_symbol ge id2 = Some b ->
  id1 = id2.
Proof.
  apply genv_vars_inj.
Qed.

Theorem global_addresses_distinct:
  forall ge id1 id2 b1 b2,
  id1 <> id2 ->
  find_symbol ge id1 = Some b1 ->
  find_symbol ge id2 = Some b2 ->
  b1 <> b2.
Proof.
  intros. red; intros; subst. elim H. destruct ge. eauto.
Qed.

Theorem invert_find_symbol:
  forall ge id b,
  invert_symbol ge b = Some id -> find_symbol ge id = Some b.
Proof.
  intros until b; unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  congruence.
  intros. destruct (eq_block b v). inv H2. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id k).
  subst. assert (m!k = Some b) by auto. congruence.
  auto.
Qed.

Theorem find_invert_symbol:
  forall ge id b,
  find_symbol ge id = Some b -> invert_symbol ge b = Some id.
Proof.
  intros until b.
  assert (find_symbol ge id = Some b -> exists id', invert_symbol ge b = Some id').
  unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  rewrite PTree.gempty; congruence.
  intros. destruct (eq_block b v). exists k; auto.
  rewrite PTree.gsspec in H2. destruct (peq id k).
  inv H2. congruence. auto.

  intros; exploit H; eauto. intros [id' A].
  assert (id = id'). eapply genv_vars_inj; eauto. apply invert_find_symbol; auto.
  congruence.
Qed.

(** ** Properties of [symboltbl] *)
(* clean
Definition advance_next (gl: list (ident * globdef unit unit)) (x: positive) :=
  List.fold_left (fun n g => Pos.succ n) gl x.
*)

Definition advance_next (gl: list (ident * globdef unit unit)) (s: sup) :=
  List.fold_left (fun s g => sup_incr s) gl s.

Remark genv_next_add_globals:
  forall gl ge,
  genv_sup (add_globals ge gl) = advance_next gl (genv_sup ge).
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl. auto.
Qed.

Remark genv_public_add_globals:
  forall gl ge,
  genv_public (add_globals ge gl) = genv_public ge.
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl; auto.
Qed.

Theorem globalenv_public:
  forall p, genv_public (symboltbl p) = prog_public p.
Proof.
  unfold symboltbl; intros. rewrite genv_public_add_globals. auto.
Qed.

Theorem block_is_volatile_below:
  forall ge b, block_is_volatile ge b = true ->  sup_In b ge.(genv_sup).
Proof.
  unfold block_is_volatile; intros.
  destruct NMap.get as [[|gv]|] eqn:FV; try discriminate.
  eapply genv_info_range; eauto.
Qed.

Lemma find_info_symbol p id gd:
  (prog_defmap p) ! id = Some gd <->
  exists b,
    find_symbol (symboltbl p) id = Some b /\
    find_info (symboltbl p) b = Some gd.
Proof.
  unfold prog_defmap, symboltbl, add_globals, PTree_Properties.of_list.
  generalize (prog_public p), (prog_defs p). clear. intros pub.
  apply rev_ind.
  - unfold empty_stbl, find_symbol, find_info. cbn. split.
    + rewrite !PTree.gempty. discriminate.
    + intros (? & ? & ?). rewrite !PTree.gempty in *. discriminate.
  - intros [i g] defs IHdefs.
    rewrite !fold_left_app. cbn.
    unfold find_symbol, find_info in *. cbn.
    destruct (peq id i).
    + subst. rewrite !PTree.gss. split.
      * inversion 1; subst. eexists. split; eauto. rewrite NMap.gss. auto.
      * intros (b & Hb & ?). inv Hb. rewrite NMap.gss in *. auto.
    + rewrite PTree.gso by auto. rewrite IHdefs. split.
      * intros (b & Hb & ?). eexists. rewrite PTree.gso by auto. split; eauto.
        rewrite NMap.gso; eauto. apply genv_symb_range in Hb.
        intro. subst. exploit freshness; eauto.
      * intros (b & Hb & ?). rewrite PTree.gso in * by auto.
        eexists. split; eauto. rewrite NMap.gso in *; auto.
        apply genv_symb_range in Hb.
        intro. subst. exploit freshness; eauto.
Qed.

(** ** Properties of [globalenv] *)

(** This characterization of [globalenv] is less computationally
  efficient than the definition but easier to reason about. *)

Lemma find_def_spec p b:
  find_def (globalenv p) b =
  match invert_symbol se b with
    | Some id => (prog_defmap p) ! id
    | None => None
  end.
Proof.
  unfold find_def. cbn.
  eapply PTree_Properties.fold_rec.
  - intros m m' a Hm. destruct invert_symbol; congruence.
  - destruct invert_symbol; rewrite !NMap.gi; auto.
  - intros defmap defs id gd Hprog_id Hdefmap_id IH. unfold add_globdef.
    destruct invert_symbol as [id'|] eqn:Hb.
    + apply invert_find_symbol in Hb. unfold find_symbol in Hb.
      destruct (peq id' id).
      * subst. rewrite Hb, !PTree.gss. rewrite NMap.gss. auto.
      * rewrite !PTree.gso by auto.
        destruct (genv_symb se) ! id as [b'|] eqn:Hb'; auto.
        rewrite NMap.gso; auto. intro. subst. eauto using genv_vars_inj.
    + destruct (genv_symb se) ! id as [b'|] eqn:Hb'; auto.
      apply find_invert_symbol in Hb'. rewrite NMap.gso; congruence.
Qed.

Theorem find_funct_prop:
  forall p v f (P: F -> Prop),
  (forall id f, In (id, Gfun f) (prog_defs p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros p v f P H. unfold find_funct, find_funct_ptr.
  destruct v; try congruence. rewrite find_def_spec.
  destruct Ptrofs.eq_dec; try congruence. subst.
  destruct invert_symbol; try congruence.
  destruct (prog_defmap p) ! i as [[fd|]|] eqn:Hgd; try congruence.
  inversion 1; subst.
  eauto using in_prog_defmap.
Qed.

Theorem find_def_symbol:
  forall p id g, valid_for (erase_program p) se ->
  (prog_defmap p)!id = Some g <-> exists b, find_symbol (globalenv p) id = Some b /\ find_def (globalenv p) b = Some g.
Proof.
  intros p id g Hse. split.
  - intros Hg. edestruct Hse as (b & g' & Hb & Hg' & LO); eauto.
    rewrite erase_program_defmap. erewrite Hg. reflexivity.
    exists b. split. assumption.
    rewrite find_def_spec. apply find_invert_symbol in Hb. rewrite Hb. auto.
  - intros (b & Hb & Hg). rewrite find_def_spec in Hg.
    destruct invert_symbol eqn:Hb'; try congruence. apply invert_find_symbol in Hb'.
    assert (i = id) by (eapply genv_vars_inj; eauto). congruence.
Qed.

(** * Construction of the initial memory state *)

Section INITMEM.

Variable ge: symtbl.

Definition store_init_data (m: mem) (b: block) (p: Z) (id: init_data) : option mem :=
  match id with
  | Init_int8 n => Mem.store Mint8unsigned m b p (Vint n)
  | Init_int16 n => Mem.store Mint16unsigned m b p (Vint n)
  | Init_int32 n => Mem.store Mint32 m b p (Vint n)
  | Init_int64 n => Mem.store Mint64 m b p (Vlong n)
  | Init_float32 n => Mem.store Mfloat32 m b p (Vsingle n)
  | Init_float64 n => Mem.store Mfloat64 m b p (Vfloat n)
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | None => None
      | Some b' => Mem.store Mptr m b p (Vptr b' ofs)
      end
  | Init_space n => Some m
  end.

Fixpoint store_init_data_list (m: mem) (b: block) (p: Z) (idl: list init_data)
                              {struct idl}: option mem :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m b p id with
      | None => None
      | Some m' => store_init_data_list m' b (p + init_data_size id) idl'
      end
  end.

Definition perm_globvar (gv: globvar unit) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable.

Definition alloc_global (m: mem) (idg: ident * globdef unit unit): option mem :=
  match idg with
  | (id, Gfun f) =>
      let (m1, b) := Mem.alloc m 0 1 in
      Mem.drop_perm m1 b 0 1 Nonempty
  | (id, Gvar v) =>
      let init := v.(gvar_init) in
      let sz := init_data_list_size init in
      let (m1, b) := Mem.alloc m 0 sz in
      match store_zeros m1 b 0 sz with
      | None => None
      | Some m2 =>
          match store_init_data_list m2 b 0 init with
          | None => None
          | Some m3 => Mem.drop_perm m3 b 0 sz (perm_globvar v)
          end
      end
  end.

Fixpoint alloc_globals (m: mem) (gl: list (ident * globdef unit unit))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Lemma alloc_globals_app : forall gl1 gl2 m m1,
  alloc_globals m gl1 = Some m1 ->
  alloc_globals m1 gl2 = alloc_globals m (gl1 ++ gl2).
Proof.
  induction gl1.
  simpl. intros.  inversion H; subst. auto.
  simpl. intros. destruct (alloc_global m a); eauto. inversion H.
Qed.

(** Next-block properties *)

Remark store_zeros_nextblock:
  forall m b p n m', store_zeros m b p n = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H; auto.
  rewrite IHo; eauto with mem.
  congruence.
Qed.

Remark store_init_data_list_nextblock:
  forall idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a); try congruence. intros.
  transitivity (Mem.nextblock m0). eauto.
  destruct a; simpl in H; try (eapply Mem.nextblock_store; eauto; fail).
  congruence.
  destruct (find_symbol ge i); try congruence. eapply Mem.nextblock_store; eauto.
Qed.

Remark store_zeros_support:
  forall m b p n m', store_zeros m b p n = Some m' -> Mem.support m' = Mem.support m.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H; auto.
  apply Mem.support_store in e0.
  rewrite <- e0. apply IHo. auto.
  congruence.
Qed.

Remark store_init_data_list_support:
  forall idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  Mem.support m' = Mem.support m.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a); try congruence. intros.
  transitivity (Mem.support m0). eauto.
  destruct a; simpl in H; try (eapply Mem.support_store; eauto; fail).
  congruence.
  destruct (find_symbol ge i); try congruence. eapply Mem.support_store; eauto.
Qed.

Remark alloc_global_support:
  forall g m m',
    alloc_global m g = Some m' ->
    Mem.support m' = sup_incr (Mem.support m).
Proof.
  unfold alloc_global. intros.
  destruct g as [id [f|v]].
  - destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
    erewrite Mem.support_drop; eauto. erewrite Mem.support_alloc;eauto.
  - set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  erewrite Mem.support_drop; eauto.
  erewrite store_init_data_list_support; eauto.
  erewrite store_zeros_support; eauto.
  erewrite Mem.support_alloc; eauto.
Qed.

Remark alloc_globals_support:
  forall gl m m',
  alloc_globals m gl = Some m' ->
  Mem.support m' = advance_next gl (Mem.support m).
Proof.
  induction gl; simpl; intros.
  congruence.
  destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite IHgl; eauto. erewrite alloc_global_support;eauto.
Qed.

(** Permissions *)

Remark store_zeros_perm:
  forall k prm b' q m b p n m',
  store_zeros m b p n = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H; tauto.
  destruct (IHo _ H); intros. split; eauto with mem.
  congruence.
Qed.

Remark store_init_data_perm:
  forall k prm b' q i b m p m',
  store_init_data m b p i = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros.
  assert (forall chunk v,
          Mem.store chunk m b p v = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem.
  destruct i; simpl in H; eauto.
  inv H; tauto.
  destruct (find_symbol ge i); try discriminate. eauto.
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl b m p m',
  store_init_data_list m b p idl = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q k prm).
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.

Remark alloc_global_perm:
  forall k prm b' q idg m m',
  alloc_global m idg = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto. eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto. eapply Mem.perm_drop_4; eauto.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto.
  erewrite <- store_init_data_list_perm; [idtac|eauto].
  erewrite <- store_zeros_perm; [idtac|eauto].
  eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto.
  erewrite store_zeros_perm; [idtac|eauto].
  erewrite store_init_data_list_perm; [idtac|eauto].
  eapply Mem.perm_drop_4; eauto.
Qed.

Remark alloc_globals_perm:
  forall k prm b' q gl m m',
  alloc_globals m gl = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction gl.
  simpl; intros. inv H. tauto.
  simpl; intros. destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite alloc_global_perm; eauto. eapply IHgl; eauto.
  unfold Mem.valid_block in *. erewrite alloc_global_support; eauto.
  apply Mem.sup_incr_in2. auto.
Qed.

(** Data preservation properties *)

Remark store_zeros_unchanged:
  forall (P: block -> Z -> Prop) m b p n m',
  store_zeros m b p n = Some m' ->
  (forall i, p <= i < p + n -> ~ P b i) ->
  Mem.unchanged_on P m m'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
- inv H; apply Mem.unchanged_on_refl.
- apply Mem.unchanged_on_trans with m'.
+ eapply Mem.store_unchanged_on; eauto. simpl. intros. apply H0. lia.
+ apply IHo; auto. intros; apply H0; lia.
- discriminate.
Qed.

Remark store_init_data_unchanged:
  forall (P: block -> Z -> Prop) b i m p m',
  store_init_data m b p i = Some m' ->
  (forall ofs, p <= ofs < p + init_data_size i -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct i; simpl in *;
  try (eapply Mem.store_unchanged_on; eauto; fail).
  inv H; apply Mem.unchanged_on_refl.
  destruct (find_symbol ge i); try congruence.
  eapply Mem.store_unchanged_on; eauto;
  unfold Mptr; destruct Archi.ptr64; eauto.
Qed.

Remark store_init_data_list_unchanged:
  forall (P: block -> Z -> Prop) b il m p m',
  store_init_data_list m b p il = Some m' ->
  (forall ofs, p <= ofs -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  induction il; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  apply Mem.unchanged_on_trans with m1.
  eapply store_init_data_unchanged; eauto. intros; apply H0; tauto.
  eapply IHil; eauto. intros; apply H0. generalize (init_data_size_pos a); lia.
Qed.

(** Properties related to [loadbytes] *)

Definition readbytes_as_zero (m: mem) (b: block) (ofs len: Z) : Prop :=
  forall p n,
  ofs <= p -> p + Z.of_nat n <= ofs + len ->
  Mem.loadbytes m b p (Z.of_nat n) = Some (List.repeat (Byte Byte.zero) n).

Lemma store_zeros_loadbytes:
  forall m b p n m',
  store_zeros m b p n = Some m' ->
  readbytes_as_zero m' b p n.
Proof.
  intros until n; functional induction (store_zeros m b p n); red; intros.
- destruct n0. simpl. apply Mem.loadbytes_empty. lia.
  rewrite Nat2Z.inj_succ in H1. extlia.
- destruct (zeq p0 p).
  + subst p0. destruct n0. simpl. apply Mem.loadbytes_empty. lia.
    rewrite Nat2Z.inj_succ in H1. rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n0)) with (1 + Z.of_nat n0) by lia.
    change (List.repeat (Byte Byte.zero) (S n0))
      with ((Byte Byte.zero :: nil) ++ List.repeat (Byte Byte.zero) n0).
    apply Mem.loadbytes_concat.
    eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 = p).
    eapply store_zeros_unchanged; eauto. intros; lia.
    intros; lia.
    replace (Byte Byte.zero :: nil) with (encode_val Mint8unsigned Vzero).
    change 1 with (size_chunk Mint8unsigned).
    eapply Mem.loadbytes_store_same; eauto.
    unfold encode_val; unfold encode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity.
    eapply IHo; eauto. lia. lia. lia. lia.
  + eapply IHo; eauto. lia. lia.
- discriminate.
Qed.

Definition bytes_of_init_data (i: init_data): list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | Init_space n => List.repeat (Byte Byte.zero) (Z.to_nat n)
  | Init_addrof id ofs =>
      match find_symbol ge id with
      | Some b => inj_value (if Archi.ptr64 then Q64 else Q32) (Vptr b ofs)
      | None   => List.repeat Undef (if Archi.ptr64 then 8%nat else 4%nat)
      end
  end.

Remark init_data_size_addrof:
  forall id ofs, init_data_size (Init_addrof id ofs) = size_chunk Mptr.
Proof.
  intros. unfold Mptr. simpl. destruct Archi.ptr64; auto.
Qed.

Lemma store_init_data_loadbytes:
  forall m b p i m',
  store_init_data m b p i = Some m' ->
  readbytes_as_zero m b p (init_data_size i) ->
  Mem.loadbytes m' b p (init_data_size i) = Some (bytes_of_init_data i).
Proof.
  intros; destruct i; simpl in H; try apply (Mem.loadbytes_store_same _ _ _ _ _ _ H).
- inv H. simpl.
  assert (EQ: Z.of_nat (Z.to_nat z) = Z.max z 0).
  { destruct (zle 0 z). rewrite Z2Nat.id; extlia. destruct z; try discriminate. simpl. extlia. }
  rewrite <- EQ. apply H0. lia. simpl. lia.
- rewrite init_data_size_addrof. simpl.
  destruct (find_symbol ge i) as [b'|]; try discriminate.
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ H).
  unfold encode_val, Mptr; destruct Archi.ptr64; reflexivity.
Qed.

Fixpoint bytes_of_init_data_list (il: list init_data): list memval :=
  match il with
  | nil => nil
  | i :: il => bytes_of_init_data i ++ bytes_of_init_data_list il
  end.

Lemma store_init_data_list_loadbytes:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  readbytes_as_zero m b p (init_data_list_size il) ->
  Mem.loadbytes m' b p (init_data_list_size il) = Some (bytes_of_init_data_list il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- apply Mem.loadbytes_empty. lia.
- generalize (init_data_size_pos i1) (init_data_list_size_pos il); intros P1 PL.
  destruct (store_init_data m b p i1) as [m1|] eqn:S; try discriminate.
  apply Mem.loadbytes_concat.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 < p + init_data_size i1).
  eapply store_init_data_list_unchanged; eauto.
  intros; lia.
  intros; lia.
  eapply store_init_data_loadbytes; eauto.
  red; intros; apply H0. lia. lia.
  apply IHil with m1; auto.
  red; intros.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => p + init_data_size i1 <= ofs1).
  eapply store_init_data_unchanged; eauto.
  intros; lia.
  intros; lia.
  apply H0. lia. lia.
  auto. auto.
Qed.

(** Properties related to [load] *)

Definition read_as_zero (m: mem) (b: block) (ofs len: Z) : Prop :=
  forall chunk p,
  ofs <= p -> p + size_chunk chunk <= ofs + len ->
  (align_chunk chunk | p) ->
  Mem.load chunk m b p =
  Some (match chunk with
        | Mint8unsigned | Mint8signed | Mint16unsigned | Mint16signed | Mint32 => Vint Int.zero
        | Mint64 => Vlong Int64.zero
        | Mfloat32 => Vsingle Float32.zero
        | Mfloat64 => Vfloat Float.zero
        | Many32 | Many64 => Vundef
        end).

Remark read_as_zero_unchanged:
  forall (P: block -> Z -> Prop) m b ofs len m',
  read_as_zero m b ofs len ->
  Mem.unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + len -> P b i) ->
  read_as_zero m' b ofs len.
Proof.
  intros; red; intros. eapply Mem.load_unchanged_on; eauto.
  intros; apply H1. lia.
Qed.

Lemma store_zeros_read_as_zero:
  forall m b p n m',
  store_zeros m b p n = Some m' ->
  read_as_zero m' b p n.
Proof.
  intros; red; intros.
  transitivity (Some(decode_val chunk (List.repeat (Byte Byte.zero) (size_chunk_nat chunk)))).
  apply Mem.loadbytes_load; auto. rewrite size_chunk_conv.
  eapply store_zeros_loadbytes; eauto. rewrite <- size_chunk_conv; auto.
  f_equal. destruct chunk; unfold decode_val; unfold decode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity.
Qed.

Fixpoint load_store_init_data (m: mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load Mint8unsigned m b p = Some(Vint(Int.zero_ext 8 n))
      /\ load_store_init_data m b (p + 1) il'
  | Init_int16 n :: il' =>
      Mem.load Mint16unsigned m b p = Some(Vint(Int.zero_ext 16 n))
      /\ load_store_init_data m b (p + 2) il'
  | Init_int32 n :: il' =>
      Mem.load Mint32 m b p = Some(Vint n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_int64 n :: il' =>
      Mem.load Mint64 m b p = Some(Vlong n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_float32 n :: il' =>
      Mem.load Mfloat32 m b p = Some(Vsingle n)
      /\ load_store_init_data m b (p + 4) il'
  | Init_float64 n :: il' =>
      Mem.load Mfloat64 m b p = Some(Vfloat n)
      /\ load_store_init_data m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
      (exists b', find_symbol ge symb = Some b' /\ Mem.load Mptr m b p = Some(Vptr b' ofs))
      /\ load_store_init_data m b (p + size_chunk Mptr) il'
  | Init_space n :: il' =>
      read_as_zero m b p n
      /\ load_store_init_data m b (p + Z.max n 0) il'
  end.

Lemma store_init_data_list_charact:
  forall b il m p m',
  store_init_data_list m b p il = Some m' ->
  read_as_zero m b p (init_data_list_size il) ->
  load_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il = Some m' ->
    Mem.load chunk m' b p = Some(Val.load_result chunk v)).
  {
    intros.
    eapply Mem.load_unchanged_on with (P := fun b' ofs' => ofs' < p + size_chunk chunk).
    eapply store_init_data_list_unchanged; eauto. intros; lia.
    intros; tauto.
    eapply Mem.load_store_same; eauto.
  }
  induction il; simpl.
- auto.
- intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  exploit IHil; eauto.
  set (P := fun (b': block) ofs' => p + init_data_size a <= ofs').
  apply read_as_zero_unchanged with (m := m) (P := P).
  red; intros; apply H0; auto. generalize (init_data_size_pos a); lia. lia.
  eapply store_init_data_unchanged with (P := P); eauto.
  intros; unfold P. lia.
  intros; unfold P. lia.
  intro D.
  destruct a; simpl in Heqo.
+ split; auto. eapply (A Mint8unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint16unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint32 (Vint i)); eauto.
+ split; auto. eapply (A Mint64 (Vlong i)); eauto.
+ split; auto. eapply (A Mfloat32 (Vsingle f)); eauto.
+ split; auto. eapply (A Mfloat64 (Vfloat f)); eauto.
+ split; auto.
  set (P := fun (b': block) ofs' => ofs' < p + init_data_size (Init_space z)).
  inv Heqo. apply read_as_zero_unchanged with (m := m1) (P := P).
  red; intros. apply H0; auto. simpl. generalize (init_data_list_size_pos il); extlia.
  eapply store_init_data_list_unchanged; eauto.
  intros; unfold P. lia.
  intros; unfold P. simpl; extlia.
+ rewrite init_data_size_addrof in *.
  split; auto.
  destruct (find_symbol ge i); try congruence.
  exists b0; split; auto.
  transitivity (Some (Val.load_result Mptr (Vptr b0 i0))).
  eapply (A Mptr (Vptr b0 i0)); eauto.
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto.
Qed.

Remark alloc_global_unchanged:
  forall (P: block -> Z -> Prop) m id g m',
  alloc_global m (id, g) = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct g as [f|v]; simpl in H.
- (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  apply Mem.unchanged_on_trans with m2.
  eapply store_zeros_unchanged; eauto.
  apply Mem.unchanged_on_trans with m3.
  eapply store_init_data_list_unchanged; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
Qed.

Remark alloc_globals_unchanged:
  forall (P: block -> Z -> Prop) gl m m',
  alloc_globals m gl = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  induction gl; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (alloc_global m a) as [m''|] eqn:?; try discriminate.
  destruct a as [id g].
  apply Mem.unchanged_on_trans with m''.
  eapply alloc_global_unchanged; eauto.
  apply IHgl; auto.
Qed.

Remark load_store_init_data_invariant:
  forall m m' b,
  (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) ->
  forall il p,
  load_store_init_data m b p il -> load_store_init_data m' b p il.
Proof.
  induction il; intro p; simpl.
  auto.
  rewrite ! H. destruct a; intuition. red; intros; rewrite H; auto.
Qed.

Definition globals_initialized (g: symtbl) (m: mem) :=
  forall b gd,
  find_info g b = Some gd ->
  match gd with
  | Gfun f =>
         Mem.perm m b 0 Cur Nonempty
      /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty)
  | Gvar v =>
         Mem.range_perm m b 0 (init_data_list_size v.(gvar_init)) Cur (perm_globvar v)
      /\ (forall ofs k p, Mem.perm m b ofs k p ->
            0 <= ofs < init_data_list_size v.(gvar_init) /\ perm_order (perm_globvar v) p)
      /\ (v.(gvar_volatile) = false -> load_store_init_data m b 0 v.(gvar_init))
      /\ (v.(gvar_volatile) = false -> Mem.loadbytes m b 0 (init_data_list_size v.(gvar_init)) = Some (bytes_of_init_data_list v.(gvar_init)))
  end.

Lemma alloc_global_initialized:
  forall g m id gd m',
  genv_sup g = Mem.support m ->
  alloc_global m (id, gd) = Some m' ->
  globals_initialized g m ->
     globals_initialized (add_global g (id, gd)) m'
  /\ genv_sup (add_global g (id, gd)) = Mem.support m'.
Proof.
  intros.
  exploit alloc_global_support; eauto. intros NB. split.
- (* globals-initialized *)
  red; intros. unfold find_info in H2; simpl in H2.
  rewrite NMap.gsspec in H2. destruct (NMap.elt_eq b (fresh_block (genv_sup g))).
+ inv H2. destruct gd0 as [f|v]; simpl in H0.
* destruct (Mem.alloc m 0 1) as [m1 b] eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intros RES. unfold Mem.nextblock in RES.
  rewrite H, <- RES. split.
  eapply Mem.perm_drop_1; eauto. lia.
  intros.
  assert (0 <= ofs < 1). { eapply Mem.perm_alloc_3; eauto. eapply Mem.perm_drop_4; eauto. }
  exploit Mem.perm_drop_2; eauto. intros ORD.
  split. lia. inv ORD; auto.
* set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  exploit Mem.alloc_result; eauto. intro RES. unfold Mem.nextblock in RES.
  replace (fresh_block(genv_sup g)) with b by congruence.
  split. red; intros. eapply Mem.perm_drop_1; eauto.
  split. intros.
  assert (0 <= ofs < sz).
  { eapply Mem.perm_alloc_3; eauto.
    erewrite store_zeros_perm by eauto.
    erewrite store_init_data_list_perm by eauto.
    eapply Mem.perm_drop_4; eauto. }
  split; auto.
  eapply Mem.perm_drop_2; eauto.
  split. intros NOTVOL. apply load_store_init_data_invariant with m3.
  intros. eapply Mem.load_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_charact; eauto.
  eapply store_zeros_read_as_zero; eauto.
  intros NOTVOL.
  transitivity (Mem.loadbytes m3 b 0 sz).
  eapply Mem.loadbytes_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_loadbytes; eauto.
  eapply store_zeros_loadbytes; eauto.
+ assert (U: Mem.unchanged_on (fun _ _ => True) m m') by (eapply alloc_global_unchanged; eauto).
  assert (VALID: Mem.valid_block m b).
  { red. rewrite <- H. eapply genv_info_range; eauto. }
  exploit H1; eauto.
  destruct gd0 as [f|v].
* intros [A B]; split; intros.
  eapply Mem.perm_unchanged_on; eauto. exact I.
  eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
* intros (A & B & C & D). split; [| split; [| split]].
  red; intros. eapply Mem.perm_unchanged_on; eauto. exact I.
  intros. eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
  intros. apply load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_unchanged_on_1; eauto. intros; exact I.
  intros. eapply Mem.loadbytes_unchanged_on; eauto. intros; exact I.
- simpl. unfold Mem.nextblock in NB. congruence.
Qed.

Lemma alloc_globals_initialized:
  forall gl ge m m',
  alloc_globals m gl = Some m' ->
  genv_sup ge = Mem.support m ->
  globals_initialized ge m ->
  globals_initialized (add_globals ge gl) m'.
Proof.
  induction gl; simpl; intros.
- inv H; auto.
- destruct a as [id g]. destruct (alloc_global m (id, g)) as [m1|] eqn:?; try discriminate.
  exploit alloc_global_initialized; eauto. intros [P Q].
  eapply IHgl; eauto.
Qed.

End INITMEM.

Definition init_mem (p: program unit unit) :=
  alloc_globals (symboltbl p) Mem.empty p.(prog_defs).

Lemma init_mem_genv_sup: forall p m,
  init_mem p = Some m ->
  genv_sup (symboltbl p) = Mem.support m.
Proof.
  unfold init_mem; intros.
  exploit alloc_globals_support; eauto. rewrite Mem.support_empty. intro.
  generalize (genv_next_add_globals (prog_defs p) (empty_stbl (prog_public p))).
  fold (symboltbl p). simpl genv_sup. intros. congruence.
Qed.

Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (symboltbl p) id = Some b -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_sup; eauto.
  eapply genv_symb_range; eauto.
Qed.

Lemma init_mem_characterization_gen:
  forall p m,
  init_mem p = Some m ->
  globals_initialized (symboltbl p) (symboltbl p) m.
Proof.
  intros. apply alloc_globals_initialized with Mem.empty. auto.
  rewrite Mem.support_empty. auto.
  red; intros. unfold find_info in H0; simpl in H0;  discriminate.
Qed.

Theorem init_mem_characterization:
  forall p b gv m,
  find_var_info (symboltbl p) b = Some gv ->
  init_mem p = Some m ->
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  /\ (forall ofs k p, Mem.perm m b ofs k p ->
        0 <= ofs < init_data_list_size gv.(gvar_init) /\ perm_order (perm_globvar gv) p)
  /\ (gv.(gvar_volatile) = false ->
      load_store_init_data (symboltbl p) m b 0 gv.(gvar_init))
  /\ (gv.(gvar_volatile) = false ->
      Mem.loadbytes m b 0 (init_data_list_size gv.(gvar_init)) = Some (bytes_of_init_data_list (symboltbl p) gv.(gvar_init))).
Proof.
  intros. rewrite find_var_info_iff in H.
  exploit init_mem_characterization_gen; eauto.
Qed.

(** ** Compatibility with memory injections *)

Section INITMEM_INJ.

Variable ge: symtbl.
Variable s: sup.
Hypothesis symb_inject: forall id b, find_symbol ge id = Some b -> sup_In b s.

Lemma store_zeros_neutral:
  forall m b p n m',
  Mem.inject_neutral s m ->
  sup_In b s ->
  store_zeros m b p n = Some m' ->
  Mem.inject_neutral s m'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros.
  inv H1; auto.
  apply IHo; auto. eapply Mem.store_inject_neutral; eauto. constructor.
  inv H1.
Qed.

Lemma store_init_data_neutral:
  forall m b p id m',
  Mem.inject_neutral s m ->
  sup_In b s ->
  store_init_data ge m b p id = Some m' ->
  Mem.inject_neutral s m'.
Proof.
  intros.
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail).
  congruence.
  destruct (find_symbol ge i) as [b'|] eqn:E; try discriminate.
  eapply Mem.store_inject_neutral; eauto.
  econstructor. unfold Mem.flat_inj. apply pred_dec_true; auto.  eauto.
  rewrite Ptrofs.add_zero. auto.
Qed.

Lemma store_init_data_list_neutral:
  forall b idl m p m',
  Mem.inject_neutral s m ->
  sup_In b s ->
  store_init_data_list ge m b p idl = Some m' ->
  Mem.inject_neutral s m'.
Proof.
  induction idl; simpl; intros.
  congruence.
  destruct (store_init_data ge m b p a) as [m1|] eqn:E; try discriminate.
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto.
Qed.

Lemma alloc_global_neutral:
  forall idg m m',
  alloc_global ge m idg = Some m' ->
  Mem.inject_neutral s m ->
  Mem.sup_include (sup_incr (Mem.support m)) s ->
  Mem.inject_neutral s m'.
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
  (* function *)
  destruct (Mem.alloc m 0 1) as [m1 b] eqn:?.
  assert (b = Mem.nextblock m). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). reflexivity.
  assert (sup_In b s). apply H1. subst b. apply Mem.sup_incr_in1.  auto. subst b.
  eapply Mem.drop_inject_neutral; eauto.
  eapply Mem.alloc_inject_neutral; eauto.
  (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list ge m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (b = Mem.nextblock m). rewrite (Mem.alloc_result _ _ _ _ _ Heqp). reflexivity.
  assert (sup_In b s). apply H1. subst b. apply Mem.sup_incr_in1. auto. subst b.

  eapply Mem.drop_inject_neutral; eauto.
  eapply store_init_data_list_neutral with (m := m2) (b := Mem.nextblock m); eauto.
  eapply store_zeros_neutral with (m := m1); eauto.
  eapply Mem.alloc_inject_neutral; eauto.
Qed.

Remark advance_next_le: forall gl s, Mem.sup_include s (advance_next gl s).
Proof.
  induction gl; simpl; intros.
  apply Mem.sup_include_refl.
  apply Mem.sup_include_trans with (sup_incr s0). intro. intro.  apply Mem.sup_incr_in2. auto.  eauto.
Qed.

Lemma alloc_globals_neutral:
  forall gl m m',
  alloc_globals ge m gl = Some m' ->
  Mem.inject_neutral s m ->
  Mem.sup_include (Mem.support m') s ->
  Mem.inject_neutral s m'.
Proof.
  induction gl; intros.
  simpl in *. congruence.
  exploit alloc_globals_support; eauto. intros EQ.
  simpl in *. destruct (alloc_global ge m a) as [m1|] eqn:E; try discriminate.
  exploit alloc_global_neutral; eauto.
  apply Mem.sup_include_trans with (Mem.support m').
  rewrite EQ. apply advance_next_le. auto.
Qed.

End INITMEM_INJ.

Theorem initmem_inject:
  forall p m,
  init_mem p = Some m ->
  Mem.inject (Mem.flat_inj (Mem.support m)) m m.
Proof.
  unfold init_mem; intros.
  apply Mem.neutral_inject.
  eapply alloc_globals_neutral; eauto.
  intros. exploit find_symbol_not_fresh; eauto.
  apply Mem.empty_inject_neutral.
Qed.

(** ** Sufficient and necessary conditions for the initial memory to exist. *)

(** Alignment properties *)

Definition init_data_alignment (i: init_data) : Z :=
  match i with
  | Init_int8 n => 1
  | Init_int16 n => 2
  | Init_int32 n => 4
  | Init_int64 n => 8
  | Init_float32 n => 4
  | Init_float64 n => 4
  | Init_addrof symb ofs => if Archi.ptr64 then 8 else 4
  | Init_space n => 1
  end.

Fixpoint init_data_list_aligned (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | i1 :: il => (init_data_alignment i1 | p) /\ init_data_list_aligned (p + init_data_size i1) il
  end.

Section INITMEM_INVERSION.

Variable ge: symtbl.

Lemma store_init_data_aligned:
  forall m b p i m',
  store_init_data ge m b p i = Some m' ->
  (init_data_alignment i | p).
Proof.
  intros.
  assert (DFL: forall chunk v,
    Mem.store chunk m b p v = Some m' ->
    align_chunk chunk = init_data_alignment i ->
    (init_data_alignment i | p)).
  { intros. apply Mem.store_valid_access_3 in H0. destruct H0. congruence. }
  destruct i; simpl in H; eauto.
  simpl. apply Z.divide_1_l.
  destruct (find_symbol ge i); try discriminate. eapply DFL. eassumption.
  unfold Mptr, init_data_alignment; destruct Archi.ptr64; auto.
Qed.

Lemma store_init_data_list_aligned:
  forall b il m p m',
  store_init_data_list ge m b p il = Some m' ->
  init_data_list_aligned p il.
Proof.
  induction il as [ | i1 il]; simpl; intros.
- auto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  split; eauto. eapply store_init_data_aligned; eauto.
Qed.

Lemma store_init_data_list_free_idents:
  forall b i o il m p m',
  store_init_data_list ge m b p il = Some m' ->
  In (Init_addrof i o) il ->
  exists b', find_symbol ge i = Some b'.
Proof.
  induction il as [ | i1 il]; simpl; intros.
- contradiction.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  destruct H0.
+ subst i1. simpl in S1. destruct (find_symbol ge i) as [b'|]. exists b'; auto. discriminate.
+ eapply IHil; eauto.
Qed.

End INITMEM_INVERSION.

Theorem init_mem_inversion:
  forall p m id v,
  init_mem p = Some m ->
  In (id, Gvar v) p.(prog_defs) ->
  init_data_list_aligned 0 v.(gvar_init)
  /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol (symboltbl p) i = Some b.
Proof.
  intros until v. unfold init_mem. set (ge := symboltbl p).
  revert m. generalize Mem.empty. generalize (prog_defs p).
  induction l as [ | idg1 defs ]; simpl; intros m m'; intros.
- contradiction.
- destruct (alloc_global ge m idg1) as [m''|] eqn:A; try discriminate.
  destruct H0.
+ subst idg1; simpl in A.
  set (il := gvar_init v) in *. set (sz := init_data_list_size il) in *.
  destruct (Mem.alloc m 0 sz) as [m1 b].
  destruct (store_zeros m1 b 0 sz) as [m2|]; try discriminate.
  destruct (store_init_data_list ge m2 b 0 il) as [m3|] eqn:B; try discriminate.
  split. eapply store_init_data_list_aligned; eauto. intros; eapply store_init_data_list_free_idents; eauto.
+ eapply IHdefs; eauto.
Qed.

Section INITMEM_EXISTS.

Variable ge: symtbl.

Lemma store_zeros_exists:
  forall m b p n,
  Mem.range_perm m b p (p + n) Cur Writable ->
  exists m', store_zeros m b p n = Some m'.
Proof.
  intros until n. functional induction (store_zeros m b p n); intros PERM.
- exists m; auto.
- apply IHo. red; intros. eapply Mem.perm_store_1; eauto. apply PERM. lia.
- destruct (Mem.valid_access_store m Mint8unsigned b p Vzero) as (m' & STORE).
  split. red; intros. apply Mem.perm_cur. apply PERM. simpl in H. lia.
  simpl. apply Z.divide_1_l.
  congruence.
Qed.

Lemma store_init_data_exists:
  forall m b p i,
  Mem.range_perm m b p (p + init_data_size i) Cur Writable ->
  (init_data_alignment i | p) ->
  (forall id ofs, i = Init_addrof id ofs -> exists b, find_symbol ge id = Some b) ->
  exists m', store_init_data ge m b p i = Some m'.
Proof.
  intros.
  assert (DFL: forall chunk v,
          init_data_size i = size_chunk chunk ->
          init_data_alignment i = align_chunk chunk ->
          exists m', Mem.store chunk m b p v = Some m').
  { intros. destruct (Mem.valid_access_store m chunk b p v) as (m' & STORE).
    split. rewrite <- H2; auto. rewrite <- H3; auto.
    exists m'; auto. }
  destruct i; eauto.
  simpl. exists m; auto.
  simpl. exploit H1; eauto. intros (b1 & FS). rewrite FS. eapply DFL.
  unfold init_data_size, Mptr. destruct Archi.ptr64; auto.
  unfold init_data_alignment, Mptr. destruct Archi.ptr64; auto.
Qed.

Lemma store_init_data_list_exists:
  forall b il m p,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
  init_data_list_aligned p il ->
  (forall id ofs, In (Init_addrof id ofs) il -> exists b, find_symbol ge id = Some b) ->
  exists m', store_init_data_list ge m b p il = Some m'.
Proof.
  induction il as [ | i1 il ]; simpl; intros.
- exists m; auto.
- destruct H0.
  destruct (@store_init_data_exists m b p i1) as (m1 & S1); eauto.
  red; intros. apply H. generalize (init_data_list_size_pos il); lia.
  rewrite S1.
  apply IHil; eauto.
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); lia.
Qed.

Lemma alloc_global_exists:
  forall m idg,
  match idg with
  | (id, Gfun f) => True
  | (id, Gvar v) =>
        init_data_list_aligned 0 v.(gvar_init)
     /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol ge i = Some b
  end ->
  exists m', alloc_global ge m idg = Some m'.
Proof.
  intros m [id [f|v]]; intros; simpl.
- destruct (Mem.alloc m 0 1) as [m1 b] eqn:ALLOC.
  destruct (Mem.range_perm_drop_2 m1 b 0 1 Nonempty) as [m2 DROP].
  red; intros; eapply Mem.perm_alloc_2; eauto.
  exists m2; auto.
- destruct H as [P Q].
  set (sz := init_data_list_size (gvar_init v)).
  destruct (Mem.alloc m 0 sz) as [m1 b] eqn:ALLOC.
  assert (P1: Mem.range_perm m1 b 0 sz Cur Freeable) by (red; intros; eapply Mem.perm_alloc_2; eauto).
  destruct (@store_zeros_exists m1 b 0 sz) as [m2 ZEROS].
  red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  rewrite ZEROS.
  assert (P2: Mem.range_perm m2 b 0 sz Cur Freeable).
  { red; intros. erewrite <- store_zeros_perm by eauto. eauto. }
  destruct (@store_init_data_list_exists b (gvar_init v) m2 0) as [m3 STORE]; auto.
  red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  rewrite STORE.
  assert (P3: Mem.range_perm m3 b 0 sz Cur Freeable).
  { red; intros. erewrite <- store_init_data_list_perm by eauto. eauto. }
  destruct (Mem.range_perm_drop_2 m3 b 0 sz (perm_globvar v)) as [m4 DROP]; auto.
  exists m4; auto.
Qed.

End INITMEM_EXISTS.

Theorem init_mem_exists:
  forall p,
  (forall id v, In (id, Gvar v) (prog_defs p) ->
        init_data_list_aligned 0 v.(gvar_init)
     /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol (symboltbl p) i = Some b) ->
  exists m, init_mem p = Some m.
Proof.
  intros. set (ge := symboltbl p) in *.
  unfold init_mem. revert H. generalize (prog_defs p) Mem.empty.
  induction l as [ | idg l]; simpl; intros.
- exists m; auto.
- destruct (@alloc_global_exists ge m idg) as [m1 A1].
  destruct idg as [id [f|v]]; eauto.
  fold ge. rewrite A1. eapply IHl; eauto.
Qed.

End GENV.

(** * Commutation with program transformations *)

Section MATCH_GENVS.

Record match_stbls (f: meminj) (ge1: symtbl) (ge2: symtbl) := {
  mge_public:
    forall id, Genv.public_symbol ge2 id = Genv.public_symbol ge1 id;
  mge_dom:
    forall b1, sup_In b1 (genv_sup ge1) ->
    exists b2, f b1 = Some (b2, 0); (* kept *)
  mge_img:
    forall b2, sup_In b2 (genv_sup ge2) ->
    exists b1, f b1 = Some (b2, 0);
  mge_symb:
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    forall id, (Genv.genv_symb ge1) ! id = Some b1 <-> (Genv.genv_symb ge2) ! id = Some b2;
  mge_info:
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    NMap.get _ b1 ge1.(genv_info) = NMap.get _ b2 ge2.(genv_info);
  mge_separated:
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    sup_In b1 (genv_sup ge1) <-> sup_In b2 (genv_sup ge2)
    (* Pos.le (genv_next ge1) b1 <-> Pos.le (genv_next ge2) b2; clean *)

}.

Record match_genvs {A B V W} (f: meminj) R (ge1: t A V) (ge2: t B W) := {
  mge_stbls :> match_stbls f ge1 ge2;
  mge_defs:
    forall b1 b2 delta, f b1 = Some (b2, delta) ->
    option_rel R (NMap.get _ b1 ge1.(genv_defs)) (NMap.get _ b2 ge2.(genv_defs));
}.

Theorem match_stbls_id ge:
  match_stbls inject_id ge ge.
Proof.
  unfold inject_id. split; eauto.
  - inversion 1. reflexivity.
  - inversion 1. auto.
  - inversion 1. reflexivity.
Qed.

Theorem match_stbls_flat_id ge:  
  match_stbls (Mem.flat_inj (genv_sup ge)) ge ge.
Proof.
  split; intros; eauto; intros; unfold Mem.flat_inj in *.
  - destruct Mem.sup_dec; try congruence. eauto.
  - exists b2. destruct Mem.sup_dec; try congruence.
  - destruct Mem.sup_dec; try congruence. inv H. reflexivity.
  - destruct Mem.sup_dec; try congruence.
  - destruct Mem.sup_dec; try congruence. inv H. reflexivity.
Qed.

Theorem match_stbls_compose f g ge1 ge2 ge3:
  match_stbls f ge1 ge2 ->
  match_stbls g ge2 ge3 ->
  match_stbls (compose_meminj f g) ge1 ge3.
Proof.
  intros H12 H23. split; intros.
  - erewrite !mge_public by eauto. reflexivity.
  - edestruct (mge_dom H12) as (b2 & Hb12); eauto.
    assert (sup_In b2 (genv_sup ge2)).
    { pose proof (mge_separated H12 _ Hb12). apply H0,H. }
    edestruct (mge_dom H23) as (b3 & Hb23); eauto.
    eexists. unfold compose_meminj. rewrite Hb12, Hb23. reflexivity.
  - edestruct (mge_img H23) as (bi & Hbi2); eauto.
    assert (sup_In bi (genv_sup ge2)).
    { pose proof (mge_separated H23 _ Hbi2). apply H0,H. }
    edestruct (mge_img H12) as (b1 & Hb12); eauto.
    eexists. unfold compose_meminj. rewrite Hb12, Hbi2. reflexivity.
  - unfold compose_meminj in H. rename b2 into b3.
    destruct (f b1) as [[b2 delta12] | ] eqn:Hb12; try discriminate.
    destruct (g b2) as [[xb3 delta23] | ] eqn:Hb23; inv H.
    eapply mge_symb in Hb12; eauto.
    eapply mge_symb in Hb23; eauto.
    etransitivity; eauto.
  - unfold compose_meminj in H. rename b2 into b3.
    destruct (f b1) as [[b2 delta12] | ] eqn:Hb12; try discriminate.
    destruct (g b2) as [[xb3 delta23] | ] eqn:Hb23; inv H.
    eapply mge_info in Hb12; eauto.
    eapply mge_info in Hb23; eauto.
    etransitivity; eauto.
  - unfold compose_meminj in H. rename b2 into b3.
    destruct (f b1) as [[b2 delta12] | ] eqn:Hb12; try discriminate.
    destruct (g b2) as [[xb3 delta23] | ] eqn:Hb23; inv H.
    eapply mge_separated in Hb12; eauto.
    eapply mge_separated in Hb23; eauto.
    etransitivity; eauto.
Qed.

Context {f se tse} (Hse: match_stbls f se tse).

Theorem match_stbls_incr f':
  inject_incr f f' ->
  (forall b1 b2 delta, f b1 = None -> f' b1 = Some (b2, delta) ->
   ~sup_In b1 se.(genv_sup) /\ ~sup_In b2 tse.(genv_sup)) ->
  match_stbls f' se tse.
Proof.
  intros Hf' SEP. split.
  - eapply mge_public; eauto.
  - intros. edestruct mge_dom as (b2 & Hb2); eauto.
  - intros. edestruct mge_img as (bi & Hbi); eauto.
  - intros. split.
    + intros Hb1. edestruct mge_dom as (b2' & Hb2'); eauto. eapply genv_symb_range; eauto.
      rewrite (Hf' _ _ _ Hb2') in H. inv H. rewrite <- mge_symb; eauto.
    + intros Hb2. destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
      * rewrite (Hf' _ _ _ Hb) in H. inv H. rewrite mge_symb; eauto.
      * edestruct SEP; eauto. apply genv_symb_range in Hb2. congruence.
  - intros b1 b2 delta Hb'.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
    + rewrite (Hf' _ _ _ Hb) in Hb'. inv Hb'.
      eapply mge_info; eauto.
    + edestruct SEP; eauto.
      destruct (NMap.get _ b1 (genv_info se)) eqn:H1. apply genv_info_range in H1. congruence.
      destruct (NMap.get _ b2 (genv_info tse)) eqn:H2. apply genv_info_range in H2. congruence.
      reflexivity.
  - intros b1 b2 delta Hb'.
    destruct (f b1) as [[xb2 xdelta] | ] eqn:Hb.
    + rewrite (Hf' _ _ _ Hb) in Hb'. inv Hb'.
      eapply mge_separated; eauto.
    + edestruct SEP; eauto. tauto.
Qed.

Theorem find_symbol_match:
  forall id b, Genv.find_symbol se id = Some b ->
  exists tb, f b = Some (tb, 0) /\ Genv.find_symbol tse id = Some tb.
Proof.
  unfold Genv.find_symbol. intros id b Hb.
  edestruct mge_dom as (tb & Htb); eauto.
  - eapply genv_symb_range. eassumption.
  - erewrite mge_symb in Hb; eauto.
Qed.

Theorem valid_for_match sk:
  valid_for sk se <->
  valid_for sk tse.
Proof.
  split.
+ intros H id g Hg.
  edestruct H as (b1 & g' & Hb1 & Hg' & Hgg'); eauto.
  edestruct mge_dom as (b2 & Hb); eauto.
  - eapply genv_symb_range; eauto.
  - unfold find_info, find_symbol in *.
    erewrite mge_info in Hg'; eauto.
    erewrite mge_symb in Hb1; eauto.
+ intros H id g Hg.
  edestruct H as (b2 & g' & Hb2 & Hg' & Hgg'); eauto.
  edestruct mge_img as (b1 & Hb); eauto.
  - eapply genv_symb_range; eauto.
  - unfold find_info, find_symbol in *.
    erewrite <- mge_info in Hg'; eauto.
    erewrite <- mge_symb in Hb2; eauto.
Qed.

Context {A B V W: Type} (R: globdef A V -> globdef B W -> Prop).

Theorem find_def_match_genvs ge tge:
  @match_genvs A B V W f R ge tge ->
  forall b tb delta g,
  find_def ge b = Some g ->
  f b = Some (tb, delta) ->
  exists tg,
  find_def tge tb = Some tg /\
  R g tg /\
  delta = 0.
Proof.
  clear. intros. unfold Genv.find_def in *.
  assert (sup_In b (genv_sup ge)) by eauto using Genv.genv_defs_range.
  edestruct mge_dom; eauto using mge_stbls.
  destruct (mge_defs H b H1); try congruence.
  exists y. intuition eauto; congruence.
Qed.

Local Notation "a # b" := (NMap.get _ b a) (at level 1).

Lemma add_globdef_match:
  forall b1 b2 delta defs1 defs2 id gd1 gd2,
  f b1 = Some (b2, delta) ->
  option_rel R (defs1 # b1) (defs2 # b2) ->
  R gd1 gd2 ->
  option_rel R ((add_globdef se defs1 id gd1) # b1) ((add_globdef tse defs2 id gd2) # b2).
Proof.
  intros until gd2. intros Hb Hdefs Hgd. unfold add_globdef. cbn.
  destruct ((genv_symb se) ! id) as [b1' | ] eqn:Hb1'.
  - edestruct mge_dom as (b2' & Hb'); eauto. eapply genv_symb_range; eauto.
    pose proof Hb1' as Hb2'. erewrite mge_symb in Hb2' by eauto. rewrite Hb2'.
    destruct (eq_block b1' b1); subst.
    + assert (b2' = b2) by congruence; subst.
      rewrite !NMap.gsspec.
      rewrite !pred_dec_true; auto. constructor. auto.
    + assert (b2' <> b2).
      { intro. subst. erewrite <- (mge_symb Hse b1) in Hb2' by eauto. congruence. }
      rewrite !NMap.gsspec, !pred_dec_false. assumption. auto. auto.
  - destruct ((genv_symb tse) ! id) as [b2' | ] eqn:Hb2'; auto.
    destruct (eq_block b2' b2); subst.
    + erewrite <- mge_symb in Hb2' by eauto. congruence.
    + rewrite NMap.gsspec, pred_dec_false. auto. auto.
Qed.

End MATCH_GENVS.

Section MATCH_PROGRAMS.

Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
Variable match_fundef: C -> F1 -> F2 -> Prop.
Variable match_varinfo: V1 -> V2 -> Prop.
Variable ctx: C.
Variable p: program F1 V1.
Variable tp: program F2 V2.
Hypothesis progmatch: match_program_gen match_fundef match_varinfo ctx p tp.
Notation match_idg := (match_ident_globdef match_fundef match_varinfo ctx).
Notation match_gd := (match_globdef match_fundef match_varinfo ctx).

Section INJECT.

Variable j: meminj.
Variable se: symtbl.
Variable tse: symtbl.
Hypothesis sematch: match_stbls j se tse.

Lemma globalenvs_match:
  match_genvs j (match_globdef match_fundef match_varinfo ctx) (globalenv se p) (globalenv tse tp).
Proof.
  intros. split; auto. intros. cbn.
  assert (Hd:forall i, option_rel match_gd (prog_defmap p)!i (prog_defmap tp)!i).
  {
    intro. eapply PTree_Properties.of_list_related. apply progmatch.
  }
  rewrite !PTree.fold_spec.
  apply PTree.elements_canonical_order' in Hd. revert Hd.
  generalize (prog_defmap p), (prog_defmap tp). intros d1 d2 Hd.
(*   cut (option_rel match_gd (PTree.empty _)!b1 (PTree.empty _)!b2). *)
  cut (option_rel match_gd
      (NMap.get _ b1 (NMap.init (option (globdef F1 V1)) None ))
      (NMap.get _ b2 (NMap.init (option (globdef F2 V2)) None ))).
  - generalize (NMap.init (option (globdef F1 V1)) None),
               (NMap.init (option (globdef F2 V2)) None).
    induction Hd as [ | [id1 g1] l1 [id2 g2] l2 [Hi Hg] Hl IH]; cbn in *; eauto.
    intros t1 t2 Ht. eapply IH. eauto. rewrite Hi.
    eapply add_globdef_match; eauto.
  - unfold NMap.get. rewrite !NMap.gi. constructor.
Qed.

Theorem find_def_match:
  forall b tb delta g,
  find_def (globalenv se p) b = Some g ->
  j b = Some (tb, delta) ->
  exists tg,
  find_def (globalenv tse tp) tb = Some tg /\
  match_globdef match_fundef match_varinfo ctx g tg /\
  delta = 0.
Proof.
  apply find_def_match_genvs, globalenvs_match.
Qed.

Theorem find_funct_match:
  forall v tv f,
  find_funct (globalenv se p) v = Some f ->
  Val.inject j v tv ->
  exists cunit tf,
  find_funct (globalenv tse tp) tv = Some tf /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v. inv H0.
  rewrite find_funct_find_funct_ptr in H. unfold find_funct_ptr in H.
  destruct find_def as [[|]|] eqn:Hf; try congruence. inv H.
  edestruct find_def_match as (tg & ? & ? & ?); eauto. subst. inv H0.
  rewrite find_funct_find_funct_ptr. unfold find_funct_ptr. rewrite H. eauto.
Qed.

Theorem find_funct_none:
  forall v tv,
  find_funct (globalenv se p) v = None ->
  Val.inject j v tv ->
  v <> Vundef ->
  find_funct (globalenv tse tp) tv = None.
Proof.
  intros v tv Hf1 INJ Hv. destruct INJ; auto; try congruence.
  destruct (Mem.sup_dec b1 se.(genv_sup)).
  - edestruct mge_dom; eauto. rewrite H1 in H. inv H.
    rewrite Ptrofs.add_zero. revert Hf1.
    unfold find_funct, find_funct_ptr, find_def.
    destruct Ptrofs.eq_dec; auto.
    destruct (mge_defs globalenvs_match b1 H1); auto.
    destruct H; congruence.
  - unfold find_funct, find_funct_ptr, find_def.
    destruct Ptrofs.eq_dec; auto.
    destruct NMap.get as [[|]|] eqn:Hdef; auto. exfalso.
    apply genv_defs_range in Hdef.
    eapply mge_separated in H; eauto. cbn in *.
    apply n,H,Hdef.
Qed.

Theorem is_internal_match `{I1: FundefIsInternal F1} `{I2: FundefIsInternal F2}:
  (forall c f tf, match_fundef c f tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    is_internal (globalenv tse tp) tv = is_internal (globalenv se p) v.
Proof.
  intros Hmatch v tv INJ DEF. unfold is_internal.
  destruct (find_funct _ v) eqn:Hf.
  - edestruct find_funct_match as (c & tf & Htf & ? & ?); try eassumption.
    rewrite Htf. eauto.
  - erewrite find_funct_none; eauto.
Qed.

End INJECT.

Section ID.

Variable se: symtbl.

Theorem find_def_match_id:
  forall g b,
  find_def (globalenv se p) b = Some g ->
  exists tg,
  find_def (globalenv se tp) b = Some tg /\
  match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  intros. edestruct find_def_match as (? & ? & ? & ?); eauto using match_stbls_id.
  reflexivity.
Qed.

Theorem find_funct_match_id:
  forall v f,
  find_funct (globalenv se p) v = Some f ->
  exists cunit tf,
  find_funct (globalenv se tp) v = Some tf /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. eapply find_funct_match; eauto using match_stbls_id.
  apply val_inject_id. auto.
Qed.

Theorem is_internal_match_id `{I1: FundefIsInternal F1} `{I2: FundefIsInternal F2}:
  (forall c f tf, match_fundef c f tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v, is_internal (globalenv se tp) v = is_internal (globalenv se p) v.
Proof.
  intros. destruct v; auto.
  eapply is_internal_match; eauto using match_stbls_id.
  apply val_inject_id; auto. congruence.
Qed.

(*
Lemma alloc_globals_match:
  forall gl1 gl2, list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 ->
  forall m m',
  alloc_globals (globalenv se p) m gl1 = Some m' ->
  alloc_globals (globalenv se tp) m gl2 = Some m'.
Proof.
  induction 1; simpl; intros.
- auto.
- destruct (alloc_global (globalenv p) m a1) as [m1|] eqn:?; try discriminate.
  assert (X: alloc_global (globalenv tp) m b1 = Some m1).
  { destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; destruct H; simpl in *.
    subst id2. inv H2.
  - auto.
  - inv H; simpl in *.
    set (sz := init_data_list_size init) in *.
    destruct (Mem.alloc m 0 sz) as [m2 b] eqn:?.
    destruct (store_zeros m2 b 0 sz) as [m3|] eqn:?; try discriminate.
    destruct (store_init_data_list (globalenv p) m3 b 0 init) as [m4|] eqn:?; try discriminate.
    erewrite store_init_data_list_match; eauto.
  }
  rewrite X; eauto.
Qed.

Theorem init_mem_match:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  unfold init_mem; intros.
  eapply alloc_globals_match; eauto. apply progmatch.
Qed.
*)

End ID.

End MATCH_PROGRAMS.

(** Special case for partial transformations that do not depend on the compilation unit *)

Section TRANSFORM_PARTIAL.

Context {A B V: Type} {LA: Linker A} {LV: Linker V}.
Context {transf: A -> res B} {p: program A V} {tp: program B V}.
Hypothesis progmatch: match_program (fun cu f tf => transf f = OK tf) eq p tp.
Variable j: meminj.
Variable se: symtbl.
Variable tse: symtbl.
Hypothesis sematch: match_stbls j se tse.

Theorem find_funct_transf_partial:
  forall v tv fd,
  Val.inject j v tv ->
  Genv.find_funct (globalenv se p) v = Some fd ->
  exists tfd,
  Genv.find_funct (globalenv tse tp) tv = Some tfd /\ transf fd = OK tfd.
Proof.
  intros. edestruct @find_funct_match as (cu & tf & P & Q & R); eauto.
Qed.

Theorem find_symbol_transf_partial:
  forall (s : ident) (b: block),
  Genv.find_symbol (globalenv se p) s = Some b ->
  exists tb, j b = Some (tb, 0) /\ Genv.find_symbol (globalenv tse tp) s = Some tb.
Proof.
  intros. edestruct @find_symbol_match as (tb & Htb & H'); eauto.
Qed.

Theorem find_funct_transf_partial_id:
  forall v f,
  Genv.find_funct (globalenv se p) v = Some f ->
  exists tf,
  Genv.find_funct (globalenv se tp) v = Some tf /\ transf f = OK tf.
Proof.
  clear tse sematch. intros.
  assert (Val.inject inject_id v v) by (apply val_inject_lessdef; auto).
  edestruct @find_funct_match as (cu & tf & P & Q & R); eauto using match_stbls_id.
Qed.

Theorem is_internal_transf_partial `{I1: FundefIsInternal A} `{I2: FundefIsInternal B}:
  (forall f tf, transf f = OK tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v tv,
    Val.inject j v tv ->
    v <> Vundef ->
    is_internal (globalenv tse tp) tv = is_internal (globalenv se p) v.
Proof.
  intro. apply (is_internal_match progmatch); auto.
Qed.

Theorem is_internal_transf_partial_id `{I1: FundefIsInternal A} `{I2: FundefIsInternal B}:
  (forall f tf, transf f = OK tf ->
   fundef_is_internal tf = fundef_is_internal f) ->
  forall v, is_internal (globalenv se tp) v = is_internal (globalenv se p) v.
Proof.
  intros. destruct v; auto.
  eapply (is_internal_match progmatch); eauto using match_stbls_id.
  apply val_inject_id; auto. congruence.
Qed.

End TRANSFORM_PARTIAL.

(** Special case for total transformations that do not depend on the compilation unit *)

Section TRANSFORM_TOTAL.

Context {A B V: Type} {LA: Linker A} {LV: Linker V}.
Context {transf: A -> B} {p: program A V} {tp: program B V}.
Context {f: meminj} {se tse: symtbl}.
Hypothesis progmatch: match_program (fun cu f tf => tf = transf f) eq p tp.
Hypothesis sematch: match_stbls f se tse.

Theorem find_funct_transf:
  forall v tv fd,
  Val.inject f v tv ->
  Genv.find_funct (globalenv se p) v = Some fd ->
  Genv.find_funct (globalenv tse tp) tv = Some (transf fd).
Proof.
  intros. edestruct @find_funct_match as (cu & tf & P & Q & R); eauto.
  congruence.
Qed.

Theorem find_symbol_transf:
  forall (s : ident) (b: block),
  Genv.find_symbol (globalenv se p) s = Some b ->
  exists tb, f b = Some (tb, 0) /\ Genv.find_symbol (globalenv tse tp) s = Some tb.
Proof.
  intros. edestruct @find_symbol_match as (tb & Htb & H'); eauto.
Qed.

Theorem find_funct_transf_id:
  forall v f,
  Genv.find_funct (globalenv se p) v = Some f ->
  Genv.find_funct (globalenv se tp) v = Some (transf f).
Proof.
  clear tse sematch. intros.
  assert (Val.inject inject_id v v) by (apply val_inject_lessdef; auto).
  edestruct @find_funct_match as (cu & tf & P & Q & R); eauto using match_stbls_id.
  congruence.
Qed.

Theorem is_internal_transf `{I1: FundefIsInternal A} `{I2: FundefIsInternal B}:
  (forall fd, fundef_is_internal (transf fd) = fundef_is_internal fd) ->
  forall v tv, Val.inject f v tv -> v <> Vundef ->
  is_internal (globalenv tse tp) tv = is_internal (globalenv se p) v.
Proof.
  intro. apply (is_internal_match progmatch); auto.
  intros; subst; auto.
Qed.

Theorem is_internal_transf_id `{I1: FundefIsInternal A} `{I2: FundefIsInternal B}:
  (forall fd, fundef_is_internal (transf fd) = fundef_is_internal fd) ->
  forall v, is_internal (globalenv se tp) v = is_internal (globalenv se p) v.
Proof.
  intros. destruct v; auto.
  eapply (is_internal_match progmatch); auto using match_stbls_id.
  intros; subst; auto. apply val_inject_id; auto. congruence.
Qed.

End TRANSFORM_TOTAL.

(** Genv.is_internal is irrelevant to the internal of F *)

Lemma erase_program_is_internal p:
  is_internal

End Genv.

Coercion Genv.to_senv : Genv.t >-> Genv.symtbl.
Hint Resolve Genv.mge_stbls : core.
