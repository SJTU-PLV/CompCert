(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Aug 11th     *)
(* *******************  *)

Require Import Coqlib Maps AST lib.Integers Values.
Require Import Events lib.Floats Memory Smallstep.
Require Import Asm RelocProg RelocProgramBytes RelocElf Globalenvs.
Require Import Stacklayout Conventions.
Require Import Linking Errors.
Require Import EncDecRet RelocElfgen.
Require Import RelocProgSemantics RelocProgSemantics1.
Require Import TranslateInstr RelocProgSemantics2 RelocElfSemantics.

Import Hex Bits.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope hex_scope.
Local Open Scope bits_scope.
Local Open Scope string_byte_scope.

Section WITH_INSTR_SIZE.

Variable instr_size : instruction -> Z.
Variable Instr_size : list Instruction -> Z.


Definition match_prog (p: program) (tp: elf_file) :=
  gen_reloc_elf p = OK tp.

(* encode decode consistency *)

Record program_equiv {F V I D: Type} (p1 p2: RelocProg.program F V I D) :=
  mk_program_equiv {
      pe_symbtable: forall id,
        p1.(prog_symbtable) ! id = p2.(prog_symbtable) ! id;
      pe_sectable: forall id,
          p1.(prog_sectable) ! id = p2.(prog_sectable) ! id;
      pe_reloctable_map: forall id,
          p1.(prog_reloctables) ! id = p2.(prog_reloctables) ! id;
      (* external function *)
      pe_prog_defs: p1.(RelocProg.prog_defs) = p2.(RelocProg.prog_defs);
      (* main function *)
      pe_prog_main: p1.(RelocProg.prog_main) = p2.(RelocProg.prog_main)
    }.

(* most important *)
Lemma gen_reloc_elf_correct: forall p elf,
    gen_reloc_elf p = OK elf ->
    exists p', decode_elf elf = OK p' /\ program_equiv p p'.
Admitted.


Lemma decode_prog_code_section_correct: forall p1 p2 p1',
    program_equiv p1 p2 ->
    decode_prog_code_section instr_size Instr_size p1 = OK p1' ->
    exists p2', decode_prog_code_section instr_size Instr_size p2 = OK p2' /\ program_equiv p1' p2'.
Proof.
  unfold decode_prog_code_section.
  intros.
  monadInv H0. 
  rewrite PTree.fold_spec in *.
  assert ((PTree.elements (prog_sectable p1)) = (PTree.elements (prog_sectable p2))).
  { exploit PTree.elements_extensional.
    intros. exploit (@pe_sectable fundef unit);eauto.
    auto. }
  unfold RelocProgramBytes.section in *.
  rewrite H0 in *. clear H0.
  set (l := (PTree.elements (prog_sectable p2))) in *.
  assert (LEN: exists n, length l = n).
  { clear EQ.
    induction l. exists O. auto.
    destruct IHl.
    exists (S x0). simpl. auto. }
  
  destruct LEN. generalize EQ H0. generalize x0 l x.
  clear l x0 H0 EQ x. 
  induction x0;intros.
  - rewrite length_zero_iff_nil in H0. subst.
    simpl in *. inv EQ.
    eexists. split. eauto. simpl.
    constructor;simpl;auto.
    eapply pe_symbtable;eauto.
    eapply pe_reloctable_map;eauto.
    eapply pe_prog_defs;eauto.
    eapply pe_prog_main;eauto.
  - exploit LocalLib.length_S_inv;eauto.
    intros (l' & a1 & A1 & B1). subst.
    clear H0.
    rewrite fold_left_app in *.
    simpl in *.
    unfold acc_PTree_fold in EQ at 1. monadInv EQ.
    exploit IHx0;eauto.
    intros (p2' & P1 & P2).
    monadInv P1. rewrite EQ1. simpl.
    clear EQ1 EQ0 IHx0.
    assert (acc_decode_code_section instr_size Instr_size
                                    (prog_reloctables p2) (fst a1) (snd a1) = OK x1).
    { unfold acc_decode_code_section in *.
      assert ((PTree.elements (prog_reloctables p1)) = (PTree.elements (prog_reloctables p2))).
      exploit PTree.elements_extensional.
      intros. exploit (@pe_reloctable_map fundef unit);eauto.
      auto.
      destruct ((prog_reloctables p1) ! (fst a1)) eqn: G.
      + apply PTree.elements_correct in G.
        rewrite H0 in G.
        apply PTree.elements_complete in G. rewrite G.
        auto.
      + destruct ((prog_reloctables p2) ! (fst a1)) eqn: G2;auto.
        apply PTree.elements_correct in G2.
        rewrite <- H0 in G2.
        apply PTree.elements_complete in G2.
        congruence. }
    rewrite H0.
    simpl. eexists. split;eauto.
    constructor;simpl;auto.
    eapply pe_symbtable;eauto.
    intros. do 2 rewrite PTree.gsspec.
    destr.
    exploit (@pe_sectable fundef unit);eauto.
    eapply pe_reloctable_map;eauto.
    eapply pe_prog_defs;auto.
    eapply pe_prog_main;eauto.
Qed.

Lemma program_equiv_symbol_address: forall D (p1 p2: RelocProg.program fundef unit instruction D),
    program_equiv p1 p2 ->
    forall id ofs, Genv.symbol_address (RelocProgSemantics.globalenv instr_size p1) id ofs = Genv.symbol_address (RelocProgSemantics.globalenv instr_size p2) id ofs.
Admitted.


Lemma store_init_data_bytes_match_ge: forall n bytes reloctbl m b p ge1 ge2 (MATCHGE: forall i ofs, RelocProgSemantics.Genv.symbol_address ge1 i ofs = RelocProgSemantics.Genv.symbol_address ge2 i ofs),
    length bytes = n ->
    store_init_data_bytes ge1 reloctbl m b p bytes = store_init_data_bytes ge2 reloctbl m b p bytes.
Admitted.

  
Lemma program_equiv_init_mem: forall p1 p2 m,
    program_equiv p1 p2 ->
    init_mem instr_size p1 = Some m ->
    init_mem instr_size p2 = Some m.
Proof.
  unfold init_mem.
  intros. destr_in H0.
  assert (alloc_sections instr_size
      (RelocProgSemantics.globalenv instr_size p2)
      (prog_symbtable p2) (prog_reloctables p2) 
      (prog_sectable p2) Mem.empty = Some m0).
  { unfold alloc_sections in *.
    rewrite PTree.fold_spec in *.
    assert ((PTree.elements (prog_sectable p1)) = (PTree.elements (prog_sectable p2))).
    { exploit PTree.elements_extensional.
      intros. exploit (@pe_sectable fundef unit);eauto.
      auto. }
    unfold RelocProgramBytes.section in *.
    rewrite H1 in *. clear H1.
    set (l := (PTree.elements (prog_sectable p2))) in *.
    assert (LEN: exists n, length l = n).
    { clear Heqo.
      induction l. exists O. auto.
      destruct IHl.
      exists (S x). simpl. auto. }
    clear H0.
    destruct LEN. generalize H0 Heqo. generalize x l m0.
    clear l H0 Heqo x. clear m0 m.
    induction x;intros.
    - rewrite length_zero_iff_nil in H0. subst.
      simpl in *. auto.
    - exploit LocalLib.length_S_inv;eauto.
      intros (l' & a1 & A1 & B1). subst.
      clear H0.
      rewrite fold_left_app in *.
      simpl in *.
      unfold alloc_section in Heqo at 1.
      destr_in Heqo.
      exploit IHx;eauto.
      intros. rewrite H0.
      simpl.
      exploit (@pe_reloctable_map fundef unit);eauto.
      intros. repeat rewrite H1 in *.
      (* program_equiv and globalenv  *)

      clear H1 H0.
      destr.
      + destruct (Mem.alloc_glob).
        destr.
        
        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto.
      + destruct (Mem.alloc_glob).
        destr.
        
        exploit store_init_data_bytes_match_ge.
        intros.
        eapply program_equiv_symbol_address;eauto.
        eauto.
        intros.
        rewrite <- H0. auto. }
  rewrite H1.
  clear H1 Heqo.
  unfold alloc_external_symbols in *.
  rewrite PTree.fold_spec in *.
  rewrite <- H0. f_equal.
  symmetry.
  eapply PTree.elements_extensional.
  eapply pe_symbtable. eauto.
Qed.


Section PRESERVATION. 
(** Transformation *)
Variable prog: program.
Variable tprog: elf_file.
Hypothesis TRANSF: match_prog prog tprog.


Let ge := RelocProgSemantics2.globalenv instr_size Instr_size prog.
Let tge := globalenv instr_size Instr_size tprog.

Lemma transf_initial_state: forall st1 rs,
    RelocProgSemantics2.initial_state instr_size Instr_size prog rs st1 ->
    exists st2, initial_state instr_size Instr_size tprog rs st2 /\ st1 = st2.
  intros st1 rs S1.
  exists st1. split;auto.
  unfold match_prog in TRANSF.
  exploit gen_reloc_elf_correct;eauto. intros (prog' & D1 & E1).  
  econstructor. eapply D1.
  inv S1.

  (* decode_prog_code_section equiv *)
  exploit decode_prog_code_section_correct;eauto.
  intros (p2' & D2 & E2). econstructor.
  eapply D2.

  (* init_mem equal *)
  exploit program_equiv_init_mem;eauto.

  (* initial_state_gen *)
  clear H H0 D2.
  inv H1. unfold rs0,ge0.
  assert ((RelocProg.prog_main prog'0) = (RelocProg.prog_main p2')).
  eapply pe_prog_main;eauto. rewrite H.
  erewrite program_equiv_symbol_address.
  econstructor;eauto. auto.
Qed.


